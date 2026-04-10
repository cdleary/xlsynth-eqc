// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, anyhow, bail};
use serde::{Deserialize, Serialize};
use xlsynth_pir::ir;
use xlsynth_pir::ir_parser;
use xlsynth_pir::ir_utils::fn_node_count;
use xlsynth_pir::node_hashing::compute_function_structural_hash;
use xlsynth_prover::prover;
use xlsynth_prover::prover::Prover;
use xlsynth_prover::prover::SolverChoice;
use xlsynth_prover::prover::types::{AssertionSemantics, EquivParallelism, EquivResult, ProverFn};

const SCHEMA_VERSION: u32 = 2;
const TREE_METADATA: &str = "metadata";
const TREE_MEMBERS: &str = "members";
const TREE_IR_TEXT: &str = "ir_text";
const TREE_TAG_INDEX: &str = "tag_index";
const KEY_SCHEMA_VERSION: &[u8] = b"schema_version";
const KEY_CANONICAL_STRUCTURAL_HASH: &[u8] = b"canonical_structural_hash";
const KEY_EXPECTED_SIGNATURE: &[u8] = b"expected_signature";
const IR_TEXT_ZSTD_MAGIC: &[u8] = b"EQCIRTXT1";
const IR_NODE_COUNT_TAG_PREFIX: &str = "ir-nodes:";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofOptions {
    pub solver: SolverChoice,
    pub tool_path: Option<PathBuf>,
}

impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            solver: SolverChoice::Auto,
            tool_path: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredMember {
    pub structural_hash: String,
    pub package_name: String,
    pub top_name: String,
    pub ir_text: String,
    pub metadata: MemberMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemberMetadata {
    pub tags: BTreeSet<String>,
    pub provenance: Option<String>,
    pub added_at_utc_secs: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewMemberMetadata {
    pub tags: BTreeSet<String>,
    pub provenance: Option<String>,
    pub added_at_utc_secs: Option<u64>,
}

impl Default for NewMemberMetadata {
    fn default() -> Self {
        Self {
            tags: BTreeSet::new(),
            provenance: None,
            added_at_utc_secs: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagCount {
    pub tag: String,
    pub count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddOutcome {
    Seeded { structural_hash: String },
    Added { structural_hash: String },
}

impl AddOutcome {
    pub fn structural_hash(&self) -> &str {
        match self {
            AddOutcome::Seeded { structural_hash } | AddOutcome::Added { structural_hash } => {
                structural_hash
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TryAddOutcome {
    Added { structural_hash: String },
    AlreadyContained { structural_hash: String },
}

impl TryAddOutcome {
    pub fn structural_hash(&self) -> &str {
        match self {
            TryAddOutcome::Added { structural_hash }
            | TryAddOutcome::AlreadyContained { structural_hash } => structural_hash,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationReport {
    pub compared_against: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvariantReport {
    pub member_count: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct StoredMemberValue {
    package_name: String,
    top_name: String,
    #[serde(default)]
    metadata: StoredMemberMetadataValue,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
struct StoredMemberMetadataValue {
    #[serde(default)]
    tags: BTreeSet<String>,
    #[serde(default)]
    provenance: Option<String>,
    #[serde(default)]
    added_at_utc_secs: u64,
}

#[derive(Debug, Clone)]
struct LoadedIr {
    origin: String,
    package: ir::Package,
    package_name: String,
    top_name: String,
    signature: String,
    structural_hash: String,
    canonical_ir_text: String,
}

impl LoadedIr {
    fn from_ir_text(
        ir_text: &str,
        top_override: Option<&str>,
        origin: impl Into<String>,
    ) -> Result<Self> {
        let origin = origin.into();
        let mut parser = ir_parser::Parser::new(ir_text);
        let mut package = parser
            .parse_and_validate_package()
            .map_err(|e| anyhow!("failed to parse/validate {origin}: {e}"))?;

        if let Some(top_name) = top_override {
            package.set_top_fn(top_name).map_err(|e| {
                anyhow!("failed to select top function '{top_name}' in {origin}: {e}")
            })?;
        }

        let top_fn = package
            .get_top_fn()
            .ok_or_else(|| anyhow!("{origin} does not contain a top function"))?;
        let top_name = top_fn.name.clone();
        let signature = format_ir_fn_signature(top_fn);
        let package_name = package.name.clone();
        let structural_hash = hash_to_hex(compute_function_structural_hash(top_fn).as_bytes());
        let canonical_ir_text = package.to_string();
        Ok(Self {
            origin,
            package,
            package_name,
            top_name,
            signature,
            structural_hash,
            canonical_ir_text,
        })
    }

    fn from_path(path: &Path, top_override: Option<&str>) -> Result<Self> {
        let ir_text = fs::read_to_string(path)
            .with_context(|| format!("failed to read IR file {}", path.display()))?;
        Self::from_ir_text(&ir_text, top_override, path.display().to_string())
    }

    fn from_stored_member(member: &StoredMember) -> Result<Self> {
        Self::from_ir_text(
            &member.ir_text,
            Some(&member.top_name),
            format!("stored member {}", member.structural_hash),
        )
    }

    fn top_fn(&self) -> &ir::Fn {
        self.package
            .get_top_fn()
            .expect("loaded IR package lost top function")
    }

    fn stored_value(&self, metadata: StoredMemberMetadataValue) -> StoredMemberValue {
        StoredMemberValue {
            package_name: self.package_name.clone(),
            top_name: self.top_name.clone(),
            metadata,
        }
    }
}

pub struct EquivalenceClassDb {
    db: sled::Db,
}

impl EquivalenceClassDb {
    pub fn init(path: &Path) -> Result<Self> {
        let db = open_db(path)?;
        let this = Self { db };
        this.ensure_initialized()?;
        Ok(this)
    }

    pub fn open(path: &Path) -> Result<Self> {
        if !path.exists() {
            bail!(
                "equivalence-class database does not exist at {}",
                path.display()
            );
        }
        let db = open_db(path)?;
        let this = Self { db };
        this.ensure_initialized()?;
        Ok(this)
    }

    pub fn len(&self) -> Result<usize> {
        Ok(self.members_tree()?.len())
    }

    pub fn expected_signature(&self) -> Result<Option<String>> {
        if let Some(existing) = self.read_expected_signature()? {
            return Ok(Some(existing));
        }

        let expected_signature = self.select_expected_signature_from_members()?;
        self.write_expected_signature(expected_signature.as_deref())?;
        self.db
            .flush()
            .context("flushing expected signature metadata")?;
        Ok(expected_signature)
    }

    pub fn set_expected_signature(&self, expected_signature: &str) -> Result<()> {
        let expected_signature = normalize_expected_signature(expected_signature)?;
        if let Some(existing) = self.read_expected_signature()? {
            if existing != expected_signature {
                bail!(
                    "equivalence-class expected signature mismatch: existing {} new {}",
                    existing,
                    expected_signature
                );
            }
            return Ok(());
        }

        if let Some(existing_member_signature) = self.select_expected_signature_from_members()? {
            if existing_member_signature != expected_signature {
                bail!(
                    "equivalence-class members use signature {} which does not match requested {}",
                    existing_member_signature,
                    expected_signature
                );
            }
        }

        self.write_expected_signature(Some(&expected_signature))?;
        self.db
            .flush()
            .context("flushing expected signature metadata")?;
        Ok(())
    }

    pub fn list_members(&self) -> Result<Vec<StoredMember>> {
        let tree = self.members_tree()?;
        let ir_text_tree = self.ir_text_tree()?;
        let mut members = Vec::with_capacity(tree.len());
        for row in &tree {
            let (key, value) = row.context("reading member row from sled")?;
            members.push(decode_member_row(&key, &value, &ir_text_tree)?);
        }
        Ok(members)
    }

    pub fn list_members_filtered_by_tags(
        &self,
        required_tags: &[String],
    ) -> Result<Vec<StoredMember>> {
        let normalized_tags = normalize_tags(required_tags)?;
        if normalized_tags.is_empty() {
            return self.list_members();
        }

        let tag_index = self.tag_index_tree()?;
        let mut matching_hashes: Option<BTreeSet<String>> = None;
        for tag in normalized_tags {
            let mut tag_hashes = BTreeSet::new();
            for row in tag_index.scan_prefix(tag_index_prefix(&tag)) {
                let (key, _) = row.context("reading tag index row from sled")?;
                let (_, structural_hash) = decode_tag_index_key(&key)?;
                tag_hashes.insert(structural_hash);
            }
            matching_hashes = Some(match matching_hashes {
                None => tag_hashes,
                Some(existing) => existing.intersection(&tag_hashes).cloned().collect(),
            });
            if matching_hashes.as_ref().is_some_and(BTreeSet::is_empty) {
                return Ok(Vec::new());
            }
        }

        let members_tree = self.members_tree()?;
        let ir_text_tree = self.ir_text_tree()?;
        let mut members = Vec::new();
        for structural_hash in matching_hashes.unwrap_or_default() {
            let value = members_tree
                .get(structural_hash.as_bytes())
                .with_context(|| format!("loading member {structural_hash} from sled"))?
                .ok_or_else(|| anyhow!("tag index referenced missing member {structural_hash}"))?;
            members.push(decode_member_row(
                structural_hash.as_bytes(),
                &value,
                &ir_text_tree,
            )?);
        }
        Ok(members)
    }

    pub fn list_tags(&self) -> Result<Vec<TagCount>> {
        let tag_index = self.tag_index_tree()?;
        let mut counts = BTreeMap::<String, usize>::new();
        for row in &tag_index {
            let (key, _) = row.context("reading tag index row from sled")?;
            let (tag, _) = decode_tag_index_key(&key)?;
            *counts.entry(tag).or_default() += 1;
        }
        Ok(counts
            .into_iter()
            .map(|(tag, count)| TagCount { tag, count })
            .collect())
    }

    pub fn contains_ir_path(&self, ir_path: &Path, top_override: Option<&str>) -> Result<bool> {
        let loaded = LoadedIr::from_path(ir_path, top_override)?;
        self.contains_structural_hash(&loaded.structural_hash)
    }

    pub fn contains_structural_hash(&self, structural_hash: &str) -> Result<bool> {
        Ok(self
            .members_tree()?
            .contains_key(structural_hash.as_bytes())
            .with_context(|| format!("checking whether hash {structural_hash} exists"))?)
    }

    pub fn validate_ir_path(
        &self,
        ir_path: &Path,
        top_override: Option<&str>,
        proof_options: &ProofOptions,
    ) -> Result<ValidationReport> {
        let candidate = LoadedIr::from_path(ir_path, top_override)?;
        self.validate_loaded(&candidate, proof_options)
    }

    pub fn add_ir_path(
        &self,
        ir_path: &Path,
        top_override: Option<&str>,
        proof_options: &ProofOptions,
    ) -> Result<AddOutcome> {
        self.add_ir_path_with_metadata(
            ir_path,
            top_override,
            &NewMemberMetadata::default(),
            proof_options,
        )
    }

    pub fn add_ir_path_with_metadata(
        &self,
        ir_path: &Path,
        top_override: Option<&str>,
        metadata: &NewMemberMetadata,
        proof_options: &ProofOptions,
    ) -> Result<AddOutcome> {
        let candidate = LoadedIr::from_path(ir_path, top_override)?;
        self.add_loaded(candidate, metadata, proof_options)
    }

    pub fn try_add_ir_path(
        &self,
        ir_path: &Path,
        top_override: Option<&str>,
        proof_options: &ProofOptions,
    ) -> Result<TryAddOutcome> {
        self.try_add_ir_path_with_metadata(
            ir_path,
            top_override,
            &NewMemberMetadata::default(),
            proof_options,
        )
    }

    pub fn try_add_ir_path_with_metadata(
        &self,
        ir_path: &Path,
        top_override: Option<&str>,
        metadata: &NewMemberMetadata,
        proof_options: &ProofOptions,
    ) -> Result<TryAddOutcome> {
        let candidate = LoadedIr::from_path(ir_path, top_override)?;
        if self.contains_structural_hash(&candidate.structural_hash)? {
            return Ok(TryAddOutcome::AlreadyContained {
                structural_hash: candidate.structural_hash,
            });
        }
        let added = self.add_loaded(candidate, metadata, proof_options)?;
        Ok(TryAddOutcome::Added {
            structural_hash: added.structural_hash().to_string(),
        })
    }

    pub fn check_invariants(&self, proof_options: &ProofOptions) -> Result<InvariantReport> {
        let members = self.list_members()?;
        let expected_signature = self.expected_signature()?;
        if members.len() <= 1 {
            if let Some(member) = members.first() {
                let loaded = LoadedIr::from_stored_member(member)?;
                if loaded.structural_hash != member.structural_hash {
                    bail!(
                        "stored hash mismatch for {}: key={} recomputed={}",
                        loaded.origin,
                        member.structural_hash,
                        loaded.structural_hash
                    );
                }
                if let Some(expected_signature) = expected_signature.as_ref() {
                    ensure_signature_matches(expected_signature, &loaded)?;
                }
            }
            return Ok(InvariantReport {
                member_count: members.len(),
            });
        }

        let canonical_hash = self
            .canonical_structural_hash()?
            .ok_or_else(|| anyhow!("missing canonical member for non-empty equivalence class"))?;

        let mut canonical = None;
        let mut other_members = Vec::with_capacity(members.len().saturating_sub(1));
        let mut actual_hashes = BTreeSet::new();
        for member in &members {
            let loaded = LoadedIr::from_stored_member(member)?;
            if loaded.structural_hash != member.structural_hash {
                bail!(
                    "stored hash mismatch for {}: key={} recomputed={}",
                    loaded.origin,
                    member.structural_hash,
                    loaded.structural_hash
                );
            }
            if !actual_hashes.insert(loaded.structural_hash.clone()) {
                bail!(
                    "duplicate structural hash detected in corpus: {}",
                    loaded.structural_hash
                );
            }
            if let Some(expected_signature) = expected_signature.as_ref() {
                ensure_signature_matches(expected_signature, &loaded)?;
            }
            if member.structural_hash == canonical_hash {
                canonical = Some(loaded);
            } else {
                other_members.push(loaded);
            }
        }

        let canonical = canonical.ok_or_else(|| {
            anyhow!(
                "canonical member {} was not found in the corpus",
                canonical_hash
            )
        })?;
        let prover = make_prover(proof_options);
        for member in &other_members {
            ensure_equivalent(
                &*prover,
                &canonical,
                member,
                &format!("stored canonical member {}", canonical.structural_hash),
                &format!("stored member {}", member.structural_hash),
            )?;
        }

        Ok(InvariantReport {
            member_count: members.len(),
        })
    }

    fn add_loaded(
        &self,
        candidate: LoadedIr,
        metadata: &NewMemberMetadata,
        proof_options: &ProofOptions,
    ) -> Result<AddOutcome> {
        if self.contains_structural_hash(&candidate.structural_hash)? {
            bail!(
                "structural hash {} is already contained in the equivalence class",
                candidate.structural_hash
            );
        }

        let existing_len = self.len()?;
        self.ensure_expected_signature_matches(&candidate)?;
        if existing_len > 0 {
            self.validate_loaded(&candidate, proof_options)?;
        }

        self.insert_member(&candidate, normalize_new_member_metadata(metadata)?)?;
        if existing_len == 0 && self.read_expected_signature()?.is_none() {
            self.write_expected_signature(Some(&candidate.signature))?;
        }
        self.db
            .flush()
            .context("flushing member and expected signature metadata")?;
        Ok(if existing_len == 0 {
            AddOutcome::Seeded {
                structural_hash: candidate.structural_hash,
            }
        } else {
            AddOutcome::Added {
                structural_hash: candidate.structural_hash,
            }
        })
    }

    fn validate_loaded(
        &self,
        candidate: &LoadedIr,
        proof_options: &ProofOptions,
    ) -> Result<ValidationReport> {
        self.ensure_expected_signature_matches(candidate)?;
        let members = self.list_members()?;
        if members.is_empty() {
            bail!("cannot validate against an empty equivalence class");
        }

        let canonical_hash = self
            .canonical_structural_hash()?
            .ok_or_else(|| anyhow!("missing canonical member for non-empty equivalence class"))?;
        let prover = make_prover(proof_options);
        let stored = self
            .member_by_structural_hash(&canonical_hash)?
            .ok_or_else(|| anyhow!("missing canonical member {}", canonical_hash))?;
        let stored = LoadedIr::from_stored_member(&stored)?;
        ensure_equivalent(
            &*prover,
            candidate,
            &stored,
            &candidate.origin,
            &format!("stored canonical member {canonical_hash}"),
        )?;

        Ok(ValidationReport {
            compared_against: 1,
        })
    }

    fn ensure_initialized(&self) -> Result<()> {
        let tree = self.metadata_tree()?;
        match tree
            .get(KEY_SCHEMA_VERSION)
            .context("reading schema version")?
        {
            Some(existing) => {
                let version = decode_schema_version(existing.as_ref())?;
                if version != SCHEMA_VERSION {
                    bail!(
                        "unsupported schema version in equivalence-class database: expected {} got {}",
                        SCHEMA_VERSION,
                        version
                    );
                }
            }
            None => {
                tree.insert(KEY_SCHEMA_VERSION, &SCHEMA_VERSION.to_be_bytes())
                    .context("writing schema version")?;
                self.db.flush().context("flushing schema metadata")?;
            }
        }
        Ok(())
    }

    fn insert_member(
        &self,
        candidate: &LoadedIr,
        metadata: StoredMemberMetadataValue,
    ) -> Result<()> {
        let metadata = with_derived_member_tags(candidate, metadata);
        let tree = self.members_tree()?;
        let ir_text_tree = self.ir_text_tree()?;
        let tag_index = self.tag_index_tree()?;
        let value = serde_json::to_vec(&candidate.stored_value(metadata.clone()))
            .context("serializing member metadata for sled storage")?;
        tree.insert(candidate.structural_hash.as_bytes(), value)
            .with_context(|| format!("inserting member {}", candidate.structural_hash))?;
        ir_text_tree
            .insert(
                candidate.structural_hash.as_bytes(),
                encode_ir_text_value(candidate.canonical_ir_text.as_bytes())?,
            )
            .with_context(|| format!("inserting IR text {}", candidate.structural_hash))?;
        for tag in &metadata.tags {
            tag_index
                .insert(tag_index_key(tag, &candidate.structural_hash), &[][..])
                .with_context(|| {
                    format!(
                        "inserting tag index row for tag={} hash={}",
                        tag, candidate.structural_hash
                    )
                })?;
        }
        self.promote_canonical_member_if_better(candidate, &metadata)?;
        self.db.flush().context("flushing member insert")?;
        Ok(())
    }

    fn canonical_structural_hash(&self) -> Result<Option<String>> {
        if let Some(existing) = self.read_canonical_structural_hash()? {
            if self
                .members_tree()?
                .contains_key(existing.as_bytes())
                .with_context(|| format!("checking canonical member {}", existing))?
            {
                return Ok(Some(existing));
            }
        }

        let canonical = self.select_canonical_structural_hash()?;
        self.write_canonical_structural_hash(canonical.as_deref())?;
        self.db
            .flush()
            .context("flushing canonical member metadata")?;
        Ok(canonical)
    }

    fn read_canonical_structural_hash(&self) -> Result<Option<String>> {
        let Some(bytes) = self
            .metadata_tree()?
            .get(KEY_CANONICAL_STRUCTURAL_HASH)
            .context("reading canonical member hash")?
        else {
            return Ok(None);
        };
        let hash = std::str::from_utf8(bytes.as_ref())
            .context("canonical member hash was not valid UTF-8")?
            .to_string();
        Ok(Some(hash))
    }

    fn read_expected_signature(&self) -> Result<Option<String>> {
        let Some(bytes) = self
            .metadata_tree()?
            .get(KEY_EXPECTED_SIGNATURE)
            .context("reading expected signature")?
        else {
            return Ok(None);
        };
        Ok(Some(
            std::str::from_utf8(bytes.as_ref())
                .context("expected signature was not valid UTF-8")?
                .to_string(),
        ))
    }

    fn write_canonical_structural_hash(&self, structural_hash: Option<&str>) -> Result<()> {
        let tree = self.metadata_tree()?;
        match structural_hash {
            Some(structural_hash) => {
                tree.insert(KEY_CANONICAL_STRUCTURAL_HASH, structural_hash.as_bytes())
                    .with_context(|| {
                        format!("writing canonical member hash {}", structural_hash)
                    })?;
            }
            None => {
                tree.remove(KEY_CANONICAL_STRUCTURAL_HASH)
                    .context("clearing canonical member hash")?;
            }
        }
        Ok(())
    }

    fn write_expected_signature(&self, expected_signature: Option<&str>) -> Result<()> {
        let tree = self.metadata_tree()?;
        match expected_signature {
            Some(expected_signature) => {
                tree.insert(KEY_EXPECTED_SIGNATURE, expected_signature.as_bytes())
                    .with_context(|| {
                        format!("writing expected signature {}", expected_signature)
                    })?;
            }
            None => {
                tree.remove(KEY_EXPECTED_SIGNATURE)
                    .context("clearing expected signature")?;
            }
        }
        Ok(())
    }

    fn select_canonical_structural_hash(&self) -> Result<Option<String>> {
        let members = self.members_tree()?;
        let ir_text_tree = self.ir_text_tree()?;
        let mut best: Option<(String, usize)> = None;
        for row in &members {
            let (key, value) = row.context("reading member row from sled")?;
            let structural_hash = std::str::from_utf8(key.as_ref())
                .context("member key was not valid UTF-8")?
                .to_string();
            let value: StoredMemberValue = serde_json::from_slice(value.as_ref())
                .context("deserializing member metadata while selecting canonical member")?;
            let node_count =
                stored_member_node_count(&structural_hash, &value.metadata, &ir_text_tree)?;
            match &best {
                Some((best_hash, best_node_count))
                    if !is_better_canonical_candidate(
                        &structural_hash,
                        node_count,
                        best_hash,
                        *best_node_count,
                    ) => {}
                _ => best = Some((structural_hash, node_count)),
            }
        }
        Ok(best.map(|(structural_hash, _)| structural_hash))
    }

    fn promote_canonical_member_if_better(
        &self,
        candidate: &LoadedIr,
        metadata: &StoredMemberMetadataValue,
    ) -> Result<()> {
        let candidate_node_count = stored_member_node_count_from_tags(&metadata.tags)?
            .unwrap_or_else(|| fn_node_count(candidate.top_fn()));
        let current_hash = self.canonical_structural_hash()?;
        let promote = match current_hash {
            Some(current_hash) if current_hash != candidate.structural_hash => {
                match self.member_node_count_by_hash(&current_hash)? {
                    Some(current_node_count) => is_better_canonical_candidate(
                        &candidate.structural_hash,
                        candidate_node_count,
                        &current_hash,
                        current_node_count,
                    ),
                    None => true,
                }
            }
            Some(_) => false,
            None => true,
        };
        if promote {
            self.write_canonical_structural_hash(Some(&candidate.structural_hash))?;
        }
        Ok(())
    }

    fn member_by_structural_hash(&self, structural_hash: &str) -> Result<Option<StoredMember>> {
        let member_row = self
            .members_tree()?
            .get(structural_hash.as_bytes())
            .with_context(|| format!("loading member {}", structural_hash))?;
        let Some(member_row) = member_row else {
            return Ok(None);
        };
        let ir_text_tree = self.ir_text_tree()?;
        Ok(Some(decode_member_row(
            structural_hash.as_bytes(),
            member_row.as_ref(),
            &ir_text_tree,
        )?))
    }

    fn member_node_count_by_hash(&self, structural_hash: &str) -> Result<Option<usize>> {
        let member_row = self
            .members_tree()?
            .get(structural_hash.as_bytes())
            .with_context(|| format!("loading member metadata for {}", structural_hash))?;
        let Some(member_row) = member_row else {
            return Ok(None);
        };
        let value: StoredMemberValue = serde_json::from_slice(member_row.as_ref())
            .with_context(|| format!("deserializing member metadata for {}", structural_hash))?;
        let ir_text_tree = self.ir_text_tree()?;
        Ok(Some(stored_member_node_count(
            structural_hash,
            &value.metadata,
            &ir_text_tree,
        )?))
    }

    fn select_expected_signature_from_members(&self) -> Result<Option<String>> {
        let mut members = self.list_members()?.into_iter();
        let Some(member) = members.next() else {
            return Ok(None);
        };
        let loaded = LoadedIr::from_stored_member(&member)?;
        Ok(Some(loaded.signature))
    }

    fn ensure_expected_signature_matches(&self, candidate: &LoadedIr) -> Result<()> {
        if let Some(expected_signature) = self.expected_signature()? {
            ensure_signature_matches(&expected_signature, candidate)?;
        }
        Ok(())
    }

    fn metadata_tree(&self) -> Result<sled::Tree> {
        self.db
            .open_tree(TREE_METADATA)
            .context("opening metadata tree")
    }

    fn members_tree(&self) -> Result<sled::Tree> {
        self.db
            .open_tree(TREE_MEMBERS)
            .context("opening members tree")
    }

    fn ir_text_tree(&self) -> Result<sled::Tree> {
        self.db
            .open_tree(TREE_IR_TEXT)
            .context("opening IR text tree")
    }

    fn tag_index_tree(&self) -> Result<sled::Tree> {
        self.db
            .open_tree(TREE_TAG_INDEX)
            .context("opening tag index tree")
    }
}

fn open_db(path: &Path) -> Result<sled::Db> {
    sled::Config::new()
        .path(path)
        .open()
        .with_context(|| format!("opening sled database at {}", path.display()))
}

fn decode_schema_version(bytes: &[u8]) -> Result<u32> {
    let version_bytes: [u8; 4] = bytes
        .try_into()
        .map_err(|_| anyhow!("invalid schema version encoding"))?;
    Ok(u32::from_be_bytes(version_bytes))
}

fn decode_member_row(key: &[u8], value: &[u8], ir_text_tree: &sled::Tree) -> Result<StoredMember> {
    let structural_hash = std::str::from_utf8(key)
        .context("member key was not valid UTF-8")?
        .to_string();
    let value: StoredMemberValue =
        serde_json::from_slice(value).context("deserializing stored member metadata value")?;
    Ok(StoredMember {
        structural_hash,
        package_name: value.package_name,
        top_name: value.top_name,
        ir_text: load_ir_text(ir_text_tree, key)?,
        metadata: decode_member_metadata(value.metadata),
    })
}

fn decode_member_metadata(value: StoredMemberMetadataValue) -> MemberMetadata {
    MemberMetadata {
        tags: value.tags,
        provenance: value.provenance,
        added_at_utc_secs: value.added_at_utc_secs,
    }
}

fn normalize_new_member_metadata(
    metadata: &NewMemberMetadata,
) -> Result<StoredMemberMetadataValue> {
    let tags = metadata
        .tags
        .iter()
        .map(|tag| normalize_tag(tag))
        .collect::<Result<BTreeSet<_>>>()?;
    let provenance = normalize_optional_string(metadata.provenance.as_deref());
    let added_at_utc_secs = metadata.added_at_utc_secs.unwrap_or_else(now_utc_secs);
    Ok(StoredMemberMetadataValue {
        tags,
        provenance,
        added_at_utc_secs,
    })
}

fn with_derived_member_tags(
    candidate: &LoadedIr,
    mut metadata: StoredMemberMetadataValue,
) -> StoredMemberMetadataValue {
    metadata.tags.insert(ir_node_count_tag(candidate.top_fn()));
    metadata
}

fn stored_member_node_count(
    structural_hash: &str,
    metadata: &StoredMemberMetadataValue,
    ir_text_tree: &sled::Tree,
) -> Result<usize> {
    if let Some(node_count) = stored_member_node_count_from_tags(&metadata.tags)? {
        return Ok(node_count);
    }

    let ir_text = load_ir_text(ir_text_tree, structural_hash.as_bytes())?;
    let loaded =
        LoadedIr::from_ir_text(&ir_text, None, format!("stored member {}", structural_hash))?;
    Ok(fn_node_count(loaded.top_fn()))
}

fn stored_member_node_count_from_tags(tags: &BTreeSet<String>) -> Result<Option<usize>> {
    let mut node_counts = tags
        .iter()
        .filter_map(|tag| tag.strip_prefix(IR_NODE_COUNT_TAG_PREFIX));
    let Some(first) = node_counts.next() else {
        return Ok(None);
    };
    let node_count = first
        .parse::<usize>()
        .with_context(|| format!("invalid IR node count tag value: {first}"))?;
    if let Some(second) = node_counts.next() {
        bail!(
            "multiple IR node count tags present: {}{}, {}",
            IR_NODE_COUNT_TAG_PREFIX,
            first,
            second
        );
    }
    Ok(Some(node_count))
}

fn ir_node_count_tag(ir_fn: &ir::Fn) -> String {
    format!("{IR_NODE_COUNT_TAG_PREFIX}{}", fn_node_count(ir_fn))
}

fn format_ir_fn_signature(ir_fn: &ir::Fn) -> String {
    let fn_type = ir_fn.get_type();
    let params = fn_type
        .param_types
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    format!("({params}) -> {}", fn_type.return_type)
}

fn normalize_expected_signature(expected_signature: &str) -> Result<String> {
    let expected_signature = expected_signature.trim();
    if expected_signature.is_empty() {
        bail!("expected signature cannot be empty");
    }
    if expected_signature.contains('\0') {
        bail!("expected signature cannot contain NUL bytes");
    }
    Ok(expected_signature.to_string())
}

fn ensure_signature_matches(expected_signature: &str, loaded: &LoadedIr) -> Result<()> {
    if loaded.signature != expected_signature {
        bail!(
            "top signature mismatch for {}: expected {} got {}",
            loaded.origin,
            expected_signature,
            loaded.signature
        );
    }
    Ok(())
}

fn is_better_canonical_candidate(
    candidate_hash: &str,
    candidate_node_count: usize,
    current_hash: &str,
    current_node_count: usize,
) -> bool {
    candidate_node_count < current_node_count
        || (candidate_node_count == current_node_count && candidate_hash < current_hash)
}

fn encode_ir_text_value(raw_bytes: &[u8]) -> Result<Vec<u8>> {
    let compressed = zstd::bulk::compress(raw_bytes, 3).context("zstd compressing IR text")?;
    let framed_len = IR_TEXT_ZSTD_MAGIC.len() + compressed.len();
    if framed_len >= raw_bytes.len() {
        return Ok(raw_bytes.to_vec());
    }
    let mut encoded = Vec::with_capacity(framed_len);
    encoded.extend_from_slice(IR_TEXT_ZSTD_MAGIC);
    encoded.extend_from_slice(&compressed);
    Ok(encoded)
}

fn decode_ir_text_value(stored_bytes: &[u8]) -> Result<String> {
    let decoded = match stored_bytes.strip_prefix(IR_TEXT_ZSTD_MAGIC) {
        Some(payload) => {
            zstd::stream::decode_all(Cursor::new(payload)).context("zstd decoding IR text")?
        }
        None => stored_bytes.to_vec(),
    };
    String::from_utf8(decoded).context("stored IR text was not valid UTF-8")
}

fn load_ir_text(ir_text_tree: &sled::Tree, key: &[u8]) -> Result<String> {
    let structural_hash = std::str::from_utf8(key)
        .context("member key was not valid UTF-8")?
        .to_string();
    let stored_bytes = ir_text_tree
        .get(key)
        .with_context(|| format!("loading IR text {structural_hash} from sled"))?
        .ok_or_else(|| anyhow!("missing IR text row for member {structural_hash}"))?;
    decode_ir_text_value(stored_bytes.as_ref())
}

fn normalize_tags(tags: &[String]) -> Result<Vec<String>> {
    tags.iter().map(|tag| normalize_tag(tag)).collect()
}

fn normalize_tag(tag: &str) -> Result<String> {
    let normalized = tag.trim();
    if normalized.is_empty() {
        bail!("tag cannot be empty");
    }
    if normalized.contains('\0') {
        bail!("tag cannot contain NUL bytes");
    }
    Ok(normalized.to_string())
}

fn normalize_optional_string(value: Option<&str>) -> Option<String> {
    value.and_then(|raw| {
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            None
        } else {
            Some(trimmed.to_string())
        }
    })
}

fn now_utc_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock was before unix epoch")
        .as_secs()
}

fn tag_index_prefix(tag: &str) -> Vec<u8> {
    let mut key = Vec::with_capacity(tag.len() + 5);
    key.extend_from_slice(b"tag\0");
    key.extend_from_slice(tag.as_bytes());
    key.push(0);
    key
}

fn tag_index_key(tag: &str, structural_hash: &str) -> Vec<u8> {
    let mut key = tag_index_prefix(tag);
    key.extend_from_slice(structural_hash.as_bytes());
    key
}

fn decode_tag_index_key(key: &[u8]) -> Result<(String, String)> {
    let mut parts = key.splitn(3, |byte| *byte == 0);
    let prefix = parts
        .next()
        .ok_or_else(|| anyhow!("tag index key missing prefix"))?;
    if prefix != b"tag" {
        bail!("tag index key had invalid prefix");
    }
    let tag = parts
        .next()
        .ok_or_else(|| anyhow!("tag index key missing tag"))?;
    let structural_hash = parts
        .next()
        .ok_or_else(|| anyhow!("tag index key missing structural hash"))?;
    Ok((
        std::str::from_utf8(tag)
            .context("tag index tag was not valid UTF-8")?
            .to_string(),
        std::str::from_utf8(structural_hash)
            .context("tag index structural hash was not valid UTF-8")?
            .to_string(),
    ))
}

fn make_prover(proof_options: &ProofOptions) -> Box<dyn Prover> {
    prover::prover_for_choice(proof_options.solver, proof_options.tool_path.as_deref())
}

fn ensure_equivalent(
    prover: &dyn Prover,
    lhs: &LoadedIr,
    rhs: &LoadedIr,
    lhs_label: &str,
    rhs_label: &str,
) -> Result<()> {
    let lhs_fn = ProverFn::new(lhs.top_fn(), Some(&lhs.package));
    let rhs_fn = ProverFn::new(rhs.top_fn(), Some(&rhs.package));
    let result = prover.prove_ir_equiv(
        &lhs_fn,
        &rhs_fn,
        EquivParallelism::SingleThreaded,
        AssertionSemantics::Ignore,
        None,
        false,
    );

    match result {
        EquivResult::Proved => Ok(()),
        EquivResult::Disproved {
            lhs_inputs,
            rhs_inputs,
            lhs_output,
            rhs_output,
        } => bail!(
            "{lhs_label} is not equivalent to {rhs_label}: lhs_inputs={lhs_inputs:?} rhs_inputs={rhs_inputs:?} lhs_output={lhs_output} rhs_output={rhs_output}"
        ),
        EquivResult::ToolchainDisproved(message) => {
            bail!("{lhs_label} is not equivalent to {rhs_label}: {message}")
        }
        EquivResult::Interrupted => {
            bail!("equivalence check interrupted for {lhs_label} vs {rhs_label}")
        }
        EquivResult::Error(message) => {
            bail!("equivalence check failed for {lhs_label} vs {rhs_label}: {message}")
        }
    }
}

fn hash_to_hex(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    const IDENTITY_IR: &str = r#"package seed

top fn seed_fn(x: bits[8]) -> bits[8] {
  ret identity.2: bits[8] = identity(x, id=2)
}
"#;

    const ADD_ZERO_IR: &str = r#"package add_zero

top fn add_zero_fn(x: bits[8]) -> bits[8] {
  literal.2: bits[8] = literal(value=0, id=2)
  ret add.3: bits[8] = add(x, literal.2, id=3)
}
"#;

    const OR_ZERO_IR: &str = r#"package or_zero

top fn or_zero_fn(x: bits[8]) -> bits[8] {
  literal.2: bits[8] = literal(value=0, id=2)
  ret or.3: bits[8] = or(x, literal.2, id=3)
}
"#;

    const NOT_IR: &str = r#"package not_pkg

top fn not_fn(x: bits[8]) -> bits[8] {
  ret not.2: bits[8] = not(x, id=2)
}
"#;

    const RENAMED_IDENTITY_IR: &str = r#"package renamed

top fn renamed_fn(arg: bits[8]) -> bits[8] {
  ret identity.2: bits[8] = identity(arg, id=2)
}
"#;

    const IDENTITY16_IR: &str = r#"package seed16

top fn seed16_fn(x: bits[16]) -> bits[16] {
  ret identity.2: bits[16] = identity(x, id=2)
}
"#;

    fn make_temp_db() -> (TempDir, PathBuf) {
        let tempdir = TempDir::new().expect("tempdir");
        let db_path = tempdir.path().join("bf16_add.eqc");
        (tempdir, db_path)
    }

    fn write_ir(tempdir: &TempDir, filename: &str, contents: &str) -> PathBuf {
        let path = tempdir.path().join(filename);
        fs::write(&path, contents).expect("write IR");
        path
    }

    fn metadata_with(
        tags: &[&str],
        provenance: Option<&str>,
        added_at_utc_secs: u64,
    ) -> NewMemberMetadata {
        NewMemberMetadata {
            tags: tags.iter().map(|tag| tag.to_string()).collect(),
            provenance: provenance.map(str::to_string),
            added_at_utc_secs: Some(added_at_utc_secs),
        }
    }

    fn ir_node_count_tag_for_path(path: &Path) -> String {
        let loaded = LoadedIr::from_path(path, None).expect("load IR for node count tag");
        ir_node_count_tag(loaded.top_fn())
    }

    fn ir_signature_for_path(path: &Path) -> String {
        LoadedIr::from_path(path, None)
            .expect("load IR for signature")
            .signature
    }

    #[test]
    fn ir_text_compression_roundtrips() {
        let raw = vec![b'a'; 4096];
        let encoded = encode_ir_text_value(&raw).expect("encode IR text");
        assert!(encoded.starts_with(IR_TEXT_ZSTD_MAGIC));
        let decoded = decode_ir_text_value(&encoded).expect("decode IR text");
        assert_eq!(decoded.as_bytes(), raw.as_slice());
    }

    #[test]
    fn member_metadata_and_ir_text_are_stored_in_separate_trees() {
        let (tempdir, db_path) = make_temp_db();
        let ir_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.add_ir_path_with_metadata(
            &ir_path,
            None,
            &metadata_with(&["bf16", "seed"], Some("generator"), 1_700_000_000),
            &ProofOptions::default(),
        )
        .expect("add with metadata");

        let member = db
            .list_members()
            .expect("list members")
            .into_iter()
            .next()
            .expect("seeded member");

        let member_row = db
            .members_tree()
            .expect("open members tree")
            .get(member.structural_hash.as_bytes())
            .expect("load member row")
            .expect("member row exists");
        let ir_text_row = db
            .ir_text_tree()
            .expect("open IR text tree")
            .get(member.structural_hash.as_bytes())
            .expect("load IR text row")
            .expect("IR text row exists");

        let stored_member_value: StoredMemberValue =
            serde_json::from_slice(member_row.as_ref()).expect("parse member metadata row");
        assert_eq!(stored_member_value.package_name, "seed");
        assert_eq!(stored_member_value.top_name, "seed_fn");
        assert_eq!(
            stored_member_value
                .metadata
                .tags
                .iter()
                .cloned()
                .collect::<Vec<_>>(),
            vec![
                "bf16".to_string(),
                ir_node_count_tag_for_path(&ir_path),
                "seed".to_string(),
            ]
        );
        let member_row_text = std::str::from_utf8(member_row.as_ref()).expect("member row utf8");
        assert!(!member_row_text.contains("\"ir_text\""));
        assert!(!member_row_text.contains("identity.2"));

        let decoded_ir_text = decode_ir_text_value(ir_text_row.as_ref()).expect("decode IR text");
        assert!(decoded_ir_text.contains("identity.2"));
    }

    #[test]
    fn init_add_contains_and_list_roundtrip() {
        let (tempdir, db_path) = make_temp_db();
        let ir_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        let outcome = db
            .add_ir_path(&ir_path, None, &ProofOptions::default())
            .expect("seed add");
        assert!(matches!(outcome, AddOutcome::Seeded { .. }));
        assert_eq!(db.len().expect("len"), 1);
        assert!(db.contains_ir_path(&ir_path, None).expect("contains"));

        let members = db.list_members().expect("list members");
        assert_eq!(members.len(), 1);
        assert_eq!(members[0].package_name, "seed");
        assert_eq!(members[0].top_name, "seed_fn");
        assert_eq!(
            members[0].metadata.tags,
            BTreeSet::from([ir_node_count_tag_for_path(&ir_path)])
        );
        assert_eq!(members[0].metadata.provenance, None);
        assert!(members[0].metadata.added_at_utc_secs > 0);
        assert_eq!(
            db.expected_signature().expect("expected signature"),
            Some(ir_signature_for_path(&ir_path))
        );
    }

    #[test]
    fn metadata_tags_roundtrip_and_filtering_work() {
        let (tempdir, db_path) = make_temp_db();
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let add_zero_path = write_ir(&tempdir, "add_zero.ir", ADD_ZERO_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.add_ir_path_with_metadata(
            &seed_path,
            None,
            &metadata_with(&["bf16", "add"], Some("mcmc seed=123"), 1_700_000_000),
            &ProofOptions::default(),
        )
        .expect("seed add with metadata");
        let seed_count_tag = ir_node_count_tag_for_path(&seed_path);
        let add_zero_count_tag = ir_node_count_tag_for_path(&add_zero_path);
        db.insert_member(
            &LoadedIr::from_path(&add_zero_path, None).expect("load add_zero"),
            normalize_new_member_metadata(&metadata_with(
                &["bf16", "identity"],
                None,
                1_700_000_005,
            ))
            .expect("normalize metadata"),
        )
        .expect("insert second metadata row");

        let members = db.list_members().expect("list members");
        assert_eq!(members.len(), 2);
        let seed_member = members
            .iter()
            .find(|member| member.metadata.provenance.as_deref() == Some("mcmc seed=123"))
            .expect("find seeded member");
        assert_eq!(
            seed_member
                .metadata
                .tags
                .iter()
                .cloned()
                .collect::<Vec<_>>(),
            vec![
                "add".to_string(),
                "bf16".to_string(),
                seed_count_tag.clone(),
            ]
        );
        assert_eq!(seed_member.metadata.added_at_utc_secs, 1_700_000_000);

        let tag_counts = db.list_tags().expect("list tags");
        let tag_counts: BTreeMap<String, usize> = tag_counts
            .into_iter()
            .map(|tag_count| (tag_count.tag, tag_count.count))
            .collect();
        assert_eq!(
            tag_counts,
            BTreeMap::from([
                ("add".to_string(), 1),
                ("bf16".to_string(), 2),
                ("identity".to_string(), 1),
                (seed_count_tag.clone(), 1),
                (add_zero_count_tag.clone(), 1),
            ])
        );

        let filtered = db
            .list_members_filtered_by_tags(&["bf16".to_string(), "identity".to_string()])
            .expect("filter by tags");
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].metadata.added_at_utc_secs, 1_700_000_005);

        let filtered_by_node_count = db
            .list_members_filtered_by_tags(std::slice::from_ref(&add_zero_count_tag))
            .expect("filter by IR node count");
        assert_eq!(filtered_by_node_count.len(), 1);
        assert_eq!(
            filtered_by_node_count[0]
                .metadata
                .tags
                .contains(&add_zero_count_tag),
            true
        );
    }

    #[test]
    fn try_add_duplicate_structural_hash_reports_already_contained() {
        let (tempdir, db_path) = make_temp_db();
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let renamed_path = write_ir(&tempdir, "renamed.ir", RENAMED_IDENTITY_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.add_ir_path(&seed_path, None, &ProofOptions::default())
            .expect("seed add");

        let original_hash = LoadedIr::from_path(&seed_path, None)
            .expect("load seed")
            .structural_hash;
        let outcome = db
            .try_add_ir_path(&renamed_path, None, &ProofOptions::default())
            .expect("try add duplicate");
        assert_eq!(
            outcome,
            TryAddOutcome::AlreadyContained {
                structural_hash: original_hash
            }
        );
        assert_eq!(db.len().expect("len"), 1);
    }

    #[test]
    fn check_invariants_detects_hash_mismatch() {
        let (tempdir, db_path) = make_temp_db();
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.add_ir_path(&seed_path, None, &ProofOptions::default())
            .expect("seed add");

        let members = db.list_members().expect("list members");
        let key = members[0].structural_hash.clone();
        let member_tree = db.members_tree().expect("open members tree");
        let ir_text_tree = db.ir_text_tree().expect("open IR text tree");
        let corrupted = StoredMemberValue {
            package_name: "not_pkg".to_string(),
            top_name: "not_fn".to_string(),
            metadata: StoredMemberMetadataValue::default(),
        };
        member_tree
            .insert(
                key.as_bytes(),
                serde_json::to_vec(&corrupted).expect("serialize corruption"),
            )
            .expect("corrupt row");
        ir_text_tree
            .insert(
                key.as_bytes(),
                encode_ir_text_value(NOT_IR.as_bytes()).expect("encode corrupt IR"),
            )
            .expect("corrupt IR row");
        db.db.flush().expect("flush db");

        let error = db
            .check_invariants(&ProofOptions::default())
            .expect_err("hash mismatch should fail");
        assert!(error.to_string().contains("stored hash mismatch"));
    }

    #[test]
    fn validate_and_check_invariants_accept_equivalent_unique_hash_members() {
        if std::env::var_os("XLSYNTH_TOOLS").is_none() {
            return;
        }

        let (tempdir, db_path) = make_temp_db();
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let add_zero_path = write_ir(&tempdir, "add_zero.ir", ADD_ZERO_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.add_ir_path(&seed_path, None, &ProofOptions::default())
            .expect("seed add");
        let outcome = db
            .add_ir_path(&add_zero_path, None, &ProofOptions::default())
            .expect("add equivalent member");
        assert!(matches!(outcome, AddOutcome::Added { .. }));

        let members = db.list_members().expect("list members");
        assert_eq!(members.len(), 2);
        assert_ne!(members[0].structural_hash, members[1].structural_hash);

        let validate_report = db
            .validate_ir_path(&add_zero_path, None, &ProofOptions::default())
            .expect("validate equivalent");
        assert_eq!(validate_report.compared_against, 1);

        let invariant_report = db
            .check_invariants(&ProofOptions::default())
            .expect("check invariants");
        assert_eq!(invariant_report.member_count, 2);
    }

    #[test]
    fn canonical_member_promotes_to_smallest_node_count_and_backfills_when_missing() {
        if std::env::var_os("XLSYNTH_TOOLS").is_none() {
            return;
        }

        let (tempdir, db_path) = make_temp_db();
        let add_zero_path = write_ir(&tempdir, "add_zero.ir", ADD_ZERO_IR);
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let or_zero_path = write_ir(&tempdir, "or_zero.ir", OR_ZERO_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        let add_zero_hash = LoadedIr::from_path(&add_zero_path, None)
            .expect("load add_zero")
            .structural_hash;
        db.add_ir_path(&add_zero_path, None, &ProofOptions::default())
            .expect("seed add");
        assert_eq!(
            db.canonical_structural_hash().expect("canonical hash"),
            Some(add_zero_hash)
        );

        let seed_hash = LoadedIr::from_path(&seed_path, None)
            .expect("load seed")
            .structural_hash;
        db.add_ir_path(&seed_path, None, &ProofOptions::default())
            .expect("add smaller canonical");
        assert_eq!(
            db.canonical_structural_hash().expect("canonical hash"),
            Some(seed_hash.clone())
        );

        db.metadata_tree()
            .expect("metadata tree")
            .remove(KEY_CANONICAL_STRUCTURAL_HASH)
            .expect("remove canonical hash");
        db.db.flush().expect("flush db");

        assert_eq!(
            db.canonical_structural_hash()
                .expect("backfilled canonical hash"),
            Some(seed_hash)
        );

        let validate_report = db
            .validate_ir_path(&or_zero_path, None, &ProofOptions::default())
            .expect("validate using canonical member only");
        assert_eq!(validate_report.compared_against, 1);
    }

    #[test]
    fn expected_signature_rejects_wrong_shape_and_backfills_when_missing() {
        let (tempdir, db_path) = make_temp_db();
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let identity16_path = write_ir(&tempdir, "seed16.ir", IDENTITY16_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.set_expected_signature(&ir_signature_for_path(&seed_path))
            .expect("set expected signature");
        db.add_ir_path(&seed_path, None, &ProofOptions::default())
            .expect("seed add");

        let error = db
            .validate_ir_path(&identity16_path, None, &ProofOptions::default())
            .expect_err("wrong signature should fail validation");
        assert!(error.to_string().contains("top signature mismatch"));

        db.metadata_tree()
            .expect("metadata tree")
            .remove(KEY_EXPECTED_SIGNATURE)
            .expect("remove expected signature");
        db.db.flush().expect("flush db");

        assert_eq!(
            db.expected_signature()
                .expect("backfilled expected signature"),
            Some(ir_signature_for_path(&seed_path))
        );
    }

    #[test]
    fn validate_rejects_inequivalent_member() {
        if std::env::var_os("XLSYNTH_TOOLS").is_none() {
            return;
        }

        let (tempdir, db_path) = make_temp_db();
        let seed_path = write_ir(&tempdir, "seed.ir", IDENTITY_IR);
        let not_path = write_ir(&tempdir, "not.ir", NOT_IR);

        let db = EquivalenceClassDb::init(&db_path).expect("init db");
        db.add_ir_path(&seed_path, None, &ProofOptions::default())
            .expect("seed add");

        let error = db
            .validate_ir_path(&not_path, None, &ProofOptions::default())
            .expect_err("inequivalent member should fail validation");
        assert!(error.to_string().contains("not equivalent"));
    }
}
