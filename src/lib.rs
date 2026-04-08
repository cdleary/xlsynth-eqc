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
use xlsynth_pir::node_hashing::compute_function_structural_hash;
use xlsynth_prover::prover;
use xlsynth_prover::prover::Prover;
use xlsynth_prover::prover::SolverChoice;
use xlsynth_prover::prover::types::{AssertionSemantics, EquivParallelism, EquivResult, ProverFn};

const SCHEMA_VERSION: u32 = 1;
const TREE_METADATA: &str = "metadata";
const TREE_MEMBERS: &str = "members";
const TREE_TAG_INDEX: &str = "tag_index";
const KEY_SCHEMA_VERSION: &[u8] = b"schema_version";
const MEMBER_ROW_ZSTD_MAGIC: &[u8] = b"EQCZSTD1";

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
    ir_text: String,
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
        let package_name = package.name.clone();
        let structural_hash = hash_to_hex(compute_function_structural_hash(top_fn).as_bytes());
        let canonical_ir_text = package.to_string();
        Ok(Self {
            origin,
            package,
            package_name,
            top_name,
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
            ir_text: self.canonical_ir_text.clone(),
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

    pub fn list_members(&self) -> Result<Vec<StoredMember>> {
        let tree = self.members_tree()?;
        let mut members = Vec::with_capacity(tree.len());
        for row in &tree {
            let (key, value) = row.context("reading member row from sled")?;
            members.push(decode_member_row(&key, &value)?);
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
        let mut members = Vec::new();
        for structural_hash in matching_hashes.unwrap_or_default() {
            let value = members_tree
                .get(structural_hash.as_bytes())
                .with_context(|| format!("loading member {structural_hash} from sled"))?
                .ok_or_else(|| anyhow!("tag index referenced missing member {structural_hash}"))?;
            members.push(decode_member_row(structural_hash.as_bytes(), &value)?);
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
            }
            return Ok(InvariantReport {
                member_count: members.len(),
            });
        }

        let mut loaded_members = Vec::with_capacity(members.len());
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
            loaded_members.push(loaded);
        }

        let prover = make_prover(proof_options);
        let canonical = &loaded_members[0];
        for member in loaded_members.iter().skip(1) {
            ensure_equivalent(
                &*prover,
                canonical,
                member,
                &format!("stored canonical member {}", canonical.structural_hash),
                &format!("stored member {}", member.structural_hash),
            )?;
        }

        Ok(InvariantReport {
            member_count: loaded_members.len(),
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
        if existing_len > 0 {
            self.validate_loaded(&candidate, proof_options)?;
        }

        self.insert_member(&candidate, normalize_new_member_metadata(metadata)?)?;
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
        let members = self.list_members()?;
        if members.is_empty() {
            bail!("cannot validate against an empty equivalence class");
        }

        let prover = make_prover(proof_options);
        for member in &members {
            let stored = LoadedIr::from_stored_member(member)?;
            ensure_equivalent(
                &*prover,
                candidate,
                &stored,
                &candidate.origin,
                &format!("stored member {}", member.structural_hash),
            )?;
        }

        Ok(ValidationReport {
            compared_against: members.len(),
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
        let tree = self.members_tree()?;
        let tag_index = self.tag_index_tree()?;
        let raw_value = serde_json::to_vec(&candidate.stored_value(metadata.clone()))
            .context("serializing member for sled storage")?;
        let value = encode_member_row_value(&raw_value)?;
        tree.insert(candidate.structural_hash.as_bytes(), value)
            .with_context(|| format!("inserting member {}", candidate.structural_hash))?;
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
        self.db.flush().context("flushing member insert")?;
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

fn decode_member_row(key: &[u8], value: &[u8]) -> Result<StoredMember> {
    let structural_hash = std::str::from_utf8(key)
        .context("member key was not valid UTF-8")?
        .to_string();
    let decoded_value = decode_member_row_value(value)?;
    let value: StoredMemberValue =
        serde_json::from_slice(&decoded_value).context("deserializing stored member value")?;
    Ok(StoredMember {
        structural_hash,
        package_name: value.package_name,
        top_name: value.top_name,
        ir_text: value.ir_text,
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

fn encode_member_row_value(raw_bytes: &[u8]) -> Result<Vec<u8>> {
    let compressed = zstd::bulk::compress(raw_bytes, 3).context("zstd compressing member row")?;
    let framed_len = MEMBER_ROW_ZSTD_MAGIC.len() + compressed.len();
    if framed_len >= raw_bytes.len() {
        return Ok(raw_bytes.to_vec());
    }
    let mut encoded = Vec::with_capacity(framed_len);
    encoded.extend_from_slice(MEMBER_ROW_ZSTD_MAGIC);
    encoded.extend_from_slice(&compressed);
    Ok(encoded)
}

fn decode_member_row_value(stored_bytes: &[u8]) -> Result<Vec<u8>> {
    let Some(payload) = stored_bytes.strip_prefix(MEMBER_ROW_ZSTD_MAGIC) else {
        return Ok(stored_bytes.to_vec());
    };
    zstd::stream::decode_all(Cursor::new(payload)).context("zstd decoding member row")
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

    #[test]
    fn member_row_compression_roundtrips() {
        let raw = vec![b'a'; 4096];
        let encoded = encode_member_row_value(&raw).expect("encode row");
        assert!(encoded.starts_with(MEMBER_ROW_ZSTD_MAGIC));
        let decoded = decode_member_row_value(&encoded).expect("decode row");
        assert_eq!(decoded, raw);
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
        assert!(members[0].metadata.tags.is_empty());
        assert_eq!(members[0].metadata.provenance, None);
        assert!(members[0].metadata.added_at_utc_secs > 0);
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
            vec!["add".to_string(), "bf16".to_string()]
        );
        assert_eq!(seed_member.metadata.added_at_utc_secs, 1_700_000_000);

        let tag_counts = db.list_tags().expect("list tags");
        assert_eq!(
            tag_counts,
            vec![
                TagCount {
                    tag: "add".to_string(),
                    count: 1
                },
                TagCount {
                    tag: "bf16".to_string(),
                    count: 2
                },
                TagCount {
                    tag: "identity".to_string(),
                    count: 1
                },
            ]
        );

        let filtered = db
            .list_members_filtered_by_tags(&["bf16".to_string(), "identity".to_string()])
            .expect("filter by tags");
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].metadata.added_at_utc_secs, 1_700_000_005);
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
        let tree = db.members_tree().expect("open members tree");
        let corrupted = StoredMemberValue {
            package_name: "not_pkg".to_string(),
            top_name: "not_fn".to_string(),
            ir_text: NOT_IR.to_string(),
            metadata: StoredMemberMetadataValue::default(),
        };
        tree.insert(
            key.as_bytes(),
            serde_json::to_vec(&corrupted).expect("serialize corruption"),
        )
        .expect("corrupt row");
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
        assert_eq!(validate_report.compared_against, 2);

        let invariant_report = db
            .check_invariants(&ProofOptions::default())
            .expect("check invariants");
        assert_eq!(invariant_report.member_count, 2);
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
