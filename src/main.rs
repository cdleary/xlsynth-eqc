// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::PathBuf;
use std::str::FromStr;

use anyhow::{Context, Result, anyhow};
use clap::{Args, Parser, Subcommand};
use xlsynth_eqc::{EquivalenceClassDb, NewMemberMetadata, ProofOptions, TryAddOutcome};
use xlsynth_pir::ir_parser;
use xlsynth_pir::ir_utils::fn_node_count;
use xlsynth_prover::prover::SolverChoice;

#[derive(Parser)]
#[command(name = "xlsynth-eqc")]
#[command(about = "Manage sled-backed XLS IR equivalence classes")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    Init(InitArgs),
    #[command(name = "init-from-corpus")]
    InitFromCorpus(InitFromCorpusArgs),
    Add(AddIrArgs),
    #[command(name = "try_add")]
    TryAdd(AddIrArgs),
    Contains(IrArgs),
    Validate(ValidateIrArgs),
    Len {
        db: PathBuf,
    },
    List(ListArgs),
    #[command(name = "list-tags")]
    ListTags {
        db: PathBuf,
    },
    CheckInvariants(ProofDbArgs),
}

#[derive(Args)]
struct IrArgs {
    db: PathBuf,
    ir_file: PathBuf,
    #[arg(long)]
    top: Option<String>,
}

#[derive(Args)]
struct InitArgs {
    db: PathBuf,
    #[arg(long)]
    signature: Option<String>,
}

#[derive(Args)]
struct ValidateIrArgs {
    db: PathBuf,
    ir_file: PathBuf,
    #[arg(long)]
    top: Option<String>,
    #[arg(long, default_value = "auto")]
    solver: String,
    #[arg(long)]
    tool_path: Option<PathBuf>,
}

#[derive(Args)]
struct AddIrArgs {
    db: PathBuf,
    ir_file: PathBuf,
    #[arg(long)]
    top: Option<String>,
    #[arg(long, default_value = "auto")]
    solver: String,
    #[arg(long)]
    tool_path: Option<PathBuf>,
    #[arg(long = "tag")]
    tags: Vec<String>,
    #[arg(long)]
    provenance: Option<String>,
}

#[derive(Args)]
struct InitFromCorpusArgs {
    db: PathBuf,
    #[arg(required = true)]
    inputs: Vec<PathBuf>,
    #[arg(long)]
    seed_ir: Option<PathBuf>,
    #[arg(long)]
    signature: Option<String>,
    #[arg(long)]
    top: Option<String>,
    #[arg(long, default_value = "auto")]
    solver: String,
    #[arg(long)]
    tool_path: Option<PathBuf>,
    #[arg(long = "tag")]
    tags: Vec<String>,
    #[arg(long)]
    provenance: Option<String>,
    #[arg(long, default_value_t = 100)]
    progress_every: usize,
    #[arg(long)]
    skip_invalid: bool,
}

#[derive(Args)]
struct ListArgs {
    db: PathBuf,
    #[arg(long = "tag")]
    tags: Vec<String>,
}

#[derive(Args)]
struct ProofDbArgs {
    db: PathBuf,
    #[arg(long, default_value = "auto")]
    solver: String,
    #[arg(long)]
    tool_path: Option<PathBuf>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Init(args) => {
            let db = EquivalenceClassDb::init(&args.db)?;
            if let Some(signature) = args.signature.as_deref() {
                db.set_expected_signature(signature)?;
                println!(
                    "initialized {} with expected signature {}",
                    args.db.display(),
                    signature.trim()
                );
            } else {
                println!("initialized {}", args.db.display());
            }
        }
        Command::InitFromCorpus(args) => init_from_corpus(args)?,
        Command::Add(args) => {
            let db = EquivalenceClassDb::open(&args.db)?;
            let proof_options = args.proof_options()?;
            let metadata = args.new_member_metadata();
            let outcome = db.add_ir_path_with_metadata(
                &args.ir_file,
                args.top.as_deref(),
                &metadata,
                &proof_options,
            )?;
            println!("{}", outcome.structural_hash());
        }
        Command::TryAdd(args) => {
            let db = EquivalenceClassDb::open(&args.db)?;
            let proof_options = args.proof_options()?;
            let metadata = args.new_member_metadata();
            match db.try_add_ir_path_with_metadata(
                &args.ir_file,
                args.top.as_deref(),
                &metadata,
                &proof_options,
            )? {
                TryAddOutcome::Added { structural_hash } => {
                    println!("added {structural_hash}");
                }
                TryAddOutcome::AlreadyContained { structural_hash } => {
                    println!("already-contained {structural_hash}");
                }
            }
        }
        Command::Contains(args) => {
            let db = EquivalenceClassDb::open(&args.db)?;
            println!(
                "{}",
                db.contains_ir_path(&args.ir_file, args.top.as_deref())?
            );
        }
        Command::Validate(args) => {
            let db = EquivalenceClassDb::open(&args.db)?;
            let proof_options = args.proof_options()?;
            db.validate_ir_path(&args.ir_file, args.top.as_deref(), &proof_options)?;
            println!("true");
        }
        Command::Len { db } => {
            let db = EquivalenceClassDb::open(&db)?;
            println!("{}", db.len()?);
        }
        Command::List(args) => {
            let db = EquivalenceClassDb::open(&args.db)?;
            for member in db.list_members_filtered_by_tags(&args.tags)? {
                println!(
                    "{}\t{}\t{}\t{}\t{}\t{}",
                    member.structural_hash,
                    member.top_name,
                    member.package_name,
                    member.metadata.added_at_utc_secs,
                    format_tags(&member.metadata.tags),
                    member.metadata.provenance.unwrap_or_default()
                );
            }
        }
        Command::ListTags { db } => {
            let db = EquivalenceClassDb::open(&db)?;
            for tag_count in db.list_tags()? {
                println!("{}\t{}", tag_count.tag, tag_count.count);
            }
        }
        Command::CheckInvariants(args) => {
            let db = EquivalenceClassDb::open(&args.db)?;
            let proof_options = args.proof_options()?;
            db.check_invariants(&proof_options)?;
            println!("true");
        }
    }
    Ok(())
}

impl ValidateIrArgs {
    fn proof_options(&self) -> Result<ProofOptions> {
        Ok(ProofOptions {
            solver: parse_solver_choice(&self.solver)?,
            tool_path: self.tool_path.clone(),
        })
    }
}

impl AddIrArgs {
    fn proof_options(&self) -> Result<ProofOptions> {
        Ok(ProofOptions {
            solver: parse_solver_choice(&self.solver)?,
            tool_path: self.tool_path.clone(),
        })
    }

    fn new_member_metadata(&self) -> NewMemberMetadata {
        NewMemberMetadata {
            tags: self.tags.iter().cloned().collect(),
            provenance: self.provenance.clone(),
            added_at_utc_secs: None,
        }
    }
}

impl InitFromCorpusArgs {
    fn proof_options(&self) -> Result<ProofOptions> {
        Ok(ProofOptions {
            solver: parse_solver_choice(&self.solver)?,
            tool_path: self.tool_path.clone(),
        })
    }

    fn new_member_metadata(&self) -> NewMemberMetadata {
        NewMemberMetadata {
            tags: self.tags.iter().cloned().collect(),
            provenance: self.provenance.clone(),
            added_at_utc_secs: None,
        }
    }
}

impl ProofDbArgs {
    fn proof_options(&self) -> Result<ProofOptions> {
        Ok(ProofOptions {
            solver: parse_solver_choice(&self.solver)?,
            tool_path: self.tool_path.clone(),
        })
    }
}

fn parse_solver_choice(value: &str) -> Result<SolverChoice> {
    SolverChoice::from_str(value).map_err(|e| anyhow!("invalid --solver value '{value}': {e}"))
}

fn format_tags(tags: &std::collections::BTreeSet<String>) -> String {
    tags.iter().cloned().collect::<Vec<_>>().join(",")
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CorpusEntry {
    path: PathBuf,
    node_count: usize,
    signature: String,
}

#[derive(Default)]
struct CorpusImportStats {
    processed: usize,
    added: usize,
    already_contained: usize,
}

struct CorpusDiscovery {
    entries: Vec<CorpusEntry>,
    skipped_invalid: usize,
    invalid_examples: Vec<String>,
}

fn init_from_corpus(args: InitFromCorpusArgs) -> Result<()> {
    if args.progress_every == 0 {
        return Err(anyhow!("--progress-every must be greater than 0"));
    }

    let discovery = collect_corpus_entries(&args.inputs, args.top.as_deref(), args.skip_invalid)?;
    let mut entries = discovery.entries;
    if entries.is_empty() {
        return Err(anyhow!("no .ir files found in the provided inputs"));
    }
    entries.sort_by(|lhs, rhs| {
        lhs.node_count
            .cmp(&rhs.node_count)
            .then_with(|| lhs.path.cmp(&rhs.path))
    });

    let seed_index = match args.seed_ir.as_ref() {
        Some(seed_ir) => entries
            .iter()
            .position(|entry| entry.path == *seed_ir)
            .ok_or_else(|| {
                anyhow!(
                    "seed IR {} was not found among the valid corpus files",
                    seed_ir.display()
                )
            })?,
        None => 0,
    };
    let seed = entries.remove(seed_index);
    let seed_signature = seed.signature.clone();
    let mut skipped_signature_mismatch = 0usize;
    let mut signature_mismatch_examples = Vec::new();
    let mut compatible_entries = Vec::with_capacity(entries.len() + 1);
    compatible_entries.push(seed);
    for entry in entries {
        if entry.signature == seed_signature {
            compatible_entries.push(entry);
        } else {
            skipped_signature_mismatch += 1;
            if signature_mismatch_examples.len() < 5 {
                signature_mismatch_examples.push(format!(
                    "{}: {}",
                    entry.path.display(),
                    entry.signature
                ));
            }
        }
    }
    let entries = compatible_entries;
    let requested_signature = args.signature.as_deref().map(str::trim);
    if let Some(requested_signature) = requested_signature {
        if requested_signature != seed_signature {
            return Err(anyhow!(
                "seed signature {} does not match requested signature {}",
                seed_signature,
                requested_signature
            ));
        }
    }

    let proof_options = args.proof_options()?;
    let metadata = args.new_member_metadata();
    let db = EquivalenceClassDb::init(&args.db)?;
    db.set_expected_signature(requested_signature.unwrap_or(&seed_signature))?;
    let starting_len = db.len()?;
    let total = entries.len();
    let seed = &entries[0];
    eprintln!("importing {total} IR files into {}", args.db.display());
    if discovery.skipped_invalid > 0 {
        for example in &discovery.invalid_examples {
            eprintln!("skipping invalid IR: {example}");
        }
        eprintln!(
            "skipped {} invalid IR files while scanning the corpus",
            discovery.skipped_invalid
        );
    }
    if skipped_signature_mismatch > 0 {
        for example in &signature_mismatch_examples {
            eprintln!("skipping signature-mismatched IR: {example}");
        }
        eprintln!(
            "skipped {} IR files whose top signature did not match the seed signature {}",
            skipped_signature_mismatch, seed_signature
        );
    }
    eprintln!(
        "selected seed candidate: {} ({} IR nodes, signature {})",
        seed.path.display(),
        seed.node_count,
        seed.signature
    );

    let mut stats = CorpusImportStats::default();
    for entry in &entries {
        let status = match db.try_add_ir_path_with_metadata(
            &entry.path,
            args.top.as_deref(),
            &metadata,
            &proof_options,
        )? {
            TryAddOutcome::Added { .. } => {
                stats.added += 1;
                "added"
            }
            TryAddOutcome::AlreadyContained { .. } => {
                stats.already_contained += 1;
                "already-contained"
            }
        };
        stats.processed += 1;

        if should_emit_progress(stats.processed, total, args.progress_every) {
            eprintln!(
                "[{}/{}] {} {} ({} IR nodes) | members={} duplicates={}",
                stats.processed,
                total,
                status,
                entry.path.display(),
                entry.node_count,
                starting_len + stats.added,
                stats.already_contained
            );
        }
    }

    println!(
        "imported {} IR files into {}: {} members added, {} already contained, {} total members",
        stats.processed,
        args.db.display(),
        stats.added,
        stats.already_contained,
        db.len()?
    );
    Ok(())
}

fn should_emit_progress(processed: usize, total: usize, progress_every: usize) -> bool {
    processed == 1 || processed == total || processed % progress_every == 0
}

fn collect_corpus_entries(
    inputs: &[PathBuf],
    top_override: Option<&str>,
    skip_invalid: bool,
) -> Result<CorpusDiscovery> {
    let mut paths = Vec::new();
    for input in inputs {
        collect_ir_paths(input, &mut paths)?;
    }
    paths.sort();
    paths.dedup();

    let mut entries = Vec::with_capacity(paths.len());
    let mut skipped_invalid = 0;
    let mut invalid_examples = Vec::new();
    for path in paths {
        match ir_metadata_for_path(&path, top_override) {
            Ok((node_count, signature)) => entries.push(CorpusEntry {
                path,
                node_count,
                signature,
            }),
            Err(error) if skip_invalid => {
                skipped_invalid += 1;
                if invalid_examples.len() < 5 {
                    invalid_examples.push(format!("{}: {}", path.display(), error));
                }
            }
            Err(error) => return Err(error),
        }
    }
    Ok(CorpusDiscovery {
        entries,
        skipped_invalid,
        invalid_examples,
    })
}

fn collect_ir_paths(path: &std::path::Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if path.is_file() {
        if path.extension().and_then(|ext| ext.to_str()) == Some("ir") {
            out.push(path.to_path_buf());
        }
        return Ok(());
    }

    if path.is_dir() {
        let mut entries = fs::read_dir(path)
            .with_context(|| format!("reading corpus directory {}", path.display()))?
            .collect::<std::result::Result<Vec<_>, _>>()
            .with_context(|| format!("listing corpus directory {}", path.display()))?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            collect_ir_paths(&entry.path(), out)?;
        }
        return Ok(());
    }

    Err(anyhow!(
        "corpus input does not exist or is not accessible: {}",
        path.display()
    ))
}

fn ir_metadata_for_path(
    path: &std::path::Path,
    top_override: Option<&str>,
) -> Result<(usize, String)> {
    let ir_text = fs::read_to_string(path)
        .with_context(|| format!("failed to read IR file {}", path.display()))?;
    let mut parser = ir_parser::Parser::new(&ir_text);
    let mut package = parser
        .parse_and_validate_package()
        .map_err(|e| anyhow!("failed to parse/validate {}: {e}", path.display()))?;
    if let Some(top_name) = top_override {
        package.set_top_fn(top_name).map_err(|e| {
            anyhow!(
                "failed to select top function '{top_name}' in {}: {e}",
                path.display()
            )
        })?;
    }
    let top_fn = package
        .get_top_fn()
        .ok_or_else(|| anyhow!("{} does not contain a top function", path.display()))?;
    Ok((fn_node_count(top_fn), format_top_signature(top_fn)))
}

fn format_top_signature(top_fn: &xlsynth_pir::ir::Fn) -> String {
    let fn_type = top_fn.get_type();
    let params = fn_type
        .param_types
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    format!("({params}) -> {}", fn_type.return_type)
}
