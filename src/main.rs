// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::str::FromStr;

use anyhow::{Result, anyhow};
use clap::{Args, Parser, Subcommand};
use xlsynth_eqc::{EquivalenceClassDb, NewMemberMetadata, ProofOptions, TryAddOutcome};
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
    Init {
        db: PathBuf,
    },
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
        Command::Init { db } => {
            EquivalenceClassDb::init(&db)?;
            println!("initialized {}", db.display());
        }
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
