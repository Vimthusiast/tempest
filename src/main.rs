use std::path::PathBuf;

use clap::{Parser, Subcommand};
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};
use tracing_tree::HierarchicalLayer;

use crate::repl::repl;

#[macro_use]
extern crate tracing;

mod repl;

#[derive(Subcommand)]
enum Command {
    /// Starts an interactive REPL-Shell for a Tempest database
    Repl {
        /// The directory to create or open the database inside of
        data_dir: PathBuf,
    },
}

/// Tempest CLI.
#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

fn main() -> anyhow::Result<()> {
    let layer = HierarchicalLayer::default()
        .with_indent_lines(true)
        .with_bracketed_fields(true)
        .with_targets(true);

    tracing_subscriber::registry()
        .with(layer)
        .with(EnvFilter::from_default_env())
        .init();

    let cli = Cli::parse();

    match cli.command {
        Command::Repl { data_dir } => repl(data_dir),
    }
}
