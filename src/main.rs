//! Moria Language CLI

use clap::{Parser, Subcommand};
use moria::{Repl, parse, Evaluator};
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "moria")]
#[command(about = "Moria Language - Minimal Implementation")]
#[command(version = "0.1.0")]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Run a Moria source file
    Run {
        /// Input file
        #[arg(value_name = "FILE")]
        file: PathBuf,
    },
    
    
    /// Start interactive REPL
    Repl,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    match cli.command {
        Some(Commands::Run { file }) => {
            run_file(&file)?;
        },
        Some(Commands::Repl) => {
            run_repl()?;
        },
        None => {
            // Default to REPL if no command is provided
            run_repl()?;
        },
    }
    
    Ok(())
}

/// Run a Moria source file
fn run_file(file: &PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    // Read the file
    let source = fs::read_to_string(file)
        .map_err(|e| format!("Failed to read file: {}", e))?;
    
    // Parse the program
    let program = parse(&source)?;
    
    // Evaluate the program
    let mut evaluator = Evaluator::with_stdlib();
    let result = evaluator.evaluate_program(&program)?;
    
    println!("Result: {}", result);
    
    Ok(())
}

/// Run the REPL
fn run_repl() -> Result<(), Box<dyn std::error::Error>> {
    let mut repl = Repl::new();
    repl.run()?;
    
    Ok(())
} 