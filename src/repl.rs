//! REPL for Moria language
use std::io::{self, Write};

use crate::error::Result;
use crate::parser::parse_expression;
use crate::type_infer::infer_expression_type;
use crate::vm::evaluate_expr_vm;

/// Interactive REPL for Moria
#[derive(Default)]
pub struct Repl {
    // no retained state VM; keep no env between lines for now
    prompt: String,
}

impl Repl {
    /// Create a new REPL with standard library
    pub fn new() -> Self {
        Self {
            prompt: "> ".to_string(),
        }
    }

    /// Set the prompt string
    pub fn with_prompt(mut self, prompt: &str) -> Self {
        self.prompt = prompt.to_string();
        self
    }

    /// Run the REPL
    pub fn run(&mut self) -> Result<()> {
        println!("Moria Language REPL");
        println!("Type 'exit' or press Ctrl+C to exit");

        loop {
            // Print prompt and flush
            print!("{}", self.prompt);
            io::stdout().flush().unwrap();

            // Read input
            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                println!("Error reading input");
                continue;
            }

            // Check for exit command
            let input = input.trim();
            if input == "exit" || input.is_empty() {
                break;
            }

            // Parse and evaluate
            match parse_expression(input) {
                Ok(expr) => {
                    match evaluate_expr_vm(&expr) {
                        Ok(value) => {
                            // Also show inferred type (best-effort)
                            match infer_expression_type(&expr) {
                                Ok(ty) => println!("{} :: {}", value, ty),
                                Err(_) => println!("{}", value),
                            }
                        }
                        Err(err) => println!("Error: {}", err),
                    }
                }
                Err(err) => println!("Parse error: {}", err),
            }
        }

        Ok(())
    }
}
