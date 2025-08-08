//! Moria Language - Minimal Implementation
//! 
//! A Scheme-inspired language with gradual typing, universal annotations,
//! and WebAssembly as the unified compilation target.

pub mod ast;
pub mod parser;
pub mod evaluator;
pub mod error;
pub mod repl;
pub mod type_infer;

pub use ast::*;
pub use parser::{parse, parse_expression};
pub use evaluator::Evaluator;
pub use error::{MoriaError, Result};
pub use repl::Repl; 
pub use type_infer::{infer_expression_type, Type as Ty};