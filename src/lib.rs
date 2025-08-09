//! Moria Language - Minimal Implementation
//!
//! A Scheme-inspired language with gradual typing, universal annotations,
//! and WebAssembly as the unified compilation target.

pub mod ast;
pub mod error;
pub mod parser;
pub mod repl;
pub mod type_infer;
pub mod vm;

pub use ast::*;
pub use error::{MoriaError, Result};
pub use parser::{parse, parse_expression};
pub use repl::Repl;
pub use type_infer::{infer_expression_type, Type as Ty};
pub use vm::{
    compile_expr, evaluate_expr_vm, evaluate_program_vm, Bytecode, Environment, Opcode, VM,
};
