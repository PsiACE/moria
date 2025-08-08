//! Error types for the Moria language

use thiserror::Error;

/// Source code span for error reporting
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

/// Main error type for Moria
#[derive(Debug, Error)]
pub enum MoriaError {
    #[error("Parse error: {message}")]
    Parse {
        message: String,
        span: Span,
        context: Option<String>,
    },
    
    #[error("Type error: {message}")]
    Type {
        message: String,
        span: Span,
        context: Option<String>,
    },
    
    #[error("Runtime error: {message}")]
    Runtime {
        message: String,
        span: Option<Span>,
        context: Option<String>,
    },
    
    #[error("Compilation error: {message}")]
    Compilation {
        message: String,
        span: Option<Span>,
        context: Option<String>,
    },
    
    #[error("{0}")]
    Generic(String),
}

/// Result type alias
pub type Result<T> = std::result::Result<T, MoriaError>;

/// Error context for better error reporting
#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub source_file: Option<String>,
    pub line: Option<usize>,
    pub column: Option<usize>,
    pub annotation: Option<String>,
} 