//! Abstract Syntax Tree definitions for Moria
use std::fmt;

use crate::error::Span;
use crate::vm::Environment;

/// A Moria value at compile time
#[derive(Debug, Clone)]
pub enum Value {
    Integer(i64),
    Float(f64),
    Boolean(bool),
    String(String),
    Symbol(String),
    List(Vec<Value>),
    Nil,
    Lambda {
        function_name: Option<String>,
        parameters: Vec<String>,
        body: Vec<Expression>,
        env: Option<Environment>,
    },
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Integer(i) => write!(f, "{}", i),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Boolean(b) => write!(f, "#{}", if *b { "t" } else { "f" }),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Symbol(s) => write!(f, "{}", s),
            Value::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            Value::Nil => write!(f, "()"),
            Value::Lambda {
                function_name: _,
                parameters,
                body: _,
                env: _,
            } => {
                write!(f, "#<lambda>(")?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Value {
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Integer(_) => "Integer",
            Value::Float(_) => "Float",
            Value::Boolean(_) => "Boolean",
            Value::String(_) => "String",
            Value::Symbol(_) => "Symbol",
            Value::List(_) => "List",
            Value::Nil => "Nil",
            Value::Lambda { .. } => "Lambda",
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Integer(a), Value::Integer(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Boolean(a), Value::Boolean(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Nil, Value::Nil) => true,
            // Lambda values are never equal (for now)
            (Value::Lambda { .. }, Value::Lambda { .. }) => false,
            _ => false,
        }
    }
}

/// Core expression types in Moria
#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    /// Literal values
    Literal { value: Value, span: Span },

    /// Variable reference
    Variable { name: String, span: Span },

    /// Function call (operator application)
    Call {
        function: Box<Expression>,
        arguments: Vec<Expression>,
        span: Span,
    },

    /// Lambda expression
    Lambda {
        parameters: Vec<Parameter>,
        body: Vec<Expression>,
        span: Span,
    },

    /// Let binding
    Let {
        bindings: Vec<Binding>,
        body: Vec<Expression>,
        span: Span,
    },

    /// Conditional expression
    If {
        condition: Box<Expression>,
        then_expr: Box<Expression>,
        else_expr: Option<Box<Expression>>,
        span: Span,
    },

    /// Definition
    Define {
        name: String,
        value: Box<Expression>,
        span: Span,
    },

    /// Function definition shorthand
    DefineFunction {
        name: String,
        parameters: Vec<Parameter>,
        body: Vec<Expression>,
        span: Span,
    },

    /// Begin (sequence)
    Begin {
        expressions: Vec<Expression>,
        span: Span,
    },

    /// Quote expression
    Quote {
        expression: Box<Expression>,
        span: Span,
    },
}

/// Function parameter
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub name: String,
    pub type_annotation: Option<TypeAnnotation>,
    pub span: Span,
}

/// Let binding
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub name: String,
    pub value: Expression,
    pub span: Span,
}

/// Type annotation
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAnnotation {
    pub type_expr: TypeExpression,
    pub span: Span,
}

/// Type expression
#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpression {
    /// Named type (e.g., Integer, String)
    Named(String),

    /// Function type (e.g., Integer -> String)
    Function {
        parameters: Vec<TypeExpression>,
        return_type: Box<TypeExpression>,
    },

    /// Type variable (e.g., 'a)
    TypeVar(String),
}

/// Program
#[derive(Debug, Clone, Default)]
pub struct Program {
    pub expressions: Vec<Expression>,
    pub span: Span,
}

impl Program {
    pub fn new() -> Self {
        Self {
            expressions: Vec::new(),
            span: Span::default(),
        }
    }
}

// Helper methods for creating expressions
impl Expression {
    pub fn integer(value: i64, span: Span) -> Self {
        Self::Literal {
            value: Value::Integer(value),
            span,
        }
    }

    pub fn float(value: f64, span: Span) -> Self {
        Self::Literal {
            value: Value::Float(value),
            span,
        }
    }

    pub fn boolean(value: bool, span: Span) -> Self {
        Self::Literal {
            value: Value::Boolean(value),
            span,
        }
    }

    pub fn string(value: String, span: Span) -> Self {
        Self::Literal {
            value: Value::String(value),
            span,
        }
    }

    pub fn symbol(value: String, span: Span) -> Self {
        Self::Literal {
            value: Value::Symbol(value),
            span,
        }
    }

    pub fn nil(span: Span) -> Self {
        Self::Literal {
            value: Value::Nil,
            span,
        }
    }

    pub fn variable(name: String, span: Span) -> Self {
        Self::Variable { name, span }
    }

    pub fn call(function: Expression, arguments: Vec<Expression>, span: Span) -> Self {
        Self::Call {
            function: Box::new(function),
            arguments,
            span,
        }
    }

    pub fn lambda(parameters: Vec<Parameter>, body: Vec<Expression>, span: Span) -> Self {
        Self::Lambda {
            parameters,
            body,
            span,
        }
    }

    pub fn if_expr(
        condition: Expression,
        then_expr: Expression,
        else_expr: Option<Expression>,
        span: Span,
    ) -> Self {
        Self::If {
            condition: Box::new(condition),
            then_expr: Box::new(then_expr),
            else_expr: else_expr.map(Box::new),
            span,
        }
    }

    pub fn begin(expressions: Vec<Expression>, span: Span) -> Self {
        Self::Begin { expressions, span }
    }

    pub fn quote(expression: Expression, span: Span) -> Self {
        Self::Quote {
            expression: Box::new(expression),
            span,
        }
    }

    pub fn define(name: String, value: Expression, span: Span) -> Self {
        Self::Define {
            name,
            value: Box::new(value),
            span,
        }
    }

    pub fn span(&self) -> &Span {
        match self {
            Expression::Literal { span, .. } => span,
            Expression::Variable { span, .. } => span,
            Expression::Call { span, .. } => span,
            Expression::Lambda { span, .. } => span,
            Expression::Let { span, .. } => span,
            Expression::If { span, .. } => span,
            Expression::Define { span, .. } => span,
            Expression::DefineFunction { span, .. } => span,
            Expression::Begin { span, .. } => span,
            Expression::Quote { span, .. } => span,
        }
    }
}
