//! Parser for Moria language using Chumsky

use chumsky::prelude::*;
use chumsky::Parser;

use crate::ast::*;
use crate::error::{MoriaError, Span, Result};

/// Parser for Moria language
#[derive(Default)]
pub struct MoriaParser;

impl MoriaParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self
    }

    /// Parse a complete program
    pub fn parse_program(&self, source: &str) -> Result<Program> {
        let preprocessed = preprocess_annotations(source);
        let len = preprocessed.len();
        let result = self.program_parser()
            .parse(preprocessed.as_str());

        if let Err(errors) = &result {
            if !errors.is_empty() {
                // Return the first error for now
                let err = &errors[0];
                return Err(MoriaError::Parse {
                    message: format!("Parse error: {}", err),
                    span: Span::new(err.span().start, err.span().end),
                    context: None,
                });
            }
        }

        result.map_err(|_| MoriaError::Parse {
            message: "Failed to parse program".to_string(),
            span: Span::new(0, len),
            context: None,
        })
    }

    /// Parse a single expression
    pub fn parse_expression(&self, source: &str) -> Result<Expression> {
        let preprocessed = preprocess_annotations(source);
        let len = preprocessed.len();
        let result = self.expression_parser()
            .parse(preprocessed.as_str());

        if let Err(errors) = &result {
            if !errors.is_empty() {
                // Return the first error for now
                let err = &errors[0];
                return Err(MoriaError::Parse {
                    message: format!("Parse error: {}", err),
                    span: Span::new(err.span().start, err.span().end),
                    context: None,
                });
            }
        }

        result.map_err(|_| MoriaError::Parse {
            message: "Failed to parse expression".to_string(),
            span: Span::new(0, len),
            context: None,
        })
    }

    /// Parser for a complete program
    fn program_parser(&self) -> impl Parser<char, Program, Error = Simple<char>> {
        self.expression_parser()
            .repeated()
            .collect::<Vec<_>>()
            .map(|expressions| {
                let span = if expressions.is_empty() {
                    Span::default()
                } else {
                    let start = expressions.first().unwrap().span().start;
                    let end = expressions.last().unwrap().span().end;
                    Span::new(start, end)
                };
                
                Program { expressions, span }
            })
            .padded_by(text::whitespace())
    }

    /// Parser for expressions
    fn expression_parser(&self) -> impl Parser<char, Expression, Error = Simple<char>> + Clone {
        recursive(|expr| {
            let atom = self.atom_parser();
            
            // List form (call, special forms)
            let list_form = expr
                .clone()
                .separated_by(text::whitespace())
                .delimited_by(
                    just('(').padded_by(text::whitespace()),
                    just(')').padded_by(text::whitespace()),
                )
                .map_with_span(|elements: Vec<Expression>, span: std::ops::Range<usize>| {
                    if elements.is_empty() {
                        return Expression::nil(Span::new(span.start, span.end));
                    }
                    
                    // Check for special forms
                    let keyword = match &elements[0] {
                        Expression::Literal { value: Value::Symbol(keyword), .. } => keyword,
                        Expression::Variable { name, .. } => name,
                        _ => return Expression::Call {
                            function: Box::new(elements[0].clone()),
                            arguments: elements[1..].to_vec(),
                            span: Span::new(span.start, span.end),
                        },
                    };
                    
                    match keyword.as_str() {
                        "define" => {
                            if elements.len() < 3 {
                                return Expression::nil(Span::new(span.start, span.end));
                            }
                            
                            // Check if it's a function definition
                            if let Expression::Call { function, arguments, .. } = &elements[1] {
                                if let Expression::Variable { name, .. } = &**function {
                                    let params = arguments
                                        .iter()
                                        .map(|arg| {
                                            if let Expression::Variable { name, span } = arg {
                                                Parameter {
                                                    name: name.clone(),
                                                    type_annotation: None,
                                                    span: *span,
                                                }
                                            } else {
                                                // Error case, but we'll handle it later
                                                Parameter {
                                                    name: "".to_string(),
                                                    type_annotation: None,
                                                    span: Span::default(),
                                                }
                                            }
                                        })
                                        .collect();
                                    
                                    return Expression::DefineFunction {
                                        name: name.clone(),
                                        parameters: params,
                                        body: elements[2..].to_vec(),
                                        span: Span::new(span.start, span.end),
                                    };
                                }
                            }
                            
                            // Regular definition
                            if let Expression::Variable { name, .. } = &elements[1] {
                                return Expression::Define {
                                    name: name.clone(),
                                    value: Box::new(elements[2].clone()),
                                    span: Span::new(span.start, span.end),
                                };
                            }
                            
                            // If the second element is not a variable, it might be a literal
                            if let Expression::Literal { value: Value::Symbol(name), .. } = &elements[1] {
                                return Expression::Define {
                                    name: name.clone(),
                                    value: Box::new(elements[2].clone()),
                                    span: Span::new(span.start, span.end),
                                };
                            }
                            
                            // Fallback to regular call if we can't parse as define
                            Expression::Call {
                                function: Box::new(elements[0].clone()),
                                arguments: elements[1..].to_vec(),
                                span: Span::new(span.start, span.end),
                            }
                        },
                        "lambda" => {
                            if elements.len() < 3 {
                                return Expression::nil(Span::new(span.start, span.end));
                            }
                            
                            // Extract parameters
                            let mut params = Vec::new();
                            if let Expression::Literal { value: Value::List(param_values), .. } = &elements[1] {
                                for param_value in param_values {
                                    if let Value::Symbol(name) = param_value {
                                        params.push(Parameter {
                                            name: name.clone(),
                                            type_annotation: None,
                                            span: Span::default(), // We don't have spans for individual params here
                                        });
                                    }
                                }
                            }
                            
                            Expression::Lambda {
                                parameters: params,
                                body: elements[2..].to_vec(),
                                span: Span::new(span.start, span.end),
                            }
                        },
                        "if" => {
                            let condition = elements.get(1).cloned().unwrap_or_else(|| 
                                Expression::boolean(false, Span::default())
                            );
                            
                            let then_expr = elements.get(2).cloned().unwrap_or_else(|| 
                                Expression::nil(Span::default())
                            );
                            
                            let else_expr = elements.get(3).cloned();
                            
                            Expression::If {
                                condition: Box::new(condition),
                                then_expr: Box::new(then_expr),
                                else_expr: else_expr.map(Box::new),
                                span: Span::new(span.start, span.end),
                            }
                        },
                        "let" => {
                            if elements.len() < 3 {
                                return Expression::nil(Span::new(span.start, span.end));
                            }

                            // Parse bindings: expect a list of pairs: ((name expr) ...)
                            let mut bindings: Vec<Binding> = Vec::new();

                            // The bindings list is represented (by our general list parser) as an Expression
                            // that is typically a Call where the function is the first pair, and the arguments
                            // are the remaining pairs. We reconstruct the sequence of pair expressions from it.
                            let mut binding_pair_exprs: Vec<Expression> = Vec::new();
                            match &elements[1] {
                                Expression::Call { function, arguments, .. } => {
                                    // First pair is the function; rest are in arguments
                                    binding_pair_exprs.push((**function).clone());
                                    binding_pair_exprs.extend(arguments.iter().cloned());
                                }
                                // In case of a single pair like: (let ((x 1)) ...), the inner list might still arrive as a single element
                                other => {
                                    binding_pair_exprs.push(other.clone());
                                }
                            }

                            for pair_expr in binding_pair_exprs {
                                match pair_expr {
                                    // Each pair should look like: (name value)
                                    Expression::Call { function, arguments, span: pair_span } => {
                                        // Expect function to be variable (the binding name)
                                        if let Expression::Variable { name, .. } = *function {
                                            if arguments.len() != 1 {
                                                // Malformed binding; skip gracefully (could also error)
                                                continue;
                                            }
                                            let value_expr = arguments[0].clone();
                                            bindings.push(Binding {
                                                name,
                                                value: value_expr,
                                                span: pair_span,
                                            });
                                        }
                                    }
                                    _ => {
                                        // Not a valid binding pair; ignore for now
                                    }
                                }
                            }

                            Expression::Let {
                                bindings,
                                body: elements[2..].to_vec(),
                                span: Span::new(span.start, span.end),
                            }
                        },
                        "begin" => {
                            Expression::Begin {
                                expressions: elements[1..].to_vec(),
                                span: Span::new(span.start, span.end),
                            }
                        },
                        "quote" => {
                            if elements.len() < 2 {
                                return Expression::nil(Span::new(span.start, span.end));
                            }
                            
                            Expression::Quote {
                                expression: Box::new(elements[1].clone()),
                                span: Span::new(span.start, span.end),
                            }
                        },
                        _ => {
                            // Regular function call
                            Expression::Call {
                                function: Box::new(elements[0].clone()),
                                arguments: elements[1..].to_vec(),
                                span: Span::new(span.start, span.end),
                            }
                        }
                    }
                });
            
            atom.or(list_form)
        })
    }

    /// Parser for atomic expressions
    fn atom_parser(&self) -> impl Parser<char, Expression, Error = Simple<char>> + Clone {
        // Integer literals
        let integer = text::int::<char, Simple<char>>(10)
            .map(|s: String| s.parse::<i64>().unwrap())
            .map_with_span(|n: i64, span: std::ops::Range<usize>| {
                Expression::integer(n, Span::new(span.start, span.end))
            });
        
        // Float literals
        let float = text::int::<char, Simple<char>>(10)
            .then(just('.'))
            .then(text::digits::<char, Simple<char>>(10))
            .map(|((i, _), f)| format!("{}.{}", i, f).parse::<f64>().unwrap())
            .map_with_span(|n: f64, span: std::ops::Range<usize>| {
                Expression::float(n, Span::new(span.start, span.end))
            });
        
        // Boolean literals
        let boolean = just("#t").to(true)
            .or(just("#f").to(false))
            .map_with_span(|b: bool, span: std::ops::Range<usize>| {
                Expression::boolean(b, Span::new(span.start, span.end))
            });
        
        // String literals
        let string = just('"')
            .ignore_then(none_of('"').repeated())
            .then_ignore(just('"'))
            .collect::<String>()
            .map_with_span(|s: String, span: std::ops::Range<usize>| {
                Expression::string(s, Span::new(span.start, span.end))
            });
        
        // Variable references / symbols: allow Scheme-style identifiers including '?', '!'
        let sym_start = one_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>?!@$%^&_~");
        let sym_rest = one_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-*/=<>?!@$%^&_~")
            .repeated()
            .collect::<String>();
        let variable = sym_start
            .then(sym_rest)
            .map(|(c, rest): (char, String)| {
                let mut s = String::new();
                s.push(c);
                s.push_str(&rest);
                s
            })
            .map_with_span(|s: String, span: std::ops::Range<usize>| {
                Expression::variable(s, Span::new(span.start, span.end))
            });
        
        choice((
            float,
            integer,
            boolean,
            string,
            variable,
        )).padded_by(text::whitespace())
    }
}

/// Parse a complete program
pub fn parse(source: &str) -> Result<Program> {
    MoriaParser::new().parse_program(source)
}

/// Parse a single expression
pub fn parse_expression(source: &str) -> Result<Expression> {
    MoriaParser::new().parse_expression(source)
}

/// Preprocess source to strip `#@` annotations so that annotated code remains parsable in the minimal bootstrap.
/// Supports single-line `#@name(...)` and multi-line parenthesized forms.
fn preprocess_annotations(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut out = String::with_capacity(source.len());
    let mut i = 0usize;
    while i < bytes.len() {
        // Strip line comments starting with ';' until newline
        if bytes[i] == b';' {
            while i < bytes.len() && bytes[i] != b'\n' { i += 1; }
            if i < bytes.len() { out.push('\n'); i += 1; }
            continue;
        }
        // Match '#@'
        if bytes[i] == b'#' && i + 1 < bytes.len() && bytes[i + 1] == b'@' {
            // Skip until we either see a '(' starting the argument list, then skip the balanced parens,
            // or until end of line if no '('.
            i += 2;
            // Skip identifier characters of annotation name
            while i < bytes.len() {
                let c = bytes[i] as char;
                if c.is_alphanumeric() || c == '-' || c == '_' { i += 1; } else { break; }
            }
            // Skip optional whitespace
            while i < bytes.len() && (bytes[i] as char).is_whitespace() && bytes[i] != b'\n' { i += 1; }
            if i < bytes.len() && bytes[i] == b'(' {
                // Skip balanced parentheses region
                let mut depth = 0i32;
                while i < bytes.len() {
                    let ch = bytes[i] as char;
                    if ch == '(' { depth += 1; }
                    if ch == ')' { depth -= 1; }
                    i += 1;
                    if depth == 0 { break; }
                }
                // Optionally skip trailing whitespace/newline
                while i < bytes.len() && (bytes[i] as char).is_whitespace() { i += 1; }
            } else {
                // No argument list; skip until end of line
                while i < bytes.len() && bytes[i] != b'\n' { i += 1; }
                // Include newline to keep line structure
                if i < bytes.len() { out.push('\n'); i += 1; }
            }
            continue;
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parse_integer() {
        let expr = parse_expression("42").unwrap();
        assert!(matches!(expr, Expression::Literal { value: Value::Integer(42), .. }));
    }
    
    #[test]
    fn test_parse_boolean() {
        let expr = parse_expression("#t").unwrap();
        assert!(matches!(expr, Expression::Literal { value: Value::Boolean(true), .. }));
        
        let expr = parse_expression("#f").unwrap();
        assert!(matches!(expr, Expression::Literal { value: Value::Boolean(false), .. }));
    }
    
    #[test]
    fn test_parse_string() {
        let expr = parse_expression("\"hello\"").unwrap();
        assert!(matches!(expr, Expression::Literal { value: Value::String(s), .. } if s == "hello"));
    }
    
    #[test]
    fn test_parse_symbol() {
        let expr = parse_expression("symbol").unwrap();
        assert!(matches!(expr, Expression::Variable { name, .. } if name == "symbol"));
    }
    
    #[test]
    fn test_parse_simple_call() {
        let expr = parse_expression("(+ 1 2)").unwrap();
        if let Expression::Call { function, arguments, .. } = expr {
            assert!(matches!(*function, Expression::Variable { name, .. } if name == "+"));
            assert_eq!(arguments.len(), 2);
        } else {
            panic!("Expected Call expression");
        }
    }
    
    #[test]
    fn test_parse_define() {
        let expr = parse_expression("(define x 42)").unwrap();
        if let Expression::Define { name, value, .. } = expr {
            assert_eq!(name, "x");
            if let Expression::Literal { value: Value::Integer(n), .. } = &*value {
                assert_eq!(*n, 42);
            } else {
                panic!("Expected integer literal");
            }
        } else {
            panic!("Expected Define expression, got {:?}", expr);
        }
    }
    
    #[test]
    fn test_parse_function_call() {
        let expr = parse_expression("(factorial n)").unwrap();
        if let Expression::Call { function, arguments, .. } = expr {
            assert!(matches!(*function, Expression::Variable { name, .. } if name == "factorial"));
            assert_eq!(arguments.len(), 1);
        } else {
            panic!("Expected Call expression");
        }
    }
    
    #[test]
    fn test_parse_define_function() {
        let expr = parse_expression("(define (factorial n) 42)").unwrap();
        if let Expression::DefineFunction { name, parameters, body, .. } = expr {
            assert_eq!(name, "factorial");
            assert_eq!(parameters.len(), 1);
            assert_eq!(parameters[0].name, "n");
            assert_eq!(body.len(), 1);
        } else {
            panic!("Expected DefineFunction expression, got {:?}", expr);
        }
    }
} 