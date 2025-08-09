//! Parser for Moria language using Chumsky 0.10 with token-based parsing

use chumsky::{input::ValueInput, prelude::*};

use crate::ast::*;
use crate::error::{MoriaError, Result, Span};

pub type CSpan = chumsky::span::SimpleSpan;
pub type Spanned<T> = (T, CSpan);

#[derive(Clone, Debug, PartialEq)]
enum Token<'src> {
    LParen,
    RParen,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(&'src str),
    Ident(&'src str),
}

/// Token lexer
fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, CSpan>>> {
    // integers and floats
    let int_part = text::int(10);
    let float = int_part
        .then(just('.').then(text::digits(10)))
        .to_slice()
        .from_str()
        .unwrapped()
        .map(Token::Float);

    let int = int_part.to_slice().from_str().unwrapped().map(Token::Int);

    let boolean = just("#t")
        .to(Token::Bool(true))
        .or(just("#f").to(Token::Bool(false)));

    let string = just('"')
        .ignore_then(none_of('"').repeated().to_slice())
        .then_ignore(just('"'))
        .map(Token::Str);

    // Scheme-like identifiers
    let ident = any()
        .filter(|c: &char| !c.is_whitespace() && *c != '(' && *c != ')' && *c != '"' && *c != ';')
        .repeated()
        .at_least(1)
        .to_slice()
        .map(Token::Ident);

    let lparen = just('(').to(Token::LParen);
    let rparen = just(')').to(Token::RParen);

    // comments: ';' to end of line
    let comment = just(';')
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    let token = float
        .or(int)
        .or(boolean)
        .or(string)
        .or(ident)
        .or(lparen)
        .or(rparen);

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

/// Parser for expressions over tokens
fn expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Expression, extra::Err<Rich<'tokens, Token<'src>, CSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = CSpan>,
{
    recursive(|expr| {
        let atom = select! {
            Token::Bool(b) => b,
        }
        .map_with(|b, e| {
            let s: CSpan = e.span();
            Expression::boolean(b, Span::new(s.start, s.end))
        })
        .or(select! { Token::Int(i) => i }.map_with(|i, e| {
            let s: CSpan = e.span();
            Expression::integer(i, Span::new(s.start, s.end))
        }))
        .or(select! { Token::Float(f) => f }.map_with(|f, e| {
            let s: CSpan = e.span();
            Expression::float(f, Span::new(s.start, s.end))
        }))
        .or(select! { Token::Str(s) => s }.map_with(|s, e| {
            let sp: CSpan = e.span();
            Expression::string(s.to_string(), Span::new(sp.start, sp.end))
        }))
        .or(select! { Token::Ident(id) => id }.map_with(|id, e| {
            let sp: CSpan = e.span();
            Expression::variable(id.to_string(), Span::new(sp.start, sp.end))
        }));

        let list = expr
            .clone()
            .repeated()
            .collect::<Vec<_>>()
            .map_with(|elements, e| {
                let se: CSpan = e.span();
                let span = Span::new(se.start, se.end);
                if elements.is_empty() {
                    return Expression::nil(span);
                }
                let keyword = match &elements[0] {
                    Expression::Literal {
                        value: Value::Symbol(s),
                        ..
                    } => s.clone(),
                    Expression::Variable { name, .. } => name.clone(),
                    _ => String::new(),
                };
                match keyword.as_str() {
                    "define" => {
                        if elements.len() < 3 {
                            return Expression::nil(span);
                        }
                        if let Expression::Call { .. } = &elements[1] {
                            // already a call form treated as function definition by char-based parser
                            if let Expression::Call {
                                function,
                                arguments,
                                ..
                            } = &elements[1]
                            {
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
                                                Parameter {
                                                    name: String::new(),
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
                                        span,
                                    };
                                }
                            }
                        }
                        if let Expression::Variable { name, .. } = &elements[1] {
                            Expression::Define {
                                name: name.clone(),
                                value: Box::new(elements[2].clone()),
                                span,
                            }
                        } else if let Expression::Literal {
                            value: Value::Symbol(name),
                            ..
                        } = &elements[1]
                        {
                            Expression::Define {
                                name: name.clone(),
                                value: Box::new(elements[2].clone()),
                                span,
                            }
                        } else {
                            Expression::Call {
                                function: Box::new(elements[0].clone()),
                                arguments: elements[1..].to_vec(),
                                span,
                            }
                        }
                    }
                    "lambda" => {
                        if elements.len() < 3 {
                            return Expression::nil(span);
                        }
                        let mut params = Vec::new();
                        if let Expression::Literal {
                            value: Value::List(param_values),
                            ..
                        } = &elements[1]
                        {
                            for p in param_values {
                                if let Value::Symbol(n) = p {
                                    params.push(Parameter {
                                        name: n.clone(),
                                        type_annotation: None,
                                        span: Span::default(),
                                    });
                                }
                            }
                        }
                        Expression::Lambda {
                            parameters: params,
                            body: elements[2..].to_vec(),
                            span,
                        }
                    }
                    "if" => {
                        let condition = elements
                            .get(1)
                            .cloned()
                            .unwrap_or_else(|| Expression::boolean(false, Span::default()));
                        let then_expr = elements
                            .get(2)
                            .cloned()
                            .unwrap_or_else(|| Expression::nil(Span::default()));
                        let else_expr = elements.get(3).cloned();
                        Expression::If {
                            condition: Box::new(condition),
                            then_expr: Box::new(then_expr),
                            else_expr: else_expr.map(Box::new),
                            span,
                        }
                    }
                    "let" => {
                        if elements.len() < 3 {
                            return Expression::nil(span);
                        }
                        let mut bindings: Vec<Binding> = Vec::new();
                        let mut pairs: Vec<Expression> = Vec::new();
                        match &elements[1] {
                            Expression::Call {
                                function,
                                arguments,
                                ..
                            } => {
                                pairs.push((**function).clone());
                                pairs.extend(arguments.iter().cloned());
                            }
                            other => pairs.push(other.clone()),
                        }
                        for pair_expr in pairs {
                            if let Expression::Call {
                                function,
                                arguments,
                                span: pair_span,
                            } = pair_expr
                            {
                                if let Expression::Variable { name, .. } = *function {
                                    if arguments.len() == 1 {
                                        bindings.push(Binding {
                                            name,
                                            value: arguments[0].clone(),
                                            span: pair_span,
                                        });
                                    }
                                }
                            }
                        }
                        Expression::Let {
                            bindings,
                            body: elements[2..].to_vec(),
                            span,
                        }
                    }
                    "begin" => Expression::Begin {
                        expressions: elements[1..].to_vec(),
                        span,
                    },
                    "quote" => {
                        if elements.len() < 2 {
                            return Expression::nil(span);
                        }
                        Expression::Quote {
                            expression: Box::new(elements[1].clone()),
                            span,
                        }
                    }
                    _ => Expression::Call {
                        function: Box::new(elements[0].clone()),
                        arguments: elements[1..].to_vec(),
                        span,
                    },
                }
            })
            .delimited_by(just(Token::LParen), just(Token::RParen));

        atom.or(list)
    })
}

/// Parse a complete program
pub fn parse(source: &str) -> Result<Program> {
    let preprocessed = preprocess_annotations(source);
    let len = preprocessed.len();

    let (tokens, lex_errs) = lexer().parse(preprocessed.as_str()).into_output_errors();
    if let Some(tokens) = &tokens {
        let (exprs, parse_errs) = expr_parser()
            .repeated()
            .collect::<Vec<_>>()
            .parse(
                tokens
                    .as_slice()
                    .map((preprocessed.len()..preprocessed.len()).into(), |(t, s)| {
                        (t, s)
                    }),
            )
            .into_output_errors();
        if !lex_errs.is_empty() || !parse_errs.is_empty() {
            if let Some(e) = parse_errs.first() {
                let sp = e.span();
                return Err(MoriaError::Parse {
                    message: format!("{:?}", e),
                    span: Span::new(sp.start, sp.end),
                    context: None,
                });
            } else if let Some(e) = lex_errs.first() {
                let sp = e.span();
                return Err(MoriaError::Parse {
                    message: format!("{:?}", e),
                    span: Span::new(sp.start, sp.end),
                    context: None,
                });
            }
        }
        if let Some(expressions) = exprs {
            let span = if expressions.is_empty() {
                Span::default()
            } else {
                let s = expressions.first().unwrap().span().start;
                let e = expressions.last().unwrap().span().end;
                Span::new(s, e)
            };
            return Ok(Program { expressions, span });
        }
    }
    Err(MoriaError::Parse {
        message: "Failed to parse program".to_string(),
        span: Span::new(0, len),
        context: None,
    })
}

/// Parse a single expression
pub fn parse_expression(source: &str) -> Result<Expression> {
    let preprocessed = preprocess_annotations(source);
    let len = preprocessed.len();
    let (tokens, lex_errs) = lexer().parse(preprocessed.as_str()).into_output_errors();
    if let Some(tokens) = &tokens {
        let (expr, parse_errs) = expr_parser()
            .map_with(|e, es| (e, es.span()))
            .parse(
                tokens
                    .as_slice()
                    .map((preprocessed.len()..preprocessed.len()).into(), |(t, s)| {
                        (t, s)
                    }),
            )
            .into_output_errors();
        if !lex_errs.is_empty() || !parse_errs.is_empty() {
            if let Some(e) = parse_errs.first() {
                let sp = e.span();
                return Err(MoriaError::Parse {
                    message: format!("{:?}", e),
                    span: Span::new(sp.start, sp.end),
                    context: None,
                });
            } else if let Some(e) = lex_errs.first() {
                let sp = e.span();
                return Err(MoriaError::Parse {
                    message: format!("{:?}", e),
                    span: Span::new(sp.start, sp.end),
                    context: None,
                });
            }
        }
        if let Some((expr, _span)) = expr {
            return Ok(expr);
        }
    }
    Err(MoriaError::Parse {
        message: "Failed to parse expression".to_string(),
        span: Span::new(0, len),
        context: None,
    })
}

/// Preprocess source to strip `#@` annotations so that annotated code remains parsable.
/// Supports single-line `#@name(...)` and multi-line parenthesized forms.
fn preprocess_annotations(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut out = String::with_capacity(source.len());
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b';' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            if i < bytes.len() {
                out.push('\n');
                i += 1;
            }
            continue;
        }
        if bytes[i] == b'#' && i + 1 < bytes.len() && bytes[i + 1] == b'@' {
            i += 2;
            while i < bytes.len() {
                let c = bytes[i] as char;
                if c.is_alphanumeric() || c == '-' || c == '_' {
                    i += 1;
                } else {
                    break;
                }
            }
            while i < bytes.len() && (bytes[i] as char).is_whitespace() && bytes[i] != b'\n' {
                i += 1;
            }
            if i < bytes.len() && bytes[i] == b'(' {
                let mut depth = 0i32;
                while i < bytes.len() {
                    let ch = bytes[i] as char;
                    if ch == '(' {
                        depth += 1;
                    }
                    if ch == ')' {
                        depth -= 1;
                    }
                    i += 1;
                    if depth == 0 {
                        break;
                    }
                }
                while i < bytes.len() && (bytes[i] as char).is_whitespace() {
                    i += 1;
                }
            } else {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                if i < bytes.len() {
                    out.push('\n');
                    i += 1;
                }
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
        assert!(matches!(
            expr,
            Expression::Literal {
                value: Value::Integer(42),
                ..
            }
        ));
    }

    #[test]
    fn test_parse_boolean() {
        let expr = parse_expression("#t").unwrap();
        assert!(matches!(
            expr,
            Expression::Literal {
                value: Value::Boolean(true),
                ..
            }
        ));

        let expr = parse_expression("#f").unwrap();
        assert!(matches!(
            expr,
            Expression::Literal {
                value: Value::Boolean(false),
                ..
            }
        ));
    }

    #[test]
    fn test_parse_string() {
        let expr = parse_expression("\"hello\"").unwrap();
        assert!(
            matches!(expr, Expression::Literal { value: Value::String(s), .. } if s == "hello")
        );
    }

    #[test]
    fn test_parse_symbol() {
        let expr = parse_expression("symbol").unwrap();
        assert!(matches!(expr, Expression::Variable { name, .. } if name == "symbol"));
    }

    #[test]
    fn test_parse_simple_call() {
        let expr = parse_expression("(+ 1 2)").unwrap();
        if let Expression::Call {
            function,
            arguments,
            ..
        } = expr
        {
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
            if let Expression::Literal {
                value: Value::Integer(n),
                ..
            } = &*value
            {
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
        if let Expression::Call {
            function,
            arguments,
            ..
        } = expr
        {
            assert!(matches!(*function, Expression::Variable { name, .. } if name == "factorial"));
            assert_eq!(arguments.len(), 1);
        } else {
            panic!("Expected Call expression");
        }
    }

    #[test]
    fn test_parse_define_function() {
        let expr = parse_expression("(define (factorial n) 42)").unwrap();
        if let Expression::DefineFunction {
            name,
            parameters,
            body,
            ..
        } = expr
        {
            assert_eq!(name, "factorial");
            assert_eq!(parameters.len(), 1);
            assert_eq!(parameters[0].name, "n");
            assert_eq!(body.len(), 1);
        } else {
            panic!("Expected DefineFunction expression, got {:?}", expr);
        }
    }
}
