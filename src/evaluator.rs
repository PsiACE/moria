//! Simple evaluator for Moria language

use std::collections::HashMap;
use crate::ast::*;
use crate::error::{MoriaError, Result, Span};

/// Environment for variable bindings
#[derive(Debug, Clone, Default)]
pub struct Environment {
    bindings: HashMap<String, Value>,
    parent: Option<Box<Environment>>,
}

impl Environment {
    /// Create a new empty environment
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }
    
    /// Create a new environment with standard library bindings
    pub fn with_stdlib() -> Self {
        let mut env = Self::new();
        
        // Add standard arithmetic operations
        env.define("+".to_string(), Value::Symbol("+".to_string()));
        env.define("-".to_string(), Value::Symbol("-".to_string()));
        env.define("*".to_string(), Value::Symbol("*".to_string()));
        env.define("/".to_string(), Value::Symbol("/".to_string()));
        
        // Add standard comparison operations
        env.define("=".to_string(), Value::Symbol("=".to_string()));
        env.define("<".to_string(), Value::Symbol("<".to_string()));
        env.define(">".to_string(), Value::Symbol(">".to_string()));
        env.define("<=".to_string(), Value::Symbol("<=".to_string()));
        env.define(">=".to_string(), Value::Symbol(">=".to_string()));

        // List and boolean utilities
        env.define("list".to_string(), Value::Symbol("list".to_string()));
        env.define("cons".to_string(), Value::Symbol("cons".to_string()));
        env.define("car".to_string(), Value::Symbol("car".to_string()));
        env.define("cdr".to_string(), Value::Symbol("cdr".to_string()));
        env.define("null?".to_string(), Value::Symbol("null?".to_string()));
        env.define("not".to_string(), Value::Symbol("not".to_string()));
        env.define("equal?".to_string(), Value::Symbol("equal?".to_string()));
        
        env
    }
    
    /// Create a new child environment
    pub fn extend(&self) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(self.clone())),
        }
    }
    
    /// Define a variable in the current environment
    pub fn define(&mut self, name: String, value: Value) {
        self.bindings.insert(name, value);
    }
    
    /// Look up a variable in the environment
    pub fn lookup(&self, name: &str) -> Option<Value> {
        if let Some(value) = self.bindings.get(name) {
            Some(value.clone())
        } else if let Some(parent) = &self.parent {
            parent.lookup(name)
        } else {
            None
        }
    }
    
    /// Set a variable's value
    pub fn set(&mut self, name: &str, value: Value) -> Result<()> {
        if self.bindings.contains_key(name) {
            self.bindings.insert(name.to_string(), value);
            Ok(())
        } else if let Some(parent) = &mut self.parent {
            parent.set(name, value)
        } else {
            Err(MoriaError::Runtime {
                message: format!("Undefined variable: {}", name),
                span: None,
                context: None,
            })
        }
    }
}

/// Simple evaluator for Moria expressions
#[derive(Default)]
pub struct Evaluator {
    pub(crate) environment: Environment,
}

impl Evaluator {
    /// Create a new evaluator with an empty environment
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }
    
    /// Create a new evaluator with standard library bindings
    pub fn with_stdlib() -> Self {
        Self {
            environment: Environment::with_stdlib(),
        }
    }
    
    /// Evaluate a program
    pub fn evaluate_program(&mut self, program: &Program) -> Result<Value> {
        let mut result = Value::Nil;
        
        for expr in &program.expressions {
            result = self.evaluate(expr)?;
        }
        
        Ok(result)
    }
    
    /// Evaluate a single expression
    pub fn evaluate(&mut self, expr: &Expression) -> Result<Value> {
        match expr {
            Expression::Literal { value, .. } => Ok(value.clone()),
            
            Expression::Variable { name, span } => {
                self.environment.lookup(name)
                    .ok_or_else(|| MoriaError::Runtime {
                        message: format!("Undefined variable: {}", name),
                        span: Some(*span),
                        context: None,
                    })
            },
            
            Expression::Call { function, arguments, span } => {
                self.evaluate_call(function, arguments, span)
            },
            
            Expression::Lambda { parameters, body, span: _ } => {
                // Capture the current environment for closure
                Ok(Value::Lambda {
                    function_name: None, // Anonymous lambda
                    parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                    body: body.clone(),
                    env: Some(self.environment.clone()),
                })
            },
            
            Expression::Let { bindings, body, span: _ } => {
                // Create a new environment for the let bindings
                let mut new_env = self.environment.extend();
                
                // Evaluate bindings in the original environment
                for binding in bindings {
                    let value = self.evaluate(&binding.value)?;
                    new_env.define(binding.name.clone(), value);
                }
                
                // Swap in the new environment
                let old_env = std::mem::replace(&mut self.environment, new_env);
                
                // Evaluate body in the new environment
                let mut result = Value::Nil;
                for expr in body {
                    result = self.evaluate(expr)?;
                }
                
                // Restore the old environment
                self.environment = old_env;
                
                Ok(result)
            },
            
            Expression::If { condition, then_expr, else_expr, span: _ } => {
                let condition_value = self.evaluate(condition)?;
                
                match condition_value {
                    Value::Boolean(false) => {
                        if let Some(else_expr) = else_expr {
                            self.evaluate(else_expr)
                        } else {
                            Ok(Value::Nil)
                        }
                    },
                    _ => self.evaluate(then_expr),
                }
            },
            
            Expression::Define { name, value, span: _ } => {
                let value = self.evaluate(value)?;
                self.environment.define(name.clone(), value.clone());
                Ok(value)
            },
            
            Expression::DefineFunction { name, parameters, body, span: _ } => {
                // Create a Value::Lambda and bind it to the name
                let lambda = Value::Lambda {
                    function_name: Some(name.clone()),
                    parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                    body: body.clone(),
                    env: Some(self.environment.clone()),
                };
                
                // Bind the function to the environment BEFORE evaluating the body
                // This allows recursive calls to work
                self.environment.define(name.clone(), lambda.clone());
                
                Ok(lambda)
            },
            
            Expression::Begin { expressions, span: _ } => {
                let mut result = Value::Nil;
                for expr in expressions {
                    result = self.evaluate(expr)?;
                }
                Ok(result)
            },
            
            Expression::Quote { expression, span: _ } => {
                self.evaluate_quote(expression)
            },
        }
    }
    
    /// Evaluate a function call
    fn evaluate_call(&mut self, function: &Expression, arguments: &[Expression], span: &Span) -> Result<Value> {
        let function_value = self.evaluate(function)?;
        
        // Evaluate arguments
        let mut arg_values = Vec::new();
        for arg in arguments {
            arg_values.push(self.evaluate(arg)?);
        }
        
        // Check if it's a built-in function
        match function_value {
            Value::Symbol(name) => {
                match name.as_str() {
                    "+" | "-" | "*" | "/" => self.arithmetic_op_symbol(name.as_str(), &arg_values),
                    "=" | "<" | ">" | "<=" | ">=" => self.numeric_comparison_op(&arg_values, name.as_str()),
                    "list" => Ok(Value::List(arg_values)),
                    "cons" => self.builtin_cons(&arg_values, span),
                    "car" => self.builtin_car(&arg_values, span),
                    "cdr" => self.builtin_cdr(&arg_values, span),
                    "null?" => Ok(Value::Boolean(self.is_null_list(&arg_values))),
                    "not" => Ok(Value::Boolean(match arg_values.get(0) { Some(Value::Boolean(false)) => true, Some(_) => false, None => true })),
                    "equal?" => {
                        if arg_values.len() != 2 {
                            return Err(MoriaError::Runtime { message: "Expected 2 arguments".to_string(), span: Some(*span), context: None });
                        }
                        Ok(Value::Boolean(arg_values[0] == arg_values[1]))
                    }
                    _ => Err(MoriaError::Runtime {
                        message: format!("Unknown function: {}", name),
                        span: Some(*span),
                        context: None,
                    }),
                }
            },
            Value::Lambda { function_name, parameters, body, env } => {
                if arguments.len() != parameters.len() {
                    return Err(MoriaError::Runtime {
                        message: format!("Expected {} arguments, got {}", parameters.len(), arguments.len()),
                        span: Some(*span),
                        context: None,
                    });
                }
                // Create a new environment for the lambda call
                let mut lambda_env = if let Some(env) = env {
                    env.extend()
                } else {
                    self.environment.extend()
                };
                // Bind arguments to parameters
                for (param, arg) in parameters.iter().zip(arguments.iter()) {
                    let value = self.evaluate(arg)?;
                    lambda_env.define(param.clone(), value);
                }
                // For recursive functions, we need to include the function itself in the environment
                // This is a simplified approach - in a real implementation, we'd need to handle the function name
                if let Some(func_name) = function_name {
                    // Include the function itself in the lambda's environment for recursive calls
                    lambda_env.define(func_name.clone(), Value::Lambda {
                        function_name: Some(func_name.clone()),
                        parameters: parameters.clone(),
                        body: body.clone(),
                        env: Some(lambda_env.clone()),
                    });
                }
                // Swap in the lambda environment
                let old_env = std::mem::replace(&mut self.environment, lambda_env);
                // Evaluate the body expressions in order
                let mut result = Value::Nil;
                for expr in body.iter() {
                    result = self.evaluate(expr)?;
                }
                // Restore the old environment
                self.environment = old_env;
                Ok(result)
            },
            Value::List(items) => {
                if items.len() >= 3 {
                    if let Value::Symbol(keyword) = &items[0] {
                        if keyword == "lambda" {
                            // This is a lambda function
                            if let Value::List(params) = &items[1] {
                                // Create a new environment for the lambda
                                let mut lambda_env = self.environment.extend();
                                
                                // Bind arguments to parameters
                                for (i, param) in params.iter().enumerate() {
                                    if let Value::Symbol(name) = param {
                                        let value = if i < arg_values.len() {
                                            arg_values[i].clone()
                                        } else {
                                            Value::Nil
                                        };
                                        
                                        lambda_env.define(name.clone(), value);
                                    }
                                }
                                
                                // Swap in the lambda environment
                                let old_env = std::mem::replace(&mut self.environment, lambda_env);
                                
                                // Evaluate the lambda body
                                let mut result = Value::Nil;
                                for body_value in &items[2..] {
                                    // Convert Value back to Expression for evaluation
                                    // This is a simplification: in a real interpreter, the lambda body would be stored as AST expressions
                                    // Here, we assume the body is always a quoted Expression::Literal
                                    if let Value::Symbol(ref s) = body_value {
                                        // Try to look up the variable/expression in the environment
                                        if let Some(expr) = self.environment.lookup(s) {
                                            result = expr;
                                        } else {
                                            // If not found, treat as symbol
                                            result = Value::Symbol(s.clone());
                                        }
                                    } else {
                                        // For literals, just use the value
                                        result = body_value.clone();
                                    }
                                }
                                // Restore the old environment
                                self.environment = old_env;
                                Ok(result)
                            } else {
                                Err(MoriaError::Runtime {
                                    message: "Invalid lambda parameters".to_string(),
                                    span: Some(*span),
                                    context: None,
                                })
                            }
                        } else {
                            Err(MoriaError::Runtime {
                                message: format!("Not a function: {}", keyword),
                                span: Some(*span),
                                context: None,
                            })
                        }
                    } else {
                        Err(MoriaError::Runtime {
                            message: "Not a function".to_string(),
                            span: Some(*span),
                            context: None,
                        })
                    }
                } else {
                    Err(MoriaError::Runtime {
                        message: "Invalid function".to_string(),
                        span: Some(*span),
                        context: None,
                    })
                }
            },
            _ => Err(MoriaError::Runtime {
                message: format!("Not a function: {}", function_value),
                span: Some(*span),
                context: None,
            }),
        }
    }
    
    /// Evaluate quoted expression
    pub(crate) fn evaluate_quote(&self, expr: &Expression) -> Result<Value> {
        match expr {
            Expression::Literal { value, .. } => Ok(value.clone()),
            Expression::Variable { name, .. } => Ok(Value::Symbol(name.clone())),
            Expression::Call { function, arguments, .. } => {
                let mut items = Vec::new();
                
                // Quote the function
                if let Expression::Variable { name, .. } = &**function {
                    items.push(Value::Symbol(name.clone()));
                } else {
                    // This is a simplification - in a real evaluator we'd handle this properly
                    items.push(Value::Symbol("unknown".to_string()));
                }
                
                // Quote the arguments
                for arg in arguments {
                    if let Expression::Literal { value, .. } = arg {
                        items.push(value.clone());
                    } else if let Expression::Variable { name, .. } = arg {
                        items.push(Value::Symbol(name.clone()));
                    } else {
                        // This is a simplification - in a real evaluator we'd handle this properly
                        items.push(Value::Symbol("unknown".to_string()));
                    }
                }
                
                Ok(Value::List(items))
            },
            _ => Ok(Value::Nil), // Simplification
        }
    }
    
    /// Evaluate arithmetic operation over integers and floats with simple numeric promotion
    pub(crate) fn arithmetic_op_symbol(&self, symbol: &str, args: &[Value]) -> Result<Value> {
        // Handle identity values when no args
        if args.is_empty() {
            return Ok(match symbol {
                "+" => Value::Integer(0),
                "*" => Value::Integer(1),
                "-" | "/" => Value::Integer(0), // minimal behavior
                _ => Value::Integer(0),
            });
        }

        // Helper to coerce Value to numeric
        enum Numeric { Int(i64), Float(f64) }
        impl Numeric {
            fn is_float(&self) -> bool { matches!(self, Numeric::Float(_)) }
            fn as_f64(&self) -> f64 { match self { Numeric::Int(i) => *i as f64, Numeric::Float(f) => *f } }
        }
        fn to_numeric(v: &Value) -> Result<Numeric> {
            match v {
                Value::Integer(i) => Ok(Numeric::Int(*i)),
                Value::Float(f) => Ok(Numeric::Float(*f)),
                _ => Err(MoriaError::Runtime { message: "Expected number".to_string(), span: None, context: None })
            }
        }

        let mut nums: Vec<Numeric> = Vec::with_capacity(args.len());
        for a in args {
            nums.push(to_numeric(a)?);
        }
        let any_float = nums.iter().any(|n| n.is_float());

        match symbol {
            "+" => {
                if any_float {
                    let sum = nums.iter().map(|n| n.as_f64()).sum::<f64>();
                    Ok(Value::Float(sum))
                } else {
                    let sum = nums.iter().map(|n| match n { Numeric::Int(i) => *i, _ => 0 }).sum::<i64>();
                    Ok(Value::Integer(sum))
                }
            }
            "-" => {
                if nums.len() == 1 {
                    // unary negation
                    return if any_float {
                        Ok(Value::Float(-nums[0].as_f64()))
                    } else {
                        match nums[0] { Numeric::Int(i) => Ok(Value::Integer(-i)), _ => Ok(Value::Integer(0)) }
                    };
                }
                if any_float {
                    let mut acc = nums[0].as_f64();
                    for n in &nums[1..] { acc -= n.as_f64(); }
                    Ok(Value::Float(acc))
                } else {
                    let mut acc = match nums[0] { Numeric::Int(i) => i, _ => 0 };
                    for n in &nums[1..] {
                        if let Numeric::Int(i) = n { acc -= i; }
                    }
                    Ok(Value::Integer(acc))
                }
            }
            "*" => {
                if any_float {
                    let mut acc = 1.0f64;
                    for n in &nums { acc *= n.as_f64(); }
                    Ok(Value::Float(acc))
                } else {
                    let mut acc: i64 = 1;
                    for n in &nums { if let Numeric::Int(i) = n { acc *= *i; } }
                    Ok(Value::Integer(acc))
                }
            }
            "/" => {
                if nums.len() == 1 {
                    // reciprocal
                    let denom = nums[0].as_f64();
                    if denom == 0.0 { return Err(MoriaError::Runtime { message: "Division by zero".to_string(), span: None, context: None }); }
                    return Ok(Value::Float(1.0 / denom));
                }
                // Compute as f64 if any float involved, else try integer division with fallback
                if any_float {
                    let mut acc = nums[0].as_f64();
                    for n in &nums[1..] {
                        let d = n.as_f64();
                        if d == 0.0 { return Err(MoriaError::Runtime { message: "Division by zero".to_string(), span: None, context: None }); }
                        acc /= d;
                    }
                    Ok(Value::Float(acc))
                } else {
                    // All ints; if divides exactly at each step, keep int; otherwise promote to float
                    let mut acc_i = if let Numeric::Int(i) = nums[0] { i } else { 0 };
                    let mut result_float: Option<f64> = None;
                    for n in &nums[1..] {
                        let d_i = if let Numeric::Int(i) = n { *i } else { 0 };
                        if d_i == 0 { return Err(MoriaError::Runtime { message: "Division by zero".to_string(), span: None, context: None }); }
                        if result_float.is_some() || acc_i % d_i != 0 {
                            // promote
                            let mut acc_f = result_float.unwrap_or(acc_i as f64);
                            acc_f /= d_i as f64;
                            result_float = Some(acc_f);
                        } else {
                            acc_i /= d_i;
                        }
                    }
                    if let Some(f) = result_float { Ok(Value::Float(f)) } else { Ok(Value::Integer(acc_i)) }
                }
            }
            _ => Err(MoriaError::Runtime { message: format!("Unknown arithmetic operator: {}", symbol), span: None, context: None })
        }
    }

    pub(crate) fn is_null_list(&self, args: &[Value]) -> bool {
        if args.len() != 1 { return false; }
        match &args[0] {
            Value::Nil => true,
            Value::List(v) => v.is_empty(),
            _ => false,
        }
    }

    pub(crate) fn builtin_cons(&self, args: &[Value], span: &Span) -> Result<Value> {
        if args.len() != 2 {
            return Err(MoriaError::Runtime { message: "Expected 2 arguments".to_string(), span: Some(*span), context: None });
        }
        let head = args[0].clone();
        match &args[1] {
            Value::List(tail) => {
                let mut v = Vec::with_capacity(tail.len() + 1);
                v.push(head);
                v.extend(tail.clone());
                Ok(Value::List(v))
            }
            Value::Nil => Ok(Value::List(vec![head])),
            other => Err(MoriaError::Runtime { message: format!("cons expects list as second argument, got {}", other.type_name()), span: Some(*span), context: None })
        }
    }

    pub(crate) fn builtin_car(&self, args: &[Value], span: &Span) -> Result<Value> {
        if args.len() != 1 { return Err(MoriaError::Runtime { message: "Expected 1 argument".to_string(), span: Some(*span), context: None }); }
        match &args[0] {
            Value::List(v) if !v.is_empty() => Ok(v[0].clone()),
            Value::Nil => Err(MoriaError::Runtime { message: "car of empty list".to_string(), span: Some(*span), context: None }),
            other => Err(MoriaError::Runtime { message: format!("car expects list, got {}", other.type_name()), span: Some(*span), context: None }),
        }
    }

    pub(crate) fn builtin_cdr(&self, args: &[Value], span: &Span) -> Result<Value> {
        if args.len() != 1 { return Err(MoriaError::Runtime { message: "Expected 1 argument".to_string(), span: Some(*span), context: None }); }
        match &args[0] {
            Value::List(v) if !v.is_empty() => Ok(Value::List(v[1..].to_vec())),
            Value::Nil => Err(MoriaError::Runtime { message: "cdr of empty list".to_string(), span: Some(*span), context: None }),
            other => Err(MoriaError::Runtime { message: format!("cdr expects list, got {}", other.type_name()), span: Some(*span), context: None }),
        }
    }

    /// Evaluate numeric comparison operation (two args) supporting ints and floats
    pub(crate) fn numeric_comparison_op(&self, args: &[Value], op: &str) -> Result<Value> {
        if args.len() != 2 {
            return Err(MoriaError::Runtime { message: "Expected 2 arguments".to_string(), span: None, context: None });
        }
        let to_num = |v: &Value| -> Result<(bool, f64, i64)> { // (is_float, as_f64, as_i64)
            match v {
                Value::Integer(i) => Ok((false, *i as f64, *i)),
                Value::Float(f) => Ok((true, *f, 0)),
                _ => Err(MoriaError::Runtime { message: "Expected number".to_string(), span: None, context: None })
            }
        };
        let (a_is_f, a_f, a_i) = to_num(&args[0])?;
        let (b_is_f, b_f, b_i) = to_num(&args[1])?;
        let result = if a_is_f || b_is_f {
            match op { "=" => a_f == b_f, "<" => a_f < b_f, ">" => a_f > b_f, "<=" => a_f <= b_f, ">=" => a_f >= b_f, _ => false }
        } else {
            match op { "=" => a_i == b_i, "<" => a_i < b_i, ">" => a_i > b_i, "<=" => a_i <= b_i, ">=" => a_i >= b_i, _ => false }
        };
        Ok(Value::Boolean(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_expression;
    
    #[test]
    fn test_evaluate_literal() {
        let mut evaluator = Evaluator::new();
        let expr = parse_expression("42").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(42));
    }
    
    #[test]
    fn test_evaluate_arithmetic() {
        let mut evaluator = Evaluator::with_stdlib();
        
        let expr = parse_expression("(+ 1 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(3));
        
        let expr = parse_expression("(- 5 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(3));
        
        let expr = parse_expression("(* 2 3)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(6));
        
        let expr = parse_expression("(/ 6 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(3));
    }
    
    #[test]
    fn test_evaluate_comparison() {
        let mut evaluator = Evaluator::with_stdlib();
        
        let expr = parse_expression("(= 1 1)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Boolean(true));
        
        let expr = parse_expression("(< 1 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Boolean(true));
        
        let expr = parse_expression("(> 1 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Boolean(false));
    }
    
    #[test]
    fn test_evaluate_define() {
        let mut evaluator = Evaluator::new();
        
        let expr = parse_expression("(define x 42)").unwrap();
        evaluator.evaluate(&expr).unwrap();
        
        let expr = parse_expression("x").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(42));
    }
    
    #[test]
    fn test_evaluate_if() {
        let mut evaluator = Evaluator::with_stdlib();
        
        let expr = parse_expression("(if #t 1 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(1));
        
        let expr = parse_expression("(if #f 1 2)").unwrap();
        let result = evaluator.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Integer(2));
    }
} 