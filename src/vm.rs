use crate::ast::{Expression, Program, Value};
use crate::error::{MoriaError, Result, Span};

use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct Environment {
    bindings: HashMap<String, Value>,
    parent: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }
    pub fn with_stdlib() -> Self {
        let mut env = Self::new();
        for s in [
            "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "list", "cons", "car", "cdr", "null?",
            "not", "equal?",
        ] {
            env.define(s.to_string(), Value::Symbol(s.to_string()));
        }
        env
    }
    pub fn extend(&self) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(self.clone())),
        }
    }
    pub fn define(&mut self, name: String, value: Value) {
        self.bindings.insert(name, value);
    }
    pub fn lookup(&self, name: &str) -> Option<Value> {
        self.bindings
            .get(name)
            .cloned()
            .or_else(|| self.parent.as_ref().and_then(|p| p.lookup(name)))
    }
}

#[derive(Debug, Clone)]
pub enum Opcode {
    PushInt(i64),
    PushFloat(f64),
    PushBool(bool),
    PushString(String),
    PushNil,
    LoadVar(String),
    DefineVar(String),
    // list ops
    List(usize),
    Cons,
    Car,
    Cdr,
    NullQ,
    Not,
    EqualQ,
    // numeric ops
    Add,
    Sub,
    Mul,
    Div,
    CmpEq,
    CmpLt,
    CmpGt,
    CmpLe,
    CmpGe,
    // control flow
    JumpIfFalse(usize),
    Jump(usize),
    // call
    CallDynamic(usize),
    // quote
    PushQuoted(Box<Expression>),
    // env management
    PushEnv,
    PopEnv,
    // end
    Return,
}

#[derive(Default, Debug, Clone)]
pub struct Bytecode {
    pub code: Vec<Opcode>,
}

#[derive(Default)]
pub struct VM;

impl VM {
    pub fn run(&mut self, env: &mut Environment, code: &Bytecode) -> Result<Value> {
        let mut ip: usize = 0;
        let mut stack: Vec<Value> = Vec::new();
        let mut env_stack: Vec<Environment> = Vec::new();
        while ip < code.code.len() {
            match &code.code[ip] {
                Opcode::PushInt(i) => stack.push(Value::Integer(*i)),
                Opcode::PushFloat(f) => stack.push(Value::Float(*f)),
                Opcode::PushBool(b) => stack.push(Value::Boolean(*b)),
                Opcode::PushString(s) => stack.push(Value::String(s.clone())),
                Opcode::PushNil => stack.push(Value::Nil),
                Opcode::LoadVar(name) => {
                    if let Some(v) = env.lookup(name) {
                        stack.push(v);
                    } else {
                        return Err(MoriaError::Runtime {
                            message: format!("Undefined variable: {}", name),
                            span: None,
                            context: None,
                        });
                    }
                }
                Opcode::DefineVar(name) => {
                    let v = stack.pop().unwrap_or(Value::Nil);
                    env.define(name.clone(), v.clone());
                    stack.push(v);
                }
                // list ops
                Opcode::List(n) => {
                    let mut items = Vec::with_capacity(*n);
                    for _ in 0..*n {
                        items.push(stack.pop().unwrap_or(Value::Nil));
                    }
                    items.reverse();
                    stack.push(Value::List(items));
                }
                Opcode::Cons => {
                    let tail = stack.pop().unwrap_or(Value::Nil);
                    let head = stack.pop().unwrap_or(Value::Nil);
                    stack.push(builtin_cons(head, tail, &Span::default())?);
                }
                Opcode::Car => {
                    let list = stack.pop().unwrap_or(Value::Nil);
                    stack.push(builtin_car(list, &Span::default())?);
                }
                Opcode::Cdr => {
                    let list = stack.pop().unwrap_or(Value::Nil);
                    stack.push(builtin_cdr(list, &Span::default())?);
                }
                Opcode::NullQ => {
                    let v = stack.pop().unwrap_or(Value::Nil);
                    let is_null = match &v {
                        Value::Nil => true,
                        Value::List(xs) => xs.is_empty(),
                        _ => false,
                    };
                    stack.push(Value::Boolean(is_null));
                }
                Opcode::Not => {
                    let v = stack.pop().unwrap_or(Value::Boolean(false));
                    stack.push(Value::Boolean(matches!(v, Value::Boolean(false))));
                }
                Opcode::EqualQ => {
                    let b = stack.pop().unwrap_or(Value::Nil);
                    let a = stack.pop().unwrap_or(Value::Nil);
                    stack.push(Value::Boolean(a == b));
                }
                // numeric ops
                Opcode::Add => bin_num(&mut stack, |a, b| a + b)?,
                Opcode::Sub => bin_num(&mut stack, |a, b| a - b)?,
                Opcode::Mul => bin_num(&mut stack, |a, b| a * b)?,
                Opcode::Div => bin_div(&mut stack)?,
                Opcode::CmpEq => bin_cmp(&mut stack, |a, b| a == b)?,
                Opcode::CmpLt => bin_cmp(&mut stack, |a, b| a < b)?,
                Opcode::CmpGt => bin_cmp(&mut stack, |a, b| a > b)?,
                Opcode::CmpLe => bin_cmp(&mut stack, |a, b| a <= b)?,
                Opcode::CmpGe => bin_cmp(&mut stack, |a, b| a >= b)?,
                // control flow
                Opcode::JumpIfFalse(target) => {
                    let v = stack.pop().unwrap_or(Value::Boolean(false));
                    let cond = match v {
                        Value::Boolean(b) => b,
                        Value::Nil => false,
                        _ => true,
                    };
                    if !cond {
                        ip = *target;
                        continue;
                    }
                }
                Opcode::Jump(target) => {
                    ip = *target;
                    continue;
                }
                // call
                Opcode::CallDynamic(argc) => {
                    let mut args = Vec::with_capacity(*argc);
                    for _ in 0..*argc {
                        args.push(stack.pop().unwrap_or(Value::Nil));
                    }
                    args.reverse();
                    let func = stack.pop().unwrap_or(Value::Nil);
                    let res = match func {
                        Value::Symbol(name) => match name.as_str() {
                            "+" | "-" | "*" | "/" => arithmetic_op_symbol(name.as_str(), &args)?,
                            "=" | "<" | ">" | "<=" | ">=" => {
                                numeric_comparison_op(&args, name.as_str())?
                            }
                            "list" => Value::List(args),
                            "cons" => {
                                if args.len() != 2 {
                                    return Err(MoriaError::Runtime {
                                        message: "Expected 2 arguments".to_string(),
                                        span: None,
                                        context: None,
                                    });
                                }
                                builtin_cons(args[0].clone(), args[1].clone(), &Span::default())?
                            }
                            "car" => {
                                if args.len() != 1 {
                                    return Err(MoriaError::Runtime {
                                        message: "Expected 1 argument".to_string(),
                                        span: None,
                                        context: None,
                                    });
                                }
                                builtin_car(args[0].clone(), &Span::default())?
                            }
                            "cdr" => {
                                if args.len() != 1 {
                                    return Err(MoriaError::Runtime {
                                        message: "Expected 1 argument".to_string(),
                                        span: None,
                                        context: None,
                                    });
                                }
                                builtin_cdr(args[0].clone(), &Span::default())?
                            }
                            "null?" => Value::Boolean(is_null_list(&args)),
                            "not" => Value::Boolean(matches!(
                                args.first(),
                                Some(Value::Boolean(false)) | None
                            )),
                            "equal?" => Value::Boolean(args.first() == args.get(1)),
                            _ => {
                                return Err(MoriaError::Runtime {
                                    message: format!("Unknown function: {}", name),
                                    span: None,
                                    context: None,
                                })
                            }
                        },
                        Value::Lambda {
                            function_name: _,
                            parameters,
                            body,
                            env: captured,
                        } => {
                            if args.len() != parameters.len() {
                                return Err(MoriaError::Runtime {
                                    message: format!(
                                        "Expected {} arguments, got {}",
                                        parameters.len(),
                                        args.len()
                                    ),
                                    span: None,
                                    context: None,
                                });
                            }
                            let mut lambda_env = if let Some(c) = captured {
                                c.extend()
                            } else {
                                env.extend()
                            };
                            for (p, v) in parameters.iter().zip(args.into_iter()) {
                                lambda_env.define(p.clone(), v);
                            }
                            // Evaluate body in nested VM
                            let mut result = Value::Nil;
                            for e in body.iter() {
                                let bc = compile_expr(e)?;
                                let mut inner_vm = VM;
                                result = inner_vm.run(&mut lambda_env, &bc)?;
                            }
                            result
                        }
                        other => {
                            return Err(MoriaError::Runtime {
                                message: format!("Not a function: {}", other),
                                span: None,
                                context: None,
                            })
                        }
                    };
                    stack.push(res);
                }
                // quote
                Opcode::PushQuoted(expr) => {
                    let v = evaluate_quote(expr);
                    stack.push(v);
                }
                // env mgmt
                Opcode::PushEnv => {
                    let new_env = env.extend();
                    let old = std::mem::replace(env, new_env);
                    env_stack.push(old);
                }
                Opcode::PopEnv => {
                    if let Some(parent) = env_stack.pop() {
                        *env = parent;
                    }
                }
                Opcode::Return => {
                    break;
                }
            }
            ip += 1;
        }
        Ok(stack.pop().unwrap_or(Value::Nil))
    }
}

fn evaluate_quote(expr: &Expression) -> Value {
    match expr {
        Expression::Literal { value, .. } => value.clone(),
        Expression::Variable { name, .. } => Value::Symbol(name.clone()),
        Expression::Call {
            function,
            arguments,
            ..
        } => {
            let mut items = Vec::new();
            if let Expression::Variable { name, .. } = &**function {
                items.push(Value::Symbol(name.clone()));
            } else {
                items.push(Value::Symbol("unknown".to_string()));
            }
            for arg in arguments {
                match arg {
                    Expression::Literal { value, .. } => items.push(value.clone()),
                    Expression::Variable { name, .. } => items.push(Value::Symbol(name.clone())),
                    _ => items.push(Value::Symbol("unknown".to_string())),
                }
            }
            Value::List(items)
        }
        _ => Value::Nil,
    }
}

fn to_f64(v: &Value) -> Result<f64> {
    match v {
        Value::Integer(i) => Ok(*i as f64),
        Value::Float(f) => Ok(*f),
        _ => Err(MoriaError::Runtime {
            message: "Expected number".to_string(),
            span: None,
            context: None,
        }),
    }
}

fn bin_num(stack: &mut Vec<Value>, f: impl Fn(f64, f64) -> f64) -> Result<()> {
    let b = stack.pop().unwrap_or(Value::Integer(0));
    let a = stack.pop().unwrap_or(Value::Integer(0));
    let (af, bf) = (to_f64(&a)?, to_f64(&b)?);
    let r = f(af, bf);
    if matches!(a, Value::Integer(_)) && matches!(b, Value::Integer(_)) && r.fract() == 0.0 {
        stack.push(Value::Integer(r as i64));
    } else {
        stack.push(Value::Float(r));
    }
    Ok(())
}

fn bin_div(stack: &mut Vec<Value>) -> Result<()> {
    let b = stack.pop().unwrap_or(Value::Integer(1));
    let a = stack.pop().unwrap_or(Value::Integer(0));
    let (af, bf) = (to_f64(&a)?, to_f64(&b)?);
    if bf == 0.0 {
        return Err(MoriaError::Runtime {
            message: "Division by zero".to_string(),
            span: None,
            context: None,
        });
    }
    let r = af / bf;
    if matches!(a, Value::Integer(_)) && matches!(b, Value::Integer(_)) && r.fract() == 0.0 {
        stack.push(Value::Integer(r as i64));
    } else {
        stack.push(Value::Float(r));
    }
    Ok(())
}

fn bin_cmp(stack: &mut Vec<Value>, cmp: impl Fn(f64, f64) -> bool) -> Result<()> {
    let b = stack.pop().unwrap_or(Value::Integer(0));
    let a = stack.pop().unwrap_or(Value::Integer(0));
    let (af, bf) = (to_f64(&a)?, to_f64(&b)?);
    stack.push(Value::Boolean(cmp(af, bf)));
    Ok(())
}

fn arithmetic_op_symbol(symbol: &str, args: &[Value]) -> Result<Value> {
    if args.is_empty() {
        return Ok(match symbol {
            "+" => Value::Integer(0),
            "*" => Value::Integer(1),
            "-" | "/" => Value::Integer(0),
            _ => Value::Integer(0),
        });
    }
    let mut nums: Vec<f64> = Vec::with_capacity(args.len());
    for a in args {
        nums.push(to_f64(a)?);
    }
    match symbol {
        "+" => Ok(Value::Float(nums.into_iter().sum::<f64>())),
        "-" => {
            if nums.len() == 1 {
                Ok(Value::Float(-nums[0]))
            } else {
                let mut acc = nums[0];
                for n in &nums[1..] {
                    acc -= *n;
                }
                Ok(Value::Float(acc))
            }
        }
        "*" => {
            let mut acc = 1.0;
            for n in &nums {
                acc *= *n;
            }
            Ok(Value::Float(acc))
        }
        "/" => {
            if nums.len() == 1 {
                if nums[0] == 0.0 {
                    return Err(MoriaError::Runtime {
                        message: "Division by zero".to_string(),
                        span: None,
                        context: None,
                    });
                }
                return Ok(Value::Float(1.0 / nums[0]));
            }
            let mut acc = nums[0];
            for n in &nums[1..] {
                if *n == 0.0 {
                    return Err(MoriaError::Runtime {
                        message: "Division by zero".to_string(),
                        span: None,
                        context: None,
                    });
                }
                acc /= *n;
            }
            Ok(Value::Float(acc))
        }
        _ => Err(MoriaError::Runtime {
            message: format!("Unknown arithmetic operator: {}", symbol),
            span: None,
            context: None,
        }),
    }
}

fn numeric_comparison_op(args: &[Value], op: &str) -> Result<Value> {
    if args.len() != 2 {
        return Err(MoriaError::Runtime {
            message: "Expected 2 arguments".to_string(),
            span: None,
            context: None,
        });
    }
    let a = to_f64(&args[0])?;
    let b = to_f64(&args[1])?;
    let res = match op {
        "=" => a == b,
        "<" => a < b,
        ">" => a > b,
        "<=" => a <= b,
        ">=" => a >= b,
        _ => false,
    };
    Ok(Value::Boolean(res))
}

fn is_null_list(args: &[Value]) -> bool {
    if args.len() != 1 {
        return false;
    }
    match &args[0] {
        Value::Nil => true,
        Value::List(v) => v.is_empty(),
        _ => false,
    }
}

fn builtin_cons(head: Value, tail: Value, span: &Span) -> Result<Value> {
    match tail {
        Value::List(mut t) => {
            let mut v = Vec::with_capacity(t.len() + 1);
            v.push(head);
            v.append(&mut t);
            Ok(Value::List(v))
        }
        Value::Nil => Ok(Value::List(vec![head])),
        other => Err(MoriaError::Runtime {
            message: format!(
                "cons expects list as second argument, got {}",
                other.type_name()
            ),
            span: Some(*span),
            context: None,
        }),
    }
}

fn builtin_car(list: Value, span: &Span) -> Result<Value> {
    match list {
        Value::List(v) if !v.is_empty() => Ok(v[0].clone()),
        Value::Nil => Err(MoriaError::Runtime {
            message: "car of empty list".to_string(),
            span: Some(*span),
            context: None,
        }),
        other => Err(MoriaError::Runtime {
            message: format!("car expects list, got {}", other.type_name()),
            span: Some(*span),
            context: None,
        }),
    }
}

fn builtin_cdr(list: Value, span: &Span) -> Result<Value> {
    match list {
        Value::List(v) if !v.is_empty() => Ok(Value::List(v[1..].to_vec())),
        Value::Nil => Err(MoriaError::Runtime {
            message: "cdr of empty list".to_string(),
            span: Some(*span),
            context: None,
        }),
        other => Err(MoriaError::Runtime {
            message: format!("cdr expects list, got {}", other.type_name()),
            span: Some(*span),
            context: None,
        }),
    }
}

pub fn compile_expr(expr: &Expression) -> Result<Bytecode> {
    let mut bc = Bytecode::default();
    emit_expr(expr, &mut bc)?;
    bc.code.push(Opcode::Return);
    Ok(bc)
}

fn emit_expr(expr: &Expression, bc: &mut Bytecode) -> Result<()> {
    match expr {
        Expression::Literal { value, .. } => match value {
            Value::Integer(i) => bc.code.push(Opcode::PushInt(*i)),
            Value::Float(f) => bc.code.push(Opcode::PushFloat(*f)),
            Value::Boolean(b) => bc.code.push(Opcode::PushBool(*b)),
            Value::String(s) => bc.code.push(Opcode::PushString(s.clone())),
            Value::Symbol(s) => bc.code.push(Opcode::LoadVar(s.clone())),
            Value::List(vs) => {
                for v in vs {
                    emit_expr(
                        &Expression::Literal {
                            value: v.clone(),
                            span: Span::default(),
                        },
                        bc,
                    )?;
                }
                bc.code.push(Opcode::List(vs.len()));
            }
            Value::Nil => bc.code.push(Opcode::PushNil),
            Value::Lambda { .. } => {
                // Store lambda as literal; call handler will interpret
                bc.code.push(Opcode::PushQuoted(Box::new(expr.clone())));
            }
        },
        Expression::Variable { name, .. } => bc.code.push(Opcode::LoadVar(name.clone())),
        Expression::Call {
            function,
            arguments,
            ..
        } => {
            emit_expr(function, bc)?;
            for arg in arguments {
                emit_expr(arg, bc)?;
            }
            bc.code.push(Opcode::CallDynamic(arguments.len()));
        }
        Expression::Lambda {
            parameters, body, ..
        } => {
            // Represent as quoted lambda AST; VM will execute body at call time
            let lit = Expression::Literal {
                value: Value::Lambda {
                    function_name: None,
                    parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                    body: body.clone(),
                    env: None,
                },
                span: Span::default(),
            };
            emit_expr(&lit, bc)?;
        }
        Expression::Let { bindings, body, .. } => {
            bc.code.push(Opcode::PushEnv);
            for b in bindings {
                emit_expr(&b.value, bc)?;
                bc.code.push(Opcode::DefineVar(b.name.clone()));
            }
            for e in body {
                emit_expr(e, bc)?;
            }
            bc.code.push(Opcode::PopEnv);
        }
        Expression::If {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            emit_expr(condition, bc)?;
            let jif_pos = bc.code.len();
            bc.code.push(Opcode::JumpIfFalse(usize::MAX));
            emit_expr(then_expr, bc)?;
            let jmp_pos = bc.code.len();
            bc.code.push(Opcode::Jump(usize::MAX));
            let else_start = bc.code.len();
            if let Some(e) = else_expr {
                emit_expr(e, bc)?;
            } else {
                bc.code.push(Opcode::PushNil);
            }
            let end = bc.code.len();
            if let Opcode::JumpIfFalse(t) = &mut bc.code[jif_pos] {
                *t = else_start;
            }
            if let Opcode::Jump(t) = &mut bc.code[jmp_pos] {
                *t = end;
            }
        }
        Expression::Define { name, value, .. } => {
            emit_expr(value, bc)?;
            bc.code.push(Opcode::DefineVar(name.clone()));
        }
        Expression::DefineFunction {
            name,
            parameters,
            body,
            ..
        } => {
            // Define as lambda value bound to name
            let lit = Expression::Literal {
                value: Value::Lambda {
                    function_name: Some(name.clone()),
                    parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                    body: body.clone(),
                    env: None,
                },
                span: Span::default(),
            };
            emit_expr(&lit, bc)?;
            bc.code.push(Opcode::DefineVar(name.clone()));
        }
        Expression::Begin { expressions, .. } => {
            for e in expressions {
                emit_expr(e, bc)?;
            }
        }
        Expression::Quote { expression, .. } => {
            bc.code.push(Opcode::PushQuoted(expression.clone()));
        }
    }
    Ok(())
}

pub fn evaluate_program_vm(program: &Program) -> Result<Value> {
    let mut env = Environment::with_stdlib();
    let mut result = Value::Nil;
    let mut vm = VM;
    for expr in &program.expressions {
        let bc = compile_expr(expr)?;
        result = vm.run(&mut env, &bc)?;
    }
    Ok(result)
}

pub fn evaluate_expr_vm(expr: &Expression) -> Result<Value> {
    let mut env = Environment::with_stdlib();
    let mut vm = VM;
    let bc = compile_expr(expr)?;
    vm.run(&mut env, &bc)
}
