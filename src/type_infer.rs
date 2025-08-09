//! Minimal Hindley-Milner-like type inference for Moria expressions

use std::collections::HashMap;
use std::fmt;

use crate::ast::{Expression, Value};
use crate::error::{MoriaError, Result, Span};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Number,
    Boolean,
    String,
    Symbol,
    Nil,
    List(Box<Type>),
    Function(Vec<Type>, Box<Type>),
    Var(TypeVarId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVarId(pub usize);

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Number => write!(f, "Number"),
            Type::Boolean => write!(f, "Boolean"),
            Type::String => write!(f, "String"),
            Type::Symbol => write!(f, "Symbol"),
            Type::Nil => write!(f, "Nil"),
            Type::List(inner) => write!(f, "List {}", inner),
            Type::Function(params, ret) => {
                write!(f, "(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ") -> {}", ret)
            }
            Type::Var(TypeVarId(id)) => write!(f, "t{}", id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme {
    pub vars: Vec<TypeVarId>,
    pub ty: Type,
}

#[derive(Debug, Default, Clone)]
pub struct Subst(HashMap<TypeVarId, Type>);

impl Subst {
    fn new() -> Self {
        Self(HashMap::new())
    }
    fn insert(&mut self, var: TypeVarId, ty: Type) {
        self.0.insert(var, ty);
    }

    fn apply_type(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => self
                .0
                .get(v)
                .map(|ty| self.apply_type(ty))
                .unwrap_or(Type::Var(*v)),
            Type::List(inner) => Type::List(Box::new(self.apply_type(inner))),
            Type::Function(params, ret) => {
                let ps = params.iter().map(|p| self.apply_type(p)).collect();
                let r = Box::new(self.apply_type(ret));
                Type::Function(ps, r)
            }
            _ => t.clone(),
        }
    }

    fn compose(&self, other: &Subst) -> Subst {
        // self after other
        let mut result = Subst::new();
        for (k, v) in &other.0 {
            result.insert(*k, self.apply_type(v));
        }
        for (k, v) in &self.0 {
            result.insert(*k, v.clone());
        }
        result
    }
}

#[derive(Debug, Default, Clone)]
pub struct TypeEnv {
    pub vars: HashMap<String, Scheme>,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }
    pub fn with_prelude() -> Self {
        let mut env = Self::new();
        let a = Type::Var(TypeVarId(0));

        // arithmetic: Number -> Number -> Number
        let num_num_num = Scheme {
            vars: vec![],
            ty: Type::Function(vec![Type::Number, Type::Number], Box::new(Type::Number)),
        };
        env.vars.insert("+".to_string(), num_num_num.clone());
        env.vars.insert("-".to_string(), num_num_num.clone());
        env.vars.insert("*".to_string(), num_num_num.clone());
        env.vars.insert("/".to_string(), num_num_num.clone());

        // comparisons: Number -> Number -> Boolean
        let num_num_bool = Scheme {
            vars: vec![],
            ty: Type::Function(vec![Type::Number, Type::Number], Box::new(Type::Boolean)),
        };
        for op in ["=", "<", ">", "<=", ">="] {
            env.vars.insert(op.to_string(), num_num_bool.clone());
        }

        // list: a ... -> List a (approximate as (a -> List a) for minimal impl)
        env.vars.insert(
            "list".to_string(),
            Scheme {
                vars: vec![TypeVarId(0)],
                ty: Type::Function(vec![a.clone()], Box::new(Type::List(Box::new(a.clone())))),
            },
        );
        // cons: a -> List a -> List a
        env.vars.insert(
            "cons".to_string(),
            Scheme {
                vars: vec![TypeVarId(0)],
                ty: Type::Function(
                    vec![a.clone(), Type::List(Box::new(a.clone()))],
                    Box::new(Type::List(Box::new(a.clone()))),
                ),
            },
        );
        // car: List a -> a
        env.vars.insert(
            "car".to_string(),
            Scheme {
                vars: vec![TypeVarId(0)],
                ty: Type::Function(vec![Type::List(Box::new(a.clone()))], Box::new(a.clone())),
            },
        );
        // cdr: List a -> List a
        env.vars.insert(
            "cdr".to_string(),
            Scheme {
                vars: vec![TypeVarId(0)],
                ty: Type::Function(
                    vec![Type::List(Box::new(a.clone()))],
                    Box::new(Type::List(Box::new(a.clone()))),
                ),
            },
        );
        // null?: List a -> Boolean
        env.vars.insert(
            "null?".to_string(),
            Scheme {
                vars: vec![TypeVarId(0)],
                ty: Type::Function(
                    vec![Type::List(Box::new(a.clone()))],
                    Box::new(Type::Boolean),
                ),
            },
        );
        // not: Boolean -> Boolean
        env.vars.insert(
            "not".to_string(),
            Scheme {
                vars: vec![],
                ty: Type::Function(vec![Type::Boolean], Box::new(Type::Boolean)),
            },
        );
        // equal? : a -> a -> Boolean
        env.vars.insert(
            "equal?".to_string(),
            Scheme {
                vars: vec![TypeVarId(0)],
                ty: Type::Function(vec![a.clone(), a.clone()], Box::new(Type::Boolean)),
            },
        );

        env
    }
}

#[derive(Default)]
pub struct Inferencer {
    next_var: usize,
}

impl Inferencer {
    pub fn new() -> Self {
        Self { next_var: 0 }
    }
    fn fresh(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(TypeVarId(id))
    }

    pub fn infer_expression(&mut self, env: &TypeEnv, expr: &Expression) -> Result<Type> {
        let (subst, ty) = self.infer(env, expr)?;
        Ok(subst.apply_type(&ty))
    }

    fn infer(&mut self, env: &TypeEnv, expr: &Expression) -> Result<(Subst, Type)> {
        match expr {
            Expression::Literal { value, .. } => Ok((
                Subst::new(),
                match value {
                    Value::Integer(_) | Value::Float(_) => Type::Number,
                    Value::Boolean(_) => Type::Boolean,
                    Value::String(_) => Type::String,
                    Value::Symbol(_) => Type::Symbol,
                    Value::List(items) => {
                        if items.is_empty() {
                            Type::List(Box::new(self.fresh()))
                        } else {
                            // Infer element type from first, no recursion into elements (minimal impl)
                            match &items[0] {
                                Value::Integer(_) | Value::Float(_) => {
                                    Type::List(Box::new(Type::Number))
                                }
                                Value::Boolean(_) => Type::List(Box::new(Type::Boolean)),
                                Value::String(_) => Type::List(Box::new(Type::String)),
                                Value::Symbol(_) => Type::List(Box::new(Type::Symbol)),
                                Value::Nil => Type::List(Box::new(self.fresh())),
                                Value::List(_) | Value::Lambda { .. } => {
                                    Type::List(Box::new(self.fresh()))
                                }
                            }
                        }
                    }
                    Value::Nil => Type::Nil,
                    Value::Lambda {
                        parameters,
                        body: _,
                        ..
                    } => {
                        let mut param_types = Vec::new();
                        for _p in parameters {
                            param_types.push(self.fresh());
                        }
                        // Minimal support: infer body as last expression type
                        let ret = self.fresh();
                        Type::Function(param_types, Box::new(ret))
                    }
                },
            )),
            Expression::Variable { name, .. } => {
                let ty = self.instantiate(env, name)?;
                Ok((Subst::new(), ty))
            }
            Expression::Call {
                function,
                arguments,
                ..
            } => {
                // Special-case variadic 'list'
                if let Expression::Variable { name, .. } = &**function {
                    if name == "list" {
                        let mut subst = Subst::new();
                        // infer all argument types and unify to a single element type
                        let elem_ty = self.fresh();
                        let mut current_elem = elem_ty.clone();
                        for arg in arguments {
                            let (si, ti) = self.infer(env, arg)?;
                            subst = subst.compose(&si);
                            let si2 =
                                unify(&subst.apply_type(&ti), &subst.apply_type(&current_elem))?;
                            subst = si2.compose(&subst);
                            current_elem = subst.apply_type(&current_elem);
                        }
                        return Ok((
                            subst.clone(),
                            Type::List(Box::new(subst.apply_type(&current_elem))),
                        ));
                    }
                }

                let (s1, t_fun) = self.infer(env, function)?;
                let mut subst = s1;
                let mut arg_types = Vec::new();
                for arg in arguments {
                    let (si, ti) = self.infer(env, arg)?;
                    subst = subst.compose(&si);
                    arg_types.push(subst.apply_type(&ti));
                }
                let ret_type = self.fresh();
                let fun_type = Type::Function(arg_types.clone(), Box::new(ret_type.clone()));
                let s_unify = unify(&subst.apply_type(&t_fun), &fun_type)?;
                let subst = s_unify.compose(&subst);
                Ok((subst.clone(), subst.apply_type(&ret_type)))
            }
            Expression::Lambda {
                parameters, body, ..
            } => {
                // Build param types
                let param_types: Vec<Type> = parameters.iter().map(|_p| self.fresh()).collect();
                // Infer body sequentially; minimal: infer last expression type
                let last_type = if let Some(last) = body.last() {
                    let (_s, t) = self.infer(env, last)?;
                    t
                } else {
                    self.fresh()
                };
                Ok((
                    Subst::new(),
                    Type::Function(param_types, Box::new(last_type)),
                ))
            }
            Expression::If {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                let (s1, t1) = self.infer(env, condition)?;
                let s_bool = unify(&t1, &Type::Boolean)?;
                let s_pre = s_bool.compose(&s1);
                let (s2, t2) = self.infer(env, then_expr)?;
                let s_pre = s2.compose(&s_pre);
                if let Some(else_e) = else_expr {
                    let (s3, t3) = self.infer(env, else_e)?;
                    let s_eq = unify(&t2, &t3)?;
                    let s_all = s_eq.compose(&s3).compose(&s_pre);
                    Ok((s_all.clone(), s_all.apply_type(&t2)))
                } else {
                    Ok((s_pre.clone(), s_pre.apply_type(&t2)))
                }
            }
            Expression::Begin { expressions, .. } => {
                let mut last_t = Type::Nil;
                let mut subst = Subst::new();
                for e in expressions {
                    let (s, t) = self.infer(env, e)?;
                    subst = subst.compose(&s);
                    last_t = subst.apply_type(&t);
                }
                Ok((subst, last_t))
            }
            Expression::Quote { .. } => Ok((Subst::new(), Type::Symbol)),
            Expression::Define { .. }
            | Expression::DefineFunction { .. }
            | Expression::Let { .. } => {
                // Minimal impl: not handling definitions/bindings yet
                Err(MoriaError::Type {
                    message: "Type inference for define/let not implemented in minimal engine"
                        .to_string(),
                    span: Span::default(),
                    context: None,
                })
            }
        }
    }

    fn instantiate(&mut self, env: &TypeEnv, name: &str) -> Result<Type> {
        let scheme = env.vars.get(name).ok_or_else(|| MoriaError::Type {
            message: format!("Unknown identifier: {}", name),
            span: Span::default(),
            context: None,
        })?;
        let mut mapping: HashMap<TypeVarId, Type> = HashMap::new();
        for v in &scheme.vars {
            mapping.insert(*v, self.fresh());
        }
        Ok(apply_scheme(scheme, &mapping))
    }
}

fn apply_scheme(s: &Scheme, map: &HashMap<TypeVarId, Type>) -> Type {
    apply_type_with_map(&s.ty, map)
}

fn apply_type_with_map(t: &Type, map: &HashMap<TypeVarId, Type>) -> Type {
    match t {
        Type::Var(v) => map.get(v).cloned().unwrap_or(Type::Var(*v)),
        Type::List(inner) => Type::List(Box::new(apply_type_with_map(inner, map))),
        Type::Function(params, ret) => {
            let ps = params.iter().map(|p| apply_type_with_map(p, map)).collect();
            let r = Box::new(apply_type_with_map(ret, map));
            Type::Function(ps, r)
        }
        _ => t.clone(),
    }
}

fn occurs(v: TypeVarId, t: &Type) -> bool {
    match t {
        Type::Var(x) => *x == v,
        Type::List(inner) => occurs(v, inner),
        Type::Function(params, ret) => params.iter().any(|p| occurs(v, p)) || occurs(v, ret),
        _ => false,
    }
}

fn unify(t1: &Type, t2: &Type) -> Result<Subst> {
    if t1 == t2 {
        return Ok(Subst::new());
    }
    match (t1, t2) {
        (Type::Var(v), t) => bind(*v, t),
        (t, Type::Var(v)) => bind(*v, t),
        (Type::Number, Type::Number) => Ok(Subst::new()),
        (Type::Boolean, Type::Boolean) => Ok(Subst::new()),
        (Type::String, Type::String) => Ok(Subst::new()),
        (Type::Symbol, Type::Symbol) => Ok(Subst::new()),
        (Type::Nil, Type::Nil) => Ok(Subst::new()),
        (Type::List(a), Type::List(b)) => unify(a, b),
        (Type::Function(ps1, r1), Type::Function(ps2, r2)) => {
            if ps1.len() != ps2.len() {
                return Err(MoriaError::Type {
                    message: "Function arity mismatch".to_string(),
                    span: Span::default(),
                    context: None,
                });
            }
            let mut s = Subst::new();
            for (a, b) in ps1.iter().zip(ps2.iter()) {
                let si = unify(&s.apply_type(a), &s.apply_type(b))?;
                s = si.compose(&s);
            }
            let sr = unify(&s.apply_type(r1), &s.apply_type(r2))?;
            Ok(sr.compose(&s))
        }
        _ => Err(MoriaError::Type {
            message: format!("Cannot unify types: {:?} and {:?}", t1, t2),
            span: Span::default(),
            context: None,
        }),
    }
}

fn bind(v: TypeVarId, t: &Type) -> Result<Subst> {
    if let Type::Var(v2) = t {
        if *v2 == v {
            return Ok(Subst::new());
        }
    }
    if occurs(v, t) {
        return Err(MoriaError::Type {
            message: "Occurs check failed".to_string(),
            span: Span::default(),
            context: None,
        });
    }
    let mut s = Subst::new();
    s.insert(v, t.clone());
    Ok(s)
}

// Convenience API
pub fn infer_expression_type(expr: &Expression) -> Result<Type> {
    let mut infer = Inferencer::new();
    let env = TypeEnv::with_prelude();
    infer.infer_expression(&env, expr)
}
