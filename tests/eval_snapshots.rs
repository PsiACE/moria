// This file was renamed from basic_tests.rs to eval_snapshots.rs
//! Basic eval/value+type snapshot tests

use moria::{compile_expr, infer_expression_type, parse_expression, Environment, VM};

fn eval(srcs: &[&str]) -> String {
    let mut out = String::new();
    let mut env = Environment::with_stdlib();
    let mut vm = VM::default();
    for src in srcs {
        let expr = parse_expression(src).unwrap();
        let bc = compile_expr(&expr).unwrap();
        let val = vm.run(&mut env, &bc).unwrap();
        let ty = infer_expression_type(&expr).ok();
        match ty {
            Some(t) => out.push_str(&format!("{} => {} :: {}\n", src, val, t)),
            None => out.push_str(&format!("{} => {}\n", src, val)),
        }
    }
    out
}

#[test]
fn snapshot_arithmetic() {
    let s = eval(&["(+ 1 2)", "(- 5 2)", "(* 2 3)", "(/ 6 2)"]);
    insta::assert_snapshot!(s, @"(+ 1 2) => 3 :: Number
(- 5 2) => 3 :: Number
(* 2 3) => 6 :: Number
(/ 6 2) => 3 :: Number
");
}

#[test]
fn snapshot_list_and_boolean_builtins() {
    let s = eval(&[
        "(list 1 2 3)",
        "(car (list 4 5 6))",
        "(cdr (list 4 5 6))",
        "(cons 0 (list 1 2))",
        "(null? (list))",
        "(not #t)",
        "(equal? 1 1)",
    ]);
    insta::assert_snapshot!(s, @"(list 1 2 3) => (1 2 3) :: List Number
(car (list 4 5 6)) => 4 :: Number
(cdr (list 4 5 6)) => (5 6) :: List Number
(cons 0 (list 1 2)) => (0 1 2) :: List Number
(null? (list)) => #t :: Boolean
(not #t) => #f :: Boolean
(equal? 1 1) => #t :: Boolean
");
}

#[test]
fn snapshot_float_arithmetic_and_comparison() {
    let s = eval(&["(+ 1 2.5)", "(/ 3 2)", "(< 1 1.5)"]);
    insta::assert_snapshot!(s, @"(+ 1 2.5) => 3.5 :: Number
(/ 3 2) => 1.5 :: Number
(< 1 1.5) => #t :: Boolean
");
}

#[test]
fn snapshot_comparison() {
    let s = eval(&["(= 1 1)", "(< 1 2)", "(> 1 2)"]);
    insta::assert_snapshot!(s, @"(= 1 1) => #t :: Boolean
(< 1 2) => #t :: Boolean
(> 1 2) => #f :: Boolean
");
}

#[test]
fn snapshot_define_and_variables() {
    let expr = parse_expression("(define x 42)").unwrap();
    let mut env = Environment::with_stdlib();
    let mut vm = VM::default();
    let bc = compile_expr(&expr).unwrap();
    let _ = vm.run(&mut env, &bc).unwrap();
    let s = {
        let mut out = String::new();
        let expr = parse_expression("x").unwrap();
        let bc = compile_expr(&expr).unwrap();
        let val = vm.run(&mut env, &bc).unwrap();
        let ty = infer_expression_type(&expr).ok();
        match ty {
            Some(t) => out.push_str(&format!("x => {} :: {}\n", val, t)),
            None => out.push_str(&format!("x => {}\n", val)),
        }
        out
    };
    insta::assert_snapshot!(s, @"x => 42
");
}

#[test]
fn snapshot_if_expression() {
    let s = eval(&["(if #t 1 2)", "(if #f 1 2)"]);
    insta::assert_snapshot!(s, @"(if #t 1 2) => 1 :: Number
(if #f 1 2) => 2 :: Number
");
}

#[test]
fn snapshot_factorial() {
    let def = parse_expression("(define (factorial n) (if (<= n 1) 1 (* n (factorial (- n 1)))))")
        .unwrap();
    // define into a shared env
    let mut env = Environment::with_stdlib();
    let mut vm = VM::default();
    let bc = compile_expr(&def).unwrap();
    let _ = vm.run(&mut env, &bc).unwrap();
    // now call
    let mut out = String::new();
    let expr = parse_expression("(factorial 5)").unwrap();
    let bc = compile_expr(&expr).unwrap();
    let val = vm.run(&mut env, &bc).unwrap();
    let ty = infer_expression_type(&expr).ok();
    match ty {
        Some(t) => out.push_str(&format!("(factorial 5) => {} :: {}\n", val, t)),
        None => out.push_str(&format!("(factorial 5) => {}\n", val)),
    }
    let s = out;
    insta::assert_snapshot!(s, @"(factorial 5) => 120
");
}
