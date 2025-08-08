// This file was renamed from basic_tests.rs to eval_snapshots.rs
//! Basic eval/value+type snapshot tests

use moria::{parse_expression, Evaluator, infer_expression_type};

fn eval(mut evaluator: Evaluator, srcs: &[&str]) -> String {
    let mut out = String::new();
    for src in srcs {
        let expr = parse_expression(src).unwrap();
        let val = evaluator.evaluate(&expr).unwrap();
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
    let s = eval(Evaluator::with_stdlib(), &["(+ 1 2)", "(- 5 2)", "(* 2 3)", "(/ 6 2)"]);
    insta::assert_snapshot!(s, @"(+ 1 2) => 3 :: Number
(- 5 2) => 3 :: Number
(* 2 3) => 6 :: Number
(/ 6 2) => 3 :: Number
");
}

#[test]
fn snapshot_list_and_boolean_builtins() {
    let s = eval(Evaluator::with_stdlib(), &[
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
    let s = eval(Evaluator::with_stdlib(), &[
        "(+ 1 2.5)",
        "(/ 3 2)",
        "(< 1 1.5)",
    ]);
    insta::assert_snapshot!(s, @"(+ 1 2.5) => 3.5 :: Number
(/ 3 2) => 1.5 :: Number
(< 1 1.5) => #t :: Boolean
");
}

#[test]
fn snapshot_comparison() {
    let s = eval(Evaluator::with_stdlib(), &["(= 1 1)", "(< 1 2)", "(> 1 2)"]);
    insta::assert_snapshot!(s, @"(= 1 1) => #t :: Boolean
(< 1 2) => #t :: Boolean
(> 1 2) => #f :: Boolean
");
}

#[test]
fn snapshot_define_and_variables() {
    let mut e = Evaluator::new();
    let expr = parse_expression("(define x 42)").unwrap();
    e.evaluate(&expr).unwrap();
    let s = eval(e, &["x"]);
    insta::assert_snapshot!(s, @"x => 42
");
}

#[test]
fn snapshot_if_expression() {
    let s = eval(Evaluator::with_stdlib(), &["(if #t 1 2)", "(if #f 1 2)"]);
    insta::assert_snapshot!(s, @"(if #t 1 2) => 1 :: Number
(if #f 1 2) => 2 :: Number
");
}

#[test]
fn snapshot_factorial() {
    let mut e = Evaluator::with_stdlib();
    let def = parse_expression("(define (factorial n) (if (<= n 1) 1 (* n (factorial (- n 1)))))").unwrap();
    e.evaluate(&def).unwrap();
    let s = eval(e, &["(factorial 5)"]);
    insta::assert_snapshot!(s, @"(factorial 5) => 120
");
}


