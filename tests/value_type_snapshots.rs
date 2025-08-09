use moria::{evaluate_expr_vm, infer_expression_type, parse_expression};

fn eval(src: &str) -> String {
    let expr = parse_expression(src).unwrap();
    let val = evaluate_expr_vm(&expr).unwrap();
    let ty = infer_expression_type(&expr).ok();
    match ty {
        Some(t) => format!("{} :: {}", val, t),
        None => format!("{}", val),
    }
}

#[test]
fn snapshot_basic_arith() {
    let out = eval("(+ 1 2)");
    insta::assert_snapshot!(out, @"3 :: Number");
}

#[test]
fn snapshot_if() {
    let out = eval("(if #t 1 2)");
    insta::assert_snapshot!(out, @"1 :: Number");
}

#[test]
fn snapshot_lists() {
    let out = eval("(list 1 2 3)");
    insta::assert_snapshot!(out, @"(1 2 3) :: List Number");

    let out = eval("(car (list 4 5))");
    insta::assert_snapshot!(out, @"4 :: Number");
}

#[test]
fn snapshot_equal_and_not() {
    let out = eval("(equal? 1 1)");
    insta::assert_snapshot!(out, @"#t :: Boolean");

    let out = eval("(not #t)");
    insta::assert_snapshot!(out, @"#f :: Boolean");
}
