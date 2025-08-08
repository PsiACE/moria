use moria::{parse_expression, infer_expression_type};

#[test]
fn infer_literals_and_simple_calls() {
    // integer literal
    let t = infer_expression_type(&parse_expression("42").unwrap()).unwrap();
    insta::assert_snapshot!(format!("{:?}", t), @"Number");

    // boolean literal
    let t = infer_expression_type(&parse_expression("#t").unwrap()).unwrap();
    insta::assert_snapshot!(format!("{:?}", t), @"Boolean");

    // simple arithmetic call
    let t = infer_expression_type(&parse_expression("(+ 1 2)").unwrap()).unwrap();
    insta::assert_snapshot!(format!("{:?}", t), @"Number");

    // comparison
    let t = infer_expression_type(&parse_expression("(< 1 2)").unwrap()).unwrap();
    insta::assert_snapshot!(format!("{:?}", t), @"Boolean");
}

#[test]
fn infer_list_functions() {
    let t = infer_expression_type(&parse_expression("(list 1 2 3)").unwrap()).unwrap();
    insta::assert_snapshot!(format!("{:?}", t), @"List(Number)");

    let t = infer_expression_type(&parse_expression("(null? (list 1 2))").unwrap()).unwrap();
    insta::assert_snapshot!(format!("{:?}", t), @"Boolean");
}


