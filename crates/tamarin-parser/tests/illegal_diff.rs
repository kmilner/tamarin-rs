//! Regression tests for the structured `diff(...)` rejection variants.

use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError};

#[track_caller]
fn assert_illegal_diff(
    src: &str,
    flags: &[&str],
    expected_diff_set: bool,
    expected_context: Option<ParseContext>,
    expected_location: (u32, u32),
) {
    let error = parse_theory(src, flags).expect_err("theory must reject the diff operator");
    let ParseError::IllegalDiffOperator {
        diff_set,
        context,
        at,
    } = error
    else {
        panic!("expected IllegalDiffOperator, got {error:?}");
    };
    assert_eq!(diff_set, expected_diff_set);
    assert_eq!(context, expected_context);
    assert_eq!((at.line, at.col), expected_location);
}

#[track_caller]
fn assert_diff_arity(src: &str, expected_used_arity: usize, expected_location: (u32, u32)) {
    let error = parse_theory(src, &["diff"]).expect_err("invalid diff arity must be rejected");
    let ParseError::FunctionUsedWithWrongArity {
        name,
        declared_arity,
        used_arity,
        declared_at,
        used_at,
    } = error
    else {
        panic!("expected FunctionUsedWithWrongArity, got {error:?}");
    };
    assert_eq!(name, "diff");
    assert_eq!(declared_arity, 2);
    assert_eq!(used_arity, expected_used_arity);
    assert!(declared_at.is_none());
    assert_eq!((used_at.line, used_at.col), expected_location);
}

#[test]
fn diff_in_a_rule_without_the_flag_is_illegal() {
    assert_illegal_diff(
        "theory T begin\nrule R:\n  [ ] --[ ]-> [ Out(diff(a, b)) ]\nend\n",
        &[],
        false,
        None,
        (3, 21),
    );
}

#[test]
fn diff_in_an_equation_without_the_flag_reports_equation_context() {
    assert_illegal_diff(
        "theory T begin\nequations: diff(a, b) = c\nend\n",
        &[],
        false,
        Some(ParseContext::Equation),
        (2, 12),
    );
}

#[test]
fn diff_in_an_equation_with_the_flag_still_reports_equation_context() {
    assert_illegal_diff(
        "theory T begin\nequations: diff(a, b) = c\nend\n",
        &["diff"],
        true,
        Some(ParseContext::Equation),
        (2, 12),
    );
}

#[test]
fn diff_in_a_rule_with_the_flag_parses() {
    parse_theory(
        "theory T begin\nrule R:\n  [ ] --[ ]-> [ Out(diff(a, b)) ]\nend\n",
        &["diff"],
    )
    .expect("the diff flag should enable diff in a rule");
}

#[test]
fn diff_with_one_argument_reports_wrong_arity() {
    assert_diff_arity(
        "theory T begin\nrule R:\n  [ ] --[ ]-> [ Out(diff(a)) ]\nend\n",
        1,
        (3, 21),
    );
}

#[test]
fn diff_with_more_than_two_arguments_reports_wrong_arity() {
    assert_diff_arity(
        "theory T begin\nrule R:\n  [ ] --[ ]-> [ Out(diff(a, b, c)) ]\nend\n",
        3,
        (3, 21),
    );
}
