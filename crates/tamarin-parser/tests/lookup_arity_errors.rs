//! Diagnostics for signature-driven function application parsing.

mod common;

use tamarin_parser::{parse_theory, ParseErrorKind};

#[track_caller]
fn assert_undeclared(source: &str, name: &str, line_column: (u32, u32)) {
    let error = parse_theory(source, &[]).expect_err("application must be rejected");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::UndeclaredFunction {
            name: name.to_string(),
        }
    );
    assert_eq!(error.line_column(), line_column);
    common::assert_span(&error, source, name);
}

#[track_caller]
fn assert_wrong_arity(
    source: &str,
    name: &str,
    declared: usize,
    used: usize,
    line_column: (u32, u32),
) {
    let error = parse_theory(source, &[]).expect_err("application must be rejected");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::WrongFunctionArity {
            name: name.to_string(),
            declared,
            used,
        }
    );
    assert_eq!(error.line_column(), line_column);
    common::assert_span(&error, source, name);
}

#[test]
fn undeclared_application_reports_its_name() {
    assert_undeclared(
        "theory T\nbegin\nrule R: [ ] --> [ Out(g('a')) ]\nend\n",
        "g",
        (3, 23),
    );
}

#[test]
fn use_before_declaration_is_still_undeclared() {
    assert_undeclared(
        "theory T\nbegin\nrule R: [ ] --> [ Out(g('a')) ]\nfunctions: g/1\nend\n",
        "g",
        (3, 23),
    );
}

#[test]
fn nested_failure_reports_the_inner_application() {
    assert_undeclared(
        "theory T\nbegin\nfunctions: g/2\nrule R: [ ] --> [ Out(g(k('x'),'b')) ]\nend\n",
        "k",
        (4, 25),
    );
}

#[test]
fn nested_wrong_arity_keeps_the_inner_application_span() {
    let source = "theory T begin\nfunctions: f/1, g/2\nrule R: [ ] --> [ Out(f(g('a'))) ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("inner arity mismatch must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::WrongFunctionArity {
            name: "g".into(),
            declared: 2,
            used: 1,
        }
    );
    common::assert_span(&error, source, "g");
}

#[test]
fn nested_reserved_builtin_keeps_the_inner_application_span() {
    let source = "theory T begin\nfunctions: g/2\nequations: g{x}exp = x\nend\n";
    let error = parse_theory(source, &[]).expect_err("reserved builtin must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::ReservedBuiltin { name, .. } if name == "exp"
    ));
    common::assert_span(&error, source, "exp");
}

#[test]
fn wrong_arity_reports_the_declaration_and_use_counts() {
    assert_wrong_arity(
        "theory T\nbegin\nfunctions: g/3\nrule R: [ ] --> [ Out(g('a','b')) ]\nend\n",
        "g",
        3,
        2,
        (4, 23),
    );
}

#[test]
fn nullary_and_builtin_arity_errors_use_the_same_variant() {
    assert_wrong_arity(
        "theory T\nbegin\nfunctions: f/0\nrule R: [ ] --> [ Out(f('a')) ]\nend\n",
        "f",
        0,
        1,
        (4, 23),
    );
    assert_wrong_arity(
        "theory T\nbegin\nbuiltins: bilinear-pairing\nrule R: [ ] --> [ Out(em('a','b','c')) ]\nend\n",
        "em",
        2,
        3,
        (4, 23),
    );
}

#[test]
fn algebraic_application_requires_a_binary_function() {
    assert_wrong_arity(
        "theory T\nbegin\nfunctions: g/3\nrule R: [ ] --> [ Out(g{'a'}'b') ]\nend\n",
        "g",
        3,
        2,
        (4, 23),
    );
}

#[test]
fn malformed_unary_arguments_remain_syntax_errors() {
    for source in [
        "theory T begin\nbuiltins: hashing\nrule R: [ ] --> [ Out(h()) ]\nend\n",
        "theory T begin\nbuiltins: hashing\nrule R: [ ] --> [ Out(h('a',)) ]\nend\n",
    ] {
        let error = parse_theory(source, &[]).expect_err("malformed application must fail");
        assert!(
            matches!(error.kind(), ParseErrorKind::Expected { .. }),
            "unexpected diagnostic: {error:?}"
        );
    }
}

#[test]
fn equation_reserved_builtin_has_a_semantic_error() {
    let source = "theory T begin\nbuiltins: diffie-hellman\nequations: exp(x,y) = x\nend\n";
    let error = parse_theory(source, &[]).expect_err("reserved builtin must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::ReservedBuiltin { name, .. } if name == "exp"
    ));
    common::assert_span(&error, source, "exp");
}
