// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The algebraic term levels are gated on the parse-time signature bits.
//!
//! `multterm`, `xorterm`, `msetterm` and `natterm`
//! (Theory/Text/Parser/Term.hs:179-208) each read one `enable…` bit off the
//! parser state and run their `chainl1` only when it is set; otherwise the
//! level is skipped and its operator is not a term operator at all.  `multterm`
//! guards `expterm` as well, so `^` needs the same `enableDH` that `*` needs.
//!
//! Operators must be rejected when disabled and lower to the right AST when enabled.

use tamarin_parser::{parse_theory, BinOp, Fact, Term, TheoryItem};

fn theory(builtins: &str, op: &str) -> String {
    let head = if builtins.is_empty() {
        String::new()
    } else {
        format!("builtins: {builtins}\n")
    };
    format!("theory T begin\n{head}rule R: [ In(x), In(y) ] --[ ]-> [ Out(x {op} y) ]\nend\n")
}

fn conclusion_op(src: &str) -> BinOp {
    let thy = parse_theory(src, &[]).expect("the probes below must all parse");
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("one rule");
    match &rule.conclusions[..] {
        [Fact { args, .. }] => match &args[..] {
            [Term::BinOp(op, _, _)] => *op,
            other => panic!("expected one binary-operator argument, got {other:?}"),
        },
        other => panic!("expected one conclusion fact, got {other:?}"),
    }
}

#[test]
fn builtin_operators_require_their_signature_flags() {
    for (signature, op, expected) in [
        ("multiset", "++", BinOp::Union),
        ("multiset", "+", BinOp::Union),
        ("natural-numbers", "%+", BinOp::NatPlus),
        ("xor", "XOR", BinOp::Xor),
        ("xor", "⊕", BinOp::Xor),
        ("diffie-hellman", "*", BinOp::Mult),
        ("diffie-hellman", "^", BinOp::Exp),
        ("bilinear-pairing", "*", BinOp::Mult),
        ("bilinear-pairing", "^", BinOp::Exp),
    ] {
        let source = theory("", op);
        let error = parse_theory(&source, &[]).unwrap_err();
        assert_eq!(error.span().start, source.find(op).unwrap());
        assert_eq!(conclusion_op(&theory(signature, op)), expected);
    }
    let source = theory("multiset", "^");
    let error = parse_theory(&source, &[]).unwrap_err();
    assert_eq!(error.span().start, source.find('^').unwrap());
}

#[test]
fn nat_literals_and_variables_need_their_builtin() {
    for term in ["1:nat", "%1", "%n", "%12", "n:nat", "%'n'"] {
        let without = format!("theory T begin\nrule R: [ ] --> [ Out({term}) ]\nend");
        assert!(
            parse_theory(&without, &[]).is_err(),
            "accepted {term} without nat"
        );
        let with = format!(
            "theory T begin\nbuiltins: natural-numbers\nrule R: [ ] --> [ Out({term}) ]\nend"
        );
        parse_theory(&with, &[]).unwrap_or_else(|e| panic!("rejected {term} with nat: {e}"));
    }
}

#[test]
fn digit_initial_nat_variable_is_not_split_as_nat_one() {
    let thy = parse_theory(
        "theory T begin\nbuiltins: natural-numbers\nrule R: [ In(%12) ] --> [ Out(%1) ]\nend",
        &[],
    )
    .expect("digit-initial nat variable");
    let rule = thy
        .items
        .iter()
        .find_map(|item| match item {
            TheoryItem::Rule(rule) => Some(rule),
            _ => None,
        })
        .expect("rule");

    assert!(matches!(
        &rule.premises[0].args[0],
        Term::Var(var) if var.name == "12" && var.sort == tamarin_term::lterm::LSort::Nat
    ));
    assert_eq!(rule.conclusions[0].args[0], Term::NatOne);
}

#[test]
fn disabled_nat_diagnostics_identify_the_construct() {
    for (term, label) in [
        ("1:nat", "1:nat"),
        ("%1", "%1"),
        ("%n", "%"),
        ("%'n'", "%"),
        ("n:nat", "nat"),
    ] {
        let src = format!("theory T begin\nrule R: [ ] --> [ Out({term}) ]\nend");
        let error = parse_theory(&src, &[]).unwrap_err();
        assert!(error
            .diagnostic_message()
            .contains("requires the natural-numbers builtin"));
        assert_eq!(&src[error.span()], label, "{term}: {error}");
    }
    for body in [
        "rule R: [] --> [Out(%n)]",
        "lemma L: \"All %n. T\"",
        "process: in('c', =%n)",
    ] {
        let source = format!("theory T begin {body} end");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(error
            .diagnostic_message()
            .contains("requires the natural-numbers builtin"));
        let start = source.find('%').unwrap();
        assert_eq!(error.span(), start..start + 1, "{body}: {error}");
        parse_theory(
            &format!("theory T begin builtins: natural-numbers {body} end"),
            &[],
        )
        .expect("enabling the builtin accepts the same construct");
    }
}

#[test]
fn multiset_comparison_needs_its_builtin() {
    let body = |builtin: &str| {
        format!("theory T begin\n{builtin}restriction R: \"All x y. x (<) y\"\nend")
    };
    assert!(parse_theory(&body(""), &[]).is_err());
    parse_theory(&body("builtins: multiset\n"), &[]).expect("multiset comparison");
}
