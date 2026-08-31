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
//! Each expectation below is the pinned oracle's stderr for the same source,
//! verbatim.

use tamarin_parser::{parse_theory, BinOp, Fact, Term, TheoryItem};

/// The frame for `src`, with `t.spthy` as the `SourcePos` file name.
fn frame(src: &str) -> String {
    parse_theory(src, &[])
        .expect_err("the probes below must all fail to parse")
        .with_source("t.spthy")
        .to_string()
}

/// A theory whose one rule sends `x <op> y`, with `builtins` in front when
/// non-empty.
fn theory(builtins: &str, op: &str) -> String {
    let head = if builtins.is_empty() {
        String::new()
    } else {
        format!("builtins: {builtins}\n")
    };
    format!("theory T begin\n{head}rule R: [ In(x), In(y) ] --[ ]-> [ Out(x {op} y) ]\nend\n")
}

/// The operator at the root of that rule's single conclusion argument.
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

/// Without `builtins: multiset` neither `++` nor `+` is a term operator, and
/// the frame is the one the closed `msetterm` level leaves.
#[test]
fn multiset_union_needs_its_builtin() {
    for op in ["++", "+"] {
        assert_eq!(
            frame(&theory("", op)),
            "\"t.spthy\" (line 2, column 42):\nunexpected \"+\"\nexpecting \".\", \",\" or \")\"",
            "{op}"
        );
        assert_eq!(conclusion_op(&theory("multiset", op)), BinOp::Union);
    }
}

/// `%+` needs `builtins: natural-numbers`.
#[test]
fn nat_plus_needs_its_builtin() {
    assert_eq!(
        frame(&theory("", "%+")),
        "\"t.spthy\" (line 2, column 42):\nunexpected \"%\"\nexpecting \".\", \",\" or \")\""
    );
    assert_eq!(
        conclusion_op(&theory("natural-numbers", "%+")),
        BinOp::NatPlus
    );
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

/// `reserved "%1"` backtracks at an identifier boundary, after which
/// upstream's alphanumeric `identStart` reads `%12` as one nat variable.
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
fn disabled_nat_diagnostics_match_haskell() {
    for (term, expected) in [
        (
            "1:nat",
            "\"t.spthy\" (line 2, column 28):\nunexpected \")\"\nnatural-number literal 1:nat requires the natural-numbers builtin",
        ),
        (
            "%1",
            "\"t.spthy\" (line 2, column 25):\nunexpected \")\"\nnatural-number literal %1 requires the natural-numbers builtin",
        ),
        (
            "%n",
            "\"t.spthy\" (line 2, column 24):\nnat-sorted variables requires the natural-numbers builtin",
        ),
        (
            "%'n'",
            "\"t.spthy\" (line 2, column 24):\nunexpected \"'\"\nnat names requires the natural-numbers builtin",
        ),
        (
            "n:nat",
            "\"t.spthy\" (line 2, column 28):\nunexpected \")\"\nnat-sorted variables requires the natural-numbers builtin",
        ),
    ] {
        let src = format!("theory T begin\nrule R: [ ] --> [ Out({term}) ]\nend");
        assert_eq!(frame(&src), expected, "{term}");
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

/// Both spellings of the xor operator (`opXor`, Token.hs:555-556) need
/// `builtins: xor`.
#[test]
fn xor_needs_its_builtin() {
    assert_eq!(
        frame(&theory("", "XOR")),
        "\"t.spthy\" (line 2, column 42):\nunexpected \"X\"\nexpecting \".\", \",\" or \")\""
    );
    assert_eq!(
        frame(&theory("", "\u{2295}")),
        "\"t.spthy\" (line 2, column 42):\nunexpected \"\\8853\"\nexpecting \".\", \",\" or \")\""
    );
    for op in ["XOR", "\u{2295}"] {
        assert_eq!(conclusion_op(&theory("xor", op)), BinOp::Xor);
    }
}

/// `multterm` guards `expterm` too, so `*` and `^` both need `enableDH` —
/// which `builtins: bilinear-pairing` also sets, through `maudeSig`'s
/// `enableDH = enableDH || enableBP` (Term/Maude/Signature.hs:110-112).
#[test]
fn mult_and_exp_need_the_dh_bit() {
    assert_eq!(
        frame(&theory("", "*")),
        "\"t.spthy\" (line 2, column 42):\nunexpected \"*\"\nexpecting \".\", \",\" or \")\""
    );
    assert_eq!(
        frame(&theory("", "^")),
        "\"t.spthy\" (line 2, column 42):\nunexpected \"^\"\nexpecting \".\", \",\" or \")\""
    );
    assert_eq!(conclusion_op(&theory("diffie-hellman", "*")), BinOp::Mult);
    assert_eq!(conclusion_op(&theory("diffie-hellman", "^")), BinOp::Exp);
    assert_eq!(conclusion_op(&theory("bilinear-pairing", "*")), BinOp::Mult);
    assert_eq!(conclusion_op(&theory("bilinear-pairing", "^")), BinOp::Exp);
}

/// The `expecting` set names exactly the levels that ARE open: with multiset
/// alone, the `^` failure carries `msetterm`'s two `opUnion` spellings and
/// nothing from the closed `multterm`/`xorterm`/`natterm` levels.
#[test]
fn the_frame_lists_only_the_open_levels() {
    assert_eq!(
        frame(&theory("multiset", "^")),
        "\"t.spthy\" (line 3, column 42):\n\
         unexpected \"^\"\n\
         expecting \".\", \"++\", \"+\", \",\" or \")\""
    );
}
