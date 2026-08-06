// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rsasse, jdreier, rkunnema, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Parity for the lowercase-fact-name rejection.
//!
//! HS `fact'` (Fact.hs:39-50, see line 46) raises `fail "facts must start
//! with upper-case letters"` right after `identifier` consumed the name.  The
//! port raises [`ParseError::FactNameMustStartWithUppercase`] carrying the
//! offending name, positioned at the name itself rather than at the token the
//! parsec frame reported after it.
//!
//! In FORMULA context the whole `fact'` sits under `try … <?> "fact"` and the
//! atom alternation falls through to the term-relational atoms, so the fact
//! message never surfaces there (the oracle reports the term path's merged
//! labels instead: `unexpected "(" / expecting letter or digit, "." or "="`).
//! That residual formula-path shape is covered by
//! `tests/lookup_arity_errors.rs`.

use tamarin_parser::{parse_theory, ParseError};

/// Asserts `src` is rejected for the lowercase fact `name`, reported at
/// `line`:`col`.
#[track_caller]
fn assert_lowercase_fact(src: &str, name: &str, line: u32, col: u32) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let at = *e.location();
    let ParseError::FactNameMustStartWithUppercase { name: got, .. } = &e else {
        panic!("expected the lowercase-fact rejection, got {e:?}");
    };
    assert_eq!(got, name);
    assert_eq!((at.line, at.col), (line, col));
    assert_eq!(
        e.notes(),
        [format!(
            "fact name `{name}` must start with an uppercase letter"
        )]
    );
}

/// A lowercase fact in a rule premise.
#[test]
fn lowercase_fact_in_premise() {
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ foo(x) ] --> [ ]\n\nend\n",
        "foo",
        3,
        11,
    );
}

/// The same in a conclusion.
#[test]
fn lowercase_fact_in_conclusion() {
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ ] --> [ foo('a') ]\n\nend\n",
        "foo",
        3,
        19,
    );
}

/// The same in an action.
#[test]
fn lowercase_fact_in_action() {
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ ] --[ foo('a') ]-> [ ]\n\nend\n",
        "foo",
        3,
        17,
    );
}

/// A persistent lowercase fact behaves the same (the `!` parses first, and
/// the position is the name's, one past the sigil).
#[test]
fn lowercase_persistent_fact() {
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ !foo(x) ] --> [ ]\n\nend\n",
        "foo",
        3,
        12,
    );
}

/// What follows the name does not move the report: whitespace before the
/// argument list, or no argument list at all, both point at the name.
#[test]
fn the_token_after_the_name_does_not_move_the_report() {
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ foo (x) ] --> [ ]\n\nend\n",
        "foo",
        3,
        11,
    );
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ foo ] --> [ ]\n\nend\n",
        "foo",
        3,
        11,
    );
}

/// The ordering case that exposed the divergence: a rule whose conclusion
/// bracket is left open swallows the following `macros:` keyword as a fact
/// name, so the rejection names `macros` rather than reporting a stray
/// keyword.
#[test]
fn macros_keyword_after_open_bracket_is_a_fact_name() {
    assert_lowercase_fact(
        "theory T begin\n\nrule R: [ ] --> [\nmacros:\nm() = 'a'\n\nend\n",
        "macros",
        4,
        1,
    );
}
