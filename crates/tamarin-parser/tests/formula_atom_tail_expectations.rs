// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rsasse, jdreier, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Formula.hs

//! Parity for the formula-atom tail error — what HS's `blatom` alternation
//! (Formula.hs:44-60) reports when no relational operator follows an atom's
//! leading term.  Two regimes:
//!
//! * A `nodevar`-consumable head (bare or `#`-prefixed identifier): the
//!   un-`try`'d node-equality alternative consumes it, so `opEqual`'s failure
//!   is a CONSUMED error — the identifier lexeme's hangovers plus `"="`.
//! * Any other head (sigil-led `~x`/`$x`/`%x`, a literal, a tuple): every
//!   alternative fails empty and the merged error keeps the furthest-position
//!   `<?>` relabels of the `try`-wrapped relational alternatives —
//!   `subterm predicate` (, `multiset comparisson` — sic, only with the
//!   multiset builtin) and `term equality`.
//!
//! Each position and expectation set below is the pinned oracle's for the
//! same source (probed 2026-08-05, the whole matrix byte-identical).

use tamarin_parser::{parse_theory, ParseError};

/// Asserts `src` fails with the [`ParseError::Expected`] bridge variant at
/// `line`:`col`, on a token starting with `found`, carrying exactly the
/// `expected` labels.
#[track_caller]
fn assert_expected(src: &str, line: u32, col: u32, found: &str, expected: &[&str]) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    assert!(
        matches!(&e, ParseError::Expected { .. }),
        "expected the `Expected` variant, got {e:?}"
    );
    let at = e.location().location().expect("expected a location");
    assert_eq!((at.line, at.col), (line, col), "position of {e:?}");
    let got = e.found().unwrap_or("");
    assert!(
        got.starts_with(found),
        "offending token {got:?} should start with {found:?}"
    );
    let labels = e.expected().unwrap_or_default();
    assert_eq!(
        labels.iter().map(String::as_str).collect::<Vec<_>>(),
        expected
    );
}

#[test]
fn a_bare_temporal_variable_atom_is_the_consumed_node_equality_frame() {
    assert_expected(
        "theory A begin\nlemma L: \"All #i. #i\"\nend\n",
        2,
        21,
        "\"",
        &["letter or digit", "\".\"", "\"=\""],
    );
}

#[test]
fn sigil_headed_atoms_keep_the_relational_alternative_labels() {
    for (src, col) in [
        ("theory B begin\nlemma L: \"Ex x. ~x\"\nend\n", 19),
        ("theory C begin\nlemma L: \"Ex x. $x\"\nend\n", 19),
        ("theory D begin\nlemma L: \"Ex x. 'c'\"\nend\n", 20),
        ("theory E begin\nlemma L: \"Ex x. <x, x>\"\nend\n", 23),
    ] {
        assert_expected(src, 2, col, "\"", &["subterm predicate", "term equality"]);
    }
    // A connective after the sigil head errors at the connective, same set.
    assert_expected(
        "theory F begin\nlemma L: \"Ex x. ~x & T\"\nend\n",
        2,
        20,
        "&",
        &["subterm predicate", "term equality"],
    );
}

#[test]
fn the_multiset_builtin_adds_the_misspelled_comparisson_label() {
    assert_expected(
        "theory G begin\nbuiltins: multiset\nlemma L: \"Ex x. ~x\"\nend\n",
        3,
        19,
        "\"",
        &["subterm predicate", "multiset comparisson", "term equality"],
    );
}

#[test]
fn a_nat_sigil_head_without_the_builtin_word_is_the_same_empty_failure() {
    assert_expected(
        "theory H begin\nbuiltins: natural-numbers\nlemma L: \"Ex x. %x\"\nend\n",
        3,
        19,
        "\"",
        &["subterm predicate", "term equality"],
    );
}
