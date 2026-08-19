// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The formula-atom tail error — what the port reports when no relational
//! operator follows an atom's leading term (HS `blatom`,
//! Theory/Text/Parser/Formula.hs:44-60).  HS's parsec merge produces
//! head-dependent label sets: the node-equality hangovers for an identifier
//! head, the `<?>` relabels `subterm predicate` / `multiset comparisson`
//! (sic) / `term equality` otherwise.  The port reports ONE uniform expected
//! set instead — the relational operators themselves.
//!
//! Each position below is the pinned oracle's for the same source (probed
//! 2026-08-05); the expected sets are the port's own.

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
    let at = e.location();
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
fn a_bare_temporal_variable_atom_reports_the_relational_set() {
    assert_expected(
        "theory A begin\nlemma L: \"All #i. #i\"\nend\n",
        2,
        21,
        "\"",
        &["=", "<<", "<", "(<)"],
    );
}

#[test]
fn sigil_headed_atoms_report_the_relational_set() {
    for (src, col) in [
        ("theory B begin\nlemma L: \"Ex x. ~x\"\nend\n", 19),
        ("theory C begin\nlemma L: \"Ex x. $x\"\nend\n", 19),
        ("theory D begin\nlemma L: \"Ex x. 'c'\"\nend\n", 20),
        ("theory E begin\nlemma L: \"Ex x. <x, x>\"\nend\n", 23),
    ] {
        assert_expected(src, 2, col, "\"", &["=", "<<", "<", "(<)"]);
    }
    // A connective after the sigil head errors at the connective, same set.
    assert_expected(
        "theory F begin\nlemma L: \"Ex x. ~x & T\"\nend\n",
        2,
        20,
        "&",
        &["=", "<<", "<", "(<)"],
    );
}

/// HS adds a `multiset comparisson` (sic) label here; the port's set does
/// not vary with the enabled builtins.
#[test]
fn the_multiset_builtin_does_not_change_the_set() {
    assert_expected(
        "theory G begin\nbuiltins: multiset\nlemma L: \"Ex x. ~x\"\nend\n",
        3,
        19,
        "\"",
        &["=", "<<", "<", "(<)"],
    );
}

#[test]
fn a_nat_sigil_head_reports_the_same_set() {
    assert_expected(
        "theory H begin\nbuiltins: natural-numbers\nlemma L: \"Ex x. %x\"\nend\n",
        3,
        19,
        "\"",
        &["=", "<<", "<", "(<)"],
    );
}
