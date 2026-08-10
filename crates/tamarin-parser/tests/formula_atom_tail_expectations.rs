// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for the formula-atom tail error — the frame HS's
//! `blatom` alternation (Parser/Formula.hs:44-60) reports when no relational
//! operator follows an atom's leading term.  Two regimes:
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
//! Each expectation below is the pinned oracle's stderr for the same source,
//! verbatim (probed 2026-08-05, the whole matrix byte-identical).

use tamarin_parser::parse_theory;

fn frame(name: &str, src: &str) -> String {
    parse_theory(src, &[])
        .expect_err("the probes below must all fail to parse")
        .with_source(name)
        .to_string()
}

#[test]
fn a_bare_temporal_variable_atom_is_the_consumed_node_equality_frame() {
    assert_eq!(
        frame("f.spthy", "theory A begin\nlemma L: \"All #i. #i\"\nend\n"),
        "\"f.spthy\" (line 2, column 21):\nunexpected \"\\\"\"\nexpecting letter or digit, \".\" or \"=\""
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
        assert_eq!(
            frame("f.spthy", src),
            format!(
                "\"f.spthy\" (line 2, column {col}):\nunexpected \"\\\"\"\nexpecting subterm predicate or term equality"
            ),
            "{src:?}"
        );
    }
    // A connective after the sigil head errors at the connective, same set.
    assert_eq!(
        frame("f.spthy", "theory F begin\nlemma L: \"Ex x. ~x & T\"\nend\n"),
        "\"f.spthy\" (line 2, column 20):\nunexpected \"&\"\nexpecting subterm predicate or term equality"
    );
}

#[test]
fn the_multiset_builtin_adds_the_misspelled_comparisson_label() {
    assert_eq!(
        frame(
            "f.spthy",
            "theory G begin\nbuiltins: multiset\nlemma L: \"Ex x. ~x\"\nend\n"
        ),
        "\"f.spthy\" (line 3, column 19):\nunexpected \"\\\"\"\nexpecting subterm predicate, multiset comparisson or term equality"
    );
}

#[test]
fn a_nat_sigil_head_without_the_builtin_word_is_the_same_empty_failure() {
    assert_eq!(
        frame(
            "f.spthy",
            "theory H begin\nbuiltins: natural-numbers\nlemma L: \"Ex x. %x\"\nend\n"
        ),
        "\"f.spthy\" (line 3, column 19):\nunexpected \"\\\"\"\nexpecting subterm predicate or term equality"
    );
}
