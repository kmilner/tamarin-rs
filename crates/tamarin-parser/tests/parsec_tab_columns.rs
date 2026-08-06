// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Parity for the column a parse error reports on a line that contains tab
//! characters.
//!
//! HS computes every `SourcePos` with parsec's `updatePosChar`
//! (Text/Parsec/Pos.hs), which expands a tab to the next 8-column tab stop:
//! `column + 8 - ((column-1) mod 8)`.  Counting a tab as one column instead
//! shifts the reported column by 7 per preceding tab, so the position the
//! user sees stops matching the oracle's on every tab-indented line —
//! including `examples/csf18-alethea/alethea_selectionphase_anonymity.spthy`,
//! whose line 104 is two tabs deep (oracle column 66, one-per-tab column 52).
//!
//! Each expected column below is the pinned oracle's for the same source.

use tamarin_parser::{parse_theory, ParseError};

/// A rule whose conclusion holds a `diff(...)` term, so the error lands at a
/// known character on the rule's (indented) line.  `indent` is inserted
/// verbatim before the premise bracket.
fn diff_rule_probe(indent: &str) -> String {
    format!("theory T begin\nrule X:\n{indent}[ ] --[ ]-> [ Out(diff(a,b)) ]\nend\n")
}

/// Asserts `src` fails with the diff-flag rejection at `line`:`col`.
#[track_caller]
fn assert_diff_error_at(src: &str, line: u32, col: u32) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let at = *e.location();
    let ParseError::Custom { message, .. } = &e else {
        panic!("expected the diff-flag rejection, got {e:?}");
    };
    assert_eq!(message, "diff operator found, but flag diff not set");
    assert_eq!((at.line, at.col), (line, col));
}

/// [`assert_diff_error_at`] for a [`diff_rule_probe`], whose error is always
/// on line 3.
#[track_caller]
fn assert_probe_column(indent: &str, col: u32) {
    assert_diff_error_at(&diff_rule_probe(indent), 3, col);
}

#[test]
fn a_leading_tab_advances_to_the_next_eight_column_stop() {
    // Column 1 -> 1 + 8 - ((1-1) mod 8) = 9: the tab is worth 8 columns, so
    // the error sits 7 past where a one-column tab would put it (29).
    assert_probe_column("\t", 36);
}

#[test]
fn each_further_tab_adds_another_stop() {
    // Two tabs: 1 -> 9 -> 17, i.e. 14 past the one-column-per-tab reading.
    assert_probe_column("\t\t", 44);
    // A space then a tab lands on the same stop as a bare tab: 2 -> 9.
    assert_probe_column(" \t", 36);
}

#[test]
fn a_tab_on_a_stop_boundary_advances_a_full_stop_not_zero() {
    // Seven spaces put the tab at column 8, one short of the stop, so it
    // advances a single column (8 -> 9) — the one case where the naive rule
    // agrees.
    assert_probe_column("       \t", 36);
    // Eight spaces put it AT a stop (column 9), and `8 - ((9-1) mod 8)` is a
    // full 8, not 0: 9 -> 17.
    assert_probe_column("        \t", 44);
}

#[test]
fn tabs_after_the_error_position_do_not_move_it() {
    assert_diff_error_at(
        "theory T begin\nrule X:\n[ ] --[ ]-> [ Out(diff(a,b)) ]\t\nend\n",
        3,
        28,
    );
}

#[test]
fn an_embedded_tab_expands_from_its_own_column() {
    // `[ ]` then a tab: column 4 -> 9, and `--[ ]->` then a tab: 16 -> 17.
    assert_diff_error_at(
        "theory T begin\nrule X:\n[ ]\t--[ ]->\t[ Out(diff(a,b)) ]\nend\n",
        3,
        32,
    );
}

#[test]
fn a_newline_resets_the_column_before_the_next_tab() {
    // The first rule's tab must not leak into the second rule's column: both
    // lines are one tab deep and both start their content at column 9, so the
    // second rule reports the same offset from its own line start.
    assert_diff_error_at(
        "theory T begin\nfunctions: h/1\nrule X:\n\t[ ] --[ ]-> [ Out(h(a)) ]\n\
         rule Y:\n\t[ ] --[ ]-> [ Out(diff(a,b)) ]\nend\n",
        6,
        36,
    );
}
