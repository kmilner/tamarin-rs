// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for the `expecting …` set a rule header leaves behind.
//!
//! `protoRuleInfo` (Parser/Rule.hs:100-107) is
//! `symbol "rule" *> optional moduloE *> identifier *> ruleAttributesp *> colon`,
//! and `ruleAttributesp = option mempty (fold <$> list ruleAttribute)`
//! (Parser/Rule.hs:97-98).  When no `[…]` follows the name, `option` returns without
//! consuming, so parsec keeps its `Expect "\"[\""` and merges it into the
//! colon's failure — the frame reads `expecting "[" or ":"`.  A present
//! attribute list consumes, which discards that expectation and leaves
//! `expecting ":"` alone.
//!
//! Each expectation below is the pinned oracle's stderr for the same source,
//! verbatim.

use tamarin_parser::parse_theory;

/// The frame for `src`, with `name` as the `SourcePos` file name.
fn frame(name: &str, src: &str) -> String {
    parse_theory(src, &[])
        .expect_err("the probes below must all fail to parse")
        .with_source(name)
        .to_string()
}

#[test]
fn a_bare_rule_name_expects_the_attribute_bracket_or_the_colon() {
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule X\nend\n"),
        "\"r.spthy\" (line 3, column 1):\nunexpected \"e\"\nexpecting \"[\" or \":\""
    );
}

#[test]
fn the_same_set_survives_to_end_of_input() {
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule X\n"),
        "\"r.spthy\" (line 3, column 1):\nunexpected end of input\nexpecting \"[\" or \":\""
    );
}

#[test]
fn a_consumed_attribute_list_drops_the_bracket_expectation() {
    // An EMPTY `[]` counts as consumed, exactly as it does for `functions:`
    // attribute lists.
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule X []\nend\n"),
        "\"r.spthy\" (line 3, column 1):\nunexpected \"e\"\nexpecting \":\""
    );
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule X [color=#ffffff]\nend\n"),
        "\"r.spthy\" (line 3, column 1):\nunexpected \"e\"\nexpecting \":\""
    );
}

#[test]
fn junk_after_the_colon_expects_let_or_the_premise_bracket() {
    // `option emptySubst letBlock` precedes the premise list (Parser/Rule.hs:131):
    // the failed non-consuming probe leaves `Expect "\"let\""` at the same
    // offset as the premise `[` failure, and parsec merges the two.
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule X: garbage here\nend\n"),
        "\"r.spthy\" (line 2, column 9):\nunexpected \"g\"\nexpecting \"let\" or \"[\""
    );
}

#[test]
fn a_missing_rule_name_expects_the_modulo_paren_or_an_identifier() {
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule !x: [] --> []\nend\n"),
        "\"r.spthy\" (line 2, column 6):\nunexpected \"!\"\nexpecting \"(\" or identifier"
    );
}

#[test]
fn a_name_failure_abutting_the_rule_letters_merges_the_formal_comment_labels() {
    // With no whitespace after `rule`, the item alternation's formalComment
    // retry — `try (many1 letter <* string "{*")` (Token.hs:377-378) —
    // re-consumes the letters and fails at the SAME offset, so its
    // `letter`/`"{*"` labels join the name position's own.
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule"),
        "\"r.spthy\" (line 2, column 5):\nunexpected end of input\nexpecting \"(\", identifier, letter or \"{*\""
    );
    assert_eq!(
        frame("r.spthy", "theory T begin\nrule!x: [] --> []\nend\n"),
        "\"r.spthy\" (line 2, column 5):\nunexpected \"!\"\nexpecting \"(\", identifier, letter or \"{*\""
    );
}
