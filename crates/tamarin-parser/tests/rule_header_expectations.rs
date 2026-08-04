// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rsasse, jdreier, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Rule.hs

//! Byte-pinned parity for the `expecting …` set a rule header leaves behind.
//!
//! `protoRuleInfo` (Rule.hs:100-107) is
//! `symbol "rule" *> optional moduloE *> identifier *> ruleAttributesp *> colon`,
//! and `ruleAttributesp = option mempty (fold <$> list ruleAttribute)`
//! (Rule.hs:97-98).  When no `[…]` follows the name, `option` returns without
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
