// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parity for the `expected` set a rule header leaves behind.
//!
//! `protoRuleInfo` (Parser/Rule.hs:100-107) is
//! `symbol "rule" *> optional moduloE *> identifier *> ruleAttributesp *> colon`,
//! and `ruleAttributesp = option mempty (fold <$> list ruleAttribute)`
//! (Parser/Rule.hs:97-98).  When no `[…]` follows the name, `option` returns without
//! consuming, so parsec keeps its `Expect "\"[\""` and merges it into the
//! colon's failure — the set reads `"[" or ":"`.  A present attribute list
//! consumes, which discards that expectation and leaves `":"` alone.
//!
//! Each position and expectation below is the pinned oracle's for the same
//! source.

use tamarin_parser::{parse_theory, ParseError};

/// Asserts `src` fails with the [`ParseError::Expected`] bridge variant at
/// `line`:`col` carrying exactly the `expected` labels.  `found` is `None`
/// at end of input, otherwise a prefix of the offending token.
#[track_caller]
fn assert_expected(src: &str, line: u32, col: u32, found: Option<&str>, expected: &[&str]) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    assert!(
        matches!(&e, ParseError::Expected { .. }),
        "expected the `Expected` variant, got {e:?}"
    );
    let at = e.location();
    assert_eq!((at.line, at.col), (line, col), "position of {e:?}");
    match found {
        None => assert_eq!(e.found(), None, "should be an end-of-input error"),
        Some(prefix) => {
            let got = e.found().unwrap_or("");
            assert!(
                got.starts_with(prefix),
                "offending token {got:?} should start with {prefix:?}"
            );
        }
    }
    let labels = e.expected().unwrap_or_default();
    assert_eq!(
        labels.iter().map(String::as_str).collect::<Vec<_>>(),
        expected
    );
}

#[test]
fn a_bare_rule_name_expects_the_attribute_bracket_or_the_colon() {
    assert_expected(
        "theory T begin\nrule X\nend\n",
        3,
        1,
        Some("end"),
        &["\"[\"", "\":\""],
    );
}

#[test]
fn the_same_set_survives_to_end_of_input() {
    assert_expected("theory T begin\nrule X\n", 3, 1, None, &["\"[\"", "\":\""]);
}

#[test]
fn a_consumed_attribute_list_drops_the_bracket_expectation() {
    assert_expected(
        "theory T begin\nrule X [color=#ffffff]\nend\n",
        3,
        1,
        Some("end"),
        &["\":\""],
    );
}

/// An EMPTY `[]` counts as consumed, exactly as it does for `functions:`
/// attribute lists: HS `ruleAttributesp`'s `list p = brackets (commaSep p)`
/// (Rule.hs:97-98, Token.hs) admits zero elements, so the header continues to
/// the colon and a complete rule with `[]` loads at exit 0.
///
/// KNOWN FAILURE — `Parser::rule_attributes` enters its attribute loop
/// unconditionally after the `[` and has no immediate-`]` exit, so it reports
/// `UnknownRuleAttribute { attribute: "" }` and rejects a legal rule.
#[test]
fn an_empty_attribute_list_is_consumed_like_a_non_empty_one() {
    assert_expected(
        "theory T begin\nrule X []\nend\n",
        3,
        1,
        Some("end"),
        &["\":\""],
    );
    parse_theory("theory T begin\nrule X []: [ ] --> [ ]\nend\n", &[])
        .expect("an empty rule attribute list is legal");
}

#[test]
fn junk_after_the_colon_expects_let_or_the_premise_bracket() {
    // `option emptySubst letBlock` precedes the premise list (Parser/Rule.hs:131):
    // the failed non-consuming probe leaves `Expect "\"let\""` at the same
    // offset as the premise `[` failure, and both are reported.
    let e = parse_theory("theory T begin\nrule X: garbage here\nend\n", &[])
        .expect_err("must fail to parse");
    assert!(
        matches!(&e, ParseError::ExpectedPunctuation { .. }),
        "expected a punctuation error, got {e:?}"
    );
    let at = e.location();
    assert_eq!((at.line, at.col), (2, 9));
    assert_eq!(e.found(), Some("garbage"));
    assert_eq!(e.expected().unwrap_or_default(), ["[", "\"let\""]);
}

#[test]
fn a_missing_rule_name_expects_the_modulo_paren_or_an_identifier() {
    assert_expected(
        "theory T begin\nrule !x: [] --> []\nend\n",
        2,
        6,
        Some("!"),
        &["\"(\"", "identifier"],
    );
}

#[test]
fn a_name_failure_abutting_the_rule_letters_merges_the_formal_comment_labels() {
    // With no whitespace after `rule`, the item alternation's formalComment
    // retry — `try (many1 letter <* string "{*")` (Token.hs:377-378) —
    // re-consumes the letters and fails at the SAME offset, so its
    // `letter`/`"{*"` labels join the name position's own.
    assert_expected(
        "theory T begin\nrule",
        2,
        5,
        None,
        &["\"(\"", "identifier", "letter", "\"{*\""],
    );
    assert_expected(
        "theory T begin\nrule!x: [] --> []\nend\n",
        2,
        5,
        Some("!"),
        &["\"(\"", "identifier", "letter", "\"{*\""],
    );
}
