// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parity for the rejection of an attribute name no `[…]` list accepts.
//!
//! HS parses each attribute list as an alternation of `symbol`s — the rule
//! list `ruleAttribute` (Theory/Text/Parser/Rule.hs:70-95), the lemma list
//! `lemmaAttribute` (Theory/Text/Parser/Lemma.hs:39-53) — so a name outside
//! the alternation fails at its first character with every legal spelling,
//! plus the list's closing `"]"`, as the `expecting` set.  The port reports
//! that as [`ParseError::UnknownItem`], whose `item_kind` names the list and
//! whose `expected()` is the legal spellings ranked by edit distance to the
//! offending name and cut to the closest three.
//!
//! The rule and lemma positions below are the pinned oracle's (Git revision
//! ef3f0468) for the same source, and every spelling asserted legal loads at
//! exit 0 there.  Restriction attributes have no oracle position: HS's
//! NON-diff grammar has no restriction attribute list at all (it rejects
//! `restriction R [left]:` at the `[`, expecting `":"`), a divergence
//! `tests/dup_rule_names.rs` pins on the accepting side.

use tamarin_parser::ast::{LemmaAttr, RestrictionAttr, RuleAttr};
use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError};

/// The `(unknown_item, (line, col), expected)` of the [`ParseError::UnknownItem`]
/// `src` fails with, asserting its `item_kind` is `kind`.
#[track_caller]
fn unknown(src: &str, kind: ParseContext) -> (String, (u32, u32), Vec<String>) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::UnknownItem {
        item_kind,
        unknown_item,
        at,
    } = &e
    else {
        panic!("expected the unknown-item variant, got {e:?}");
    };
    assert_eq!(*item_kind, kind, "item kind of {e:?}");
    (
        unknown_item.clone(),
        (at.line, at.col),
        e.expected().expect("an unknown item carries suggestions"),
    )
}

/// A rule header carrying the attribute list `attrs`.
fn rule_theory(attrs: &str) -> String {
    format!("theory T begin\nrule R [{attrs}]:\n [] --> []\nend\n")
}

/// A lemma header carrying the attribute list `attrs`, with a second lemma
/// `M` for `hide_lemma=` to name.
fn lemma_theory(attrs: &str) -> String {
    format!("theory T begin\nrule R: [] --> []\nlemma L [{attrs}]: \"T\"\nlemma M: \"T\"\nend\n")
}

/// A restriction carrying the attribute list `attrs`.
fn restriction_theory(attrs: &str) -> String {
    format!("theory T begin\nrestriction R [{attrs}]: \"T\"\nend\n")
}

/// An accepted spelling of the rule attribute `name` — the value-taking ones
/// with a value, `x-` with a name after the prefix.
fn rule_spelling(name: &str) -> String {
    match name {
        "colour" | "color" => format!("{name}=#ffffff"),
        "process" => "process=\"P\"".to_string(),
        "role" => "role=\"A\"".to_string(),
        "no_derivcheck" | "issapicrule" => name.to_string(),
        n if n.starts_with("x-") => "x-foo".to_string(),
        n => panic!("no accepted spelling recorded for rule attribute `{n}`"),
    }
}

/// An accepted spelling of the lemma attribute `name`.
fn lemma_spelling(name: &str) -> String {
    match name {
        "hide_lemma" => "hide_lemma=M".to_string(),
        "heuristic" => "heuristic=S".to_string(),
        "output" => "output=[spthy]".to_string(),
        "typing" | "sources" | "reuse" | "diff_reuse" | "use_induction" | "left" | "right" => {
            name.to_string()
        }
        n => panic!("no accepted spelling recorded for lemma attribute `{n}`"),
    }
}

/// An unknown rule attribute is reported at the attribute's first character —
/// the oracle's line 2 column 9, where it lists `"colour="`, `"color="`,
/// `"process="`, `"no_derivcheck"`, `"role="`, `"issapicrule"`, `"x-"` and
/// `"]"`.
#[test]
fn an_unknown_rule_attribute_is_reported_at_the_attribute() {
    let (found, at, expected) = unknown(&rule_theory("bogus"), ParseContext::RuleAttribute);
    assert_eq!(found, "bogus");
    assert_eq!(at, (2, 9));
    assert_eq!(expected.len(), 3, "the closest three: {expected:?}");

    // An empty list and a legal list occupy the same position (oracle exit 0).
    parse_theory(&rule_theory(""), &[]).expect("an empty rule attribute list is legal");
    parse_theory(&rule_theory("color=#ffffff, no_derivcheck"), &[])
        .expect("a two-element rule attribute list is legal");
}

/// An unknown lemma attribute is reported at the attribute's first character —
/// the oracle's line 3 column 10, where it lists `"typing"`, `"sources"`,
/// `"reuse"`, `"diff_reuse"`, `"use_induction"`, `"hide_lemma"`,
/// `"heuristic"`, `"output"`, `"left"`, `"right"` and `"]"`.
#[test]
fn an_unknown_lemma_attribute_is_reported_at_the_attribute() {
    let (found, at, expected) = unknown(&lemma_theory("bogus"), ParseContext::LemmaAttribute);
    assert_eq!(found, "bogus");
    assert_eq!(at, (3, 10));
    assert_eq!(expected.len(), 3, "the closest three: {expected:?}");

    parse_theory(&lemma_theory(""), &[]).expect("an empty lemma attribute list is legal");
    parse_theory(&lemma_theory("sources, reuse"), &[])
        .expect("a two-element lemma attribute list is legal");
}

/// The restriction list admits only `left` and `right`, and reports anything
/// else at the attribute.  Both names survive the cut, ranked closest first.
#[test]
fn an_unknown_restriction_attribute_is_reported_at_the_attribute() {
    let (found, at, expected) = unknown(
        &restriction_theory("bogus"),
        ParseContext::RestrictionAttribute,
    );
    assert_eq!(found, "bogus");
    assert_eq!(at, (2, 16));
    assert_eq!(expected, ["right", "left"]);

    for attrs in ["left", "right", "left, right"] {
        parse_theory(&restriction_theory(attrs), &[])
            .unwrap_or_else(|e| panic!("[{attrs}] rejected: {e:?}"));
    }
}

/// A list that runs out of input is reported where a named attribute would
/// be — the oracle's line 2 column 9 for the rule list and line 3 column 10
/// for the lemma list, where it says `unexpected end of input`.
#[test]
fn an_unterminated_list_is_reported_at_the_attribute_position() {
    let (_, at, _) = unknown("theory T begin\nrule R [", ParseContext::RuleAttribute);
    assert_eq!(at, (2, 9));
    let (_, at, _) = unknown(
        "theory T begin\nrule R: [] --> []\nlemma L [",
        ParseContext::LemmaAttribute,
    );
    assert_eq!(at, (3, 10));
}

/// Every name the `expected` sets enumerate is a spelling the loop accepts, so
/// following a suggestion cannot produce a second rejection.
#[test]
fn every_enumerated_spelling_is_accepted() {
    // Sizes first: an emptied list would make the loops below assert nothing.
    assert_eq!(RuleAttr::expected().len(), 7);
    assert_eq!(LemmaAttr::expected().len(), 10);
    assert_eq!(RestrictionAttr::iter().count(), 2);

    for name in RuleAttr::expected() {
        let spelling = rule_spelling(name);
        parse_theory(&rule_theory(&spelling), &[])
            .unwrap_or_else(|e| panic!("rule attribute `{spelling}` rejected: {e:?}"));
    }
    for name in LemmaAttr::expected() {
        let spelling = lemma_spelling(name);
        parse_theory(&lemma_theory(&spelling), &[])
            .unwrap_or_else(|e| panic!("lemma attribute `{spelling}` rejected: {e:?}"));
    }
    for attr in RestrictionAttr::iter() {
        parse_theory(&restriction_theory(attr.as_str()), &[])
            .unwrap_or_else(|e| panic!("restriction attribute `{attr:?}` rejected: {e:?}"));
    }
}

/// Each suggestion set is drawn from its own list, and a one-edit typo puts
/// the intended name first.
#[test]
fn the_suggestions_come_from_the_lists_own_names() {
    let (_, _, expected) = unknown(&rule_theory("colr"), ParseContext::RuleAttribute);
    assert_eq!(expected[0], "color");
    for suggestion in &expected {
        assert!(
            RuleAttr::expected().contains(&suggestion.as_str()),
            "`{suggestion}` is not a rule attribute"
        );
    }

    let (_, _, expected) = unknown(&lemma_theory("reus"), ParseContext::LemmaAttribute);
    assert_eq!(expected[0], "reuse");
    for suggestion in &expected {
        assert!(
            LemmaAttr::expected().contains(&suggestion.as_str()),
            "`{suggestion}` is not a lemma attribute"
        );
    }

    let (_, _, expected) = unknown(
        &restriction_theory("lef"),
        ParseContext::RestrictionAttribute,
    );
    assert_eq!(expected[0], "left");
}
