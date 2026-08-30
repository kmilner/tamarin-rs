// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for the duplicate-rule / duplicate-restriction guards
//! `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) runs after each
//! protocol rule parses:
//!
//!   * `addOpenProtoRule` (OpenTheory.hs:691-702) rejects a rule whose name is
//!     already bound to a DIFFERENT rule — an identical duplicate passes the
//!     guard and is appended a second time;
//!   * each `_restrict` formula's minted `Restr_<rule>_<i>` restriction goes
//!     through `addRestriction` (TheoryObject.hs:453-456) FIRST, which rejects
//!     on an existing NAME alone.
//!
//! Both rejections are `throwM` → `fail (show e)` (Token.hs:210-211) with
//! `show (DuplicateItem …)` (Parser/Exceptions.hs:38-40): an ordinary parsec
//! `fail` at the position after the rule, merging the trailing
//! `option [] $ symbol "variants" …` label (Parser/Rule.hs:134).
//!
//! The item-level guards work the same way: `liftedAddLemma`
//! (Theory/Text/Parser.hs:141-147) and `liftedAddRestriction`
//! (Theory/Text/Parser.hs:129-134) reject a reused lemma/restriction NAME,
//! and `liftedAddPredicate` (Theory/Text/Parser/Signature.hs:328-331)
//! rejects a redeclared predicate fact TAG — each failing at the position
//! past its item, merging whatever labels stand there.
//!
//! Every expected
//! string below is the stderr the pinned Haskell oracle (Git revision
//! ef3f0468) prints for the same theory, minus the three `maude tool:` banner
//! lines; every accepted theory loads with exit 0 there.

use tamarin_parser::ast::TheoryItem;
use tamarin_parser::parse_theory;

/// The parse error for `src`, rendered with `file` as parsec's `SourcePos`
/// name — the same string HS's `show err` produces (and the RS CLI prints).
fn err(src: &str, file: &str) -> String {
    parse_theory(src, &[])
        .unwrap_err()
        .with_source(file)
        .to_string()
}

/// The names of the protocol-rule items in `src`'s parsed theory.
fn rule_names(src: &str) -> Vec<String> {
    parse_theory(src, &[])
        .expect("theory should parse")
        .items
        .iter()
        .filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r.name.clone()),
            _ => None,
        })
        .collect()
}

/// Same name, different `color=` attribute: attributes are part of the
/// `ProtoRuleE` the guard compares (`ru ==`, OpenTheory.hs:697), so this is a
/// different rule and dies at the second rule's add — the fail sits at the
/// next token (`end`), after the second rule's trailing `variants` attempt.
#[test]
fn different_color_same_name_is_a_duplicate() {
    let src = "theory T begin\n\n\
               rule R1[color=ff0000]: [ ] --> [ ]\n\
               rule R1[color=00ff00]: [ ] --> [ ]\n\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 6, column 1):\n\
         unexpected \"e\"\n\
         expecting \"variants\"\n\
         duplicate rule: R1"
    );
}

/// Same name, different conclusions.
#[test]
fn different_body_same_name_is_a_duplicate() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 6, column 1):\n\
         unexpected \"e\"\n\
         expecting \"variants\"\n\
         duplicate rule: R1"
    );
}

/// The guard fires as soon as the second rule has parsed — mid-file, before a
/// later parse error is ever reached (`unexpected "r"` is the following
/// `rule` keyword's first char).
#[test]
fn duplicate_fires_before_a_later_parse_error() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               rule Broken: [ ] --> [\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 6, column 1):\n\
         unexpected \"r\"\n\
         expecting \"variants\"\n\
         duplicate rule: R1"
    );
}

/// A byte-identical duplicate passes `addOpenProtoRule`'s
/// `maybe True (ru ==) …` guard and is appended AGAIN — both copies are
/// items (and both render).  The corpus relies on this (e.g.
/// examples/asiaccs20-POIDC/OIDC_CodeFlow_with_ClientSecret.spthy carries
/// two identical `Get_pk` rules, which is the shape of the second case).  The
/// oracle loads both theories with exit 0.  It prints their
/// `rule (modulo E) …` echo twice.
#[test]
fn identical_duplicates_are_accepted_and_appended_twice() {
    for (case, name, src) in [
        (
            "empty rule",
            "R1",
            "theory T begin\n\n\
             rule R1: [ ] --> [ ]\n\
             rule R1: [ ] --> [ ]\n\n\
             end\n",
        ),
        (
            "corpus shape",
            "Get_pk",
            "theory T begin\n\n\
             rule Get_pk:\n    [ !Pk(A, pubkey) ]\n  -->\n    [ Out(pubkey) ]\n\n\
             rule Get_pk:\n    [ !Pk(A, pubkey) ]\n  -->\n    [ Out(pubkey) ]\n\n\
             end\n",
        ),
    ] {
        assert_eq!(rule_names(src), [name, name], "case {case}");
    }
}

/// Two `_restrict`-carrying rules with the same name die at the RESTRICTION
/// guard, before the rule-equality comparison: `liftedAddProtoRule` adds the
/// expanded `Restr_<rule>_<i>` restrictions first (Text/Parser.hs:177-179), and
/// `addRestriction` rejects on the existing NAME even though both rules (and
/// both restrictions) are byte-identical.
#[test]
fn identical_restrict_duplicate_dies_at_the_restriction() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 6, column 1):\n\
         unexpected \"e\"\n\
         expecting \"variants\"\n\
         duplicate restriction: Restr_R1_1"
    );
}

/// A user restriction that happens to carry a minted `Restr_<rule>_<i>` name
/// blocks the `_restrict` expansion the same way — `addRestriction` checks
/// against ALL restrictions in the theory.
#[test]
fn user_restriction_blocks_restrict_expansion() {
    let src = "theory T begin\n\n\
               restriction Restr_R1_1:\n  \
               \"All x #i #j. B(x) @ #i & B(x) @ #j ==> #i = #j\"\n\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 8, column 1):\n\
         unexpected \"e\"\n\
         expecting \"variants\"\n\
         duplicate restriction: Restr_R1_1"
    );
}

/// When only the SECOND rule carries `_restrict`, its restriction name is
/// fresh, so the restriction adds fine and the guard falls through to the
/// rule comparison — which fails on the differing actions.
#[test]
fn second_rule_with_restrict_is_a_duplicate_rule() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 6, column 1):\n\
         unexpected \"e\"\n\
         expecting \"variants\"\n\
         duplicate rule: R1"
    );
}

/// The guard spans `#include` fragments: HS runs one `addItems` accumulation
/// across included files, so a rule in the fragment collides with a
/// different same-named rule in the including file.  The error sits in the
/// including file, at the token after its rule.
#[test]
fn duplicate_across_include_is_rejected() {
    let dir = std::env::temp_dir().join(format!(
        "tamarin_parser_dup_rule_names_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("mkdir");
    std::fs::write(
        dir.join("frag.spthy"),
        "rule R1[color=ff0000]: [ ] --> [ ]\n",
    )
    .expect("write fragment");
    let src = "theory T begin\n\n\
               #include \"frag.spthy\"\n\n\
               rule R1[color=00ff00]: [ ] --> [ ]\n\n\
               end\n";
    let e = tamarin_parser::parse_theory_with_base(src, &[], Some(dir.clone()))
        .unwrap_err()
        .with_source("dup.spthy")
        .to_string();
    assert_eq!(
        e,
        "\"dup.spthy\" (line 7, column 1):\n\
         unexpected \"e\"\n\
         expecting \"variants\"\n\
         duplicate rule: R1"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A second lemma with a reused name dies at `addLemma`'s name guard
/// (TheoryObject.hs:462-465, reached through `liftedAddLemma`,
/// Theory/Text/Parser.hs:280-282).  Neither lemma carries a proof, so the
/// unmatched `startProofSkeleton` alternatives
/// (Theory/Text/Parser/Lemma.hs:85, Theory/Text/Parser/Proof.hs:76-115) leave
/// their labels at the item's end, and the fail merges them in.
#[test]
fn duplicate_lemma_without_proof_carries_the_skeleton_labels() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 5, column 1):\n\
         unexpected \"e\"\n\
         expecting \"SOLVED\", \"by\", \"sorry\", \"simplify\", \"solve\", \"contradiction\", \
         \"induction\", \"INVALIDATED\" or \"UNFINISHABLE\"\n\
         duplicate lemma: l"
    );
}

/// When the second lemma DOES carry a proof, the skeleton alternatives were
/// consumed, no labels stand at the item's end, and the frame is bare.
#[test]
fn duplicate_lemma_with_proof_has_a_bare_frame() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               simplify\n\
               by sorry\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 7, column 1):\n\
         unexpected \"e\"\n\
         duplicate lemma: l"
    );
}

#[test]
fn sided_lemmas_still_share_the_regular_lemma_namespace() {
    let src = "theory T begin\n\
               lemma l [left]: exists-trace \"Ex #i. A() @ #i\"\n\
               lemma l [left]: exists-trace \"Ex #i. A() @ #i\"\n\
               end\n";
    assert!(
        err(src, "dup.spthy").contains("duplicate lemma: l"),
        "a non-diff theory must reject duplicate sided lemmas"
    );
}

/// A second `restriction` item with a reused name dies at `addRestriction`'s
/// name guard (TheoryObject.hs:453-456, reached through
/// `liftedAddRestriction`, Theory/Text/Parser.hs:129-134).  The closing
/// quote's lexeme leaves no labels, so the frame is bare.
#[test]
fn duplicate_restriction_item_is_rejected() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               restriction one: \"All #i #j x. A(x)@i & A(x)@j ==> #i = #j\"\n\
               restriction one: \"All #i #j x. A(x)@i & A(x)@j ==> #i = #j\"\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 5, column 1):\n\
         unexpected \"e\"\n\
         duplicate restriction: one"
    );
}

/// Lemmas and restrictions have separate name spaces: `lookupLemma` only
/// sees `LemmaItem`s and `lookupRestriction` only `RestrictionItem`s
/// (TheoryObject.hs:671-676), so a lemma may reuse a restriction's name.
#[test]
fn lemma_and_restriction_names_do_not_collide() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               restriction Smaller: \"All #i #j x. A(x)@i & A(x)@j ==> #i = #j\"\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               lemma Smaller: exists-trace \"Ex #i x. K(x)@i\"\n\
               end\n";
    assert!(parse_theory(src, &[]).is_ok());
}

/// A predicate redeclared in a LATER block dies at `addPredicate`'s tag guard
/// (TheoryObject.hs:540-543 via `lookupPredicate`,
/// Theory/Syntactic/Predicate.hs:77-80), raised past the second block.  The
/// last formula ends right after the timepoint variable `#i`, whose pending
/// dot-index attempt contributes the leading `"."` label ahead of the formula
/// operators and `commaSep1`'s comma.
#[test]
fn duplicate_predicate_across_blocks_is_rejected() {
    let src = "theory T begin\n\
               predicates: P(x) <=> Ex #i. A(x)@i\n\
               predicates: P(x) <=> Ex #i. A(x)@i\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 4, column 1):\n\
         unexpected \"r\"\n\
         expecting \".\", \"&\", \"∧\", \"|\", \"∨\", \"==>\", \"⇒\", \"<=>\", \"⇔\" or \",\"\n\
         duplicate predicate: P( x )"
    );
}

/// The same collision with the formula ending in a closing paren: the paren's
/// lexeme moved past the variable's dot-index attempt, so no `"."` label.
#[test]
fn duplicate_predicate_after_paren_has_no_dot_label() {
    let src = "theory T begin\n\
               predicates: P(x) <=> (Ex #i. A(x)@i)\n\
               predicates: P(x) <=> (Ex #i. A(x)@i)\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 4, column 1):\n\
         unexpected \"r\"\n\
         expecting \"&\", \"∧\", \"|\", \"∨\", \"==>\", \"⇒\", \"<=>\", \"⇔\" or \",\"\n\
         duplicate predicate: P( x )"
    );
}

/// `lookupPredicate` appends the builtin predicates to the lookup list
/// (Theory/Syntactic/Predicate.hs:58-67,78), so declaring `Smaller/2`
/// collides with the builtin.  The formula's last term ends after a message
/// variable, so the enabled multiset operator labels sit between the dot
/// attempt and the formula operators.
#[test]
fn predicate_collides_with_builtin_smaller() {
    let src = "theory T begin\n\
               builtins: multiset\n\
               predicates: Smaller(x,y) <=> Ex z. y = x ++ z\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 4, column 1):\n\
         unexpected \"r\"\n\
         expecting \".\", \"++\", \"+\", \"&\", \"∧\", \"|\", \"∨\", \"==>\", \"⇒\", \"<=>\", \"⇔\" or \",\"\n\
         duplicate predicate: Smaller( x, y )"
    );
}

/// The duplicate key is the fact TAG (`sameName` is tag equality,
/// Theory/Syntactic/Predicate.hs:78-80), so a persistent head only collides
/// with a persistent head, and the message renders `showFactTag`'s `!`.
#[test]
fn duplicate_persistent_predicate_renders_the_bang() {
    let src = "theory T begin\n\
               predicates: !P(x) <=> Ex #i. A(x)@i\n\
               predicates: !P(x) <=> Ex #i. A(x)@i\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_eq!(
        err(src, "dup.spthy"),
        "\"dup.spthy\" (line 4, column 1):\n\
         unexpected \"r\"\n\
         expecting \".\", \"&\", \"∧\", \"|\", \"∨\", \"==>\", \"⇒\", \"<=>\", \"⇔\" or \",\"\n\
         duplicate predicate: !P( x )"
    );
}
