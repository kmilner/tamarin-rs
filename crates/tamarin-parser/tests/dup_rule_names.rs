//! Duplicate declarations are rejected without depending on error-frame formatting.

use tamarin_parser::ast::{Rule, TheoryItem};
use tamarin_parser::{
    parse_theory, parse_theory_with_rule_check, ParseContext, ParseErrorKind, RuleConflictCheck,
};

fn err(src: &str, file: &str) -> tamarin_parser::ParseError {
    parse_theory(src, &[]).unwrap_err().with_source(file)
}

fn is_duplicate(error: &tamarin_parser::ParseError, context: ParseContext, name: &str) -> bool {
    matches!(error.kind(),
        ParseErrorKind::DuplicateDeclaration { name: n, context: c }
        | ParseErrorKind::ConflictingDeclaration { name: n, context: c }
        if n == name && *c == context)
}

/// A [`tamarin_parser::RuleConflictCheck`] over the parsed rules alone, so
/// these tests pin where and when the parser raises the conflict.  The
/// elaborated comparison the CLI installs is tested in `tamarin-theory`.
#[derive(Default)]
struct RulesDifferAsParsed {
    rules: Vec<Rule>,
}

impl RuleConflictCheck for RulesDifferAsParsed {
    fn declare(&mut self, item: &TheoryItem) {
        if let TheoryItem::Rule(r) = item {
            self.rules.push(r.clone());
        }
    }

    fn conflicts(&mut self, new: &Rule) -> bool {
        self.rules
            .iter()
            .find(|r| r.name == new.name)
            .is_some_and(|prev| {
                (&prev.attributes, &prev.lets, &prev.premises, &prev.actions)
                    != (&new.attributes, &new.lets, &new.premises, &new.actions)
                    || (
                        &prev.conclusions,
                        &prev.embedded_restrictions,
                        &prev.variants,
                    ) != (&new.conclusions, &new.embedded_restrictions, &new.variants)
            })
    }
}

fn rules_differ_as_parsed() -> Box<dyn RuleConflictCheck> {
    Box::new(RulesDifferAsParsed::default())
}

fn checked_err(src: &str, file: &str) -> tamarin_parser::ParseError {
    parse_theory_with_rule_check(src, &[], None, rules_differ_as_parsed())
        .unwrap_err()
        .with_source(file)
}

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

#[test]
fn different_color_same_name_is_a_duplicate() {
    let src = "theory T begin\n\n\
               rule R1[color=ff0000]: [ ] --> [ ]\n\
               rule R1[color=00ff00]: [ ] --> [ ]\n\n\
               end\n";
    assert!(is_duplicate(
        &checked_err(src, "dup.spthy"),
        ParseContext::Rule,
        "R1"
    ));
}

#[test]
fn different_body_same_name_is_a_duplicate() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               end\n";
    assert!(is_duplicate(
        &checked_err(src, "dup.spthy"),
        ParseContext::Rule,
        "R1"
    ));
}

/// HS raises `duplicate rule` while parsing (`liftedAddProtoRule`,
/// Theory/Text/Parser.hs), so it wins over a parse error further on.
#[test]
fn duplicate_fires_before_a_later_parse_error() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               rule Broken: [ ] --> [\n\
               end\n";
    assert!(is_duplicate(
        &checked_err(src, "dup.spthy"),
        ParseContext::Rule,
        "R1"
    ));
}

/// Without an installed check the parser leaves the comparison to
/// elaboration, so both rules parse.
#[test]
fn without_a_check_a_conflicting_rule_parses() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               end\n";
    assert_eq!(rule_names(src), ["R1", "R1"]);
}

/// The check is told the signature-shaping items and the rules in source
/// order, and asked about each rule before it is declared.
#[test]
fn the_check_sees_the_declarations_and_rules_in_order() {
    use std::cell::RefCell;
    use std::rc::Rc;
    struct Recorder(Rc<RefCell<Vec<String>>>);
    impl RuleConflictCheck for Recorder {
        fn declare(&mut self, item: &TheoryItem) {
            self.0.borrow_mut().push(match item {
                TheoryItem::Functions(_) => "functions".to_string(),
                TheoryItem::Builtins(_) => "builtins".to_string(),
                TheoryItem::Predicates(_) => "predicates".to_string(),
                TheoryItem::Rule(r) => r.name.clone(),
                _ => "other".to_string(),
            });
        }
        fn conflicts(&mut self, new: &Rule) -> bool {
            self.0.borrow_mut().push(format!("check {}", new.name));
            false
        }
    }
    let src = "theory T begin\n\
               builtins: hashing\n\
               rule R1: [ ] --> [ ]\n\
               functions: f/1\n\
               lemma L: \"F\"\n\
               predicates: P(x) <=> F\n\
               rule R2: [ ] --> [ ]\n\
               rule R1: [ ] --> [ ]\n\
               end\n";
    let seen = Rc::new(RefCell::new(Vec::new()));
    parse_theory_with_rule_check(src, &[], None, Box::new(Recorder(seen.clone()))).expect("parses");
    assert_eq!(
        *seen.borrow(),
        [
            "builtins",
            "check R1",
            "R1",
            "functions",
            "predicates",
            "check R2",
            "R2",
            "check R1",
            "R1"
        ]
    );
}

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

#[test]
fn identical_restrict_duplicate_dies_at_the_restriction() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert!(is_duplicate(
        &err(src, "dup.spthy"),
        ParseContext::Restriction,
        "Restr_R1_1"
    ));
}

#[test]
fn user_restriction_blocks_restrict_expansion() {
    let src = "theory T begin\n\n\
               restriction Restr_R1_1:\n  \
               \"All x #i #j. B(x) @ #i & B(x) @ #j ==> #i = #j\"\n\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert!(is_duplicate(
        &err(src, "dup.spthy"),
        ParseContext::Restriction,
        "Restr_R1_1"
    ));
}

#[test]
fn second_rule_with_restrict_is_a_duplicate_rule() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert!(is_duplicate(
        &checked_err(src, "dup.spthy"),
        ParseContext::Rule,
        "R1"
    ));
}

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
    let e = parse_theory_with_rule_check(src, &[], Some(dir.clone()), rules_differ_as_parsed())
        .unwrap_err()
        .with_source("dup.spthy");
    assert!(is_duplicate(&e, ParseContext::Rule, "R1"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn diff_right_lemma_namespace_crosses_include_boundary() {
    let dir = std::env::temp_dir().join(format!(
        "tamarin_parser_diff_include_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("mkdir");
    std::fs::write(
        dir.join("frag.spthy"),
        "lemma l [right]: exists-trace \"Ex #i. A() @ #i\"\n",
    )
    .expect("write fragment");
    let src = "theory T begin\n\
               #include \"frag.spthy\"\n\
               lemma l [right]: exists-trace \"Ex #i. A() @ #i\"\n\
               end\n";
    let error = tamarin_parser::parse_diff_theory_with_base(src, &[], Some(dir.clone()))
        .expect_err("the included right-side lemma occupies the namespace");
    assert!(is_duplicate(&error, ParseContext::Lemma, "l"), "{error}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn duplicate_lemma_without_proof_is_rejected() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               end\n";
    assert!(is_duplicate(
        &err(src, "dup.spthy"),
        ParseContext::Lemma,
        "l"
    ));
}

#[test]
fn duplicate_lemma_with_proof_is_rejected() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               lemma l: exists-trace \"Ex #i x. K(x)@i\"\n\
               simplify\n\
               by sorry\n\
               end\n";
    assert!(is_duplicate(
        &err(src, "dup.spthy"),
        ParseContext::Lemma,
        "l"
    ));
}

#[test]
fn sided_lemmas_still_share_the_regular_lemma_namespace() {
    let src = "theory T begin\n\
               lemma l [left]: exists-trace \"Ex #i. A() @ #i\"\n\
               lemma l [left]: exists-trace \"Ex #i. A() @ #i\"\n\
               end\n";
    assert!(
        is_duplicate(&err(src, "dup.spthy"), ParseContext::Lemma, "l"),
        "a non-diff theory must reject duplicate sided lemmas"
    );
}

#[test]
fn duplicate_restriction_item_is_rejected() {
    let src = "theory T begin\n\
               rule r: [ Fr(~k) ] --> [ Out(~k) ]\n\
               restriction one: \"All #i #j x. A(x)@i & A(x)@j ==> #i = #j\"\n\
               restriction one: \"All #i #j x. A(x)@i & A(x)@j ==> #i = #j\"\n\
               end\n";
    assert!(is_duplicate(
        &err(src, "dup.spthy"),
        ParseContext::Restriction,
        "one"
    ));
}

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

#[test]
fn duplicate_predicate_across_blocks_is_rejected() {
    let src = "theory T begin\n\
               predicates: P(x) <=> Ex #i. A(x)@i\n\
               predicates: P(x) <=> Ex #i. A(x)@i\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_duplicate_predicate(src, "P");
}

#[test]
fn duplicate_predicate_after_paren_is_rejected() {
    let src = "theory T begin\n\
               predicates: P(x) <=> (Ex #i. A(x)@i)\n\
               predicates: P(x) <=> (Ex #i. A(x)@i)\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_duplicate_predicate(src, "P");
}

#[test]
fn predicate_annotations_do_not_distinguish_declarations() {
    let src = "theory T begin\n\
               predicates: P(x)[-] <=> x = x\n\
               predicates: P(y)[+] <=> y = y\n\
               end\n";
    assert_duplicate_predicate(src, "P");
}

#[test]
fn predicate_collides_with_builtin_smaller() {
    let src = "theory T begin\n\
               builtins: multiset\n\
               predicates: Smaller(x,y) <=> Ex z. y = x ++ z\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_duplicate_predicate(src, "Smaller");
}

#[test]
fn duplicate_persistent_predicate_is_rejected() {
    let src = "theory T begin\n\
               predicates: !P(x) <=> Ex #i. A(x)@i\n\
               predicates: !P(x) <=> Ex #i. A(x)@i\n\
               rule r: [ In(x) ] --> [ Out(x) ]\n\
               end\n";
    assert_duplicate_predicate(src, "P");
}

fn assert_duplicate_predicate(source: &str, name: &str) {
    let error = parse_theory(source, &[]).unwrap_err();
    assert!(
        matches!(error.kind(), ParseErrorKind::DuplicateDeclaration { name: n, context: ParseContext::Predicate } if n == name),
        "{error:?}"
    );
    let head = source.rfind(&format!("{name}(")).unwrap();
    assert_eq!(error.span(), head..head + name.len());
}

#[test]
fn predicate_collision_keys_preserve_arity_and_multiplicity() {
    parse_theory(
        "theory T begin predicates: P(x) <=> T, P(x,y) <=> T, !P(x) <=> T end",
        &[],
    )
    .unwrap();
    assert_duplicate_predicate(
        "theory T begin predicates: ! /* first */ P(x) <=> T, ! /* second */ P(y) <=> T end",
        "P",
    );
}

#[test]
fn predicate_block_finishes_parsing_before_duplicate_validation() {
    let error = parse_theory(
        "theory T begin predicates: P(x) <=> T, P(y) <=> T, Q(z) <=> ",
        &[],
    )
    .unwrap_err();
    assert!(!matches!(
        error.kind(),
        ParseErrorKind::DuplicateDeclaration { .. }
    ));
}

#[test]
fn explicit_family_names_include_the_parent_and_each_member() {
    for members in [
        "rule (modulo AC) R: [] --> []",
        "rule (modulo AC) V: [] --> [], rule (modulo AC) V: [] --> []",
    ] {
        let source = format!("theory T begin\nrule R: [] --> [] variants {members}\nend");
        let error = err(&source, "duplicate_variant.spthy");
        assert!(is_duplicate(&error, ParseContext::Rule, "R"), "{error:?}");
        let start = source.find("R:").unwrap();
        assert_eq!(error.span(), start..start + 1);
    }
}

#[test]
fn explicit_member_names_may_overlap_unrelated_families() {
    let source = "theory T begin
rule R: [] --> [] variants rule (modulo AC) V: [] --> []
rule V: [] --> [] variants rule (modulo AC) W: [] --> []
rule S: [] --> [] variants rule (modulo AC) V: [] --> []
end";
    assert_eq!(rule_names(source), ["R", "V", "S"]);
}
