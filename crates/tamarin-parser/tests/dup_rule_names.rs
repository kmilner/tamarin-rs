//! Duplicate declarations are rejected without depending on error-frame formatting.

use tamarin_parser::ast::TheoryItem;
use tamarin_parser::{parse_theory, ParseContext, ParseErrorKind};

fn err(src: &str, file: &str) -> tamarin_parser::ParseError {
    parse_theory(src, &[]).unwrap_err().with_source(file)
}

fn is_duplicate(error: &tamarin_parser::ParseError, context: ParseContext, name: &str) -> bool {
    matches!(error.kind(),
        ParseErrorKind::DuplicateDeclaration { name: n, context: c }
        | ParseErrorKind::ConflictingDeclaration { name: n, context: c }
        if n == name && *c == context)
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
        &err(src, "dup.spthy"),
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
        &err(src, "dup.spthy"),
        ParseContext::Rule,
        "R1"
    ));
}

#[test]
fn duplicate_fires_before_a_later_parse_error() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               rule Broken: [ ] --> [\n\
               end\n";
    assert!(is_duplicate(
        &err(src, "dup.spthy"),
        ParseContext::Rule,
        "R1"
    ));
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
        &err(src, "dup.spthy"),
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
    let e = tamarin_parser::parse_theory_with_base(src, &[], Some(dir.clone()))
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
