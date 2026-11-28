//! Contracts of the parser's Rust API that no differential sees: where a
//! diagnostic's labels point, which source an error carries, bounded payloads,
//! and the shape-preserving properties of the term grammar.

use tamarin_parser::ast::{Rule, TheoryItem};
use tamarin_parser::{
    parse_theory, parse_theory_with_base, parse_theory_with_rule_check, ParseContext,
    ParseErrorKind, RuleConflictCheck,
};
use tamarin_term::maude_sig::pair_maude_sig;

/// The primary label covers `expected` in `source`.
#[track_caller]
fn assert_span(error: &tamarin_parser::ParseError, source: &str, expected: &str) {
    let labels = error.diagnostic_labels_with_source(source);
    assert_eq!(&source[labels[0].span.clone()], expected);
}

#[test]
fn standalone_formula_errors_do_not_retain_their_source() {
    for (source, offending) in [("P(x) & ?", "?"), ("P(x) garbage", "g")] {
        let error = tamarin_parser::parser::parse_formula_str(source, &pair_maude_sig())
            .expect_err("invalid formula must fail");
        assert_eq!(error.source_text(), None);
        assert_span(&error, source, offending);
    }
}

#[test]
fn source_text_can_be_attached_explicitly_without_being_replaced() {
    let source = "not a theory";
    let error = parse_theory(source, &[])
        .expect_err("invalid theory must fail")
        .with_source_text("", source)
        .with_source_text("named.spthy", "different");
    assert_eq!(error.source_name(), Some("named.spthy"));
    assert_eq!(error.source_text(), Some(source));
}

#[test]
fn attaching_source_does_not_change_the_semantic_span() {
    let source = "?";
    let error = parse_theory(source, &[]).expect_err("junk must fail");
    let span = error.span();

    let error = error.with_source_text("bad.spthy", source);

    assert_eq!(error.span(), span);
    assert_eq!(span, 0..0);
    assert_eq!(
        error.diagnostic_labels_with_source(source)[0].span.clone(),
        0..1
    );
}

#[test]
fn source_names_are_first_write_wins() {
    let error = parse_theory("not a theory", &[])
        .expect_err("invalid theory must fail")
        .with_source("upload.spthy")
        .with_source("root.spthy");
    assert_eq!(error.source_name(), Some("upload.spthy"));
    assert!(error.to_string().starts_with("upload.spthy:"));
}

#[test]
fn an_unclosed_list_labels_both_ends() {
    let source = "theory T begin\nrule R: [ ] --> [ Out('a' ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("unclosed fact must fail");
    let ParseErrorKind::UnclosedDelimiter {
        opening,
        opening_span,
        closing,
        ..
    } = error.kind()
    else {
        panic!("expected delimiter error, got {error:?}");
    };
    assert_eq!((*opening, *closing), ('(', ')'));
    assert_eq!(&source[opening_span.clone()], "(");
    let labels = error.diagnostic_labels();
    assert_eq!(labels.len(), 2);
    assert_eq!(labels[1].message, "`(` opened here");
    assert!(error
        .render_plain_with_source("input.spthy", source)
        .contains("`(` opened here"));
    assert!(!error.render_plain().contains("opened here"));
}

#[test]
fn all_semantic_error_payloads_have_a_central_bound() {
    let name = "f".repeat(10_000);
    let source = format!("theory T begin\nfunctions: {name}/1, {name}/2\nend\n");
    let error = parse_theory(&source, &[]).expect_err("conflicting declarations must fail");
    let ParseErrorKind::ConflictingDeclaration { name, .. } = error.kind() else {
        panic!("expected conflicting declaration, got {error:?}");
    };
    assert!(name.ends_with('…'));
    assert!(name.chars().count() <= 81);
    assert!(error.to_string().len() < 2_000);
    assert!(error.render_plain().len() < 2_000);
}

#[test]
fn included_file_errors_keep_the_included_source() {
    let dir =
        std::env::temp_dir().join(format!("tamarin_structured_errors_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create scratch directory");
    let included = dir.join("bad.spthy");
    std::fs::write(&included, "unknown_item: x\n").expect("write included theory");

    let root = "theory T begin\n#include \"bad.spthy\"\nend\n";
    let error = parse_theory_with_base(root, &[], Some(dir.clone()))
        .expect_err("bad included theory must fail")
        .with_source("root.spthy");

    assert_eq!(
        error.source_name(),
        Some(included.to_string_lossy().as_ref())
    );
    assert!(
        error
            .to_string()
            .starts_with(&format!("{}:", included.display())),
        "Display lost the included source name: {error}"
    );
    assert_eq!(error.source_text(), Some("unknown_item: x\n"));
    assert_span(&error, error.source_text().unwrap(), "unknown_item");
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn unnamed_sources_render_with_the_input_placeholder() {
    let error = parse_theory("not a theory", &[]).expect_err("invalid theory must fail");
    assert_eq!(error.source_name(), None);
    assert!(error.render_plain().starts_with("<input>:1:1:"));
}

/// A declaration label joins an error only from the file the error is in.
#[test]
fn related_labels_do_not_cross_include_boundaries() {
    let dir = std::env::temp_dir().join(format!(
        "tamarin_structured_related_sources_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create scratch directory");
    let included = dir.join("decl.spthy");
    for (fragment, root, labels) in [
        (
            "functions: f/2\n",
            "theory T begin\nfunctions: f/1\n#include \"decl.spthy\"\nend\n",
            1,
        ),
        (
            "functions: g/1\n",
            "theory T begin\n#include \"decl.spthy\"\nfunctions: g/2\nend\n",
            1,
        ),
        // A redundant local declaration does not become the first site.
        (
            "functions: h/1\n",
            "theory T begin\n#include \"decl.spthy\"\nfunctions: h/1, h/2\nend\n",
            1,
        ),
        // The use and its declaration are both in the included file.
        (
            "functions: f/2\nrule R: [] --> [Out(f(x))]\n",
            "theory T begin\n#include \"decl.spthy\"\nend",
            2,
        ),
    ] {
        std::fs::write(&included, fragment).expect("write included theory");
        let error = parse_theory_with_base(root, &[], Some(dir.clone())).expect_err(fragment);
        let got = error.diagnostic_labels_with_source(root);
        assert_eq!(got.len(), labels, "{fragment}: {error:?}");
        if labels == 2 {
            assert_eq!(error.source_text(), Some(fragment));
            assert_eq!(got[1].span.start, fragment.find("f/2").unwrap());
        }
    }
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn grouped_uppercase_function_terms_parse_as_relations() {
    use tamarin_parser::ast::TheoryItem;
    for operator in ["=", "<<", "⊏"] {
        for name in ["f", "G"] {
            let body = format!("{name}(x) {operator} x");
            let grouped = format!("(({name}(x))) {operator} x");
            let parse = |formula: &str| {
                let source =
                    format!("theory T begin functions: {name}/1 lemma L: \"{formula}\" end");
                let theory = parse_theory(&source, &[]).unwrap();
                let TheoryItem::Lemma(lemma) = &theory.items[1] else {
                    panic!("expected lemma");
                };
                lemma.formula.clone()
            };
            assert_eq!(parse(&grouped), parse(&body), "{grouped}");
        }
    }
    for formula in ["(G(x)) ==> G(x)", "(G(x)) <=> G(x)"] {
        parse_theory(&format!("theory T begin lemma L: \"{formula}\" end"), &[])
            .expect("logical operators must preserve the grouped formula");
    }
}

#[test]
fn compound_function_operands_use_the_complete_term_grammar() {
    use tamarin_parser::ast::TheoryItem;
    for (signature, operator) in [
        ("builtins: diffie-hellman", "^"),
        ("builtins: diffie-hellman", "*"),
        ("builtins: multiset", "++"),
        ("builtins: xor", "⊕"),
        ("builtins: xor", "XOR"),
        ("builtins: multiset", "+"),
        ("builtins: natural-numbers", "%+"),
        ("functions: X/2 [AC]", "X"),
    ] {
        for name in ["g", "G"] {
            let parse = |operand: &str| {
                let source = format!("theory T begin {signature} functions: {name}/1 lemma L: \"{operand} {operator} y = z\" end");
                let theory = parse_theory(&source, &[])
                    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
                let TheoryItem::Lemma(lemma) = theory.items.last().unwrap() else {
                    panic!("expected lemma");
                };
                lemma.formula.clone()
            };
            let bare = format!("{name}(x)");
            for grouped in [format!("({bare})"), format!("(({bare}))")] {
                assert_eq!(parse(&grouped), parse(&bare));
            }
        }
    }
}

#[test]
fn syntax_expectations_report_context_and_found_token() {
    for (source, context, expected, token) in [
        (
            "theory T begin rule : [] --> [] end",
            ParseContext::Rule,
            "identifier",
            ':',
        ),
        (
            "theory T begin process: ? end",
            ParseContext::Process,
            "process",
            '?',
        ),
        (
            "theory T begin lemma L: \"T\" by wobble end",
            ParseContext::Proof,
            "proof method",
            'w',
        ),
        (
            "theory T begin lemma L: \"T\" by solve(splitEqs(x)) end",
            ParseContext::Proof,
            "a split id",
            'x',
        ),
    ] {
        let error = parse_theory(source, &[]).expect_err("invalid syntax");
        assert_eq!(error.kind(), &ParseErrorKind::Expected { context });
        assert_eq!(
            error.diagnostic_notes(),
            [format!("expected {expected}; found {token:?}")]
        );
        assert_eq!(source[error.span().start..].chars().next(), Some(token));
    }
}

/// Without an installed check the parser leaves the comparison to
/// elaboration, so both rules parse.
#[test]
fn without_a_check_a_conflicting_rule_parses() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               end\n";
    let names: Vec<_> = parse_theory(src, &[])
        .expect("theory should parse")
        .items
        .into_iter()
        .filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r.name),
            _ => None,
        })
        .collect();
    assert_eq!(names, ["R1", "R1"]);
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
