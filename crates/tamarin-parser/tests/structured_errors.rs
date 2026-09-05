mod common;

use tamarin_parser::{
    parse_theory, parse_theory_with_base, IllegalDiffReason, ParseContext, ParseError,
    ParseErrorKind,
};
use tamarin_term::maude_sig::pair_maude_sig;

#[test]
fn semantic_errors_keep_the_offending_token_span() {
    let cases = [
        (
            "theory T begin\nbuiltins: hasing\nend\n",
            "hasing",
            ParseContext::Builtin,
        ),
        (
            "theory T begin\nnot_an_item: x\nend\n",
            "not_an_item",
            ParseContext::TheoryItem,
        ),
    ];

    for (source, expected_item, expected_context) in cases {
        let error = parse_theory(source, &[]).expect_err("invalid input must fail");
        let ParseErrorKind::UnknownItem { item, context } = error.kind() else {
            panic!("expected unknown-item error, got {error:?}");
        };
        assert_eq!(item, expected_item);
        assert_eq!(*context, expected_context);
        common::assert_span(&error, source, expected_item);
    }
}

#[test]
fn theory_item_errors_name_their_construct() {
    let cases = [
        ("options:\n", ParseContext::Options),
        ("predicates\n", ParseContext::Predicate),
        ("heuristic\n", ParseContext::Heuristic),
        ("tactic: t presort: ?\n", ParseContext::Tactic),
        ("test t = x\n", ParseContext::CaseTest),
        ("export tag\n", ParseContext::Export),
    ];

    for (item, expected) in cases {
        let source = format!("theory T begin\n{item}end\n");
        let error = parse_theory(&source, &[]).expect_err("malformed item must fail");
        assert_eq!(
            error.kind(),
            &ParseErrorKind::Expected { context: expected },
            "{item:?}: {error:?}",
        );
    }
}

#[test]
fn long_unknown_items_have_bounded_diagnostic_payloads() {
    let identifier = "a".repeat(10_000);
    let source = format!("theory T begin\n{identifier}: x\nend\n");
    let error = parse_theory(&source, &[]).expect_err("unknown item must fail");
    let ParseErrorKind::UnknownItem { item, .. } = error.kind() else {
        panic!("expected unknown-item error, got {error:?}");
    };
    assert!(item.ends_with('…'));
    assert!(item.chars().count() <= 81);
    assert_eq!(error.span().len(), identifier.len());
    assert!(error.render_plain().len() < 1_000);
}

#[test]
fn standalone_formula_errors_do_not_retain_their_source() {
    for (source, offending) in [("P(x) & ?", "?"), ("P(x) garbage", "g")] {
        let error = tamarin_parser::parser::parse_formula_str(source, &pair_maude_sig())
            .expect_err("invalid formula must fail");
        assert_eq!(error.source_text(), None);
        common::assert_span(&error, source, offending);
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
fn owned_source_text_moves_into_an_error_without_copying() {
    let contents = String::from("included source");
    let allocation = contents.as_ptr();
    let error = parse_theory("not a theory", &[])
        .expect_err("invalid theory must fail")
        .with_source_text("include.spthy", contents);
    assert_eq!(error.source_text().unwrap().as_ptr(), allocation);
}

#[test]
fn parse_errors_keep_the_result_payload_compact() {
    assert!(
        std::mem::size_of::<ParseError>() <= 128,
        "ParseError grew to {} bytes",
        std::mem::size_of::<ParseError>()
    );
}

#[test]
fn source_names_are_first_write_wins() {
    let error = parse_theory("not a theory", &[])
        .expect_err("invalid theory must fail")
        .with_source("upload.spthy")
        .with_source("root.spthy");
    assert_eq!(error.source_name(), Some("upload.spthy"));
    assert!(error.to_string().starts_with("\"upload.spthy\""));
}

#[test]
fn conflicting_functions_retain_their_option_details() {
    let source = "theory T begin\nfunctions: f/1, f/2\nend\n";
    let error = parse_theory(source, &[]).expect_err("conflicting functions must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::ConflictingDeclaration { .. }
    ));
    let notes = error.diagnostic_notes();
    assert_eq!(notes.len(), 1);
    assert!(
        notes[0].contains("conflicting arities/options"),
        "{notes:?}"
    );
    assert!(
        notes[0].contains("(1,Public,Constructor,NotNDC)"),
        "{notes:?}"
    );
    assert!(
        notes[0].contains("(2,Public,Constructor,NotNDC)"),
        "{notes:?}"
    );
}

#[test]
fn applications_report_the_real_failure() {
    let source = "theory T begin\nrule R: [ ] --> [ Out(g('a')) ]\nend\n";
    let undeclared = parse_theory(source, &[]).expect_err("undeclared application must fail");
    assert_eq!(
        undeclared.kind(),
        &ParseErrorKind::UndeclaredFunction { name: "g".into() }
    );
    common::assert_span(&undeclared, source, "g");

    let source = "theory T begin\nfunctions: g/3\nrule R: [ ] --> [ Out(g('a','b')) ]\nend\n";
    let wrong_arity = parse_theory(source, &[]).expect_err("wrong arity must fail");
    assert_eq!(
        wrong_arity.kind(),
        &ParseErrorKind::WrongFunctionArity {
            name: "g".into(),
            declared: 3,
            used: 2,
        }
    );
    common::assert_span(&wrong_arity, source, "g");
}

#[test]
fn formula_facts_preserve_nested_and_arity_errors() {
    let source = "theory T begin\nlemma L: \"All #i. Foo(g('a')) @ #i\"\nend\n";
    let error = parse_theory(source, &[]).expect_err("nested application must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::UndeclaredFunction { name: "g".into() }
    );
    assert_eq!(&source[error.span()], "g");

    let source = "theory T begin\nlemma L: \"All #i. Out() @ #i\"\nend\n";
    let error = parse_theory(source, &[]).expect_err("wrong fact arity must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::FactArity {
            name: "Out".into(),
            arity: 0,
        }
    );
    assert_eq!(&source[error.span()], "Out");
}

#[test]
fn proof_errors_keep_their_exact_nested_and_tabbed_spans() {
    let source =
        "theory T begin\nfunctions: Foo/1\nlemma L: \"T\"\nby solve( Foo(g('a')) @ #i )\nend\n";
    let error = parse_theory(source, &[]).expect_err("invalid solve goal must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::UndeclaredFunction { name: "g".into() }
    );
    assert_eq!(&source[error.span()], "g");

    let source = "theory T begin\nlemma L: \"T\"\nby\t?\nend\n";
    let error = parse_theory(source, &[]).expect_err("invalid proof method must fail");
    assert_eq!(error.line_column(), (3, 9));
    common::assert_span(&error, source, "?");

    let source = "theory T begin\nlemma L: \"T\"\n    by\t?\nend\n";
    let error = parse_theory(source, &[]).expect_err("indented invalid proof method must fail");
    assert_eq!(error.line_column(), (3, 9));
    common::assert_span(&error, source, "?");

    let source = "theory T begin\nfunctions: Foo/1\nlemma L: \"T\"\n    by solve(\tFoo(g('a')) @ #i )\nend\n";
    let error = parse_theory(source, &[]).expect_err("indented solve goal must fail");
    assert_eq!(error.line_column(), (4, 21));
    common::assert_span(&error, source, "g");

    let source = "theory D begin\ndiffLemma E:\n    rule-equivalence\n    case R\n    by step(\t? )\n    qed\nend\n";
    let error = tamarin_parser::parse_diff_theory(source, &[])
        .expect_err("indented invalid diff proof method must fail");
    assert_eq!(error.line_column(), (5, 17));
    common::assert_span(&error, source, "?");
}

#[test]
fn unknown_attributes_report_their_context() {
    let cases = [
        (
            "theory T begin\nrule R [bogus]: [ ] --> [ ]\nend\n",
            ParseContext::RuleAttribute,
        ),
        (
            "theory T begin\nrule R: [ ] --> [ ]\nlemma L [bogus]: \"T\"\nend\n",
            ParseContext::LemmaAttribute,
        ),
        (
            "theory T begin\nrestriction R [bogus]: \"T\"\nend\n",
            ParseContext::RestrictionAttribute,
        ),
    ];

    for (source, expected_context) in cases {
        let error = parse_theory(source, &[]).expect_err("unknown attribute must fail");
        assert!(matches!(
            error.kind(),
            ParseErrorKind::UnknownItem { item, context }
                if item == "bogus" && *context == expected_context
        ));
        common::assert_span(&error, source, "bogus");
    }
}

#[test]
fn invalid_fact_and_diff_errors_are_classified() {
    let fact_source = "theory T begin\nrule R: [ lower() ] --> [ ]\nend\n";
    let fact = parse_theory(fact_source, &[]).expect_err("lowercase fact must fail");
    assert_eq!(
        fact.kind(),
        &ParseErrorKind::InvalidFactName {
            name: "lower".into()
        }
    );
    common::assert_span(&fact, fact_source, "lower");

    let diff_source = "theory T begin\nrule R: [ ] --> [ Out(diff(a,b)) ]\nend\n";
    let diff = parse_theory(diff_source, &[]).expect_err("diff without flag must fail");
    assert_eq!(
        diff.kind(),
        &ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::DiffModeDisabled)
    );
    common::assert_span(&diff, diff_source, "diff");
    assert_eq!(
        diff.diagnostic_notes(),
        ["the `diff` operator requires diff mode"]
    );

    let equation_source = "theory T begin\nequations: diff('a','b') = 'a'\nend\n";
    let equation = parse_theory(equation_source, &["diff"])
        .expect_err("diff in an equation must fail even in diff mode");
    assert_eq!(
        equation.kind(),
        &ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::InEquation)
    );
    assert_eq!(
        equation.diagnostic_notes(),
        ["the `diff` operator is not allowed in equations"]
    );
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
fn long_undeclared_functions_have_bounded_diagnostic_payloads() {
    let name = "f".repeat(10_000);
    let source = format!("theory T begin\nrule R: [ ] --> [ Out({name}('a')) ]\nend\n");
    let error = parse_theory(&source, &[]).expect_err("undeclared function must fail");
    let ParseErrorKind::UndeclaredFunction { name } = error.kind() else {
        panic!("expected undeclared-function error, got {error:?}");
    };
    assert!(name.ends_with('…'));
    assert!(name.chars().count() <= 81);
    assert!(error.to_string().len() < 1_000);
    assert!(error.render_plain().len() < 1_000);
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
fn a_missing_list_separator_is_not_an_unclosed_delimiter() {
    let source = "theory T begin\nrule R: [ In('a') In('b') ] --> [ ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("missing comma must fail");
    assert!(matches!(error.kind(), ParseErrorKind::Expected { .. }));
}

#[test]
fn punctuation_attributes_use_the_source_character_span() {
    let source = "theory T begin\nrule R [?]: [ ] --> [ ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("unknown attribute must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::UnknownItem { item, .. } if item == "?"
    ));
    common::assert_span(&error, source, "?");
}

#[test]
fn delayed_semantic_errors_point_at_the_declaration() {
    let duplicate_cases = [
        (
            "theory T begin\nrestriction R: \"T\"\nrestriction R: \"T\"\nend\n",
            "R",
        ),
        ("theory T begin\nlemma L: \"T\"\nlemma L: \"T\"\nend\n", "L"),
    ];
    for (source, name) in duplicate_cases {
        let error = parse_theory(source, &[]).expect_err("duplicate must fail");
        assert!(matches!(
            error.kind(),
            ParseErrorKind::DuplicateDeclaration { .. }
        ));
        common::assert_span(&error, source, name);
        assert_eq!(
            error.diagnostic_notes(),
            [format!("`{name}` was already declared")]
        );
    }

    let source =
        "theory T begin\nrule R: [ ] --> [ Out('a') ]\nrule R: [ ] --> [ Out('b') ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("conflicting rule must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::ConflictingDeclaration { .. }
    ));
    common::assert_span(&error, source, "R");
}

#[test]
fn malformed_colors_point_at_the_hex_code() {
    let source = "theory T begin\nrule R [color=f0f]: [ ] --> [ ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("short color must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::MalformedHexColor { .. }
    ));
    common::assert_span(&error, source, "f0f");
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
            .starts_with(&format!("\"{}\"", included.display())),
        "legacy and structured source names diverged: {error}"
    );
    assert_eq!(error.source_text(), Some("unknown_item: x\n"));
    common::assert_span(&error, error.source_text().unwrap(), "unknown_item");
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn missing_includes_point_at_the_path() {
    let source = "theory T begin\n#include \"does-not-exist.spthy\"\nend\n";
    let error = parse_theory_with_base(source, &[], Some(std::env::temp_dir()))
        .expect_err("missing include must fail");
    assert!(matches!(error.kind(), ParseErrorKind::IncludeIo { .. }));
    common::assert_span(&error, source, "\"does-not-exist.spthy\"");
}

#[test]
fn escaped_include_paths_use_the_literal_source_span() {
    let source = "theory T begin\n#include \"no\\x2dsuch-\\&é.spthy\"\nend\n";
    let error = parse_theory_with_base(source, &[], Some(std::env::temp_dir()))
        .expect_err("missing include must fail");
    assert!(matches!(error.kind(), ParseErrorKind::IncludeIo { .. }));
    common::assert_span(&error, source, "\"no\\x2dsuch-\\&é.spthy\"");
}

#[test]
fn generic_failures_keep_their_grammar_context() {
    let source = "theory T begin\nrule R [color=ffffff] [ ] --> [ ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("missing rule colon must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::Expected {
            context: ParseContext::Rule
        }
    ));
    assert_eq!(
        error.diagnostic_message(),
        "Unexpected input while parsing rule"
    );
}

#[test]
fn unnamed_sources_render_with_the_input_placeholder() {
    let error = parse_theory("not a theory", &[]).expect_err("invalid theory must fail");
    assert_eq!(error.source_name(), None);
    assert!(error.render_plain().starts_with("<input>:1:1:"));
}

#[test]
fn empty_and_trailing_comma_lists_report_the_opening_delimiter() {
    for source in [
        "theory T begin\nrule R: [",
        "theory T begin\nrule R: [ In('a'),",
    ] {
        let error = parse_theory(source, &[]).expect_err("unclosed list must fail");
        let ParseErrorKind::UnclosedDelimiter {
            opening,
            opening_span,
            closing,
            ..
        } = error.kind()
        else {
            panic!("expected delimiter error, got {error:?}");
        };
        assert_eq!((*opening, *closing), ('[', ']'));
        assert_eq!(&source[opening_span.clone()], "[");
    }
}

#[test]
fn stray_closers_are_not_reported_as_unclosed_lists() {
    let source = "theory T begin\nrule R: [ In('a') } ] --> [ ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("stray closer must fail");
    assert!(
        !matches!(error.kind(), ParseErrorKind::UnclosedDelimiter { .. }),
        "unexpected delimiter diagnostic: {error:?}"
    );
}

#[test]
fn builtin_spans_preserve_whitespace_before_hyphens() {
    let source = "theory T begin\nbuiltins: diffie -helman\nend\n";
    let error = parse_theory(source, &[]).expect_err("misspelled builtin must fail");
    common::assert_span(&error, source, "diffie -helman");
}

#[test]
fn duplicate_macro_arguments_point_at_the_name_after_a_sigil() {
    let source = "theory T begin\nmacros: m($foobar, $   foobar) = $foobar\nend\n";
    let error = parse_theory(source, &[]).expect_err("duplicate argument must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::DuplicateMacroArgument { argument } if argument == "foobar"
    ));
    common::assert_span(&error, source, "foobar");
    assert_eq!(
        error.span().start,
        source.find("foobar) =").expect("second argument name"),
    );
}

#[test]
fn line_columns_are_derived_from_source_text() {
    let source = "theory T begin\n\tunknown: x\nend\n";
    let error = parse_theory(source, &[]).expect_err("unknown item must fail");
    assert_eq!(error.line_column(), (2, 9));
}

#[test]
fn semantic_errors_survive_a_missing_outer_delimiter() {
    let invalid_fact = "theory T begin\nrule R: [ lower()\nend\n";
    let error = parse_theory(invalid_fact, &[]).expect_err("lowercase fact must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::InvalidFactName {
            name: "lower".into(),
        }
    );

    let wrong_arity = "theory T begin\nfunctions: f/2\nrule R: [ Out(f(x))\nend\n";
    let error = parse_theory(wrong_arity, &[]).expect_err("wrong arity must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::WrongFunctionArity {
            name: "f".into(),
            declared: 2,
            used: 1,
        }
    );
}

#[test]
fn raw_semantic_failures_are_not_relabelled_as_unclosed_delimiters() {
    for (item, message) in [
        (
            "process: out(%x",
            "nat-sorted variables requires the natural-numbers builtin",
        ),
        (
            "process: out(%1",
            "natural-number literal %1 requires the natural-numbers builtin",
        ),
        (
            "process: out(1:nat",
            "natural-number literal 1:nat requires the natural-numbers builtin",
        ),
    ] {
        let source = format!("theory T begin\n{item}\nend\n");
        let error = parse_theory(&source, &[]).expect_err("missing builtin must fail");
        assert!(matches!(error.kind(), ParseErrorKind::Custom), "{error:?}");
        assert!(error.to_string().contains(message), "{error:?}");
    }
}

#[test]
fn balanced_malformed_symmetric_delimiters_keep_the_syntax_error() {
    for item in [
        "restriction A: \"x=x lemma L: all-traces\"",
        "restriction A: \"x=x rule R: [ ] --> [ ]\"",
        "restriction A: \"x=x garbage\"\nrestriction B: \"T",
        "rule R [color='#12 rule X: [']: [ ] --> [ ]",
    ] {
        let source = format!("theory T begin\n{item}\nend\n");
        let error = parse_theory(&source, &[]).expect_err("malformed item must fail");
        assert!(
            !matches!(error.kind(), ParseErrorKind::UnclosedDelimiter { .. }),
            "{item}: {error:?}"
        );
    }
}

#[test]
fn pipe_delimited_process_attributes_do_not_panic() {
    parse_theory("theory T begin process: 0 | bogus", &[])
        .expect_err("malformed process attributes must fail without recovery panics");
}

#[test]
fn unterminated_comments_have_their_own_diagnostic() {
    for source in [
        "theory T begin /* unfinished",
        "theory T begin end /* unfinished",
        "theory T begin rule R: [ /* unfinished",
        "theory T begin lemma L: \"T\" by sorry /* unfinished",
    ] {
        let error = parse_theory(source, &[]).expect_err("comment must close");
        assert!(
            matches!(error.kind(), ParseErrorKind::UnclosedBlockComment { .. }),
            "{error:?}"
        );
        let labels = error.diagnostic_labels_with_source(source);
        assert_eq!(&source[labels[1].span.clone()], "/*");
    }
    let error = tamarin_parser::parser::parse_formula_str("T /* unfinished", &pair_maude_sig())
        .expect_err("formula comment must close");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::UnclosedBlockComment { .. }
    ));
    let error = tamarin_parser::parse_intruder_rules(&pair_maude_sig(), "/* unfinished")
        .expect_err("intruder-rule comments must close");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::UnclosedBlockComment { .. }
    ));
    let parent = tamarin_parser::parser::Parser::new("", &[], false);
    let error = tamarin_parser::parse_proof_tree("by solve( /* unfinished", &parent)
        .expect_err("standalone proof comments must close");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::UnclosedBlockComment { .. }
    ));
}

#[test]
fn dual_function_names_label_the_resolved_declaration() {
    for (declarations, expected_site) in [("f/2 [AC], f/2", 1), ("f/2, f/2 [AC]", 0)] {
        let source = format!(
            "theory T begin\nfunctions: {declarations}\nrule R: [ ] --> [ Out(f(x)) ]\nend\n"
        );
        let sites: Vec<_> = source.match_indices("f/2").map(|(site, _)| site).collect();
        let error = parse_theory(&source, &[]).expect_err("wrong arity must fail");
        let labels = error.diagnostic_labels_with_source(&source);
        assert_eq!(labels.len(), 2, "{error:?}");
        assert_eq!(labels[1].span.start, sites[expected_site]);
    }
}

#[test]
fn builtin_conflicts_label_the_exact_function_variant() {
    let source =
        "theory T begin\nfunctions: senc/2 [AC], senc/1\nbuiltins: symmetric-encryption\nend\n";
    let declarations: Vec<_> = source
        .match_indices("senc/")
        .map(|(offset, _)| offset)
        .collect();
    let error = parse_theory(source, &[]).expect_err("builtin conflict must fail");
    let labels = error.diagnostic_labels_with_source(source);
    assert_eq!(labels.len(), 2, "{error:?}");
    assert_eq!(labels[1].span.start, declarations[1]);
}

#[test]
fn diff_lemma_declarations_are_secondary_labels() {
    for source in [
        "theory D begin\nlemma L [left]: \"T\"\nlemma L [left]: \"T\"\nend\n",
        "theory D begin\nlemma L [right]: \"T\"\nlemma L [right]: \"T\"\nend\n",
        "theory D begin\nlemma L [left]: \"T\"\nlemma L: \"T\"\nend\n",
        "theory D begin\ndiffLemma L: by sorry\ndiffLemma L: by sorry\nend\n",
    ] {
        let error = tamarin_parser::parse_diff_theory(source, &[])
            .expect_err("duplicate diff-theory lemma must fail");
        let labels = error.diagnostic_labels_with_source(source);
        assert_eq!(labels.len(), 2, "{error:?}");
        assert_eq!(&source[labels[0].span.clone()], "L");
        assert_eq!(&source[labels[1].span.clone()], "L");
        assert!(labels[1].span.start < labels[0].span.start);
    }
}

#[test]
fn related_labels_do_not_cross_include_boundaries() {
    let dir = std::env::temp_dir().join(format!(
        "tamarin_structured_related_sources_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create scratch directory");
    let included = dir.join("decl.spthy");

    std::fs::write(&included, "functions: f/2\n").expect("write included theory");
    let root = "theory T begin\nfunctions: f/1\n#include \"decl.spthy\"\nend\n";
    let error = parse_theory_with_base(root, &[], Some(dir.clone()))
        .expect_err("included conflict must fail");
    assert_eq!(error.diagnostic_labels().len(), 1);

    std::fs::write(&included, "functions: g/1\n").expect("write included theory");
    let root = "theory T begin\n#include \"decl.spthy\"\nfunctions: g/2\nend\n";
    let error =
        parse_theory_with_base(root, &[], Some(dir.clone())).expect_err("root conflict must fail");
    assert_eq!(error.diagnostic_labels_with_source(root).len(), 1);

    std::fs::write(&included, "functions: h/1\n").expect("write included theory");
    let root = "theory T begin\n#include \"decl.spthy\"\nfunctions: h/1, h/2\nend\n";
    let error = parse_theory_with_base(root, &[], Some(dir.clone()))
        .expect_err("redundant local declaration must not become the first site");
    assert_eq!(error.diagnostic_labels_with_source(root).len(), 1);

    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn declaration_labels_use_the_original_source_positions() {
    for (source, token) in [
        (
            "theory T begin functions: f/2 rule R: [] --> [Out(f(x))] end",
            "f",
        ),
        ("theory T begin functions: f/2, f/3 end", "f"),
        ("theory T begin lemma L: \"T\" lemma L: \"T\" end", "L"),
        (
            "theory T begin restriction R: \"T\" restriction R: \"T\" end",
            "R",
        ),
        (
            "theory T begin builtins: symmetric-encryption rule R: [] --> [Out(senc(x))] end",
            "symmetric-encryption",
        ),
        (
            "theory T begin functions: f/2 lemma L: \"T\" by solve(Out(f(x)) @ #i) end",
            "f",
        ),
    ] {
        let error = parse_theory(source, &[]).expect_err("invalid use");
        let labels = error.diagnostic_labels_with_source(source);
        assert_eq!(labels.len(), 2, "{error:?}");
        assert_eq!(&source[labels[1].span.clone()], token);
        assert!(labels[1].span.start < labels[0].span.start);
    }
}

#[test]
fn quoted_path_errors_keep_the_actual_failure_position() {
    let source = r#"theory T begin
#include "bad\q"
end"#;
    let error = parse_theory(source, &[]).expect_err("invalid escape");
    common::assert_span(&error, source, "q");
    let source = "theory T begin #include \"unfinished";
    let error = parse_theory(source, &[]).expect_err("unclosed path");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::UnclosedDelimiter { opening: '"', .. }
    ));
    assert_eq!(error.span().start, source.len());
}

#[test]
fn lemma_attribute_labels_cover_the_keyword_only() {
    let source = "theory T begin lemma L [bogus=something]: \"T\" end";
    let error = parse_theory(source, &[]).expect_err("unknown attribute");
    common::assert_span(&error, source, "bogus");
}

#[test]
fn parenthesized_terms_remain_valid_formula_operands() {
    for operator in ["=", "<<"] {
        let source =
            format!("theory T begin\nfunctions: F/1\nlemma L: \"(F(x)) {operator} F(x)\"\nend\n");
        parse_theory(&source, &[]).expect("parenthesized relational operand must parse");
    }
}

#[test]
fn parenthesized_terms_preserve_semantic_failures() {
    let source = "theory T begin\nfunctions: F/2\nlemma L: \"(F(x)) = x\"\nend\n";
    let error = parse_theory(source, &[]).expect_err("wrong arity must fail");
    assert_eq!(
        error.kind(),
        &ParseErrorKind::WrongFunctionArity {
            name: "F".into(),
            declared: 2,
            used: 1,
        }
    );
}

#[test]
fn identifier_spans_do_not_erase_comment_failures() {
    for source in [
        "x = y /* unfinished",
        "P(x) @ #i /* unfinished",
        "T /* unfinished",
    ] {
        let error = tamarin_parser::parser::parse_formula_str(source, &pair_maude_sig())
            .expect_err("unterminated comment must fail");
        assert!(
            matches!(error.kind(), ParseErrorKind::UnclosedBlockComment { .. }),
            "{error:?}"
        );
    }
    for source in [
        "theory T begin lemma L: \"x = y /* unfinished",
        "theory T begin rule R: [Out(x /* unfinished",
    ] {
        let error = parse_theory(source, &[]).expect_err("unterminated comment must fail");
        assert!(
            matches!(error.kind(), ParseErrorKind::UnclosedBlockComment { .. }),
            "{error:?}"
        );
    }
}

#[test]
fn later_proof_comments_do_not_replace_earlier_failures() {
    let source =
        "theory T begin functions: f/2 lemma L: \"T\" by solve(Out(f(x)) @ #i) /* unfinished";
    let error = parse_theory(source, &[]).expect_err("wrong arity");
    assert!(
        matches!(error.kind(), ParseErrorKind::WrongFunctionArity { .. }),
        "{error:?}"
    );
    common::assert_span(&error, source, "f");
    let source = "theory T begin lemma L: \"T\" by nonsense /* unfinished";
    let error = parse_theory(source, &[]).expect_err("invalid proof method");
    assert!(
        !matches!(error.kind(), ParseErrorKind::UnclosedBlockComment { .. }),
        "{error:?}"
    );
    assert!(error.diagnostic_message().contains("proof"), "{error:?}");
}

#[test]
fn parenthesized_formulas_preserve_inner_failures() {
    for (formula, token) in [("(Out(g(x)) @ #i)", "g"), ("(Out(x,y) @ #i)", "Out")] {
        let source = format!("theory T begin lemma L: \"{formula}\" end");
        let error = parse_theory(&source, &[]).expect_err("invalid fact");
        if token == "g" {
            assert!(
                matches!(error.kind(), ParseErrorKind::UndeclaredFunction { name } if name == "g"),
                "{error:?}"
            );
        } else {
            assert!(
                matches!(error.kind(), ParseErrorKind::FactArity { .. }),
                "{error:?}"
            );
        }
        common::assert_span(&error, &source, token);
    }
    let source = "theory T begin lemma L: \"(P(x) & ?)\" end";
    let error = parse_theory(source, &[]).expect_err("missing formula operand");
    assert!(error.span().start >= source.find('?').unwrap(), "{error:?}");
}

#[test]
fn malformed_equation_split_preserves_its_cause() {
    let source = "theory T begin lemma L: \"T\" by solve(splitEqs(x)) end";
    let error = parse_theory(source, &[]).expect_err("split id must be numeric");
    assert!(
        error.diagnostic_message().contains("expected a split id"),
        "{error:?}"
    );
    common::assert_span(&error, source, "x");
    parse_theory(
        "theory T begin lemma L: \"T\" by solve(splitEqs(1)) end",
        &[],
    )
    .expect("numeric split id remains valid");
}

#[test]
fn long_duplicate_names_keep_the_original_declaration_label() {
    for name in ["L".repeat(81), "λ".repeat(81)] {
        let source = format!("theory T begin lemma {name}: \"T\" lemma {name}: \"T\" end");
        let error = parse_theory(&source, &[]).expect_err("duplicate lemma");
        let labels = error.diagnostic_labels_with_source(&source);
        assert_eq!(labels.len(), 2, "{error:?}");
        assert_eq!(&source[labels[1].span.clone()], name);
        assert_eq!(labels[1].span.start, source.find(&name).unwrap());
        assert!(labels[1].span.start < labels[0].span.start);
    }
}
