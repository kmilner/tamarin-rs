use tamarin_parser::{parse_theory, parse_theory_with_base, ParseContext, ParseErrorKind};
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
        assert_eq!(&source[error.span().as_range()], expected_item);
    }
}

#[test]
fn standalone_formula_errors_attach_their_source() {
    for (source, offending) in [("P(x) & ?", "?"), ("P(x) garbage", "g")] {
        let error = tamarin_parser::parser::parse_formula_str(source, &pair_maude_sig())
            .expect_err("invalid formula must fail");
        assert_eq!(error.source_text(), Some(source));
        assert_eq!(&source[error.span().as_range()], offending);
    }
}

#[test]
fn applications_report_the_real_failure() {
    let undeclared = parse_theory(
        "theory T begin\nrule R: [ ] --> [ Out(g('a')) ]\nend\n",
        &[],
    )
    .expect_err("undeclared application must fail");
    assert_eq!(
        undeclared.kind(),
        &ParseErrorKind::UndeclaredFunction { name: "g".into() }
    );
    assert_eq!(
        &undeclared.source_text().unwrap()[undeclared.span().as_range()],
        "g"
    );

    let wrong_arity = parse_theory(
        "theory T begin\nfunctions: g/3\nrule R: [ ] --> [ Out(g('a','b')) ]\nend\n",
        &[],
    )
    .expect_err("wrong arity must fail");
    assert_eq!(
        wrong_arity.kind(),
        &ParseErrorKind::WrongFunctionArity {
            name: "g".into(),
            declared: 3,
            used: 2,
        }
    );
    assert_eq!(
        &wrong_arity.source_text().unwrap()[wrong_arity.span().as_range()],
        "g"
    );
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
        assert_eq!(&source[error.span().as_range()], "bogus");
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
    assert_eq!(&fact_source[fact.span().as_range()], "lower");

    let diff_source = "theory T begin\nrule R: [ ] --> [ Out(diff(a,b)) ]\nend\n";
    let diff = parse_theory(diff_source, &[]).expect_err("diff without flag must fail");
    assert_eq!(
        diff.kind(),
        &ParseErrorKind::IllegalDiffOperator {
            diff_enabled: false,
            in_equation: false,
        }
    );
    assert_eq!(&diff_source[diff.span().as_range()], "diff");
    assert_eq!(
        diff.diagnostic_notes(),
        ["the `diff` operator requires diff mode"]
    );

    let equation_source = "theory T begin\nequations: diff('a','b') = 'a'\nend\n";
    let equation = parse_theory(equation_source, &["diff"])
        .expect_err("diff in an equation must fail even in diff mode");
    assert_eq!(
        equation.kind(),
        &ParseErrorKind::IllegalDiffOperator {
            diff_enabled: true,
            in_equation: true,
        }
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
    } = error.kind()
    else {
        panic!("expected delimiter error, got {error:?}");
    };
    assert_eq!((opening.as_str(), closing.as_str()), ("(", ")"));
    assert_eq!(&source[opening_span.as_range()], "(");
    let labels = error.diagnostic_labels();
    assert_eq!(labels.len(), 2);
    assert!(labels.iter().any(|label| !label.primary));
    assert!(error.render_plain().contains("`(` opened here"));
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
    assert_eq!(&source[error.span().as_range()], "?");
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
        assert_eq!(&source[error.span().as_range()], name);
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
    assert_eq!(&source[error.span().as_range()], "R");
}

#[test]
fn malformed_colors_point_at_the_hex_code() {
    let source = "theory T begin\nrule R [color=f0f]: [ ] --> [ ]\nend\n";
    let error = parse_theory(source, &[]).expect_err("short color must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::MalformedHexColor { .. }
    ));
    assert_eq!(&source[error.span().as_range()], "f0f");
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
    assert_eq!(error.source_text(), Some("unknown_item: x\n"));
    assert_eq!(
        &error.source_text().unwrap()[error.span().as_range()],
        "unknown_item"
    );
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn missing_includes_point_at_the_path() {
    let source = "theory T begin\n#include \"does-not-exist.spthy\"\nend\n";
    let error = parse_theory_with_base(source, &[], Some(std::env::temp_dir()))
        .expect_err("missing include must fail");
    assert!(matches!(error.kind(), ParseErrorKind::IncludeIo { .. }));
    assert_eq!(&source[error.span().as_range()], "\"does-not-exist.spthy\"");
}

#[test]
fn escaped_include_paths_use_the_literal_source_span() {
    let source = "theory T begin\n#include \"no\\x2dsuch-\\&é.spthy\"\nend\n";
    let error = parse_theory_with_base(source, &[], Some(std::env::temp_dir()))
        .expect_err("missing include must fail");
    assert!(matches!(error.kind(), ParseErrorKind::IncludeIo { .. }));
    assert_eq!(
        &source[error.span().as_range()],
        "\"no\\x2dsuch-\\&é.spthy\""
    );
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
        } = error.kind()
        else {
            panic!("expected delimiter error, got {error:?}");
        };
        assert_eq!((opening.as_str(), closing.as_str()), ("[", "]"));
        assert_eq!(&source[opening_span.as_range()], "[");
    }
}

#[test]
fn duplicate_macro_arguments_point_at_the_name_after_a_sigil() {
    let source = "theory T begin\nmacros: m($foobar, $foobar) = $foobar\nend\n";
    let error = parse_theory(source, &[]).expect_err("duplicate argument must fail");
    assert!(matches!(
        error.kind(),
        ParseErrorKind::DuplicateMacroArgument { argument } if argument == "foobar"
    ));
    assert_eq!(&source[error.span().as_range()], "foobar");
}

#[test]
fn line_columns_are_derived_from_source_text() {
    let source = "theory T begin\n\tunknown: x\nend\n";
    let error = parse_theory(source, &[]).expect_err("unknown item must fail");
    assert_eq!(error.line_column(), (2, 9));
}
