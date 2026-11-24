//! Rule header failures report the required syntax at the stopping point.
use tamarin_parser::parse_theory;

#[test]
fn incomplete_rule_headers_report_the_missing_construct() {
    for (body, tail, expected) in [
        ("rule X\n", "end", ":"),
        ("rule X\n", "", ":"),
        ("rule X []\n", "end", ":"),
        ("rule X [color=#ffffff]\n", "end", ":"),
        ("rule X: ", "garbage here\nend", "["),
        ("rule ", "!x: [] --> []\nend", "identifier"),
        ("rule", "", "identifier"),
        ("rule", "!x: [] --> []\nend", "identifier"),
    ] {
        let prefix = format!("theory T begin\n{body}");
        let source = format!("{prefix}{tail}");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert_eq!(error.span().start, prefix.len(), "{source}: {error:?}");
        assert!(
            error.diagnostic_message().contains(expected)
                || error
                    .diagnostic_notes()
                    .iter()
                    .any(|note| note.contains(expected)),
            "{error:?}"
        );
    }
}

/// HS reads a rule's `left`/`right` bodies in diff theories only
/// (`diffRule`, Theory/Text/Parser/Rule.hs): elsewhere `left` is not part of
/// the rule, and parsing stops there.
#[test]
fn left_right_rule_bodies_belong_to_diff_theories() {
    let prefix = "theory T begin\nrule R: [ ] --> [ ]\n";
    let source = format!(
        "{prefix}left rule A: [ ] --> [ Out('a') ]\nright rule B: [ ] --> [ Out('b') ]\nend"
    );
    let error = parse_theory(&source, &[]).unwrap_err();
    assert_eq!(error.span().start, prefix.len(), "{error:?}");
    let parsed = tamarin_parser::parse_diff_theory(&source, &[]).expect("a diff theory");
    assert!(parsed.items.iter().any(|item| matches!(
        item,
        tamarin_parser::ast::TheoryItem::Rule(r) if r.left_right.is_some()
    )));
}
