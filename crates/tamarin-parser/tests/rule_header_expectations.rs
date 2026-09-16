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
