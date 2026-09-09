//! Invalid fact names retain their name spans in every rule position.
use tamarin_parser::{parse_theory, ParseErrorKind};

#[test]
fn lowercase_fact_names_point_at_the_name() {
    for (rule, name) in [
        ("rule R: [ foo(x) ] --> []", "foo"),
        ("rule R: [] --> [ foo('a') ]", "foo"),
        ("rule R: [] --[ foo('a') ]-> []", "foo"),
        ("rule R: [ !foo(x) ] --> []", "foo"),
        ("rule R: [ ! /* comment */ foo(x) ] --> []", "foo"),
        ("rule R: [ foo (x) ] --> []", "foo"),
        ("rule R: [ foo ] --> []", "foo"),
        ("rule R: [] --> [\nmacros:\nm() = 'a'", "macros"),
    ] {
        let source = format!("theory T begin\n{rule}\nend");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::InvalidFactName { name: n } if n == name),
            "{rule}: {error:?}"
        );
        let start = source.find(name).unwrap();
        assert_eq!(error.span(), start..start + name.len());
    }
}
