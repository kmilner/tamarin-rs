//! A term alone is not a formula; report the missing relation at its end.
use tamarin_parser::{parse_theory, ParseContext, ParseErrorKind};

#[test]
fn missing_relations_point_after_the_complete_term() {
    for (signature, term) in [
        ("", "#i"),
        ("", "~x"),
        ("", "$x"),
        ("", "'c'"),
        ("", "<x,x>"),
        ("functions: g/1", "g(x)"),
        ("functions: g/1", "(g(x))"),
        ("builtins: diffie-hellman", "x^y"),
        ("builtins: natural-numbers", "%x"),
        ("builtins: multiset", "~x"),
    ] {
        for tail in ["\" end", "& T\" end"] {
            let source = format!("theory T begin {signature} lemma L: \"{term} {tail}");
            let error = parse_theory(&source, &[]).unwrap_err();
            assert!(
                matches!(
                    error.kind(),
                    ParseErrorKind::Expected {
                        context: ParseContext::Formula
                    }
                ),
                "{source}: {error:?}"
            );
            assert_eq!(error.span().start, source.len() - tail.len());
            assert!(
                error
                    .diagnostic_notes()
                    .iter()
                    .any(|n| n.contains("term relation")),
                "{error:?}"
            );
        }
    }
}
