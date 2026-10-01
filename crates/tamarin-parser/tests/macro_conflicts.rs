//! Macro guards preserve rejection, priority, and structured causes.
use tamarin_parser::{parse_theory, ParseContext, ParseErrorKind};

#[test]
fn reserved_macro_names_fail_before_arguments_or_body() {
    for name in [
        "mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor",
    ] {
        for tail in ["(", "(x, x) = x", "(x)", "(x) = x"] {
            let source = format!("theory T begin macros: {name}{tail} end");
            let error = parse_theory(&source, &[]).unwrap_err();
            assert!(
                matches!(error.kind(), ParseErrorKind::ReservedBuiltin { name: n, context: ParseContext::Macro } if n == name),
                "{error:?}"
            );
            assert_eq!(&source[error.span()], name);
        }
    }
}

#[test]
fn duplicate_macro_arguments_compare_name_sort_and_index() {
    for args in [
        "x, x",
        "x, x:msg",
        "x:msg, x",
        "x:pub, x:pub",
        "x.1, y, x.1",
        "x, x,",
    ] {
        let source = format!("theory T begin macros: m({args}) = x end");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::DuplicateMacroArgument { argument } if argument == "x"),
            "{error:?}"
        );
        let repeated_name = source.find("m(").unwrap() + 2 + args.rfind('x').unwrap();
        assert_eq!(error.span(), repeated_name..repeated_name + 1);
    }
    for args in ["x, x.1", "x:fresh, x:msg", "$x, ~x, #x"] {
        parse_theory(&format!("theory T begin macros: m({args}) = x end"), &[]).unwrap();
    }
    let error = parse_theory("theory T begin macros: m(x,x)", &[]).unwrap_err();
    assert!(matches!(
        error.kind(),
        ParseErrorKind::DuplicateMacroArgument { .. }
    ));
}

#[test]
fn macro_conflicts_cover_signature_sources_and_body_shapes() {
    for (signature, name) in [
        ("functions: f/1", "f"),
        ("macros: m(x) = x", "m"),
        ("builtins: hashing", "h"),
        ("", "fst"),
        ("builtins: diffie-hellman", "DH_neutral"),
        ("builtins: bilinear-pairing", "DH_neutral"),
        ("builtins: natural-numbers", "tone"),
        ("functions: f/2 [AC]", "f"),
        (
            "builtins: diffie-hellman,xor,multiset,natural-numbers functions: f/1",
            "f",
        ),
    ] {
        assert_macro_conflict(signature, name, "x");
    }
    for body in ["$y", "(x)", "x:pub", "x.1", "'a'", "pair(x,x)", "pair{x}x"] {
        assert_macro_conflict("functions: f/1", "f", body);
    }
    for name in ["DH_neutral", "tone"] {
        parse_theory(&format!("theory T begin macros: {name}(x) = x end"), &[]).unwrap();
    }
}

#[test]
fn missing_macro_body_is_rejected_at_end_of_input() {
    let source = "theory T begin macros: m(x) = end";
    let error = parse_theory(source, &[]).unwrap_err();
    assert_eq!(error.span().start, source.len());
}

fn assert_macro_conflict(signature: &str, name: &str, body: &str) {
    let source = format!("theory T begin {signature} macros: {name}(x) = {body} end");
    let error = parse_theory(&source, &[]).unwrap_err();
    assert!(
        matches!(error.kind(), ParseErrorKind::ConflictingDeclaration { name: n, context: ParseContext::Macro } if n == name),
        "{source}: {error:?}"
    );
    assert_eq!(&source[error.span()], name);
}
