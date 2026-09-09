// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Rule colors retain their literal grammar and six-digit validation.

use tamarin_parser::ast::{RuleAttr, TheoryItem};
use tamarin_parser::{parse_theory, ParseErrorKind};

fn color_theory(value: &str) -> String {
    format!("theory T begin\n\nrule R1[color={value}]: [ ] --> [ ]\n\nend\n")
}

/// The stored `Color` attribute of the accepted theory with `color=<value>`.
fn accepted_code(value: &str) -> String {
    stored_code(&color_theory(value))
}

/// The single `Color` attribute of `src`'s single rule.
fn stored_code(src: &str) -> String {
    let thy = parse_theory(src, &[]).expect("theory should parse");
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("one rule");
    match &rule.attributes[..] {
        [RuleAttr::Color(c)] => c.clone(),
        other => panic!("expected a single Color attribute, got {other:?}"),
    }
}

/// The four accepted spellings — bare, `#`-prefixed, single-quoted, quoted
/// with `#` — all reduce to the bare six-digit code (quotes/`#` stripped).
/// `readHex` accepts both cases, so uppercase codes load too; the stored code
/// keeps its case (rendering lowercases, matching `rgbToHex` of the parsed
/// `RGB` value).
#[test]
fn six_digit_codes_are_accepted() {
    assert_eq!(accepted_code("ff00ff"), "ff00ff");
    assert_eq!(accepted_code("#ff00ff"), "ff00ff");
    assert_eq!(accepted_code("'ff00ff'"), "ff00ff");
    assert_eq!(accepted_code("'#ff00ff'"), "ff00ff");
    assert_eq!(accepted_code("FF00FF"), "FF00FF");
}

/// `ruleAttribute` offers the British spelling first (Parser/Rule.hs:72-73),
/// and it stores the same attribute.  The oracle loads
/// `rule R1[colour=ff00ff]` at exit 0.  It renders that attribute as
/// `color=#ff00ff`.  That is the spelling the corpus uses
/// (examples/eurosp19-eccDAA/ISOIEC_20008_2013_2_ECC_DAA.fixed.spthy).
#[test]
fn the_british_spelling_stores_the_same_attribute() {
    assert_eq!(
        stored_code("theory T begin\n\nrule R1[colour=ff00ff]: [ ] --> [ ]\n\nend\n"),
        "ff00ff"
    );
    assert_eq!(
        stored_code("theory T begin\n\nrule R1[colour='#ff00ff']: [ ] --> [ ]\n\nend\n"),
        "ff00ff"
    );
}

#[test]
fn wrong_length_colors_point_at_the_code() {
    for (value, code) in [
        ("f0f", "f0f"),
        ("ff00ff0", "ff00ff0"),
        ("f0f ", "f0f"),
        ("'ff00'", "ff00"),
        ("ff00zz", "ff00"),
    ] {
        let source = color_theory(value);
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::MalformedHexColor { .. }),
            "{value}: {error:?}"
        );
        assert_eq!(&source[error.span()], code);
    }
}

#[test]
fn missing_digits_and_unclosed_quotes_point_at_the_failure() {
    for (value, tail) in [
        ("", "]"),
        ("gg0011", "gg0011"),
        ("#", "]"),
        ("''", "'"),
        ("'#'", "'"),
        ("'ff00zz'", "zz'"),
    ] {
        let source = color_theory(value);
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            source[error.span().start..].starts_with(tail),
            "{value}: {error:?}"
        );
    }
}
