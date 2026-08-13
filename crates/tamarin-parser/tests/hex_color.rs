// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rsasse, jdreier, rkunnema, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs,
//   lib/utils/src/Data/Color.hs

//! Parity for the `color=`/`colour=` rule-attribute value.
//!
//! HS lexes the value with `hexColor` (Token.hs:403-406, `lexeme (singleQuoted
//! hexCode <|> hexCode)`, `hexCode = optional (symbol "#") *> many1 hexDigit`)
//! and validates it with `hexToRGB` (Data/Color.hs:149-155), which only
//! matches a SIX-character code; `parseColor` (Parser/Rule.hs:81-85) turns a
//! `Nothing` into `fail ("Color code " ++ show hc ++ " could not be parsed to
//! RGB")`, which the port reports as a [`ParseError::Custom`] with the same
//! message.  A lexing failure short of that keeps its expectation set.
//!
//! Every message, position and expectation set below is the pinned Haskell
//! oracle's (Git revision ef3f0468) for the same theory; every accepted
//! theory loads with exit 0 there and renders the attribute as lowercase
//! `color=#<code>`.

use tamarin_parser::ast::{RuleAttr, TheoryItem};
use tamarin_parser::{parse_theory, ParseError, RuleAttrKind};

fn color_theory(value: &str) -> String {
    format!("theory T begin\n\nrule R1[color={value}]: [ ] --> [ ]\n\nend\n")
}

/// Asserts `color=<value>` is rejected by `hexToRGB` with HS's message, at
/// `line`:`col`.
#[track_caller]
fn assert_bad_rgb(value: &str, code: &str, line: u32, col: u32) {
    let e = parse_theory(&color_theory(value), &[]).expect_err("must fail to parse");
    let at = *e.location();
    let ParseError::Custom { message, .. } = &e else {
        panic!("expected the `hexToRGB` rejection, got {e:?}");
    };
    assert_eq!(
        message,
        &format!("Color code \"{code}\" could not be parsed to RGB")
    );
    assert_eq!((at.line, at.col), (line, col));
}

/// Asserts `color=<value>` fails while LEXING the code, at `line`:`col` on a
/// token starting with `found`, carrying exactly the `expected` labels.
#[track_caller]
fn assert_lex_expected(value: &str, line: u32, col: u32, found: &str, expected: &[&str]) {
    let e = parse_theory(&color_theory(value), &[]).expect_err("must fail to parse");
    assert!(
        matches!(&e, ParseError::Expected { .. }),
        "expected the `Expected` variant, got {e:?}"
    );
    let at = e.location();
    assert_eq!((at.line, at.col), (line, col), "position of {e:?}");
    let got = e.found().unwrap_or("");
    assert!(
        got.starts_with(found),
        "offending token {got:?} should start with {found:?}"
    );
    let labels = e.expected().unwrap_or_default();
    assert_eq!(
        labels.iter().map(String::as_str).collect::<Vec<_>>(),
        expected
    );
}

/// The stored `Color` attribute of the accepted theory with `color=<value>`.
fn accepted_code(value: &str) -> String {
    let thy = parse_theory(&color_theory(value), &[]).expect("theory should parse");
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("one rule");
    match &rule.attributes[..] {
        [RuleAttr {
            kind: RuleAttrKind::Color(c),
            ..
        }] => c.clone(),
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

/// Three digits lex fine but fail `hexToRGB`: the rejection sits after the
/// code, at the `]`.
#[test]
fn three_digit_code_fails_hex_to_rgb() {
    assert_bad_rgb("f0f", "f0f", 3, 18);
}

/// Seven digits likewise.
#[test]
fn seven_digit_code_fails_hex_to_rgb() {
    assert_bad_rgb("ff00ff0", "ff00ff0", 3, 22);
}

/// Whitespace between the code and the next token moves the rejection to the
/// post-whitespace position (`lexeme`'s trailing whiteSpace consumed input).
#[test]
fn whitespace_after_short_code_moves_the_position() {
    assert_bad_rgb("f0f ", "f0f", 3, 19);
}

/// A quoted short code is rejected at the token after the closing `'`.
#[test]
fn quoted_short_code_is_rejected_after_the_quote() {
    assert_bad_rgb("'ff00'", "ff00", 3, 21);
}

/// No code at all: `many1 hexDigit` fails at its first char, and the
/// alternation's other leading tokens (`'`, `#`) merge their labels in.
#[test]
fn empty_value_reports_the_alternation_labels() {
    assert_lex_expected("", 3, 15, "]", &["\"'\"", "\"#\"", "hexadecimal digit"]);
}

/// A non-hex first char reports the same label set at that char.
#[test]
fn non_hex_value_reports_the_alternation_labels() {
    assert_lex_expected(
        "gg0011",
        3,
        15,
        "g",
        &["\"'\"", "\"#\"", "hexadecimal digit"],
    );
}

/// After a bare `#` the quote/hash alternatives are spent — only the digit
/// label remains.
#[test]
fn hash_without_digits_expects_a_digit() {
    assert_lex_expected("#", 3, 16, "]", &["hexadecimal digit"]);
}

/// Inside quotes the `'` alternative is spent: `''` fails at the closing
/// quote expecting `#` or a digit.
#[test]
fn empty_quotes_expect_hash_or_digit() {
    assert_lex_expected("''", 3, 16, "'", &["\"#\"", "hexadecimal digit"]);
}

/// A quoted code with a bad tail fails at the closing-quote `symbol`, with
/// `many1 hexDigit`'s pending label ahead of it (parsec's merge keeps the
/// earlier-accumulated message first).
#[test]
fn quoted_bad_tail_expects_digit_or_quote() {
    assert_lex_expected("'ff00zz'", 3, 20, "z", &["hexadecimal digit", "\"'\""]);
}

/// An unquoted bad tail: the digit run stops at `z`, the code is short, and
/// the `hexToRGB` rejection lands at that char.
#[test]
fn unquoted_bad_tail_fails_hex_to_rgb_at_the_bad_char() {
    assert_bad_rgb("ff00zz", "ff00", 3, 19);
}
