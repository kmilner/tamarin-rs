// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for the `color=`/`colour=` rule-attribute value.
//!
//! HS lexes the value with `hexColor` (Token.hs:403-406, `lexeme (singleQuoted
//! hexCode <|> hexCode)`, `hexCode = optional (symbol "#") *> many1 hexDigit`)
//! and validates it with `hexToRGB` (Data/Color.hs:149-155), which only
//! matches a SIX-character code; `parseColor` (Parser/Rule.hs:81-85) turns a
//! `Nothing` into `fail ("Color code " ++ show hc ++ " could not be parsed to
//! RGB")`.  Every expected string below is the stderr the pinned Haskell
//! oracle (Git revision ef3f0468) prints for the same theory, minus the three
//! `maude tool:` banner lines; every accepted theory loads with exit 0 there
//! and renders the attribute as lowercase `color=#<code>`.

use tamarin_parser::ast::{RuleAttr, TheoryItem};
use tamarin_parser::parse_theory;

fn color_theory(value: &str) -> String {
    format!("theory T begin\n\nrule R1[color={value}]: [ ] --> [ ]\n\nend\n")
}

/// The parse error for the theory with `color=<value>`, rendered as HS's
/// `show err` with `hex.spthy` as the `SourcePos` name.
fn err(value: &str) -> String {
    parse_theory(&color_theory(value), &[])
        .unwrap_err()
        .with_source("hex.spthy")
        .to_string()
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

/// `ruleAttribute` offers the British spelling FIRST (Parser/Rule.hs:72-73),
/// and it stores the same attribute — the oracle loads
/// `rule R1[colour=ff00ff]` at exit 0 and renders it as `color=#ff00ff`, the
/// spelling the corpus uses (examples/eurosp19-eccDAA/
/// ISOIEC_20008_2013_2_ECC_DAA.fixed.spthy).
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

/// Three digits lex fine but fail `hexToRGB`: the `fail` sits after the code
/// (at `]`), merging `many1 hexDigit`'s pending label.
#[test]
fn three_digit_code_fails_hex_to_rgb() {
    assert_eq!(
        err("f0f"),
        "\"hex.spthy\" (line 3, column 18):\n\
         unexpected \"]\"\n\
         expecting hexadecimal digit\n\
         Color code \"f0f\" could not be parsed to RGB"
    );
}

/// Seven digits likewise.
#[test]
fn seven_digit_code_fails_hex_to_rgb() {
    assert_eq!(
        err("ff00ff0"),
        "\"hex.spthy\" (line 3, column 22):\n\
         unexpected \"]\"\n\
         expecting hexadecimal digit\n\
         Color code \"ff00ff0\" could not be parsed to RGB"
    );
}

/// Whitespace between the code and the next token discards the pending
/// `hexadecimal digit` label (`lexeme`'s trailing whiteSpace consumed input).
#[test]
fn whitespace_after_short_code_drops_the_digit_label() {
    assert_eq!(
        err("f0f "),
        "\"hex.spthy\" (line 3, column 19):\n\
         unexpected \"]\"\n\
         Color code \"f0f\" could not be parsed to RGB"
    );
}

/// A quoted short code has no pending label either — the closing `'` consumed
/// input after the digit run.
#[test]
fn quoted_short_code_has_no_digit_label() {
    assert_eq!(
        err("'ff00'"),
        "\"hex.spthy\" (line 3, column 21):\n\
         unexpected \"]\"\n\
         Color code \"ff00\" could not be parsed to RGB"
    );
}

/// No code at all: `many1 hexDigit` fails at its first char, and the
/// alternation's other leading tokens (`'`, `#`) merge their labels in.
#[test]
fn empty_value_reports_the_alternation_labels() {
    assert_eq!(
        err(""),
        "\"hex.spthy\" (line 3, column 15):\n\
         unexpected \"]\"\n\
         expecting \"'\", \"#\" or hexadecimal digit"
    );
}

/// A non-hex first char reports the same label set at that char.
#[test]
fn non_hex_value_reports_the_alternation_labels() {
    assert_eq!(
        err("gg0011"),
        "\"hex.spthy\" (line 3, column 15):\n\
         unexpected \"g\"\n\
         expecting \"'\", \"#\" or hexadecimal digit"
    );
}

/// After a bare `#` the quote/hash alternatives are spent — only the digit
/// label remains.
#[test]
fn hash_without_digits_expects_a_digit() {
    assert_eq!(
        err("#"),
        "\"hex.spthy\" (line 3, column 16):\n\
         unexpected \"]\"\n\
         expecting hexadecimal digit"
    );
}

/// Inside quotes the `'` alternative is spent: `''` fails at the closing
/// quote expecting `#` or a digit.
#[test]
fn empty_quotes_expect_hash_or_digit() {
    assert_eq!(
        err("''"),
        "\"hex.spthy\" (line 3, column 16):\n\
         unexpected \"'\"\n\
         expecting \"#\" or hexadecimal digit"
    );
}

/// Inside quotes AFTER a `#` both prefix alternatives are spent — only the
/// digit label remains, at the closing quote.
#[test]
fn quoted_hash_without_digits_expects_a_digit() {
    assert_eq!(
        err("'#'"),
        "\"hex.spthy\" (line 3, column 17):\n\
         unexpected \"'\"\n\
         expecting hexadecimal digit"
    );
}

/// A quoted code with a bad tail fails at the closing-quote `symbol`, with
/// `many1 hexDigit`'s pending label merged in FIRST (parsec's merge keeps the
/// earlier-accumulated message ahead).
#[test]
fn quoted_bad_tail_expects_digit_or_quote() {
    assert_eq!(
        err("'ff00zz'"),
        "\"hex.spthy\" (line 3, column 20):\n\
         unexpected \"z\"\n\
         expecting hexadecimal digit or \"'\""
    );
}

/// An unquoted bad tail: the digit run stops at `z`, the code is short, and
/// the `fail` merges the pending digit label at that char.
#[test]
fn unquoted_bad_tail_fails_hex_to_rgb_at_the_bad_char() {
    assert_eq!(
        err("ff00zz"),
        "\"hex.spthy\" (line 3, column 19):\n\
         unexpected \"z\"\n\
         expecting hexadecimal digit\n\
         Color code \"ff00\" could not be parsed to RGB"
    );
}
