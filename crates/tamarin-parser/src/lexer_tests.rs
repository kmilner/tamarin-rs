// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

#[test]
fn skip_whitespace_and_comments() {
    let mut l = Lexer::new("  // a line\n /* block */ x");
    l.skip_ws();
    assert_eq!(l.peek(), Some('x'));
}

#[test]
fn nested_block_comment() {
    let mut l = Lexer::new("/* outer /* inner */ still */ x");
    l.skip_ws();
    assert_eq!(l.peek(), Some('x'));
}

#[test]
fn identifier_then_symbol() {
    let mut l = Lexer::new("foo  bar123");
    assert_eq!(l.identifier().as_deref(), Some("foo"));
    assert_eq!(l.identifier().as_deref(), Some("bar123"));
}

#[test]
fn symbol_word_boundary() {
    // `theory` should not match `theoryX`
    let mut l = Lexer::new("theoryX");
    assert!(!l.symbol("theory"));
    assert_eq!(l.identifier().as_deref(), Some("theoryX"));
}

#[test]
fn natural_subscript_digits() {
    let mut l = Lexer::new("\u{2081}\u{2082}\u{2083}");
    assert_eq!(l.natural_subscript(), Some(123));
}

#[test]
fn double_quoted_with_escape() {
    // The leading whitespace is a lexeme boundary.  `string_literal` skips
    // that whitespace before it looks for the opening quote.
    let mut l = Lexer::new(r#" "abc \"x\" def" "#);
    assert_eq!(l.string_literal().as_deref(), Some(r#"abc "x" def"#));

    // The literal fails and the lexer backtracks when the input ends
    // before the closing quote.  The lexer must not read `"abc` as the
    // string `abc`.
    let mut l = Lexer::new("\"abc");
    assert_eq!(l.string_literal(), None);
    assert_eq!(l.pos(), Pos::ZERO, "cursor moved on failure");
}

#[test]
fn single_quoted_basic() {
    // The leading whitespace is a lexeme boundary.  `single_quoted` skips
    // that whitespace before it looks for the opening quote.
    let mut l = Lexer::new(" 'foo'  ");
    assert_eq!(l.single_quoted().as_deref(), Some("foo"));

    // `singleQuotedString = singleQuoted $ many1 (noneOf "'\n")`
    // (Token.hs:452-453).  `many1` needs one body character, so `''`
    // fails.  A newline or the end of the input before the closing quote
    // leaves the literal unclosed.  Every failure backtracks.  Parsec
    // wraps the lexeme in `try`, so the lexeme must leave the cursor for
    // the enclosing alternative.
    for src in ["''", "'unterminated", "'no\nclose'"] {
        let mut l = Lexer::new(src);
        assert_eq!(l.single_quoted(), None, "must reject {src:?}");
        assert_eq!(l.pos(), Pos::ZERO, "cursor moved on failure: {src:?}");
    }
}

#[test]
fn formal_comment_basic() {
    let mut l = Lexer::new(" text{* hello *} ");
    let (h, b) = l.formal_comment().unwrap();
    assert_eq!(h, "text");
    assert_eq!(b, " hello ");
}

// --- string_literal: full Parsec/Haskell escape decoding ---

#[test]
fn string_literal_decodes_char_escapes() {
    // HS `T.stringLiteral` decodes `\n`->LF, `\t`->TAB, `\\`->`\`, `\"`->`"`.
    let mut l = Lexer::new("\"a\\nb\\tc\\\\d\\\"e\"");
    assert_eq!(l.string_literal().as_deref(), Some("a\nb\tc\\d\"e"));
}

#[test]
fn string_literal_decodes_numeric_escapes() {
    // \65 (dec) = 'A', \o101 (oct) = 'A', \x41 (hex) = 'A'.
    let mut l = Lexer::new("\"\\65 \\o101 \\x41\"");
    assert_eq!(l.string_literal().as_deref(), Some("A A A"));
}

#[test]
fn string_literal_ascii_name_and_control() {
    // \BEL = 0x07, \^A = 0x01, \NUL = 0x00.
    let mut l = Lexer::new("\"\\BEL\\^A\\NUL\"");
    assert_eq!(l.string_literal().as_deref(), Some("\u{07}\u{01}\u{00}"));
}

#[test]
fn string_literal_empty_and_gap_escapes() {
    // `\&` empty escape joins `A`+`B`; `\   \` gap is dropped.
    let mut l = Lexer::new("\"A\\&B\\   \\C\"");
    assert_eq!(l.string_literal().as_deref(), Some("ABC"));
}

#[test]
fn string_literal_rejects_bad_escape() {
    // `\q` is not a valid escape; HS fails the whole literal.
    let mut l = Lexer::new("\"a\\qb\"");
    assert_eq!(l.string_literal(), None);
}

// --- export_body: strict grammar ---

#[test]
fn export_body_accepts_only_backslash_and_quote_escapes() {
    // HS export `bodyChar`: `\\`->`\`, `\"`->`"`.
    let mut l = Lexer::new("\"a\\\\b\\\"c\"");
    assert_eq!(l.export_body().as_deref(), Some("a\\b\"c"));
}

#[test]
fn export_body_preserves_leading_whitespace_and_comments() {
    let mut l = Lexer::new("\"  // body text\nnext\"  tail");
    assert_eq!(l.export_body().as_deref(), Some("  // body text\nnext"));
    assert_eq!(l.rest(), "tail");
}

#[test]
fn export_body_rejects_newline_escape() {
    // HS export `bodyChar` FAILS on any `\x` other than `\\`/`\"` (e.g. `\n`).
    // Confirmed against tamarin-prover v1.13.0:
    //   `export foo: "a\nb"` => "unexpected n, expecting \"\\\\\" or \"\\\"\"".
    let mut l = Lexer::new("\"a\\nb\"");
    assert_eq!(l.export_body(), None);
    assert_eq!(l.pos(), Pos::ZERO, "cursor moved on failure");

    // `many bodyChar` never finds the closing `"` when the input ends.
    // An escaped final quote also does not close the body.
    for src in ["\"abc", "\"abc\\\""] {
        let mut l = Lexer::new(src);
        assert_eq!(l.export_body(), None, "must reject {src:?}");
        assert_eq!(l.pos(), Pos::ZERO, "cursor moved on failure: {src:?}");
    }
}

// --- formal_comment: every way the body can fail after `{*` ---

#[test]
fn formal_comment_rejects_every_failing_body() {
    // `many bodyChar <* string "*}"` (Token.hs:379) uses `bodyChar`
    // (Token.hs:382-387).  After the lexer reads the opening `{*`, the
    // body can fail in exactly three ways.  Upstream rejects each of the
    // three inputs as well.  The messages below come from the pinned
    // oracle on `theory T\nbegin\n\nnote{* ... \n\nend\n`:
    //
    //   `note{* a*b *}`       `'*' -> mzero` stops `many bodyChar`.  The
    //                         required `string "*}"` then fails at the
    //                         `*`:
    //                         (line 4, column 9)
    //                         unexpected "b" / expecting "*}"
    //   `note{* a\qb *}`      the `'\\'` branch accepts only `\` or `*`:
    //                         (line 4, column 10)
    //                         unexpected "q" / expecting "\\" or "*"
    //   `note{* unterminated` `anyChar` fails at the end of the input, so
    //                         `string "*}"` fails too:
    //                         (line 5, column 1)
    //                         unexpected end of input / expecting "*}"
    //
    // A probe of this port, not the oracle, gives the `Pos::ZERO` half.
    // HS wraps only `many1 letter <* string "{*"` in `try`
    // (Token.hs:378).  A body failure is therefore a parsec failure that
    // has consumed input.  The enclosing item alternation cannot backtrack
    // past such a failure.  For that reason every oracle frame above
    // points into the body.  This lexer rewinds to the start of the header
    // instead.  `Parser::theory_item` then falls through to its keyword
    // alternatives and reports at the item position.  All three inputs
    // give `unexpected "{"` / `expecting letter or "{*"` (probed at this
    // tip).  The assertions below record that rewind as the port's current
    // behaviour.  Work that closes the divergence must update them
    // deliberately.
    for src in ["note{* a*b *}", r"note{* a\qb *}", "note{* unterminated"] {
        let mut l = Lexer::new(src);
        assert_eq!(l.formal_comment(), None, "must reject {src:?}");
        assert_eq!(l.pos(), Pos::ZERO, "cursor moved on failure: {src:?}");
    }

    // The case the lexer accepts.  `\*` and `\\` are the two escapes that
    // `bodyChar` takes.  The body keeps the escaped character and drops
    // the backslash.  The oracle loads that theory and prints the item
    // again as `note{* a*b\c *}`.  `prettyFormalComment` puts the stored
    // body between `{*` and `*}` without any change.
    let mut ok = Lexer::new(r"note{* a\*b\\c *}");
    assert_eq!(
        ok.formal_comment(),
        Some(("note".to_string(), r" a*b\c ".to_string()))
    );
}

// --- single_quoted: strips leading whitespace (lexeme open quote) ---

#[test]
fn single_quoted_strips_leading_ws_keeps_trailing() {
    // HS `singleQuoted` opens with `symbol "'"` (lexeme), dropping leading ws;
    // the body `many1 (noneOf "'\n")` keeps trailing ws.
    let mut a = Lexer::new("' n'");
    assert_eq!(a.single_quoted().as_deref(), Some("n"));
    let mut b = Lexer::new("'n '");
    assert_eq!(b.single_quoted().as_deref(), Some("n "));
}

// --- identifier: rejects reserved names ---

#[test]
fn identifier_rejects_reserved_names() {
    for kw in ["in", "let", "rule", "diff"] {
        let mut l = Lexer::new(kw);
        assert_eq!(
            l.identifier(),
            None,
            "reserved name `{kw}` must not be an identifier"
        );
    }
    // Non-reserved lookalikes still parse.
    let mut l = Lexer::new("diffuse");
    assert_eq!(l.identifier().as_deref(), Some("diffuse"));
    let mut l2 = Lexer::new("rules");
    assert_eq!(l2.identifier().as_deref(), Some("rules"));
}
