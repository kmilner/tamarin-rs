// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

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
fn whitespace_fast_path_preserves_unicode_and_positions() {
    for ch in (0..=255).filter_map(char::from_u32).chain([
        '\u{1680}', '\u{2000}', '\u{2003}', '\u{2028}', '\u{2029}', '\u{202f}', '\u{205f}',
        '\u{3000}', '\u{200b}', 'λ',
    ]) {
        let source = format!("{ch}x");
        let mut lexer = Lexer::new(&source);
        lexer.skip_ws();
        let expected = if ch.is_whitespace() {
            let mut cursor = Lexer::new(&source);
            cursor.bump();
            cursor.pos()
        } else {
            Pos::ZERO
        };
        assert_eq!(lexer.pos(), expected, "{ch:?}");
        lexer.skip_ws();
        assert_eq!(lexer.pos(), expected, "repeated probe for {ch:?}");
    }
    let mut lexer = Lexer::new(" \t/* λ /* inner */ */\n\u{2003}x");
    lexer.skip_ws();
    assert_eq!(
        (lexer.peek(), lexer.pos().line, lexer.pos().col),
        (Some('x'), 2, 2)
    );
}

#[test]
fn identifier_spans_preserve_unicode_and_reserved_word_backtracking() {
    let source = " \tλong_identifier_123é /* trailing */ next";
    let mut lexer = Lexer::new(source);
    let (name, pos) = lexer.identifier_spanned().unwrap();
    assert_eq!(name, "λong_identifier_123é");
    assert_eq!(
        pos,
        Pos {
            offset: 2,
            line: 1,
            col: 9
        }
    );
    assert_eq!(&source[pos.offset..pos.offset + name.len()], name);
    assert_eq!(lexer.identifier().as_deref(), Some("next"));

    let mut lexer = Lexer::new("  rule /* comment */");
    assert_eq!(lexer.identifier(), None);
    assert_eq!(
        lexer.pos(),
        Pos {
            offset: 2,
            line: 1,
            col: 3
        }
    );
    assert!(lexer.symbol("rule"));
    assert!(lexer.is_eof());
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

#[derive(Debug, Clone, Copy)]
enum Lexeme {
    /// HS `T.stringLiteral` (Token.hs): Haskell escapes, decoded.
    StringLiteral,
    /// HS export `bodyChar`: only `\\` and `\"` escape.
    ExportBody,
    /// HS `singleQuoted $ many1 (noneOf "'\n")`: the opening quote is a
    /// `symbol`, so whitespace after it goes; trailing whitespace stays.
    SingleQuoted,
    /// HS `formalComment`, read as `header|body`: `\*` and `\\` escape, and a
    /// failure rewinds to the header (the oracle's error points into the
    /// body instead, which the parse table's outcome rows cannot see).
    FormalComment,
}

enum LiteralExpect {
    /// The decoded value and the input left after it.
    Decodes(&'static str, &'static str),
    /// A failure at this offset, where the cursor also stops.
    FailsAt(usize),
}

/// Each literal lexeme's decoding and where it fails (Token.hs).
#[test]
fn literals_decode_and_fail_as_parsec_does() {
    use Lexeme::*;
    use LiteralExpect::{Decodes, FailsAt};
    let rows: &[(Lexeme, &str, LiteralExpect)] = &[
        // Leading whitespace is a lexeme boundary.
        (
            StringLiteral,
            r#" "abc \"x\" def" "#,
            Decodes(r#"abc "x" def"#, ""),
        ),
        (StringLiteral, "\"abc", FailsAt(4)),
        (
            StringLiteral,
            "\"a\\nb\\tc\\\\d\\\"e\"",
            Decodes("a\nb\tc\\d\"e", ""),
        ),
        (StringLiteral, "\"\\65 \\o101 \\x41\"", Decodes("A A A", "")),
        (
            StringLiteral,
            "\"\\BEL\\^A\\NUL\"",
            Decodes("\u{07}\u{01}\u{00}", ""),
        ),
        // `\&` is empty and a `\   \` gap is dropped.
        (StringLiteral, "\"A\\&B\\   \\C\"", Decodes("ABC", "")),
        (StringLiteral, "\"a\\qb\"", FailsAt(3)),
        (ExportBody, "\"a\\\\b\\\"c\"", Decodes("a\\b\"c", "")),
        (
            ExportBody,
            "\"  // body text\nnext\"  tail",
            Decodes("  // body text\nnext", "tail"),
        ),
        (ExportBody, "\"a\\nb\"", FailsAt(3)),
        (ExportBody, "\"abc", FailsAt(4)),
        // An escaped final quote does not close the body.
        (ExportBody, "\"abc\\\"", FailsAt(6)),
        (SingleQuoted, " 'foo'  ", Decodes("foo", "")),
        (SingleQuoted, "' n'", Decodes("n", "")),
        (SingleQuoted, "'n '", Decodes("n ", "")),
        // `many1` needs a body character; a newline or the end of the input
        // leaves the literal unclosed.
        (SingleQuoted, "''", FailsAt(1)),
        (SingleQuoted, "'unterminated", FailsAt(13)),
        (SingleQuoted, "'no\nclose'", FailsAt(3)),
        (
            FormalComment,
            " text{* hello *} ",
            Decodes("text| hello ", ""),
        ),
        (
            FormalComment,
            r"note{* a\*b\\c *}",
            Decodes(r"note| a*b\c ", ""),
        ),
        (FormalComment, "note{* a*b *}", FailsAt(0)),
        (FormalComment, r"note{* a\qb *}", FailsAt(0)),
        (FormalComment, "note{* unterminated", FailsAt(0)),
    ];
    for (literal, src, expect) in rows {
        let mut l = Lexer::new(src);
        let got: Result<String, Pos> = match literal {
            StringLiteral => l
                .string_literal_spanned()
                .map(|(text, _)| text)
                .map_err(|e| e.position),
            ExportBody => l.export_body().map_err(|e| e.position),
            SingleQuoted => l.single_quoted(),
            FormalComment => l
                .formal_comment()
                .map(|(header, body)| format!("{header}|{body}"))
                .ok_or(Pos::ZERO),
        };
        match (expect, got) {
            (Decodes(value, rest), Ok(got)) => {
                assert_eq!(
                    (got.as_str(), l.rest()),
                    (*value, *rest),
                    "{literal:?} {src:?}"
                );
            }
            (FailsAt(at), Err(position)) => {
                assert_eq!(position, l.pos(), "{literal:?} {src:?}");
                assert_eq!(position.offset, *at, "{literal:?} {src:?}");
            }
            (_, got) => panic!("{literal:?} {src:?}: {got:?}"),
        }
    }
}

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
