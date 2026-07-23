// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Lexer for `.spthy` files.
//!
//! The lexer is a streaming character cursor that exposes higher-level
//! "skip whitespace, then peek/consume" operations rather than a separate
//! token stream. This matches Parsec's style and is convenient for
//! context-sensitive lexing (e.g. natural-number subscripts, formal
//! comments `name{* ... *}`, hex colour codes, multi-character symbol
//! choices like `++` vs `+`).

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    pub offset: usize,
    pub line: u32,
    pub col: u32,
}

impl Pos {
    pub const ZERO: Pos = Pos {
        offset: 0,
        line: 1,
        col: 1,
    };
}

#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    src: &'a str,
    pos: Pos,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            src,
            pos: Pos::ZERO,
        }
    }

    pub fn pos(&self) -> Pos {
        self.pos
    }
    pub fn set_pos(&mut self, p: Pos) {
        self.pos = p;
    }
    pub fn src(&self) -> &'a str {
        self.src
    }
    pub fn rest(&self) -> &'a str {
        &self.src[self.pos.offset..]
    }
    pub fn is_eof(&self) -> bool {
        self.pos.offset >= self.src.len()
    }

    pub fn line_col(&self) -> (u32, u32) {
        (self.pos.line, self.pos.col)
    }

    /// Peek the next char without advancing.
    pub fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    /// Peek the char immediately after the next one (the second remaining char).
    pub fn peek2(&self) -> Option<char> {
        let mut it = self.rest().chars();
        it.next();
        it.next()
    }

    /// Advance one char, updating line/col.
    pub fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        let len = c.len_utf8();
        self.pos.offset += len;
        if c == '\n' {
            self.pos.line += 1;
            self.pos.col = 1;
        } else {
            self.pos.col += 1;
        }
        Some(c)
    }

    /// If the next char matches `c`, consume and return true.
    pub fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Try to consume the literal string `s` at current position.
    pub fn eat_str(&mut self, s: &str) -> bool {
        if self.rest().starts_with(s) {
            for _ in s.chars() {
                self.bump();
            }
            true
        } else {
            false
        }
    }

    /// Consume a maximal run of ASCII-alphabetic characters and return it
    /// (empty when the next char is not ASCII-alphabetic). Does NOT skip
    /// leading whitespace — used to read `#directive` names and formal-comment
    /// headers, where the run starts exactly at the cursor.
    pub fn ascii_alpha_run(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphabetic() {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }
        s
    }

    // ---------- Whitespace and comments ----------

    /// Skip Whitespace, line comments `//...`, and nested block comments `/* ... */`.
    /// `#`-prefixed preprocessor directives are NOT skipped (they're tokens).
    pub fn skip_ws(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    self.bump();
                }
                Some('/') => {
                    if self.rest().starts_with("//") {
                        // line comment to EOL
                        while let Some(c) = self.peek() {
                            if c == '\n' {
                                break;
                            }
                            self.bump();
                        }
                    } else if self.rest().starts_with("/*") {
                        self.bump();
                        self.bump();
                        let mut depth = 1usize;
                        while depth > 0 {
                            match self.peek() {
                                None => return, // unterminated, stop
                                Some('/') if self.rest().starts_with("/*") => {
                                    self.bump();
                                    self.bump();
                                    depth += 1;
                                }
                                Some('*') if self.rest().starts_with("*/") => {
                                    self.bump();
                                    self.bump();
                                    depth -= 1;
                                }
                                _ => {
                                    self.bump();
                                }
                            }
                        }
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    // ---------- Symbol matchers ----------

    /// Try to consume a literal symbol after skipping whitespace.
    /// Symbol is matched verbatim, but if it ends with an alphanum we also
    /// require the next char to NOT be alphanum (word boundary).
    pub fn symbol(&mut self, s: &str) -> bool {
        self.skip_ws();
        if !self.rest().starts_with(s) {
            return false;
        }
        // Word-boundary check for keyword-like symbols.
        if s.chars().last().is_some_and(is_ident_char) {
            let after = &self.rest()[s.len()..];
            if after.chars().next().is_some_and(is_ident_char) {
                return false;
            }
        }
        for _ in s.chars() {
            self.bump();
        }
        self.skip_ws();
        true
    }

    /// Like [`symbol`], but does not consume on failure.
    pub fn try_symbol(&mut self, s: &str) -> bool {
        let save = self.pos;
        if self.symbol(s) {
            true
        } else {
            self.pos = save;
            false
        }
    }

    /// Peek for a symbol (with word-boundary check) without consuming.
    pub fn peek_symbol(&mut self, s: &str) -> bool {
        let save = self.pos;
        let r = self.try_symbol(s);
        self.pos = save;
        r
    }

    // ---------- Identifiers ----------

    /// Parse an identifier: alphanum start, alphanum or `_` continuation.
    /// Returns None if the next char isn't alphanumeric.
    ///
    /// Mirrors `identifier = T.identifier spthy` (Token.hs:393-394), which rejects
    /// the reserved names `["in","let","rule","diff"]` (Token.hs:214-230, see line 225): a word equal
    /// to one of those is not a valid identifier, so we backtrack and return None.
    /// The `diff` term operator does NOT go through this — it is matched as a
    /// keyword/symbol (HS `diffOp = symbol "diff" *> parens ...`, Term.hs:108-110).
    pub fn identifier(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        let mut s = String::new();
        match self.peek() {
            Some(c) if c.is_alphanumeric() => {
                s.push(c);
                self.bump();
            }
            _ => {
                self.pos = save;
                return None;
            }
        }
        while let Some(c) = self.peek() {
            if is_ident_char(c) {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }
        if is_reserved_name(&s) {
            self.pos = save;
            return None;
        }
        self.skip_ws();
        Some(s)
    }

    /// Peek an identifier without consuming.
    pub fn peek_identifier(&mut self) -> Option<String> {
        let save = self.pos;
        let id = self.identifier();
        self.pos = save;
        id
    }

    /// Parse a natural number literal (decimal only).
    ///
    /// Haskell `T.natural spthy` (Token.hs:340-341, see line 341) is Parsec's `natural`, which also
    /// accepts `0x`/`0o` hex/octal prefixes and returns an unbounded `Integer`.
    /// Every `natural` call site is a small decimal index (premise/conclusion
    /// numbers, function arity, reuse limit, `x.1` subscripts) that no real
    /// `.spthy` file writes in an alternate radix or larger than `u64`, so the
    /// decimal-only `u64` restriction is benign.
    pub fn natural(&mut self) -> Option<u64> {
        self.skip_ws();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }
        if s.is_empty() {
            None
        } else {
            let n = s.parse().ok();
            self.skip_ws();
            n
        }
    }

    /// Subscript-digit natural (Unicode subscripts ₀–₉).
    pub fn natural_subscript(&mut self) -> Option<u64> {
        self.skip_ws();
        let mut n: u64 = 0;
        let mut got = false;
        while let Some(c) = self.peek() {
            let d = match c {
                '\u{2080}' => 0,
                '\u{2081}' => 1,
                '\u{2082}' => 2,
                '\u{2083}' => 3,
                '\u{2084}' => 4,
                '\u{2085}' => 5,
                '\u{2086}' => 6,
                '\u{2087}' => 7,
                '\u{2088}' => 8,
                '\u{2089}' => 9,
                _ => break,
            };
            n = n * 10 + d;
            got = true;
            self.bump();
        }
        if got {
            self.skip_ws();
            Some(n)
        } else {
            None
        }
    }

    /// Double-quoted string literal, decoding Haskell/Parsec string escapes.
    ///
    /// Mirrors Haskell `stringLiteral = T.stringLiteral spthy` (Token.hs:366-367),
    /// i.e. Parsec's default Haskell-report string literal (`T.makeTokenParser`,
    /// Token.hs:214-230). It decodes:
    ///   * char escapes `\a \b \f \n \r \t \v \\ \" \'`,
    ///   * numeric escapes `\65` (decimal), `\o101` (octal), `\x41` (hex),
    ///   * control escapes `\^A`,
    ///   * ASCII-name escapes `\NUL`..`\DEL` (e.g. `\BEL`, `\SP`),
    ///   * the empty escape `\&` (produces nothing),
    ///   * gap escapes `\<whitespace+>\` (produces nothing).
    ///
    /// On an unrecognised escape the whole literal fails to parse (Parsec
    /// backtracks the surrounding `stringLiteral`).
    ///
    /// Note: export bodies use a *different*, stricter character grammar — see
    /// [`Lexer::export_body`].
    pub fn string_literal(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat('"') {
            self.pos = save;
            return None;
        }
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    self.pos = save;
                    return None;
                }
                Some('"') => {
                    self.bump();
                    self.skip_ws();
                    return Some(s);
                }
                Some('\\') => {
                    self.bump();
                    match self.string_escape() {
                        Some(Some(c)) => s.push(c),
                        Some(None) => {} // empty escape `\&` or gap `\  \`
                        None => {
                            self.pos = save;
                            return None;
                        }
                    }
                }
                Some(c) => {
                    s.push(c);
                    self.bump();
                }
            }
        }
    }

    /// Decode one Parsec string escape after the leading `\` has been consumed.
    /// Returns `Some(Some(c))` for a produced char, `Some(None)` for an escape
    /// that produces nothing (`\&` or a gap `\<ws+>\`), or `None` on a malformed
    /// escape (which fails the surrounding string literal).
    fn string_escape(&mut self) -> Option<Option<char>> {
        match self.peek() {
            // escapeEmpty
            Some('&') => {
                self.bump();
                Some(None)
            }
            // escapeGap: many1 space then `\`
            Some(c) if c.is_whitespace() => {
                while self.peek().is_some_and(|c| c.is_whitespace()) {
                    self.bump();
                }
                if self.eat('\\') {
                    Some(None)
                } else {
                    None
                }
            }
            // charEsc
            Some('a') => {
                self.bump();
                Some(Some('\u{07}'))
            }
            Some('b') => {
                self.bump();
                Some(Some('\u{08}'))
            }
            Some('f') => {
                self.bump();
                Some(Some('\u{0C}'))
            }
            Some('n') => {
                self.bump();
                Some(Some('\n'))
            }
            Some('r') => {
                self.bump();
                Some(Some('\r'))
            }
            Some('t') => {
                self.bump();
                Some(Some('\t'))
            }
            Some('v') => {
                self.bump();
                Some(Some('\u{0B}'))
            }
            Some('\\') => {
                self.bump();
                Some(Some('\\'))
            }
            Some('"') => {
                self.bump();
                Some(Some('"'))
            }
            Some('\'') => {
                self.bump();
                Some(Some('\''))
            }
            // charNum: decimal / octal (\o) / hex (\x)
            Some('o') => {
                self.bump();
                self.string_escape_radix(8)
            }
            Some('x') => {
                self.bump();
                self.string_escape_radix(16)
            }
            Some(d) if d.is_ascii_digit() => self.string_escape_radix(10),
            // charControl: \^A .. \^_ (and \^@)
            Some('^') => {
                self.bump();
                match self.peek() {
                    Some(c) if ('@'..='_').contains(&c) => {
                        self.bump();
                        Some(Some(char::from(c as u8 - b'@')))
                    }
                    _ => None,
                }
            }
            // charAscii: control names like NUL, SOH, ..., SP, DEL.
            Some(c) if c.is_ascii_uppercase() => self.string_escape_ascii_name(),
            _ => None,
        }
    }

    /// Parse a numeric character escape body in the given radix and return the
    /// resulting char, or `None` if no digits / out of Unicode range.
    fn string_escape_radix(&mut self, radix: u32) -> Option<Option<char>> {
        let mut acc: u32 = 0;
        let mut got = false;
        while let Some(c) = self.peek() {
            match c.to_digit(radix) {
                Some(d) => {
                    acc = acc.checked_mul(radix)?.checked_add(d)?;
                    got = true;
                    self.bump();
                }
                None => break,
            }
        }
        if !got {
            return None;
        }
        char::from_u32(acc).map(Some)
    }

    /// Parse an ASCII control-name escape (e.g. `NUL`, `BEL`, `SP`, `DEL`).
    /// Matches the longest name; returns `None` if the upcoming letters are not a
    /// known name (mirrors Parsec `charAscii`'s `try`-based ordered choice).
    fn string_escape_ascii_name(&mut self) -> Option<Option<char>> {
        // Names ordered longest-first so prefixes (e.g. `S` of `SOH`/`SO`) resolve
        // greedily, matching Parsec's `asciiMap` (sorted by descending length).
        const ASCII: &[(&str, u8)] = &[
            ("NUL", 0),
            ("SOH", 1),
            ("STX", 2),
            ("ETX", 3),
            ("EOT", 4),
            ("ENQ", 5),
            ("ACK", 6),
            ("BEL", 7),
            ("DLE", 16),
            ("DC1", 17),
            ("DC2", 18),
            ("DC3", 19),
            ("DC4", 20),
            ("NAK", 21),
            ("SYN", 22),
            ("ETB", 23),
            ("CAN", 24),
            ("SUB", 26),
            ("ESC", 27),
            ("DEL", 127),
            ("EM", 25),
            ("FS", 28),
            ("GS", 29),
            ("RS", 30),
            ("US", 31),
            ("SP", 32),
            ("BS", 8),
            ("HT", 9),
            ("LF", 10),
            ("VT", 11),
            ("FF", 12),
            ("CR", 13),
            ("SO", 14),
            ("SI", 15),
        ];
        for &(name, code) in ASCII {
            if self.rest().starts_with(name) {
                for _ in name.chars() {
                    self.bump();
                }
                return Some(Some(char::from(code)));
            }
        }
        None
    }

    /// Strict export-body character stream, mirroring Haskell `bodyChar` in the
    /// `export` parser (Signature.hs:282-287): each char is taken verbatim except
    /// `\`, which must be followed by `\` or `"` (the second char is returned and
    /// the backslash dropped); a bare `"` terminates the body and any other `\x`
    /// fails the whole parse. Used for `export <tag>: "..."` blocks.
    pub fn export_body(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat('"') {
            self.pos = save;
            return None;
        }
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    self.pos = save;
                    return None;
                }
                Some('"') => {
                    self.bump();
                    self.skip_ws();
                    return Some(s);
                }
                Some('\\') => {
                    self.bump();
                    match self.peek() {
                        Some(c @ '\\') | Some(c @ '"') => {
                            s.push(c);
                            self.bump();
                        }
                        // Any other `\x` makes `bodyChar` (wrapped in `try`)
                        // backtrack, so `many bodyChar` stops and the closing
                        // `"` is never found at this position — the export fails.
                        _ => {
                            self.pos = save;
                            return None;
                        }
                    }
                }
                Some(c) => {
                    s.push(c);
                    self.bump();
                }
            }
        }
    }

    /// Single-quoted string literal — not allowing single-quote or newline inside.
    pub fn single_quoted(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat('\'') {
            self.pos = save;
            return None;
        }
        // Haskell `singleQuoted = between (symbol "'") (symbol "'")` (Token.hs:296-297):
        // the opening `symbol "'"` is `lexeme (string "'")`, so it consumes whitespace
        // (and comments) AFTER the opening quote. The body `many1 (noneOf "'\n")`
        // (Token.hs:452-453, see line 453) keeps interior/trailing spaces, so only the leading run is
        // dropped here.
        self.skip_ws();
        let mut s = String::new();
        loop {
            match self.peek() {
                None | Some('\n') | Some('\'') => break,
                Some(c) => {
                    s.push(c);
                    self.bump();
                }
            }
        }
        // Haskell `singleQuotedString = singleQuoted $ many1 (noneOf "'\n")`
        // (Token.hs:452-453): `many1` requires at least one body char, so `''`
        // must fail.
        if s.is_empty() {
            self.pos = save;
            return None;
        }
        if !self.eat('\'') {
            self.pos = save;
            return None;
        }
        self.skip_ws();
        Some(s)
    }

    /// Formal comment: `<header>{* body *}` (header is one or more letters).
    pub fn formal_comment(&mut self) -> Option<(String, String)> {
        self.skip_ws();
        let save = self.pos;
        let header = self.ascii_alpha_run();
        if header.is_empty() {
            self.pos = save;
            return None;
        }
        if !self.eat_str("{*") {
            self.pos = save;
            return None;
        }
        let mut body = String::new();
        loop {
            match self.peek() {
                None => {
                    self.pos = save;
                    return None;
                }
                Some('*') if self.rest().starts_with("*}") => {
                    self.bump();
                    self.bump();
                    self.skip_ws();
                    return Some((header, body));
                }
                // Haskell `bodyChar` (Token.hs:382-387): `'*' -> mzero`. A lone `*`
                // that is not the start of the `*}` closer makes `bodyChar` fail, so
                // `many bodyChar` stops and the required `string "*}"` then fails at
                // the `*`, failing the whole formalComment.
                Some('*') => {
                    self.pos = save;
                    return None;
                }
                Some('\\') => {
                    self.bump();
                    match self.peek() {
                        Some(c @ '\\') | Some(c @ '*') => {
                            body.push(c);
                            self.bump();
                        }
                        // Haskell `bodyChar` (Token.hs:382-387): on `\` the inner
                        // `char '\\' <|> char '*'` only accepts `\` or `*`; any
                        // other `\x` makes `bodyChar` (wrapped in `try`) backtrack
                        // un-consuming the `\`, so `many bodyChar` stops and the
                        // required `string "*}"` then fails at the `\` — i.e. the
                        // whole formalComment fails.
                        _ => {
                            self.pos = save;
                            return None;
                        }
                    }
                }
                Some(c) => {
                    body.push(c);
                    self.bump();
                }
            }
        }
    }

    /// Hex colour code (optionally prefixed with `#`, optionally single-quoted).
    ///
    /// Unlike the Haskell `symbol`-based parser (Token.hs:404-406), this does not
    /// skip whitespace after the opening quote or after `#`, so `' #FF'` / `'# FF'`
    /// are rejected here though Haskell accepts them. Real colour attributes are
    /// always tight (e.g. `'#111111'`), so this whitespace divergence has no
    /// practical effect.
    pub fn hex_color(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        let quoted = self.eat('\'');
        let _ = self.eat('#');
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_hexdigit() {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }
        if quoted && !self.eat('\'') {
            self.pos = save;
            return None;
        }
        if s.is_empty() {
            self.pos = save;
            return None;
        }
        self.skip_ws();
        Some(s)
    }

    /// External identifier: `x-<ident>`.
    pub fn ext_identifier(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat_str("x-") {
            self.pos = save;
            return None;
        }
        let id = self.identifier()?;
        Some(format!("x-{}", id))
    }
}

#[inline]
pub fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Reserved names that `T.identifier spthy` rejects (Token.hs:214-230, see line 225). A word equal
/// to one of these is not a valid identifier.
#[inline]
pub fn is_reserved_name(s: &str) -> bool {
    matches!(s, "in" | "let" | "rule" | "diff")
}

#[cfg(test)]
mod tests {
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
        let mut l = Lexer::new(r#" "abc \"x\" def" "#);
        assert_eq!(l.string_literal().as_deref(), Some(r#"abc "x" def"#));
    }

    #[test]
    fn single_quoted_basic() {
        let mut l = Lexer::new(" 'foo'  ");
        assert_eq!(l.single_quoted().as_deref(), Some("foo"));
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
    fn export_body_rejects_newline_escape() {
        // HS export `bodyChar` FAILS on any `\x` other than `\\`/`\"` (e.g. `\n`).
        // Confirmed against tamarin-prover v1.13.0:
        //   `export foo: "a\nb"` => "unexpected n, expecting \"\\\\\" or \"\\\"\"".
        let mut l = Lexer::new("\"a\\nb\"");
        assert_eq!(l.export_body(), None);
    }

    // --- formal_comment: rejects a body-internal lone `*` ---

    #[test]
    fn formal_comment_rejects_internal_lone_star() {
        // HS `bodyChar` does `'*' -> mzero`; `text{* a*b *}` is a parse error.
        // Confirmed against v1.13.0: "unexpected b, expecting \"*}\"".
        let mut l = Lexer::new("text{* a*b *}");
        assert_eq!(l.formal_comment(), None);
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
}
