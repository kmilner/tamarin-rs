// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Lexer for `.spthy` files.
//!
//! The lexer is a streaming character cursor that exposes higher-level
//! "skip whitespace, then peek/consume" operations rather than a separate
//! token stream. This matches Parsec's style and is convenient for
//! context-sensitive lexing (e.g. natural-number subscripts, formal
//! comments `name{* ... *}`, multi-character symbol choices like `++`
//! vs `+`).

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
    unterminated_comment: Option<Pos>,
}

pub(crate) struct QuotedError {
    pub position: Pos,
    pub unterminated: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            src,
            pos: Pos::ZERO,
            unterminated_comment: None,
        }
    }

    /// Whitespace parsing cannot return an error directly. Publish a consumed
    /// unterminated comment at the enclosing parser boundary.
    pub(crate) fn finish<T>(
        &self,
        result: Result<T, crate::parser::ParseError>,
    ) -> Result<T, crate::parser::ParseError> {
        if let (Some(opening), Err(error)) = (self.unterminated_comment, &result)
            // An attached source belongs to an included file; its offsets
            // cannot be ordered against this lexer's comment opener.
            && (error.source_text().is_some() || error.pos.offset < opening.offset)
        {
            return result;
        }
        match self.unterminated_comment {
            Some(opening) => Err(
                crate::parser::ParseError::at(self.pos, Vec::new()).with_kind(
                    crate::parse_error::ParseErrorKind::UnclosedBlockComment {
                        opening_span: opening.offset..opening.offset + 2,
                    },
                ),
            ),
            None => result,
        }
    }

    pub fn pos(&self) -> Pos {
        self.pos
    }
    pub fn set_pos(&mut self, p: Pos) {
        if p.offset < self.pos.offset {
            self.unterminated_comment = None;
        }
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
    ///
    /// Columns follow parsec's `updatePosChar` (Text/Parsec/Pos.hs): `\n`
    /// starts a new line at column 1, a tab advances to the next 8-column
    /// tab stop (`col + 8 - ((col-1) mod 8)`), and every other character
    /// advances by one.  The tab rule is load-bearing for byte parity: the
    /// `SourcePos` in a parse-error frame is the one parsec computed, so a
    /// tab-indented line reports the expanded column (e.g.
    /// `examples/csf18-alethea/alethea_selectionphase_anonymity.spthy`
    /// line 104 is two tabs deep and its error is at column 66, not 52).
    pub fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        let len = c.len_utf8();
        self.pos.offset += len;
        crate::parse_error::advance_line_column(&mut self.pos.line, &mut self.pos.col, c);
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
                        let opening = self.pos;
                        self.bump();
                        self.bump();
                        let mut depth = 1usize;
                        while depth > 0 {
                            match self.peek() {
                                None => {
                                    self.unterminated_comment = Some(opening);
                                    return;
                                }
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
        let save = self.clone();
        if self.symbol(s) {
            true
        } else {
            *self = save;
            false
        }
    }

    /// Peek for a symbol (with word-boundary check) without consuming.
    pub fn peek_symbol(&mut self, s: &str) -> bool {
        let save = self.clone();
        let r = self.try_symbol(s);
        *self = save;
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
    /// keyword/symbol (HS `diffOp = symbol "diff" *> parens ...`,
    /// Parser/Term.hs:123-125).
    pub fn identifier(&mut self) -> Option<String> {
        self.identifier_spanned().map(|(identifier, _)| identifier)
    }

    pub(crate) fn identifier_spanned(&mut self) -> Option<(String, Pos)> {
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
        Some((s, save))
    }

    /// Peek an identifier without consuming.
    pub fn peek_identifier(&mut self) -> Option<String> {
        let save = self.clone();
        let id = self.identifier();
        *self = save;
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
        self.quoted(Self::string_escape)
    }

    /// Parse a string literal and also return its exact half-open source range,
    /// including the quotes but excluding trailing whitespace.
    pub(crate) fn string_literal_spanned(
        &mut self,
    ) -> Result<(String, std::ops::Range<usize>), QuotedError> {
        self.quoted_spanned(Self::string_escape)
    }

    /// A double-quoted run: every char up to the closing `"` is taken
    /// verbatim except `\`, which is consumed and the rest of the escape
    /// handed to `escape`.  `escape` returns `Some(Some(c))` for a produced
    /// char, `Some(None)` for an escape that produces nothing, and `None` to
    /// fail the whole literal. A failure — an unterminated run included —
    /// restores the position, so the caller can offer another alternative.
    /// Trailing whitespace after the closing quote is always consumed.
    fn quoted<F>(&mut self, mut escape: F) -> Option<String>
    where
        F: FnMut(&mut Self) -> Option<Option<char>>,
    {
        self.quoted_spanned(&mut escape)
            .ok()
            .map(|(value, _)| value)
    }

    fn quoted_spanned<F>(
        &mut self,
        mut escape: F,
    ) -> Result<(String, std::ops::Range<usize>), QuotedError>
    where
        F: FnMut(&mut Self) -> Option<Option<char>>,
    {
        self.skip_ws();
        let save = self.pos;
        if !self.eat('"') {
            self.pos = save;
            return Err(QuotedError {
                position: save,
                unterminated: false,
            });
        }
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    let position = self.pos;
                    self.pos = save;
                    return Err(QuotedError {
                        position,
                        unterminated: true,
                    });
                }
                Some('"') => {
                    self.bump();
                    let end = self.pos.offset;
                    self.skip_ws();
                    return Ok((s, save.offset..end));
                }
                Some('\\') => {
                    self.bump();
                    match escape(self) {
                        Some(Some(c)) => s.push(c),
                        Some(None) => {}
                        None => {
                            let position = self.pos;
                            self.pos = save;
                            return Err(QuotedError {
                                position,
                                unterminated: false,
                            });
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
    /// `export` parser (Parser/Signature.hs:297-302): each char is taken verbatim except
    /// `\`, which must be followed by `\` or `"` (the second char is returned and
    /// the backslash dropped); a bare `"` terminates the body and any other `\x`
    /// fails the whole parse. Used for `export <tag>: "..."` blocks.
    pub fn export_body(&mut self) -> Option<String> {
        self.quoted(|lexer| match lexer.peek() {
            Some(c @ ('\\' | '"')) => {
                lexer.bump();
                Some(Some(c))
            }
            _ => None,
        })
    }

    /// Single-quoted string literal — not allowing single-quote or newline inside.
    pub fn single_quoted(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.clone();
        match self.single_quoted_checked() {
            Ok(text) => Some(text),
            Err(_) => {
                *self = save;
                None
            }
        }
    }

    /// Preserve the real failure position for callers that report diagnostics.
    pub(crate) fn single_quoted_checked(&mut self) -> Result<String, Pos> {
        self.skip_ws();
        if !self.eat('\'') {
            return Err(self.pos);
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
            return Err(self.pos);
        }
        if !self.eat('\'') {
            return Err(self.pos);
        }
        self.skip_ws();
        Ok(s)
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

    /// External identifier: `x-<ident>`.
    pub fn ext_identifier(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat_str("x-") {
            self.pos = save;
            return None;
        }
        match self.identifier() {
            Some(id) => Some(format!("x-{}", id)),
            None => {
                self.pos = save;
                None
            }
        }
    }
}

#[inline]
pub(crate) fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Reserved names that `T.identifier spthy` rejects (Token.hs:214-230, see line 225). A word equal
/// to one of these is not a valid identifier.
#[inline]
pub(crate) fn is_reserved_name(s: &str) -> bool {
    matches!(s, "in" | "let" | "rule" | "diff")
}

#[cfg(test)]
#[path = "lexer_tests.rs"]
mod tests;
