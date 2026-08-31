// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Recursive-descent parser for `.spthy` files.

// flag-name set import; membership dedup only;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Arc;

use tamarin_term::function_symbols::{
    bp_fun_sig, dh_fun_sig, nat_fun_sig, xor_fun_sig, Constructability, FunSig, FunSym, NdcState,
    NoEqSym, Privacy,
};
use tamarin_term::lterm::LSort;
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, hash_maude_sig,
    location_report_maude_sig, mset_maude_sig, nat_maude_sig, pair_dest_maude_sig,
    reveal_signature_maude_sig, signature_dest_maude_sig, signature_maude_sig,
    sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};

use crate::ast::*;
use crate::lexer::{is_ident_char, is_reserved_name, Lexer, Pos};
use crate::proof_tree::{parse_proof_tree, validate_diff_proof_tree};

// =============================================================================
// Errors
// =============================================================================

/// A single parsec-style error message.
///
/// Direct port of parsec's `data Message` (`Text.Parsec.Error`, the
/// `parsec-3.1.16.1` bundled with the GHC-9.6.7 that builds the HS oracle).
/// The four constructors and their ordering are load-bearing: parsec's
/// `instance Ord Message` compares *only* the constructor rank (`fromEnum`,
/// `SysUnExpect`=0 … `Message`=3), and `errorMessages = sort msgs` stable-sorts
/// by that rank before rendering, so the groups always appear in this order.
#[derive(Debug, Clone)]
pub enum Message {
    /// Library-generated "unexpected" (parsec `SysUnExpect`): the token found
    /// where the grammar could not continue.  Rendered `unexpected <tok>`, or
    /// `unexpected end of input` when the string is empty.
    SysUnExpect(String),
    /// User "unexpected" (parsec `UnExpect`, via the `unexpected` combinator).
    UnExpect(String),
    /// "expecting" label (parsec `Expect`, from `<?>` and the token parsers).
    Expect(String),
    /// Raw message (parsec `Message`, e.g. via `fail`).  Rendered verbatim.
    Message(String),
}

impl Message {
    /// parsec `fromEnum :: Message -> Int` (`Text.Parsec.Error`).
    fn rank(&self) -> u8 {
        match self {
            Message::SysUnExpect(_) => 0,
            Message::UnExpect(_) => 1,
            Message::Expect(_) => 2,
            Message::Message(_) => 3,
        }
    }
    /// parsec `messageString :: Message -> String`.
    fn string(&self) -> &str {
        match self {
            Message::SysUnExpect(s)
            | Message::UnExpect(s)
            | Message::Expect(s)
            | Message::Message(s) => s,
        }
    }
}

/// One of the GHC `error` calls the HS parser raises from inside a parser
/// action, e.g. `macro`'s two rejections (Theory/Text/Parser/Macro.hs:34-38).
///
/// `error` is not a parsec failure: the exception escapes the parser run
/// entirely, so it carries no source position and no `expecting`/`unexpected`
/// labels — nothing merges into it and nothing can recover from it.  GHC's
/// top-level handler prints `tamarin-prover: ` followed by the exception's
/// `displayException` (the message plus the `HasCallStack` frame) and exits 1.
#[derive(Debug, Clone)]
pub struct GhcError {
    /// The string the `error` call is applied to.
    pub message: String,
    /// The `error, called at <call_site>` location of the `HasCallStack` frame:
    /// `src/<path>:<line>:<column> in <package-id>:<module>`.
    pub call_site: String,
}

impl GhcError {
    /// GHC's `displayException` of the raised `ErrorCall`: the message, then
    /// the one-frame `HasCallStack` block.  Batch mode's stderr is this text
    /// prefixed by `tamarin-prover: `.
    pub fn display_exception(&self) -> String {
        format!(
            "{}\nCallStack (from HasCallStack):\n  error, called at {}",
            self.message, self.call_site
        )
    }
}

impl std::fmt::Display for GhcError {
    /// The message alone — the `HasCallStack` block belongs to the surface that
    /// reports the exception, see [`GhcError::display_exception`].
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// A parse error, modelled on parsec's `ParseError` (`Text.Parsec.Error`): a
/// source position plus a list of [`Message`]s.  Rendering (the [`Display`]
/// impl) is a verbatim port of parsec's `instance Show ParseError` +
/// `showErrorMessages` + `instance Show SourcePos` (`Text.Parsec.Pos`), so the
/// user-facing frame is byte-identical to HS's `show err`:
///
/// ```text
/// "path/file.spthy" (line 2, column 5):
/// unexpected " "
/// expecting letter or "{*"
/// ```
///
/// The line/col/offset are retained as public fields for callers that inspect
/// the position; `source` is the parsec `SourcePos` "name" (the file path in
/// the header), injected by each surface via [`ParseError::with_source`] —
/// mirroring parsec threading `parseString`'s `inFile` into the `SourcePos`.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub line: u32,
    pub col: u32,
    pub offset: usize,
    /// parsec `SourcePos` name (file path printed in the header).  Empty until
    /// a surface injects it, in which case the header omits the quoted name
    /// exactly as parsec's null-name `show SourcePos` branch does.
    pub source: String,
    /// Unsorted parsec-style messages; [`Display`] sorts + dedups them exactly
    /// as parsec's `errorMessages` + `showErrorMessages` do.
    pub messages: Vec<Message>,
    /// Set when the parse aborted through a GHC `error` raised inside a parser
    /// action rather than through a parsec failure (see [`GhcError`]).  The
    /// position then only records where the parser stood, `messages` is empty,
    /// and [`Display`] renders the raw message instead of a parsec frame.
    pub ghc_error: Option<GhcError>,
}

impl ParseError {
    /// A parsec failure carrying `messages` at `pos`.
    fn at(pos: Pos, messages: Vec<Message>) -> ParseError {
        ParseError {
            line: pos.line,
            col: pos.col,
            offset: pos.offset,
            source: String::new(),
            messages,
            ghc_error: None,
        }
    }

    /// Attach the source-file name parsec prints in the header.  Each surface
    /// injects the path it knows (batch: the CLI arg; server eager-load: the
    /// on-disk path; web upload: the uploaded filename) — the same value HS
    /// passes as `inFile` to `parseString`.
    pub fn with_source(mut self, name: impl Into<String>) -> Self {
        self.source = name.into();
        self
    }

    /// Port of parsec's `showErrorMessages` (`Text.Parsec.Error`) instantiated
    /// with the exact argument strings from `instance Show ParseError`:
    /// `showErrorMessages "or" "unknown parse error" "expecting" "unexpected"
    /// "end of input"`.  Produces the message body (each line already prefixed
    /// with `\n`, matching `concat $ map ("\n"++) …`).
    fn show_error_messages(&self) -> String {
        // errorMessages = sort msgs  (stable sort by constructor rank).
        let mut msgs: Vec<&Message> = self.messages.iter().collect();
        msgs.sort_by_key(|m| m.rank());
        if msgs.is_empty() {
            // parsec: `| null msgs = msgUnknown` (returned with NO leading '\n').
            return "unknown parse error".to_string();
        }
        // span by rank into (sysUnExpect, unExpect, expect, messages).
        let strings = |rank: u8| -> Vec<&str> {
            msgs.iter()
                .filter(|m| m.rank() == rank)
                .map(|m| m.string())
                .collect()
        };
        let sys = strings(0);
        let un = strings(1);
        let exp = strings(2);
        let raw = strings(3);

        let show_expect = show_many("expecting", &exp);
        let show_unexpect = show_many("unexpected", &un);
        // showSysUnExpect: suppressed if there are UnExpect messages or no
        // SysUnExpect; else uses only the FIRST sysUnExpect (empty → EOF).
        let show_sys = if !un.is_empty() || sys.is_empty() {
            String::new()
        } else if sys[0].is_empty() {
            "unexpected end of input".to_string()
        } else {
            format!("unexpected {}", sys[0])
        };
        let show_messages = show_many("", &raw);

        // concat $ map ("\n"++) $ clean [showSys, showUn, showExp, showMsg]
        let parts = clean_dedup(&[
            show_sys.as_str(),
            show_unexpect.as_str(),
            show_expect.as_str(),
            show_messages.as_str(),
        ]);
        parts.iter().map(|p| format!("\n{p}")).collect()
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // A GHC `error` never became a parsec `ParseError` in HS, so there is
        // no frame to show — only the message the `error` was applied to.
        if let Some(g) = &self.ghc_error {
            return write!(f, "{g}");
        }
        // Port of parsec `instance Show ParseError` (`show pos ++ ":" ++ …`)
        // and `instance Show SourcePos` (`Text.Parsec.Pos`): the quoted name is
        // omitted when empty, and there is a single space before "(line …".
        let line_col = format!("(line {}, column {})", self.line, self.col);
        if self.source.is_empty() {
            write!(f, "{}:{}", line_col, self.show_error_messages())
        } else {
            write!(
                f,
                "\"{}\" {}:{}",
                self.source,
                line_col,
                self.show_error_messages()
            )
        }
    }
}

impl std::error::Error for ParseError {}

/// parsec `clean = nub . filter (not . null)` — drop empties, dedup preserving
/// first occurrence.
fn clean_dedup(items: &[&str]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for s in items {
        if s.is_empty() || out.iter().any(|x| x == s) {
            continue;
        }
        out.push((*s).to_string());
    }
    out
}

/// parsec `commasOr` (with `msgOr = "or"`): join with ", " and " or " before
/// the last element.
fn commas_or(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [m] => m.clone(),
        _ => {
            let (init, last) = items.split_at(items.len() - 1);
            // commaSep = separate ", " . clean  (init is already clean here)
            format!("{} or {}", init.join(", "), last[0])
        }
    }
}

/// parsec `showMany pre msgs`: clean+dedup, then `commasOr`, optionally prefixed
/// by `pre` and a space.
fn show_many(pre: &str, msgs: &[&str]) -> String {
    let cleaned = clean_dedup(msgs);
    if cleaned.is_empty() {
        return String::new();
    }
    let co = commas_or(&cleaned);
    if pre.is_empty() {
        co
    } else {
        format!("{pre} {co}")
    }
}

/// Haskell `show :: [String] -> String`: a bracketed, comma-separated list of
/// double-quoted elements with no spaces — the rendering `function`'s and
/// `extendSig`'s diagnostics embed (Theory/Text/Parser/Signature.hs:112-119,
/// 204-207).  The elements are plain identifiers, so no escaping is needed.
fn show_string_list(items: &[&str]) -> String {
    let quoted: Vec<String> = items.iter().map(|s| format!("\"{s}\"")).collect();
    format!("[{}]", quoted.join(","))
}

/// The show of a single-character token as parsec's Char-stream primitives
/// render it: `show [c]` (Haskell `show :: String -> String` of a one-char
/// string).  parsec's `Text.Parsec.Char.satisfy`/`string` use `show [c]` for
/// the `SysUnExpect` token, so an unexpected `t` prints as `"t"`, a space as
/// `" "`, a quote as `"\""`, a newline as `"\n"`, etc.
/// One-line `prettyFact prettyLVar` of a predicate's declared head fact
/// (Theory/Model/Fact.hs:567-572, `showFactTag` prefixing `!` for a
/// persistent tag): the name and the arguments between `( ` and ` )`.
/// `prettyLVar` is `show` (Term/LTerm.hs:922-923) — the sort prefix, the
/// name, and `.<idx>` when the index is nonzero or the name ends in a digit
/// (Term/LTerm.hs:550-557).  HS parses the head with `fact' lvar`
/// (Theory/Text/Parser/Signature.hs:271-273), so its arguments are variables;
/// any other argument shape renders as its `Debug` form.
fn pred_fact_text(f: &Fact) -> String {
    let mut s = String::new();
    if f.persistent {
        s.push('!');
    }
    s.push_str(&f.name);
    if f.args.is_empty() {
        s.push_str("( )");
        return s;
    }
    s.push_str("( ");
    for (k, a) in f.args.iter().enumerate() {
        if k > 0 {
            s.push_str(", ");
        }
        match a {
            Term::Var(v) => {
                s.push_str(tamarin_term::lterm::sort_prefix(v.sort));
                s.push_str(&v.name);
                if v.idx != 0 || v.name.ends_with(|c: char| c.is_ascii_digit()) {
                    s.push('.');
                    s.push_str(&v.idx.to_string());
                }
            }
            other => s.push_str(&format!("{other:?}")),
        }
    }
    s.push_str(" )");
    s
}

fn show_char_token(c: char) -> String {
    show_lit_string(&c.to_string())
}

/// Byte offset of the 1-based `(line, col)` position in `text`.
fn offset_at_line_col(text: &str, line: u32, col: u32) -> usize {
    let mut current_line = 1;
    let mut current_col = 1;
    for (offset, ch) in text.char_indices() {
        if current_line == line && current_col == col {
            return offset;
        }
        if ch == '\n' {
            current_line += 1;
            current_col = 1;
        } else {
            current_col += 1;
        }
    }
    text.len()
}

/// GHC's `show :: String -> String`: the string in double quotes, every
/// character through [`show_lit_char`], and the `\&` separator GHC's
/// `showLitString` puts between a numeric escape and a following decimal digit
/// so the two do not read as one longer escape.
pub fn show_lit_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        let numeric = show_lit_char(c, &mut out);
        if numeric && chars.peek().is_some_and(|n| n.is_ascii_digit()) {
            out.push_str("\\&");
        }
    }
    out.push('"');
    out
}

/// Port of GHC's `showLitChar` for the characters that appear inside a
/// double-quoted string literal.  Returns whether it wrote a decimal escape,
/// which is what [`show_lit_string`] guards with `\&`.
fn show_lit_char(c: char, out: &mut String) -> bool {
    match c {
        '"' => out.push_str("\\\""),
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\t' => out.push_str("\\t"),
        '\r' => out.push_str("\\r"),
        '\u{0B}' => out.push_str("\\v"),
        '\u{0C}' => out.push_str("\\f"),
        '\u{07}' => out.push_str("\\a"),
        '\u{08}' => out.push_str("\\b"),
        c if (' '..='~').contains(&c) => out.push(c),
        // Control / non-ASCII: GHC uses a decimal escape `\NNN`.
        c => {
            out.push('\\');
            out.push_str(&(c as u32).to_string());
            return true;
        }
    }
    false
}

/// The merged `expecting` labels of the top-level item alternation, in HS's
/// exact order and spelling.  This is the base set parsec accumulates from
/// `addItems`'s `asum` (`Theory/Text/Parser.hs:243-303`) — each alternative's
/// leading `symbol`/`<?>` label — plus `letter` (from `formalComment`'s
/// `many1 letter`, `Token.hs:377-378`) and the trailing `symbol_ "end"`.
/// Captured empirically from the HS binary at a fresh item position (right
/// after `begin`, no preceding item leftover).  After other items, parsec
/// *prepends* the previous item's trailing-optional labels (rule →
/// `"variants"`, functions → `"["`,`","`, …); [`Parser::item_hangover`] carries
/// those for the three items that record them, the rest remain a known residue.
const TOP_LEVEL_ITEM_EXPECTS: &[&str] = &[
    "\"heuristic\"",
    "\"tactic\"",
    "\"builtins\"",
    "\"options\"",
    "\"functions\"",
    "\"function\"",
    "\"equations\"",
    "\"macros\"",
    "\"restriction\"",
    "\"axiom\"",
    "\"test\"",
    "\"lemma\"",
    "\"rule\"",
    "letter",
    "top-level process",
    "\"let\"",
    "\"equivLemma\"",
    "\"diffEquivLemma\"",
    "predicate block",
    "export block",
    "\"#ifdef\"",
    "\"#define\"",
    "\"#include\"",
    "\"end\"",
];

/// The labels HS `typep` (Token.hs:472-473) offers when neither alternative
/// matches: `symbol defaultSapicTypeS`'s `<?> "\"Any\""` (Token.hs:272-273) and
/// `identifier`'s `<?> "identifier"` (parsec's `Text.Parsec.Token.ident`).
const TYPEP_EXPECTS: &[&str] = &["\"Any\"", "identifier"];

/// The labels HS `sortedLVarNoSuffix [minBound..]` (Token.hs:486-499) offers
/// when no variable alternative matches: the five sort-prefix parsers in
/// LSort order — `$` (pub), `~` (fresh), a bare `identifier` (msg), `#`
/// (node), `%` (nat).
const SORTED_LVAR_NO_SUFFIX_EXPECTS: &[&str] = &["\"$\"", "\"~\"", "identifier", "\"#\"", "\"%\""];

// =============================================================================
// Parser entry points
// =============================================================================

/// Parse an `OpenTheory` (the default `theory ... begin ... end` form).
///
/// Anything after the closing `end` is ignored: Tamarin theories are commonly
/// followed by analysis banners and other free text that the official parser
/// also tolerates.
pub fn parse_theory(input: &str, flags: &[&str]) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, false);
    let thy = p.theory()?;
    Ok(thy)
}

/// Parse a diff theory, enabling both the `diff(a, b)` term and the diff-only
/// top-level namespaces. This is the syntax-level counterpart of HS
/// `parseOpenDiffTheoryString` (`Theory/Text/Parser.hs:84-86`).
pub fn parse_diff_theory(input: &str, flags: &[&str]) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, true);
    let thy = p.theory()?;
    Ok(thy)
}

/// Like [`parse_theory`], but threads the **including file's directory** so that
/// `#include "file"` directives resolve relative to it.
///
/// Direct port of HS `include` (Theory/Text/Parser.hs:323-343): the path is
/// resolved against `takeDirectory inFile0`, the included header-less fragment
/// is parsed as a continuation of the current item stream (same parser state —
/// signature, known functions, flags thread through), and nested includes
/// resolve relative to the included file's own directory.  `base_dir` is the
/// directory of the file `input` was read from (`takeDirectory inFile0`).
pub fn parse_theory_with_base(
    input: &str,
    flags: &[&str],
    base_dir: Option<PathBuf>,
) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, false);
    p.base_dir = base_dir;
    let thy = p.theory()?;
    Ok(thy)
}

/// Like [`parse_diff_theory`], but resolves includes relative to `base_dir`.
pub fn parse_diff_theory_with_base(
    input: &str,
    flags: &[&str],
    base_dir: Option<PathBuf>,
) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, true);
    p.base_dir = base_dir;
    let thy = p.theory()?;
    Ok(thy)
}

/// Parse a stream of intruder-rule declarations of the form
///     `rule (modulo AC) <name>[<limit>]: [..] --[..]-> [..]`
/// (with no surrounding `theory ... begin ... end` wrapper).
///
/// Direct port of HS `parseIntruderRules` (Theory/Text/Parser/Rule.hs:223-228):
/// ```haskell
/// parseIntruderRules
///     :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
/// parseIntruderRules msig ctxtDesc =
///     parseString [] ctxtDesc (setState (mkStateSig msig) >> many intrRule)
///   . T.unpack . TE.decodeUtf8
/// ```
/// `msig` is the signature HS installs with `setState (mkStateSig msig)`
/// (Theory/Text/Parser/Rule.hs:227, called from TheoryLoader.hs:860-876);
/// [`Parser::seed_signature`] does the same here, so `nullaryApp` resolves
/// the constants these machine-generated files use — `one` and `DH_neutral`
/// in the cached DH file — instead of reading them as variables.
///
/// The bodies are parsed using the existing `parse_rule_ac` path.
/// The caller is responsible for translating the parser-AST rules into
/// `IntrRuleAC` (incl. the `c_`/`d_` name dispatch HS `intrInfo` does
/// at Theory/Text/Parser/Rule.hs:163-172).
pub fn parse_intruder_rules(msig: &MaudeSig, input: &str) -> Result<Vec<Rule>, ParseError> {
    let mut p = Parser::new(input, &[], false);
    p.seed_signature(msig);
    // The caller resolves application heads against `msig` afterwards
    // (`KnownFuns`), so accept them structurally, which admits exactly the
    // same rules.
    p.resolve_prefix_apps = false;
    let mut rules = Vec::new();
    loop {
        p.skip_ws();
        if p.lx.is_eof() {
            break;
        }
        // HS `intrRule` uses `try (symbol "rule" *> moduloAC *> intrInfo <* colon)`
        // (Theory/Text/Parser/Rule.hs:156-161, see line 159) — i.e. requires the
        // `rule (modulo AC) name:` head.
        // `parse_rule_ac` enforces the same shape.
        let r = p.parse_rule_ac()?;
        rules.push(r);
    }
    Ok(rules)
}

/// Strip `//` line comments and `/* */` block comments from a lemma's verbatim
/// source span, used to populate `ast::Lemma::plaintext`.  Faithful port of HS
/// `removeComments` / `removeCommentBlock` (`Theory/Text/Parser/Lemma.hs:62-74`),
/// including the newline-swallowing behaviour that HS relies on: a `\n`
/// immediately preceding a comment is consumed with the comment, and a block
/// comment's closing `*/\n` consumes the trailing newline.  This determines the
/// textarea's `rows` count in the web Edit form (HS `textHeight = 2 + number of
/// '\n'`), so it must match char-for-char.
pub(crate) fn remove_comments(s: &str) -> String {
    let cs: Vec<char> = s.chars().collect();
    let n = cs.len();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < n {
        // '\n' : '/' : '/'  — drop the leading newline + the comment body,
        //                     keeping the terminating newline (dropWhile /= '\n').
        if cs[i] == '\n' && i + 2 < n && cs[i + 1] == '/' && cs[i + 2] == '/' {
            i += 3;
            while i < n && cs[i] != '\n' {
                i += 1;
            }
            continue;
        }
        // '/' : '/'  — drop up to (not including) the next newline.
        if cs[i] == '/' && i + 1 < n && cs[i + 1] == '/' {
            i += 2;
            while i < n && cs[i] != '\n' {
                i += 1;
            }
            continue;
        }
        // '\n' : '/' : '*'  — drop the leading newline, enter block-comment mode.
        if cs[i] == '\n' && i + 2 < n && cs[i + 1] == '/' && cs[i + 2] == '*' {
            i = remove_comment_block(&cs, i + 3);
            continue;
        }
        // '/' : '*'  — enter block-comment mode.
        if cs[i] == '/' && i + 1 < n && cs[i + 1] == '*' {
            i = remove_comment_block(&cs, i + 2);
            continue;
        }
        out.push(cs[i]);
        i += 1;
    }
    out
}

/// Consume a `/* ... */` block comment body starting at `i`, returning the
/// index just past the closing `*/` (and its trailing `\n` if present).
/// Mirrors HS `removeCommentBlock`.
fn remove_comment_block(cs: &[char], mut i: usize) -> usize {
    let n = cs.len();
    while i < n {
        if cs[i] == '*' && i + 1 < n && cs[i + 1] == '/' {
            // '*' : '/' : '\n'  swallows the newline; otherwise stop after '*/'.
            if i + 2 < n && cs[i + 2] == '\n' {
                return i + 3;
            }
            return i + 2;
        }
        i += 1;
    }
    n
}

// =============================================================================
// Parser state
// =============================================================================

/// The `(arity, Privacy, Constructability, NDCstate)` options tuple HS carries
/// per free function symbol (HS `NoEqSym`, Term/Term/FunctionSymbols.hs:132).
///
/// [`FunOptions::show`] is the Haskell `show` of that 4-tuple, which
/// `function`'s conflict diagnostic embeds verbatim
/// (Theory/Text/Parser/Signature.hs:214-216).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FunOptions {
    arity: usize,
    private: bool,
    destructor: bool,
    /// `[NDC]` was requested for this symbol.
    ndc: bool,
    /// `[NDC-diff]` was requested for this symbol.
    ndc_diff: bool,
}

impl FunOptions {
    /// A public constructor of the given arity with no NDC property — the
    /// shape of every symbol in HS's `pairFunSig`
    /// (Term/Term/FunctionSymbols.hs:299-300).
    fn plain(arity: usize) -> Self {
        FunOptions {
            arity,
            private: false,
            destructor: false,
            ndc: false,
            ndc_diff: false,
        }
    }

    /// The options carried by a `NoEqSym` of a signature.
    fn of_no_eq(sym: &NoEqSym) -> Self {
        FunOptions {
            arity: sym.arity,
            private: sym.privacy == Privacy::Private,
            destructor: sym.constructability == Constructability::Destructor,
            ndc: matches!(sym.ndc, NdcState::IsNdc | NdcState::IsNdcBoth),
            ndc_diff: matches!(sym.ndc, NdcState::IsNdcDiff | NdcState::IsNdcBoth),
        }
    }

    /// HS's derived `Ord` on the `NoEqSym` payload
    /// `(Int, Privacy, Constructability, NDCstate)`: componentwise, with each
    /// constructor ranked by declaration order — `Private < Public`,
    /// `Constructor < Destructor` and `IsNDC < NotNDC < IsNDCDiff < IsNDCBoth`
    /// (Term/Term/FunctionSymbols.hs:110-126).
    fn ord_key(&self) -> (usize, u8, u8, u8) {
        (
            self.arity,
            u8::from(!self.private),
            u8::from(self.destructor),
            match (self.ndc, self.ndc_diff) {
                (true, false) => 0,
                (false, false) => 1,
                (false, true) => 2,
                (true, true) => 3,
            },
        )
    }

    /// Haskell `show (k, priv, destr, ndc)`: a parenthesised tuple with no
    /// spaces after the commas, each component shown by its derived `Show`
    /// instance (`Public`/`Private`, `Constructor`/`Destructor`, and the four
    /// `NDCstate` constructors of Term/Term/FunctionSymbols.hs:125).
    ///
    /// The NDC component is HS's `joinNDC` of the two requested flags
    /// (Term/Term/FunctionSymbols.hs:181-186).
    fn show(&self) -> String {
        format!(
            "({},{},{},{})",
            self.arity,
            if self.private { "Private" } else { "Public" },
            if self.destructor {
                "Destructor"
            } else {
                "Constructor"
            },
            match (self.ndc, self.ndc_diff) {
                (false, false) => "NotNDC",
                (true, false) => "IsNDC",
                (false, true) => "IsNDCDiff",
                (true, true) => "IsNDCBoth",
            }
        )
    }
}

/// The `MaudeSig` each `builtins:` name enables, in HS's `builtinsNames` order
/// (Theory/Text/Parser/Signature.hs:78-86, whose tail is `builtinsDiffNames`,
/// Theory/Text/Parser/Signature.hs:58-76) — the order `builtinReservedNames`
/// (Theory/Text/Parser/Signature.hs:178-181) is built in and therefore the
/// order `function`'s `conflictingBuiltins` list is rendered in.
///
/// `reliable-channel` is absent on purpose: it maps to `Nothing`
/// (Theory/Text/Parser/Signature.hs:84), so it neither merges a signature nor
/// reserves anything.
macro_rules! builtin_maude_sigs {
    ($($name:literal => $sig:path),+ $(,)?) => {
        /// Names whose parser builtin contributes a Maude signature.
        ///
        /// Exposed so elaboration can test that its independently maintained
        /// name-to-signature dispatch remains complete.
        #[doc(hidden)]
        pub const BUILTIN_MAUDE_SIG_NAMES: &[&str] = &[$($name),+];

        const BUILTIN_MAUDE_SIGS: &[(&str, fn() -> MaudeSig)] = &[
            $(($name, $sig)),+
        ];
    };
}

builtin_maude_sigs! {
    "locations-report" => location_report_maude_sig,
    "diffie-hellman" => dh_maude_sig,
    "bilinear-pairing" => bp_maude_sig,
    "multiset" => mset_maude_sig,
    "xor" => xor_maude_sig,
    "symmetric-encryption" => sym_enc_maude_sig,
    "asymmetric-encryption" => asym_enc_maude_sig,
    "signing" => signature_maude_sig,
    "dest-pairing" => pair_dest_maude_sig,
    "dest-symmetric-encryption" => sym_enc_dest_maude_sig,
    "dest-asymmetric-encryption" => asym_enc_dest_maude_sig,
    "dest-signing" => signature_dest_maude_sig,
    "revealing-signing" => reveal_signature_maude_sig,
    "hashing" => hash_maude_sig,
    "natural-numbers" => nat_maude_sig,
}

/// The `stFunSyms` of every [`BUILTIN_MAUDE_SIGS`] row, i.e. the free function
/// symbols enabling that builtin adds to the parse-time signature, each row in
/// the `S.toList` (ascending, raw-byte) order HS's `extendSig` iterates
/// (Theory/Text/Parser/Signature.hs:102-135, see line 105).
///
/// The rows whose `MaudeSig` only flips an enable flag (`diffie-hellman`,
/// `bilinear-pairing`, `multiset`, `xor`, `natural-numbers` —
/// Term/Maude/Signature.hs:200-205) are empty and reserve no names.
fn builtin_st_fun_sym_table() -> &'static [(&'static str, Vec<NoEqSym>)] {
    use std::sync::OnceLock;
    static TABLE: OnceLock<Vec<(&'static str, Vec<NoEqSym>)>> = OnceLock::new();
    TABLE.get_or_init(|| {
        BUILTIN_MAUDE_SIGS
            .iter()
            .map(|(name, sig)| (*name, sig().st_fun_syms.into_iter().collect()))
            .collect()
    })
}

/// The `stFunSyms` a `builtins:` name contributes, or `None` for a name with no
/// `MaudeSig` (`reliable-channel`) and for names this parser does not know.
fn builtin_st_fun_syms(name: &str) -> Option<&'static [NoEqSym]> {
    builtin_st_fun_sym_table()
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, syms)| syms.as_slice())
}

/// A builtin symbol's name as text.  Every name the builtin `MaudeSig`s carry
/// is ASCII (Term/Builtin/Signature.hs:18-44,
/// Term/Term/FunctionSymbols.hs:221-243).
fn sym_name(sym: &NoEqSym) -> &'static str {
    std::str::from_utf8(sym.name).expect("builtin symbol names are ASCII")
}

/// The non-AC (`NoEq`) symbols each theory-level enable flag folds into
/// `funSyms` (Term/Maude/Signature.hs:110-125): the flags contribute whole
/// `FunSig`s, of which only the `NoEq` members reach `noEqFunSyms` and hence
/// `userDefinedFunSyms` (Term/Maude/Signature.hs:157-164) — the set the
/// macro-name conflict check searches (Theory/Text/Parser/Macro.hs:43).
/// Their AC members (`Mult`, `Xor`, `Union`, `NatPlus`) and BP's `C EMap` are
/// not `NoEq`/`ACfct` and never enter that set.
struct TheoryNoEqSyms {
    /// `dhFunSig`'s `NoEq` part (Term/Term/FunctionSymbols.hs:283-284),
    /// contributed when `enableDH || enableBP` (the `maudeSig` smart
    /// constructor forces `enableDH` under BP,
    /// Term/Maude/Signature.hs:110-112).
    dh: Vec<NoEqSym>,
    /// `bpFunSig`'s `NoEq` part (Term/Term/FunctionSymbols.hs:291-292).
    bp: Vec<NoEqSym>,
    /// `xorFunSig`'s `NoEq` part (Term/Term/FunctionSymbols.hs:287-288).
    xor: Vec<NoEqSym>,
    /// `natFunSig`'s `NoEq` part (Term/Term/FunctionSymbols.hs:324-325).
    nat: Vec<NoEqSym>,
}

/// [`TheoryNoEqSyms`] read off the four `FunSig`s.
fn theory_noeq_syms() -> &'static TheoryNoEqSyms {
    use std::sync::OnceLock;
    static SYMS: OnceLock<TheoryNoEqSyms> = OnceLock::new();
    SYMS.get_or_init(|| {
        fn noeq(sig: FunSig) -> Vec<NoEqSym> {
            sig.into_iter()
                .filter_map(|s| match s {
                    FunSym::NoEq(f) => Some(f),
                    _ => None,
                })
                .collect()
        }
        TheoryNoEqSyms {
            dh: noeq(dh_fun_sig()),
            bp: noeq(bp_fun_sig()),
            xor: noeq(xor_fun_sig()),
            nat: noeq(nat_fun_sig()),
        }
    })
}

/// Intern an AC-symbol name for the `'static` borrow [`BinOp::AcFct`]
/// carries.  Names are deduplicated process-wide, so re-parses leak at most
/// one allocation per distinct `[AC]` symbol name.  Equality on the variant is
/// by string VALUE (`str: PartialEq`), so entries interned here compare equal
/// to ones other crates intern for the same name.
fn intern_ac_name(name: &str) -> &'static str {
    use std::collections::BTreeSet;
    use std::sync::{Mutex, OnceLock};
    static INTERNED: OnceLock<Mutex<BTreeSet<&'static str>>> = OnceLock::new();
    let mut set = INTERNED
        .get_or_init(|| Mutex::new(BTreeSet::new()))
        .lock()
        .expect("AC-name interner poisoned");
    match set.get(name) {
        Some(s) => s,
        None => {
            let leaked: &'static str = Box::leak(name.to_owned().into_boxed_str());
            set.insert(leaked);
            leaked
        }
    }
}

/// Resolution of a prefix-application head — see [`Parser::lookup_arity`].
#[derive(Clone, Copy, Debug)]
enum ArityRes {
    /// `NoEqUser` (or a macro name, or the appended `em` row): the whole
    /// `(k, priv, cnstr, ndc)` tuple `lookupArity` hands back
    /// (Theory/Text/Parser/Term.hs:66-67), of which `naryOpApp` checks the
    /// arity (Theory/Text/Parser/Term.hs:97-100) and passes the rest into
    /// `fAppNoEq`'s symbol.
    NoEq { opts: FunOptions },
    /// `ACfctUser`: any argument count is accepted
    /// (`Theory/Text/Parser/Term.hs:98` gates the
    /// check on `NotAC`) and the application builds `fAppAC (ACfct …)`.
    Ac,
}

impl ArityRes {
    /// Whether an application of `id` resolving this way builds HS `expSym`
    /// — `("exp", (2, Public, Constructor, NotNDC))`
    /// (Term/Term/FunctionSymbols.hs:245,251), the one `NoEq` symbol
    /// `prettyTerm` renders infix as `t1^t2` (Term/Term.hs:310).  Both
    /// application spellings emit [`BinOp::Exp`] for it, which is what the
    /// `^` operator parses to, so the printers reach that rendering from
    /// either source spelling.
    fn is_dh_exp(self, id: &str) -> bool {
        id == "exp"
            && matches!(
                self,
                ArityRes::NoEq {
                    opts: FunOptions {
                        arity: 2,
                        private: false,
                        destructor: false,
                        ndc: false,
                        ndc_diff: false,
                    }
                }
            )
    }
}

pub struct Parser<'a> {
    lx: Lexer<'a>,
    /// Defined preprocessor flags. Mutated by `#define` directives.
    // parsed flag-name set; membership only, never iterated into output;
    // std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    flags: HashSet<String>,
    /// Whether we're parsing a diff theory. Set only from the `Parser::new`
    /// argument supplied by the caller and echoed into `Theory::is_diff`;
    /// `theory()` does not derive it from `flags` or a `#define diff` preamble.
    is_diff: bool,
    /// HS `enableDiff . sig` — the signature bit that makes the `diff(a, b)`
    /// term operator legal (Theory/Text/Parser/Term.hs:123-135, see line 128).
    ///
    /// Three sites set it, and they are the only ones:
    ///   * `theory` when the CLI-defined flag set contains `diff`
    ///     (Theory/Text/Parser.hs:232-237, see line 234) — i.e. `-D=diff`;
    ///   * `diffTheory`, unconditionally (Theory/Text/Parser.hs:399-410, see line 401);
    ///   * `diffEquivLemma`, right after its colon, for the rest of the parse
    ///     (Theory/Text/Parser/Sapic.hs:212-217, see line 215).
    ///
    /// It is deliberately NOT read off [`Parser::flags`]: that set is mutated by
    /// `#define`, whereas HS reads `flags0` once at `theory`'s entry.  (`#define
    /// diff` cannot define it anyway — `diff` is a reserved name, so the
    /// directive's `identifier` rejects it.)
    enable_diff: bool,
    /// Directory of the file currently being parsed (`takeDirectory inFile0` in
    /// HS).  `#include "file"` resolves relative to this; `None` (no source
    /// file) means includes are taken verbatim, mirroring HS's `Nothing` case.
    base_dir: Option<PathBuf>,
    /// Names of the user-declared AC function symbols (`functions:` entries
    /// carrying the `[AC]` attribute), which `acterm` turns into infix
    /// operators.  This is the parse-time signature state HS reads as
    /// `stACFunSyms . sig <$> getState` (Theory/Text/Parser/Term.hs:165-174):
    /// only symbols declared EARLIER in the file are infix operators for the
    /// terms that follow.
    ///
    /// Held ascending by name (and deduplicated), matching the
    /// `S.toList (stACFunSyms sig)` order HS's nested `parseACSym` recursion
    /// consumes — `ACfctSym`'s `Ord` compares the name first, so set order is
    /// name order.  The order is load-bearing: the LAST symbol in the list binds
    /// tightest.
    ac_fun_syms: Arc<Vec<String>>,
    /// The free function symbols known at this point of the parse, the
    /// parse-time slice of HS's `stFunSyms . sig <$> getState` that
    /// `function`'s conflict check reads (Theory/Text/Parser/Signature.hs:212).
    ///
    /// Seeded with `pairFunSig` (`fst/1`, `pair/2`, `snd/1`, all
    /// `Public, Constructor, NotNDC` — Term/Term/FunctionSymbols.hs:247-261) in
    /// `S.toList` order, because `parseFile` starts from `sig = pairMaudeSig`
    /// (Token.hs:260-261).  A `builtins:` item merges the row of
    /// [`builtin_st_fun_sym_table`] it names; user `functions:` declarations add
    /// their own symbol, except `[AC]` ones (HS files those under
    /// `stACFunSyms` via `ACfctUser`, Term/Maude/Signature.hs:170-173).
    ///
    /// Held as an ordered set — ascending by name, then by
    /// [`FunOptions::ord_key`] — because HS's `lookup f (S.toList …)` takes the
    /// FIRST match, and one name can carry two entries (e.g. `builtins:
    /// symmetric-encryption, dest-symmetric-encryption` leaves both the
    /// constructor and the destructor `sdec`).
    fun_syms: Arc<Vec<(String, FunOptions)>>,
    /// The macro names known at this point of the parse (HS `macroNames`),
    /// each registered as `(k, Private, Destructor, NotNDC)`
    /// (Theory/Text/Parser/Macro.hs:46).  Searched after [`Parser::fun_syms`],
    /// matching HS's `lookup f (S.toList (stFunSyms sign) ++ S.toList
    /// (macroNames sign))` (Theory/Text/Parser/Signature.hs:212).
    macro_syms: Arc<Vec<(String, FunOptions)>>,
    /// HS `reservedBuiltinNames` (Theory/Text/Parser/Token.hs parser state):
    /// the names of the `stFunSyms` of every builtin a `builtins:` item has
    /// enabled so far, appended by `extendSig`
    /// (Theory/Text/Parser/Signature.hs:132-134).
    ///
    /// Only the non-diff `builtins` parser fills it; `diffbuiltins`
    /// (Theory/Text/Parser/Signature.hs:141-148) merges the signature without
    /// touching it, so a
    /// diff theory reserves nothing and `function`'s builtin pre-check can
    /// never fire there.
    reserved_builtin_names: Vec<String>,
    /// The `enableDH`/`enableBP`/`enableXor`/`enableMSet`/`enableNat` bits of
    /// HS's parse-time `MaudeSig` (Term/Maude/Signature.hs:90-108), flipped by
    /// the `builtins:` names whose signatures carry only these flags
    /// (Term/Maude/Signature.hs:200-205).
    ///
    /// Each one opens its own term chain level: `*` and `^`
    /// ([`Parser::multterm`], [`Parser::expterm`]), `XOR`/`⊕`
    /// ([`Parser::xorterm`]), `%+` ([`Parser::natterm`]) and `++`/`+`
    /// ([`Parser::msetterm_inner`]), each level falling through to the next one
    /// down while its bit is clear (Theory/Text/Parser/Term.hs:179-208).  They
    /// also select the theory-level function symbols `funSyms` contributes to
    /// the macro-name conflict check (Theory/Text/Parser/Macro.hs:43,
    /// Term/Maude/Signature.hs:110-125,163-164) and the operator `expecting`
    /// labels the open levels leave behind ([`Parser::term_carry_labels`]).
    ///
    /// `sig_enable_dh` covers `enableBP` too: the `maudeSig` smart constructor
    /// sets `enableDH = enableDH || enableBP` (Term/Maude/Signature.hs:110-112),
    /// so `builtins: bilinear-pairing` sets both bits here.
    sig_enable_dh: bool,
    sig_enable_bp: bool,
    sig_enable_xor: bool,
    sig_enable_mset: bool,
    sig_enable_nat: bool,
    /// Whether the last atomic term consumed was a variable whose optional
    /// dot-index attempt failed at the position the parse now stands at.
    ///
    /// parsec state: HS `indexedIdentifier`'s trailing `option 0 (try (dot *>
    /// natural))` (Token.hs:395-400) runs after `identifier`'s lexeme has
    /// consumed trailing whitespace, so a variable WITHOUT an explicit index
    /// or sort suffix leaves an `Expect "\".\""` at the following token's
    /// position.  A `fail` raised there (the macro-name conflict,
    /// Theory/Text/Parser/Macro.hs:44) merges that label into its error, which
    /// is the only place this flag is read.  Every other atom shape ends in a
    /// non-identifier lexeme (`)`, `>`, a quoted name, …) whose trailing
    /// attempts happen before the whitespace, so they leave nothing.
    var_dot_hangover: bool,
    /// Whether the most recent [`Parser::try_dot_index`] consumed an explicit
    /// `.<index>` — in HS terms, whether `indexedIdentifier`'s single `option 0
    /// (try (dot *> natural))` attempt (Token.hs:395-400) was spent on a
    /// successful parse (in which case nothing hangs over) rather than left as
    /// a pending `Expect "\".\""`.  Read by [`Self::note_var_dot_hangover`],
    /// which runs before any other `try_dot_index` call can intervene.
    dot_index_consumed: bool,
    /// Whether [`Self::attach_sort_suffix`] consumed a `:sort` suffix for the
    /// variable it last ran on.  HS's `sortedLVar` suffix arm ends in
    /// `symbol_ (sortSuffix s)` (Token.hs:409-421), a lexeme of its own, so
    /// the variable's `indexedIdentifier` hangovers are already behind the
    /// parse when the suffix closes it.  Read by
    /// [`Self::note_var_dot_hangover`], which runs immediately after every
    /// `attach_sort_suffix` call.
    sort_suffix_consumed: bool,
    /// Byte offset just past the identifier characters of the most recently
    /// consumed variable/application name (BEFORE the lexeme's trailing
    /// whitespace).  `T.identifier`'s trailing `many identLetter` fails there
    /// and leaves alphaNum's `Expect "letter or digit"` (Token.hs:392-394),
    /// which survives into an error raised at exactly that offset and is
    /// dropped once whitespace moved past it.  Set at the identifier-consuming
    /// sites of the term path, read via [`Parser::var_hangover_ident_end`].
    last_ident_end: Option<usize>,
    /// [`Parser::last_ident_end`] snapshotted for the variable atom that set
    /// [`Parser::var_dot_hangover`] — the offset where that variable's
    /// `letter or digit` hangover sits.
    var_hangover_ident_end: Option<usize>,
    /// parsec's carried error where the most recent term parse stopped:
    /// `(offset, letter_or_digit, dot, eqn)` — the byte offset
    /// (post-whitespace), whether the last atom's `letter or digit`
    /// identifier hangover sits exactly there, whether its `"."` dot-index
    /// hangover is pending, and the chain's `eqn` flag.  A consumed failure
    /// raised at exactly that offset (fact-argument close, tuple close,
    /// `equations:`' `=`, the top-level item alternation) renders these
    /// hangovers plus the enabled operator labels
    /// ([`Self::term_carry_labels`]) ahead of its own labels, exactly as
    /// parsec's `mergeError` does at equal positions.  Refreshed at the end
    /// of every [`Self::msetterm`]/[`Self::acterm`]; the outermost term level
    /// finishes last, so the stored value is always the enclosing context's.
    term_carry: Option<(usize, bool, bool, bool)>,
    /// Offset where a just-parsed fact's ABSENT annotation list left its
    /// `Expect "\"[\""` — `option [] $ list factAnnotation`
    /// (Theory/Text/Parser/Fact.hs:48)
    /// attempts `[` right after the closing `)` lexeme and fails there when
    /// no annotation follows.  Merged by the consumed failures that can sit
    /// at that exact offset ([`Self::formula_close_error`], the fact-list
    /// close of [`Self::sep_end_by`]).
    fact_annot_hangover: Option<usize>,
    /// Whether prefix applications resolve through [`Self::lookup_arity`]
    /// (HS `naryOpApp`/`binaryAlgApp`, Theory/Text/Parser/Term.hs:88-121).  True
    /// for theory parsing and for [`parse_parens_goal`], which runs inside the
    /// theory parser's symbol state; [`parse_formula_str`] and
    /// [`parse_intruder_rules`] clear it because they re-parse RENDERED text
    /// whose heads their callers resolve, where every application must be
    /// accepted structurally.
    resolve_prefix_apps: bool,
    /// Whether a `:` after a variable names a SAPIC TYPE rather than a sort
    /// suffix.  Set while parsing a SAPIC process (and a process definition's
    /// parameter list), where HS uses `sapicvar` — `lvarNoSuffix` plus
    /// `option Nothing (colon *> typep)` (Token.hs:487-510) — instead of the
    /// suffix-accepting `msgvar`/`lvar` used everywhere else.  So `x:nat`
    /// inside a process is `x` typed `"nat"`, while the same text in a rule is
    /// the nat-sorted `x`.
    sapic_var_types: bool,
    /// Whether a `=`-pattern (`Term::PatMatch`) may start a term.  On only in
    /// the three positions where HS threads a PATTERN literal parser: an `in`
    /// message (`ltypedpatternlit`, Theory/Text/Parser/Sapic.hs:102,109), the
    /// pattern side of a process `let` binding (`sapicpatternterm`,
    /// Parser/Sapic.hs:264), and an embedded MSR rule — all fact rows plus its
    /// `_restrict` formulas (`genericRule sapicpatternvar`, Parser/Sapic.hs:155).
    /// Everywhere else HS's literal parser has no `=` alternative, so a `=`
    /// starts no term and falls through to the no-alternative error.
    allow_pat: bool,
    /// The `expecting` labels a completed top-level item leaves behind at the
    /// byte offset it stopped at, and that offset.
    ///
    /// parsec carries the error of a *consumed-ok* parse forward and merges it
    /// into whatever the continuation reports at the same position, so an
    /// item's trailing optional parsers (`option [] $ symbol "variants" …` at
    /// the end of `protoRule`, Theory/Text/Parser/Rule.hs:134; `commaSep1`'s
    /// `comma`) prepend
    /// their labels to the next item-position error.  Consumed by
    /// [`Parser::item_position_error`].
    item_hangover: Option<(usize, &'static [&'static str])>,
    /// First occurrence of each protocol-rule name parsed so far, in item
    /// order — the lookup set HS `lookupOpenProtoRule` (OpenTheory.hs:679-682,
    /// a `find` over `theoryRules`, hence first occurrence wins) consults when
    /// `addOpenProtoRule` (OpenTheory.hs:691-702) guards a newly parsed rule.
    /// Fed and read by [`Parser::guard_duplicate_rule`]; threaded through
    /// `#include` sub-parsers like the signature state (HS runs one `addItems`
    /// accumulation across included files).
    seen_rules: Vec<Rule>,
    /// Names of the restrictions in the theory so far: user
    /// `restriction:`/`axiom:` items plus the `Restr_<rule>_<i>` restrictions
    /// that `_restrict` expansion mints per rule (HS `fromRuleRestriction`,
    /// Model/Restriction.hs:141-149, `restrPrefix = "Restr_"`).  This is the
    /// name set `addRestriction` (TheoryObject.hs:453-456) guards against when
    /// `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) inserts a rule's
    /// expanded restrictions — checked BEFORE the rule-name guard itself.
    seen_restriction_names: Vec<String>,
    /// Names of the lemmas parsed so far — the set `addLemma`
    /// (TheoryObject.hs:462-465, a name lookup via `lookupLemma`) guards
    /// against when `liftedAddLemma` (Theory/Text/Parser.hs:141-147) inserts
    /// a newly parsed lemma; a reused name fails as `duplicate lemma: <name>`
    /// (Theory/Text/Parser/Exceptions.hs:39).  Threaded through `#include`
    /// sub-parsers like [`Parser::seen_rules`].
    seen_lemma_names: Vec<String>,
    /// `(persistent, name, arity)` — the fact-tag key `lookupPredicate`
    /// compares (Theory/Syntactic/Predicate.hs:77-80, `sameName` is tag
    /// equality) — of each predicate declared so far, seeded with the builtin
    /// `Smaller/2` (Theory/Syntactic/Predicate.hs:58-67), which the lookup
    /// list always appends.  `addPredicate` (TheoryObject.hs:540-543) guards
    /// a new declaration against this set; a collision fails as
    /// `duplicate predicate: <fact>` (Theory/Text/Parser/Exceptions.hs:43).
    seen_predicates: Vec<(bool, String, usize)>,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str, flags: &[&str], is_diff: bool) -> Self {
        // flag-name dedup set; .insert/.contains only;
        // std kept (byte-inert) — iteration order never reaches output.
        #[allow(clippy::disallowed_types)]
        let mut flags_set = HashSet::new();
        for f in flags {
            flags_set.insert((*f).to_string());
        }
        Parser {
            lx: Lexer::new(src),
            enable_diff: is_diff || flags_set.contains("diff"),
            flags: flags_set,
            is_diff,
            base_dir: None,
            ac_fun_syms: Arc::new(Vec::new()),
            fun_syms: Arc::new(vec![
                ("fst".to_string(), FunOptions::plain(1)),
                ("pair".to_string(), FunOptions::plain(2)),
                ("snd".to_string(), FunOptions::plain(1)),
            ]),
            macro_syms: Arc::new(Vec::new()),
            reserved_builtin_names: Vec::new(),
            sig_enable_dh: false,
            sig_enable_bp: false,
            sig_enable_xor: false,
            sig_enable_mset: false,
            sig_enable_nat: false,
            var_dot_hangover: false,
            dot_index_consumed: false,
            sort_suffix_consumed: false,
            last_ident_end: None,
            var_hangover_ident_end: None,
            term_carry: None,
            fact_annot_hangover: None,
            resolve_prefix_apps: true,
            sapic_var_types: false,
            allow_pat: false,
            item_hangover: None,
            seen_rules: Vec::new(),
            seen_restriction_names: Vec::new(),
            seen_lemma_names: Vec::new(),
            seen_predicates: vec![(false, "Smaller".to_string(), 2)],
        }
    }

    // -------- Error helpers --------

    /// A raw-message parse error at the current position (parsec `Message`).
    /// Renders as `"<path>" (line, column):\n<msg>` — the correct parsec frame
    /// with a single message line, even though the message text itself is not a
    /// `unexpected …`/`expecting …` pair.  Used by the many hand-coded error
    /// sites that do not (yet) track a parsec-style expected set.
    fn err(&self, msg: impl Into<String>) -> ParseError {
        ParseError::at(self.lx.pos(), vec![Message::Message(msg.into())])
    }

    /// The `SysUnExpect` token parsec's Char-stream primitives fill in at the
    /// current position: `show [c]` of the next character, or empty (which
    /// renders as `end of input`) at EOF.
    fn unexpected_token(&self) -> String {
        match self.lx.peek() {
            Some(c) => show_char_token(c),
            None => String::new(),
        }
    }

    /// A parsec-shaped `unexpected TOKEN / expecting …` error at the current
    /// (post-whitespace) position — the shape a failing `symbol`/token parser
    /// produces.  `expects` are the raw `<?>` label strings, already carrying
    /// any quoting (e.g. `"\"theory\""`).  The `SysUnExpect` token is `show [c]`
    /// of the next char, or empty (→ `end of input`) at EOF, exactly as
    /// parsec's Char-stream `SysUnExpect` is filled.  Whitespace is skipped
    /// first so the reported position/token is the token start, matching
    /// parsec (where `lexeme` has already consumed leading whitespace).
    fn err_expect(&mut self, expects: &[&str]) -> ParseError {
        self.skip_ws();
        let pos = self.lx.pos();
        let unexpected = self.unexpected_token();
        let mut messages = Vec::with_capacity(expects.len() + 1);
        messages.push(Message::SysUnExpect(unexpected));
        for e in expects {
            messages.push(Message::Expect((*e).to_string()));
        }
        ParseError::at(pos, messages)
    }

    /// The error parsec's `fail` raises immediately after a lexeme.
    ///
    /// `fail msg` attaches a `Message` at the *current* position, which
    /// `lexeme`'s trailing `whiteSpace` has already advanced past the preceding
    /// token; the empty error that `whiteSpace`'s `skipMany` accumulated there
    /// (a `SysUnExpect` naming the next character) merges into it under
    /// parsec's bind, so the frame reads `unexpected <tok>` followed by the raw
    /// message.
    fn err_fail(&mut self, msg: impl Into<String>) -> ParseError {
        self.skip_ws();
        let pos = self.lx.pos();
        let unexpected = self.unexpected_token();
        ParseError::at(
            pos,
            vec![
                Message::SysUnExpect(unexpected),
                Message::Message(msg.into()),
            ],
        )
    }

    /// The error value for a GHC `error` raised inside a parser action (see
    /// [`GhcError`]).  The position is where the parser stood when it aborted —
    /// HS discards it, since the exception bypasses parsec's error machinery
    /// altogether, and so does every rendering of this error.
    fn err_ghc(&self, message: String, call_site: String) -> ParseError {
        ParseError {
            ghc_error: Some(GhcError { message, call_site }),
            ..ParseError::at(self.lx.pos(), Vec::new())
        }
    }

    /// [`Self::err_fail`] as an enclosing `<?>` label rewrites it.
    ///
    /// parsec's `labels` (`Text.Parsec.Prim`) post-processes a *non-consuming*
    /// failure with `setExpectErrors`, which drops every `Expect` the error
    /// carries and installs the label's own; `SysUnExpect`, `UnExpect` and raw
    /// `Message`s survive untouched.  A `fail` raised inside a `try`ed
    /// alternative of `term … <?> "term"`
    /// (Theory/Text/Parser/Term.hs:138-163, see line 154)
    /// therefore reaches the user as `unexpected <tok> / expecting term /
    /// <msg>`.
    fn err_fail_labelled(&mut self, msg: impl Into<String>, label: &str) -> ParseError {
        let mut e = self.err_fail(msg);
        e.messages.push(Message::Expect(label.to_string()));
        e
    }

    /// Byte offset just past `name`'s characters for the identifier lexeme
    /// that began at `start` — i.e. BEFORE the lexeme's trailing whitespace,
    /// which `Lexer::identifier` has already skipped.  Replays the lexeme like
    /// [`Self::fact`]'s uppercase check does; the parser position is restored.
    fn ident_end_from(&mut self, start: Pos, name: &str) -> usize {
        let after = self.save();
        self.restore(start);
        self.skip_ws();
        for _ in name.chars() {
            self.lx.bump();
        }
        let end = self.lx.pos().offset;
        self.restore(after);
        end
    }

    /// Record [`Parser::term_carry`] for the term chain that just finished:
    /// the pending `Expect` labels parsec would carry at the current
    /// (post-whitespace) position.  In HS these accumulate as the `chainl1`
    /// levels of Theory/Text/Parser/Term.hs:165-212 unwind, each level's failed
    /// operator attempt
    /// leaving its `symbol` label — innermost first: the user-defined `[AC]`
    /// operators (one level per symbol, the LAST in set order innermost —
    /// `parseACSym`, Theory/Text/Parser/Term.hs:165-172), then `^`/`*` (DH,
    /// forced on by BP —
    /// Term/Maude/Signature.hs:111-112), `XOR`/`⊕` (xor), `%+` (nat) and
    /// `++`/`+` (multiset), each only when its signature bit is enabled and
    /// the chain is open (`not eqn`; the AC levels ignore `eqn`).  Ahead of
    /// those sit the last variable atom's own hangovers: `letter or digit`
    /// (identifier continuation, only while no whitespace intervened) and
    /// `"."` (the unspent dot-index attempt, [`Parser::var_dot_hangover`]).
    fn finish_term_carry(&mut self, eqn: bool) {
        self.skip_ws();
        let off = self.lx.pos().offset;
        self.term_carry = Some((
            off,
            self.var_dot_hangover && self.var_hangover_ident_end == Some(off),
            self.var_dot_hangover,
            eqn,
        ));
    }

    /// Render the `Expect` labels [`Parser::term_carry`] stands for when its
    /// offset is `at`: the variable hangovers, then one label per operator the
    /// enabled chain levels attempted there — innermost first (see
    /// [`Self::finish_term_carry`]).
    fn term_carry_labels(&self, at: usize) -> Vec<Message> {
        let Some((off, lod, dot, eqn)) = self.term_carry else {
            return Vec::new();
        };
        if off != at {
            return Vec::new();
        }
        let mut labels: Vec<Message> = Vec::new();
        if lod {
            labels.push(Message::Expect("letter or digit".to_string()));
        }
        if dot {
            labels.push(Message::Expect("\".\"".to_string()));
        }
        for name in self.ac_fun_syms.iter().rev() {
            labels.push(Message::Expect(format!("\"{name}\"")));
        }
        if !eqn {
            if self.sig_enable_dh {
                labels.push(Message::Expect("\"^\"".to_string()));
                labels.push(Message::Expect("\"*\"".to_string()));
            }
            if self.sig_enable_xor {
                labels.push(Message::Expect("\"XOR\"".to_string()));
                labels.push(Message::Expect("\"⊕\"".to_string()));
            }
            if self.sig_enable_nat {
                labels.push(Message::Expect("\"%+\"".to_string()));
            }
            if self.sig_enable_mset {
                labels.push(Message::Expect("\"++\"".to_string()));
                labels.push(Message::Expect("\"+\"".to_string()));
            }
        }
        labels
    }

    /// A consumed failure at the current position whose grammar continuation
    /// expected `site_labels`, merged with whatever term hangovers
    /// ([`Parser::term_carry`]) and fact-annotation hangover
    /// ([`Parser::fact_annot_hangover`]) sit at exactly that offset — parsec's
    /// `mergeError` of the carried error into a failure at an equal position.
    /// The carried labels were accumulated first, so they render first.
    fn err_expect_after_term(&mut self, site_labels: &[&str]) -> ParseError {
        self.skip_ws();
        let pos = self.lx.pos();
        let mut messages = vec![Message::SysUnExpect(self.unexpected_token())];
        messages.extend(self.term_carry_labels(pos.offset));
        if self.fact_annot_hangover == Some(pos.offset) {
            messages.push(Message::Expect("\"[\"".to_string()));
        }
        messages.extend(
            site_labels
                .iter()
                .map(|l| Message::Expect((*l).to_string())),
        );
        ParseError::at(pos, messages)
    }

    /// The parse error parsec produces at a top-level *item* position when no
    /// item alternative matches — a faithful reproduction of the merged error
    /// from `addItems`'s `asum` (`Theory/Text/Parser.hs:243-303`) `<* symbol_
    /// "end"`.
    ///
    /// Two shapes, exactly as parsec's longest-match error merging yields:
    ///
    /// * If the next token starts with letters, `formalComment`'s
    ///   `try (many1 letter <* string "{*")` (`Token.hs:377-378`) consumes them
    ///   and is the furthest-reaching alternative, so it dominates: the error
    ///   sits *after* the letters and reads `unexpected <c> / expecting letter
    ///   or "{*"` (the `many1 letter` hangover merged with the `string "{*"`
    ///   expectation).
    /// * Otherwise every alternative fails at the same position, so parsec
    ///   unions all of their leading labels → [`TOP_LEVEL_ITEM_EXPECTS`].
    ///
    /// Residue: the previous item's trailing-optional labels prepend here for
    /// the three sites `item_hangover` tracks (rule `variants`, builtins /
    /// functions commas); hangovers from OTHER items (e.g. a `macros:` body)
    /// are not tracked — those cases match on frame+position+base-list but
    /// omit the leading prefix.
    fn item_position_error(&mut self) -> ParseError {
        self.skip_ws();
        let start = self.save();
        let mut saw_letter = false;
        while self.lx.peek().is_some_and(|c| c.is_alphabetic()) {
            self.lx.bump();
            saw_letter = true;
        }
        if saw_letter {
            let pos = self.lx.pos();
            return ParseError::at(
                pos,
                vec![
                    Message::SysUnExpect(self.unexpected_token()),
                    Message::Expect("letter".to_string()),
                    Message::Expect("\"{*\"".to_string()),
                ],
            );
        }
        self.restore(start);
        let mut e = self.err_expect(TOP_LEVEL_ITEM_EXPECTS);
        // The previous item's trailing optional parsers left their labels at
        // the offset it stopped at; parsec merges them into an error raised
        // there, and `errorMessages`'s stable sort keeps them ahead of this
        // alternation's own (they were accumulated first).  When that item
        // ended in a term (a `macros:` body, an equation's right-hand side),
        // the term's own hangovers ([`Parser::term_carry`]) were accumulated
        // even earlier and render first.
        let mut prefix: Vec<Message> = self.term_carry_labels(e.offset);
        if let Some((at, labels)) = self.item_hangover {
            if at == e.offset {
                prefix.extend(labels.iter().map(|l| Message::Expect((*l).to_string())));
            }
        }
        if !prefix.is_empty() {
            let mut messages = vec![e.messages.remove(0)];
            messages.append(&mut prefix);
            messages.append(&mut e.messages);
            e.messages = messages;
        }
        e
    }

    /// Record the `expecting` labels the item just parsed leaves at the offset
    /// it stopped at (see [`Parser::item_hangover`]).  Called after the trailing
    /// optional parser that produced them, so the current position IS that
    /// offset.
    fn set_item_hangover(&mut self, labels: &'static [&'static str]) {
        self.skip_ws();
        self.item_hangover = Some((self.lx.pos().offset, labels));
    }

    fn save(&self) -> Pos {
        self.lx.pos()
    }
    fn restore(&mut self, p: Pos) {
        self.lx.set_pos(p);
    }

    fn skip_ws(&mut self) {
        self.lx.skip_ws();
    }

    /// parsec `chainl1 p op` (`Text.Parsec.Combinator`): one `operand`, then
    /// as many `op`-then-`operand` pairs as parse, folded left.  `op` consumes
    /// the operator and names it, or returns `None` to end the chain; `build`
    /// turns that name and the two operands into the combined value, standing
    /// for the combining function parsec's `op` yields.
    fn chainl1<T, O>(
        &mut self,
        mut operand: impl FnMut(&mut Self) -> Result<T, ParseError>,
        mut op: impl FnMut(&mut Self) -> Option<O>,
        build: impl Fn(O, T, T) -> T,
    ) -> Result<T, ParseError> {
        let mut lhs = operand(self)?;
        while let Some(o) = op(self) {
            let rhs = operand(self)?;
            lhs = build(o, lhs, rhs);
        }
        Ok(lhs)
    }

    fn at_keyword(&mut self, kw: &str) -> bool {
        // Single non-consuming probe: scan the keyword once, check the
        // trailing-`-` boundary, then always restore.
        let save = self.save();
        if !self.lx.try_symbol(kw) {
            self.restore(save);
            return false;
        }
        // Reject if followed by `-` (e.g. `rule-equivalence` is NOT `rule`).
        let next = self.lx.peek();
        self.restore(save);
        next != Some('-')
    }
    fn try_kw(&mut self, kw: &str) -> bool {
        // Scan the keyword once; consume iff matched and not followed by `-`.
        let save = self.save();
        if !self.lx.try_symbol(kw) {
            self.restore(save);
            return false;
        }
        if self.lx.peek() == Some('-') {
            self.restore(save);
            return false;
        }
        true
    }
    fn require_kw(&mut self, kw: &str) -> Result<(), ParseError> {
        // HS `symbol_ kw` = `void (try (T.symbol spthy kw) <?> ("\""++kw++"\""))`
        // (Token.hs:272-277): on failure, Expect is the quoted keyword.
        if self.try_kw(kw) {
            Ok(())
        } else {
            let label = format!("\"{kw}\"");
            Err(self.err_expect(&[&label]))
        }
    }

    fn require_punct(&mut self, p: &str) -> Result<(), ParseError> {
        self.skip_ws();
        if self.lx.eat_str(p) {
            self.skip_ws();
            Ok(())
        } else {
            // HS `symbol p` labels the failure with the quoted punctuation
            // (Token.hs:272-273).
            let label = format!("\"{p}\"");
            Err(self.err_expect(&[&label]))
        }
    }

    fn try_punct(&mut self, p: &str) -> bool {
        self.skip_ws();
        let save = self.save();
        if self.lx.eat_str(p) {
            self.skip_ws();
            true
        } else {
            self.restore(save);
            false
        }
    }

    /// Non-consuming lookahead for a punctuation token.
    fn peek_punct(&mut self, p: &str) -> bool {
        let save = self.save();
        let m = self.try_punct(p);
        self.restore(save);
        m
    }

    /// Non-consuming lookahead for a term-relational operator that `fatom`'s
    /// term-level atom path handles: `=` (opEqual), `<<`/`⊏` (opSubterm),
    /// `(<)` (opLessTerm), or `<` (opLess). Used to mirror HS `blatom`
    /// (Theory/Text/Parser/Formula.hs:45-57), where Subterm/Less/smallerp/EqE
    /// come before the
    /// bare-fact `Pred` alternative. Guards against the logical operators that
    /// share a prefix: `==>` (opImplies) and `<=>` (opLEquiv) must NOT count as
    /// `=` or `<`, nor must `<-`.
    fn peek_atom_relop(&mut self) -> bool {
        self.skip_ws();
        let r = self.lx.rest();
        if r.starts_with("<<") || r.starts_with('⊏') || r.starts_with("(<)") {
            return true;
        }
        // `=` but not `==`/`=>` (no real `==`/`=>` token, but `==>` is opImplies).
        if let Some(after) = r.strip_prefix('=') {
            return !after.starts_with('=') && !after.starts_with('>');
        }
        // `<` (opLess) but not `<<`/`<=`/`<-` (handled above / opLEquiv / arrow).
        if let Some(after) = r.strip_prefix('<') {
            return !after.starts_with('=') && !after.starts_with('-');
        }
        false
    }

    fn ident(&mut self) -> Result<String, ParseError> {
        if let Some(id) = self.lx.identifier() {
            return Ok(id);
        }
        if let Some(e) = self.err_reserved_word() {
            return Err(e);
        }
        Err(self.err("expected identifier"))
    }

    /// The error HS `T.identifier` (Token.hs:393-394) raises when the token
    /// here is one of the reserved names `["in","let","rule","diff"]`
    /// (Token.hs:214-230, see line 225), or `None` if it is not.
    ///
    /// `identifier = lexeme $ try $ do { name <- ident; if isReservedName name
    /// then unexpected ("reserved word " ++ show name) else return name }`.
    /// `ident`'s trailing `many identLetter` (`alphaNum <|> oneOf "_"`) has
    /// already failed just past the word, leaving an `Expect "letter or digit"`
    /// from `alphaNum`'s label there; `unexpected` adds its `UnExpect` at the
    /// same position, and the lexeme's trailing whitespace never runs — so the
    /// frame sits on the word's last character + 1, and the `UnExpect`
    /// suppresses the `SysUnExpect` when parsec renders it.
    fn err_reserved_word(&mut self) -> Option<ParseError> {
        self.skip_ws();
        let save = self.save();
        let mut word = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphanumeric() => {
                word.push(c);
                self.lx.bump();
            }
            _ => {
                self.restore(save);
                return None;
            }
        }
        while let Some(c) = self.lx.peek() {
            if !is_ident_char(c) {
                break;
            }
            word.push(c);
            self.lx.bump();
        }
        let pos = self.lx.pos();
        self.restore(save);
        if !is_reserved_name(&word) {
            return None;
        }
        Some(ParseError::at(
            pos,
            vec![
                Message::UnExpect(format!("reserved word \"{word}\"")),
                Message::Expect("letter or digit".to_string()),
            ],
        ))
    }

    fn string_literal(&mut self) -> Result<String, ParseError> {
        self.lx
            .string_literal()
            .ok_or_else(|| self.err("expected string literal"))
    }

    // =========================================================================
    // Top-level theory
    // =========================================================================

    pub fn theory(&mut self) -> Result<Theory, ParseError> {
        self.skip_ws();
        // Optional leading `#` directives. Handle them as items inside the body
        // — `theory` keyword must come first.
        self.require_kw("theory")?;
        let name = self.ident()?;
        let mut configuration = None;
        if self.try_kw("configuration") {
            // HS: `symbol "configuration" <* colon` then `stringLiteral <*
            // symbol_ "begin"` (Theory/Text/Parser.hs:238,241); the trailing
            // `begin` here
            // is a plain `symbol_ "begin"`, label `"begin"`.
            self.require_punct(":")?;
            configuration = Some(self.string_literal()?);
            self.require_kw("begin")?;
        } else if !self.try_kw("begin") {
            // HS: `try (symbol "configuration" <* colon) <|> symbol "begin"
            //      <?> "configuration or begin"` (Theory/Text/Parser.hs:230-393,
            // see line 238) — the whole
            // choice is relabelled, so the failure Expect is the single custom
            // label, not the two quoted keywords.
            return Err(self.err_expect(&["configuration or begin"]));
        }
        let items = self.theory_items_until_end()?;
        // HS `addItems … <* symbol_ "end"` (Theory/Text/Parser.hs:230-393, see
        // line 243,245): when `end` is
        // absent the trailing-`end` failure merges with the item alternation's
        // error, so report the full item-position error rather than a bare
        // `expecting "end"`.
        if !self.try_kw("end") {
            return Err(self.item_position_error());
        }
        // Parsing stops at `end`; any trailing text is left unconsumed (callers
        // ignore it), as Haskell's parser does.
        Ok(Theory {
            is_diff: self.is_diff,
            name,
            configuration,
            items,
        })
    }

    /// Parse items until we encounter `end` (top-level) or `#endif` / `#else`.
    fn theory_items_until_end(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        let mut items = Vec::new();
        loop {
            self.skip_ws();
            if self.lx.is_eof() {
                break;
            }
            if self.at_keyword("end") {
                break;
            }
            // Pre-processor: #ifdef, #endif, #else terminate or extend.
            let save = self.save();
            if self.lx.eat_str("#") {
                // peek directive name
                let mut probe = self.lx.clone();
                let buf = probe.ascii_alpha_run();
                let directive = buf.as_str();
                if directive == "endif" || directive == "else" {
                    self.restore(save);
                    break;
                }
                if directive == "include" {
                    // HS `include` (Theory/Text/Parser.hs:328-348): consume the
                    // directive,
                    // resolve the path relative to the including file's dir,
                    // recursively parse the header-less fragment with the SAME
                    // parser state, and SPLICE its items in place (no `Include`
                    // node survives).  Item order = directive position.
                    self.restore(save);
                    let included = self.expand_include()?;
                    items.extend(included);
                    continue;
                }
                if directive == "ifdef" {
                    // HS `ifdef` (Parser.hs): evaluate the flag formula at
                    // parse time and add the live branch's items inline, so
                    // they are ordinary top-level items.  Splice the same way
                    // (no preprocessor node survives; every downstream
                    // consumer of `Theory::items` sees the flat live stream).
                    self.restore(save);
                    let live = self.expand_ifdef()?;
                    items.extend(live);
                    continue;
                }
                self.restore(save);
            }
            let item = self.theory_item()?;
            items.push(item);
        }
        Ok(items)
    }

    fn theory_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.skip_ws();
        // Only the item immediately preceding an item-position error prepends
        // its trailing labels, so each new item starts from a clean slate —
        // but when NO alternative matches, the error position IS the previous
        // item's stop position and its labels apply (offset-gated), so the
        // fallthrough below restores the snapshot.
        let prev_item_hangover = self.item_hangover.take();

        // Try preprocessor directives (start with `#`).
        if let Some(item) = self.try_preproc()? {
            return Ok(item);
        }

        // Try formal comment first (header `{* body *}`)
        let save = self.save();
        if let Some((h, b)) = self.lx.formal_comment() {
            return Ok(TheoryItem::FormalComment { header: h, body: b });
        }
        self.restore(save);

        // Try keyword-led items in priority order.
        if self.at_keyword("builtins") {
            return self.builtins();
        }
        if self.at_keyword("options") {
            return self.options();
        }
        if self.at_keyword("functions") || self.at_keyword("function") {
            return self.functions();
        }
        if self.at_keyword("equations") {
            return self.equations();
        }
        if self.at_keyword("macros") || self.at_keyword("macro") {
            return self.macros();
        }
        if self.at_keyword("predicates") || self.at_keyword("predicate") {
            return self.predicates();
        }
        if self.at_keyword("heuristic") {
            return self.heuristic();
        }
        if self.at_keyword("tactic") {
            return self.tactic();
        }
        if self.at_keyword("restriction") {
            return self.restriction_item();
        }
        if self.at_keyword("axiom") {
            return self.legacy_axiom();
        }
        if self.at_keyword("rule") {
            return self.rule_item();
        }
        if self.at_keyword("lemma") {
            return self.lemma_item();
        }
        if self.at_keyword("diffLemma") {
            return self.diff_lemma_item();
        }
        if self.at_keyword("test") {
            return self.case_test_item();
        }
        if self.at_keyword("equivLemma") {
            return self.equiv_lemma(false);
        }
        if self.at_keyword("diffEquivLemma") {
            return self.equiv_lemma(true);
        }
        if self.at_keyword("export") {
            return self.export_item();
        }
        if self.at_keyword("process") {
            return self.toplevel_process();
        }
        if self.at_keyword("let") {
            return self.process_def();
        }

        // Accountability: `lemma X [accountability_attrs] ...` is matched by lemma_item.
        // A lemmaAcc requires >=1 case-test ident before `accounts for` (HS
        // `commaSep1`, Theory/Text/Parser/Accountability.hs:30-39, see line 36);
        // the zero-ident form falls back to
        // a normal lemma.

        // No item alternative matched: reproduce parsec's merged item-position
        // error (`addItems` `asum` <* `symbol_ "end"`), including the labels
        // the previous item left at exactly this offset.
        self.item_hangover = prev_item_hangover;
        Err(self.item_position_error())
    }

    // -------------------- Preprocessor --------------------

    fn try_preproc(&mut self) -> Result<Option<TheoryItem>, ParseError> {
        let save = self.save();
        self.skip_ws();
        if !self.lx.eat_str("#") {
            self.restore(save);
            return Ok(None);
        }
        // Read directive name.
        let name = self.lx.ascii_alpha_run();
        match name.as_str() {
            "define" => {
                self.skip_ws();
                let id = self.ident()?;
                self.flags.insert(id.clone());
                Ok(Some(TheoryItem::Define(id)))
            }
            "include" => {
                self.skip_ws();
                let path = self.string_literal()?;
                Ok(Some(TheoryItem::Include(path)))
            }
            "endif" | "else" => {
                // Should have been handled by the matching #ifdef. We restore.
                self.restore(save);
                Ok(None)
            }
            other => Err(self.err(format!("unknown preprocessor directive `#{}`", other))),
        }
    }

    /// `#ifdef <flag-formula>` … `[#else …] #endif`: evaluate the condition
    /// against the active flag set and return the LIVE branch's items; the
    /// dead branch's text is skipped without parsing (so a `#define` inside
    /// it never fires).  Mirrors HS `ifdef` (Parser.hs), which evaluates the
    /// formula at parse time and `addItems`-splices the live items inline —
    /// the caller extends the surrounding item stream with the result, so no
    /// preprocessor structure survives in the AST.
    fn expand_ifdef(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        self.skip_ws();
        if !self.lx.eat_str("#") {
            return Err(self.err("expected `#ifdef`"));
        }
        if self.lx.ascii_alpha_run() != "ifdef" {
            return Err(self.err("expected `#ifdef`"));
        }
        self.skip_ws();
        let cond = self.flag_disjuncts()?;
        if self.eval_flagformula(&cond) {
            let items = self.theory_items_until_end()?;
            if self.try_punct("#else") {
                // Else branch text is skipped.
                self.skip_until("#endif");
            } else if !self.try_punct("#endif") {
                return Err(self.err("expected #endif or #else"));
            }
            Ok(items)
        } else {
            // Skip then-branch.
            match self.skip_until_branch_terminator() {
                BranchEnd::Else => {
                    let items = self.theory_items_until_end()?;
                    self.require_punct("#endif")?;
                    Ok(items)
                }
                BranchEnd::Endif => Ok(Vec::new()),
                BranchEnd::Eof => Err(self.err("unterminated #ifdef")),
            }
        }
    }

    /// Expand a `#include "file"` directive at the current position into the
    /// sequence of theory items declared in the referenced file.
    ///
    /// HS `include` (Theory/Text/Parser.hs:323-343):
    /// ```haskell
    /// include inFile0 thy = do
    ///    filepath <- try (symbol "#include") *> filePathParser
    ///    st <- getState
    ///    let (thy', st') = unsafePerformIO (parseFileWState st ... filepath)
    ///    _ <- putState st'
    ///    addItems inFile0 $ set (sigpMaudeSig . thySignature) (sig st') thy'
    ///  where
    ///    filePathParser = case takeDirectory <$> inFile0 of
    ///        Nothing -> doubleQuoted filePath
    ///        Just s  -> (s </>) <$> doubleQuoted filePath
    /// ```
    /// The `#include` token + double-quoted path are consumed here; the path is
    /// resolved against `self.base_dir` (HS `takeDirectory inFile0`); the file
    /// is read and its header-less fragment parsed by [`parse_include_fragment`]
    /// — which threads parser state both ways (signature / known funcs / flags),
    /// matching HS's `getState`/`putState` round-trip and `sig st'` merge.
    fn expand_include(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        // Consume `#include`.
        self.skip_ws();
        if !self.lx.eat_str("#include") {
            return Err(self.err("expected `#include`"));
        }
        self.skip_ws();
        let raw_path = self.string_literal()?;

        // HS `filePathParser`: resolve relative to the including file's dir when
        // we know it (`Just s -> s </> path`), else verbatim (`Nothing`).
        let resolved: PathBuf = match &self.base_dir {
            Some(dir) => dir.join(&raw_path),
            None => PathBuf::from(&raw_path),
        };

        let content = std::fs::read_to_string(&resolved).map_err(|e| {
            self.err(format!(
                "failed to read included file {}: {}",
                resolved.display(),
                e
            ))
        })?;

        // Nested includes in the fragment resolve relative to ITS directory
        // (HS recurses: `takeDirectory filepath`).
        let sub_base = resolved.parent().map(|p| p.to_path_buf());
        self.parse_include_fragment(&content, sub_base)
    }

    /// Parse a header-less theory-item fragment (an included file body — no
    /// `theory … begin … end` wrapper) using a sub-parser that SHARES this
    /// parser's mutable state.
    ///
    /// Mirrors HS `parseFileWState`: the included file is parsed as a
    /// continuation of `addItems` (a plain item sequence terminated by EOF, not
    /// `end`), threading the parser `State` in and back out so that signature
    /// declarations (`functions:`/`builtins:`/`equations:`) and `#define` flags
    /// from the included file are visible to the rest of the parse.
    fn parse_include_fragment(
        &mut self,
        content: &str,
        sub_base: Option<PathBuf>,
    ) -> Result<Vec<TheoryItem>, ParseError> {
        let mut sub = Parser::new(content, &[], self.is_diff);
        // Thread parser state IN (HS `getState` before `parseFileWState`).
        sub.flags = self.flags.clone();
        sub.enable_diff = self.enable_diff;
        sub.ac_fun_syms = self.ac_fun_syms.clone();
        sub.fun_syms = self.fun_syms.clone();
        sub.macro_syms = self.macro_syms.clone();
        sub.reserved_builtin_names = self.reserved_builtin_names.clone();
        sub.sig_enable_dh = self.sig_enable_dh;
        sub.sig_enable_bp = self.sig_enable_bp;
        sub.sig_enable_xor = self.sig_enable_xor;
        sub.sig_enable_mset = self.sig_enable_mset;
        sub.sig_enable_nat = self.sig_enable_nat;
        sub.base_dir = sub_base;
        // The duplicate-rule / duplicate-restriction guards run over the whole
        // accumulated theory (HS: one `addItems` fold spans included files), so
        // the registries thread in and back out with the rest of the state.
        sub.seen_rules = std::mem::take(&mut self.seen_rules);
        sub.seen_restriction_names = std::mem::take(&mut self.seen_restriction_names);
        sub.seen_lemma_names = std::mem::take(&mut self.seen_lemma_names);
        sub.seen_predicates = std::mem::take(&mut self.seen_predicates);

        // Parse the header-less item stream: same loop as a theory body, but it
        // terminates at EOF (there is no `end` keyword in a fragment).
        let items = sub.theory_items_until_end()?;
        sub.skip_ws();
        if !sub.lx.is_eof() {
            return Err(sub.err("unexpected trailing input in included file"));
        }

        // Thread parser state BACK (HS `putState st'` + `sig st'` merge): pick up
        // any new flags and AC function symbols the included file declared.
        self.flags = sub.flags;
        self.enable_diff = sub.enable_diff;
        self.ac_fun_syms = sub.ac_fun_syms;
        self.fun_syms = sub.fun_syms;
        self.macro_syms = sub.macro_syms;
        self.reserved_builtin_names = sub.reserved_builtin_names;
        self.sig_enable_dh = sub.sig_enable_dh;
        self.sig_enable_bp = sub.sig_enable_bp;
        self.sig_enable_xor = sub.sig_enable_xor;
        self.sig_enable_mset = sub.sig_enable_mset;
        self.sig_enable_nat = sub.sig_enable_nat;
        self.seen_rules = sub.seen_rules;
        self.seen_restriction_names = sub.seen_restriction_names;
        self.seen_lemma_names = sub.seen_lemma_names;
        self.seen_predicates = sub.seen_predicates;

        Ok(items)
    }

    fn skip_until(&mut self, terminator: &str) {
        loop {
            self.skip_ws();
            if self.lx.is_eof() {
                return;
            }
            if self.try_punct(terminator) {
                return;
            }
            self.lx.bump();
        }
    }

    fn skip_until_branch_terminator(&mut self) -> BranchEnd {
        let mut depth = 0u32;
        loop {
            self.skip_ws();
            if self.lx.is_eof() {
                return BranchEnd::Eof;
            }
            if self.lx.peek() == Some('#') {
                self.lx.bump();
                let name = self.lx.ascii_alpha_run();
                match name.as_str() {
                    "ifdef" => {
                        depth += 1;
                    }
                    "endif" => {
                        if depth == 0 {
                            return BranchEnd::Endif;
                        }
                        depth -= 1;
                    }
                    "else" if depth == 0 => {
                        return BranchEnd::Else;
                    }
                    _ => {}
                }
            } else {
                self.lx.bump();
            }
        }
    }

    // -------------------- Builtins / options / heuristic / tactic --------------------

    fn builtins(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("builtins")?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            let name = self.hyphen_identifier()?;
            // HS `builtinTheory = asum $ map (try . extendSig) builtinsNames`
            // (Theory/Text/Parser/Signature.hs:139): `extendSig` runs per name,
            // right after its
            // `symbol`, so a conflict is diagnosed against the signature the
            // EARLIER names in the same list already merged, at the position
            // that name's lexeme reached.
            self.enable_builtin(&name)?;
            names.push(name);
            if !self.try_punct(",") {
                break;
            }
        }
        // `commaSep1`'s trailing `comma` (Token.hs:353-355) fails here.
        self.set_item_hangover(&["\",\""]);
        Ok(TheoryItem::Builtins(names))
    }

    /// HS `extendSig` (Theory/Text/Parser/Signature.hs:102-135) for one
    /// `builtins:` name: reject the conflicts it names, then merge the builtin's
    /// `stFunSyms` into [`Parser::fun_syms`] and add its names to
    /// [`Parser::reserved_builtin_names`].
    ///
    /// A name with no `MaudeSig` (`reliable-channel`) takes the second
    /// `extendSig` equation (Theory/Text/Parser/Signature.hs:136-138), which
    /// only consumes the
    /// symbol.  Names outside HS's table are a parse error there and are
    /// accepted-and-ignored here, as elsewhere in this parser.
    ///
    /// `diffbuiltins` (Theory/Text/Parser/Signature.hs:141-148), the parser a
    /// diff theory uses,
    /// merges the signature with neither check and reserves no names.
    fn enable_builtin(&mut self, name: &str) -> Result<(), ParseError> {
        let Some(syms) = builtin_st_fun_syms(name) else {
            return Ok(());
        };
        // The `MaudeSig`s of these names carry only an enable flag
        // (Term/Maude/Signature.hs:200-205); `mappend` ORs it into the
        // signature.  Recorded for both the diff and non-diff builtins parsers,
        // which merge signatures identically
        // (Theory/Text/Parser/Signature.hs:102-148).
        match name {
            "diffie-hellman" => self.sig_enable_dh = true,
            // `maudeSig` sets `enableDH = enableDH || enableBP`
            // (Term/Maude/Signature.hs:110-112).
            "bilinear-pairing" => {
                self.sig_enable_bp = true;
                self.sig_enable_dh = true;
            }
            "xor" => self.sig_enable_xor = true,
            "multiset" => self.sig_enable_mset = true,
            "natural-numbers" => self.sig_enable_nat = true,
            _ => {}
        }
        if !self.is_diff {
            // `functionConflicts` (Theory/Text/Parser/Signature.hs:110-115): a
            // name the builtin
            // brings that the signature already carries at a DIFFERENT options
            // tuple.  `dest-pairing` is exempt — it is expected to replace the
            // seeded `fst`/`snd` constructors with their destructor variants.
            if name != "dest-pairing" {
                // The comprehension pairs every builtin symbol with every
                // signature entry of the same name, so a name carrying two
                // differing entries is listed twice.
                let mut clashes: Vec<&str> = Vec::new();
                for s in syms {
                    let want = FunOptions::of_no_eq(s);
                    for (n, o) in self.fun_syms.iter() {
                        if n.as_bytes() == s.name && *o != want {
                            clashes.push(sym_name(s));
                        }
                    }
                }
                if !clashes.is_empty() {
                    return Err(self.err_fail(format!(
                        "Builtin '{}' conflicts with existing function(s) (same name, \
                         different arity or function options): {}. Please remove these \
                         function definitions or use different names.",
                        name,
                        show_string_list(&clashes)
                    )));
                }
            }
            // `macroConflicts` (Theory/Text/Parser/Signature.hs:117-122): the
            // same test against
            // the macro names, with no `dest-pairing` exemption and with a
            // single `lookup` (first match) per builtin symbol.
            let mut macro_clashes: Vec<&str> = Vec::new();
            for s in syms {
                let want = FunOptions::of_no_eq(s);
                if let Some((_, o)) = self.macro_syms.iter().find(|(n, _)| n.as_bytes() == s.name) {
                    if *o != want {
                        macro_clashes.push(sym_name(s));
                    }
                }
            }
            if !macro_clashes.is_empty() {
                return Err(self.err_fail(format!(
                    "Builtin '{}' conflicts with existing macro '{}'",
                    name,
                    show_string_list(&macro_clashes)
                )));
            }
            self.reserved_builtin_names
                .extend(syms.iter().map(|s| sym_name(s).to_string()));
        }
        // `modifyStateSig (mappend msig)`, whose `unionExceptPairSym`
        // (Term/Maude/Signature.hs:126-146) makes the pair projections
        // exclusive: whichever variant the incoming signature carries evicts
        // the other one.
        for s in syms {
            let fname = sym_name(s);
            if fname == "fst" || fname == "snd" {
                let opts = FunOptions::of_no_eq(s);
                let evicted = FunOptions {
                    destructor: !opts.destructor,
                    ..opts
                };
                Arc::make_mut(&mut self.fun_syms).retain(|(n, o)| !(n == fname && *o == evicted));
            }
            self.insert_fun_sym(fname, FunOptions::of_no_eq(s));
        }
        Ok(())
    }

    /// Insert into [`Parser::fun_syms`] keeping it the ordered set HS's
    /// `S.insert` maintains: ascending by name (raw bytes), then by
    /// [`FunOptions::ord_key`], with equal elements collapsing.
    fn insert_fun_sym(&mut self, name: &str, opts: FunOptions) {
        let key = (name.as_bytes(), opts.ord_key());
        match self
            .fun_syms
            .binary_search_by(|(n, o)| (n.as_bytes(), o.ord_key()).cmp(&key))
        {
            Ok(_) => {}
            Err(idx) => Arc::make_mut(&mut self.fun_syms).insert(idx, (name.to_string(), opts)),
        }
    }

    /// Take the whole parse-time signature from `sig` — HS `mkStateSig`
    /// (Theory/Text/Parser/Token.hs:175-176), the state
    /// `parseIntruderRules` installs before its rules
    /// (Theory/Text/Parser/Rule.hs:223-228).
    ///
    /// It supplies the three tables the term parser reads: the free symbols
    /// `lookupArity` and `nullaryApp` search
    /// (Theory/Text/Parser/Term.hs:62-72,158-163), the `[AC]` names `acterm`
    /// turns into infix operators (Theory/Text/Parser/Term.hs:165-174), and
    /// the macro names both of the first two append.  The theory-level `NoEq`
    /// symbols come with the enable flags, as they do in HS's `funSyms`
    /// (Term/Maude/Signature.hs:110-125).
    pub(crate) fn seed_signature(&mut self, sig: &MaudeSig) {
        Arc::make_mut(&mut self.fun_syms).clear();
        for f in &sig.st_fun_syms {
            self.insert_fun_sym(&String::from_utf8_lossy(f.name), FunOptions::of_no_eq(f));
        }
        self.ac_fun_syms = Arc::new(
            sig.st_ac_fun_syms
                .iter()
                .map(|a| String::from_utf8_lossy(a.name).into_owned())
                .collect(),
        );
        let ac_fun_syms = Arc::make_mut(&mut self.ac_fun_syms);
        ac_fun_syms.sort();
        ac_fun_syms.dedup();
        self.macro_syms = Arc::new(
            sig.macro_names
                .iter()
                .map(|m| {
                    (
                        String::from_utf8_lossy(m.name).into_owned(),
                        FunOptions::of_no_eq(m),
                    )
                })
                .collect(),
        );
        self.sig_enable_dh = sig.enable_dh || sig.enable_bp;
        self.sig_enable_bp = sig.enable_bp;
        self.sig_enable_xor = sig.enable_xor;
        self.sig_enable_mset = sig.enable_mset;
        self.sig_enable_nat = sig.enable_nat;
    }

    /// Copy the symbol state a sub-parser reads from the parser whose text
    /// carried it.  HS runs a nested parse in the enclosing parser's state,
    /// which supplies `acterm` the INFIX spelling of the user-declared `[AC]`
    /// symbols (Theory/Text/Parser/Term.hs:166-172), `nullaryApp` the arity-0
    /// constants (Theory/Text/Parser/Term.hs:158-163) and `diff` its gate.
    fn seed_from(&mut self, parent: &Parser<'_>) {
        self.fun_syms = parent.fun_syms.clone();
        self.ac_fun_syms = parent.ac_fun_syms.clone();
        self.macro_syms = parent.macro_syms.clone();
        self.sig_enable_dh = parent.sig_enable_dh;
        self.sig_enable_bp = parent.sig_enable_bp;
        self.sig_enable_xor = parent.sig_enable_xor;
        self.sig_enable_mset = parent.sig_enable_mset;
        self.sig_enable_nat = parent.sig_enable_nat;
        self.enable_diff = parent.enable_diff;
    }

    /// Whether the lexer sits on the `-` of a hyphenated identifier: a dash
    /// with a letter directly after it.
    fn at_hyphen_join(&self) -> bool {
        if self.lx.peek() != Some('-') {
            return false;
        }
        let mut probe = self.lx.clone();
        probe.bump();
        probe.peek().is_some_and(|c| c.is_alphabetic())
    }

    /// Identifier that may contain hyphens (e.g. `asymmetric-encryption`,
    /// `diffie-hellman`, `dest-pairing`).  Each segment is an
    /// [`Self::ident`], whose lexeme skips the whitespace after it, so a
    /// space may precede a joining dash but never follow one.
    fn hyphen_identifier(&mut self) -> Result<String, ParseError> {
        let mut s = self.ident()?;
        while self.at_hyphen_join() {
            self.lx.bump(); // consume `-`
            s.push('-');
            let id = self.ident()?;
            s.push_str(&id);
        }
        Ok(s)
    }

    fn options(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("options")?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            let mut found = None;
            for option in DeclarableOption::ALL {
                if self.try_kw(option.as_str()) {
                    found = Some(option.as_str().to_string());
                    break;
                }
            }
            let Some(name) = found else {
                let labels: Vec<String> = DeclarableOption::ALL
                    .map(|option| format!("\"{}\"", option.as_str()))
                    .into();
                let expects: Vec<&str> = labels.iter().map(String::as_str).collect();
                return Err(self.err_expect(&expects));
            };
            names.push(name);
            if !self.try_punct(",") {
                break;
            }
        }
        Ok(TheoryItem::Options(names))
    }

    fn heuristic(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("heuristic")?;
        self.require_punct(":")?;
        // Read until newline as raw text. Heuristic rankings are flexible; we
        // take everything up to next newline / `\n` boundary.
        let raw = self.read_to_eol();
        Ok(TheoryItem::Heuristic(raw.trim().to_string()))
    }

    fn read_to_eol(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.lx.peek() {
            if c == '\n' {
                break;
            }
            s.push(c);
            self.lx.bump();
        }
        // Trailing inline comments are left intact; trimming is the consumer's job.
        s
    }

    fn tactic(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("tactic")?;
        self.require_punct(":")?;
        let name = self.ident()?;
        let mut presort = 's';
        if self.try_kw("presort") {
            self.require_punct(":")?;
            let start = self.save();
            let word = self.lx.ascii_alpha_run();
            if word.is_empty() {
                return Err(ParseError::at(
                    start,
                    vec![Message::Expect("letter".to_string())],
                ));
            }
            self.skip_ws();
            let allowed = if self.is_diff { "sScC" } else { "sSpPcCiI" };
            if word.chars().count() != 1 || !allowed.contains(&word) {
                return Err(self.err(format!("unknown proof method ranking `{word}`")));
            }
            presort = word.chars().next().expect("validated presort");
        }

        let mut prios = Vec::new();
        while self.try_kw("prio") {
            prios.push(self.tactic_prio_block()?);
        }
        let mut deprios = Vec::new();
        while self.try_kw("deprio") {
            deprios.push(self.tactic_prio_block()?);
        }
        Ok(TheoryItem::Tactic(Tactic {
            name,
            presort,
            prios,
            deprios,
        }))
    }

    fn tactic_prio_block(&mut self) -> Result<PrioBlock, ParseError> {
        self.require_punct(":")?;
        let ranking = if self.try_punct("{") {
            let ranking = self.ident()?;
            self.require_punct("}")?;
            ranking
        } else {
            "id".to_string()
        };
        let mut selectors = Vec::new();
        loop {
            if self.at_keyword("prio") || self.at_keyword("deprio") || self.at_keyword("presort") {
                break;
            }
            let Some(selector) = self.tactic_disjunction()? else {
                break;
            };
            selectors.push(selector);
        }
        if selectors.is_empty() {
            return Err(self.err("expected at least one tactic selector"));
        }
        Ok(PrioBlock { ranking, selectors })
    }

    fn tactic_disjunction(&mut self) -> Result<Option<SelectorExpr>, ParseError> {
        let Some(mut expr) = self.tactic_conjunction()? else {
            return Ok(None);
        };
        while self.try_punct("|") || self.try_punct("∨") {
            let Some(right) = self.tactic_conjunction()? else {
                return Err(self.err("expected tactic selector after disjunction"));
            };
            expr = SelectorExpr::Or(Box::new(expr), Box::new(right));
        }
        Ok(Some(expr))
    }

    fn tactic_conjunction(&mut self) -> Result<Option<SelectorExpr>, ParseError> {
        let Some(mut expr) = self.tactic_negation()? else {
            return Ok(None);
        };
        while self.try_punct("&") || self.try_punct("∧") {
            let Some(right) = self.tactic_negation()? else {
                return Err(self.err("expected tactic selector after conjunction"));
            };
            expr = SelectorExpr::And(Box::new(expr), Box::new(right));
        }
        Ok(Some(expr))
    }

    fn tactic_negation(&mut self) -> Result<Option<SelectorExpr>, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let Some(expr) = self.tactic_function()? else {
                return Err(self.err("expected tactic selector after negation"));
            };
            Ok(Some(SelectorExpr::Not(Box::new(expr))))
        } else {
            self.tactic_function()
        }
    }

    fn tactic_function(&mut self) -> Result<Option<SelectorExpr>, ParseError> {
        let start = self.save();
        let Some(name) = self.lx.identifier() else {
            self.restore(start);
            return Ok(None);
        };
        let mut params = Vec::new();
        while let Some(param) = self.tactic_function_param() {
            params.push(param);
        }
        if params.is_empty() {
            self.restore(start);
            return Ok(None);
        }
        Ok(Some(SelectorExpr::Leaf(SelectorLeaf { name, params })))
    }

    /// Tactic function values are deliberately not Haskell string literals:
    /// every character except the closing quote is literal, including `\\`.
    fn tactic_function_param(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.save();
        if !self.lx.eat('"') {
            self.restore(start);
            return None;
        }
        let mut param = String::new();
        loop {
            match self.lx.peek() {
                Some('"') => {
                    self.lx.bump();
                    self.skip_ws();
                    return Some(param);
                }
                Some(c) => {
                    param.push(c);
                    self.lx.bump();
                }
                None => {
                    self.restore(start);
                    return None;
                }
            }
        }
    }

    /// Read raw text until we see an identifier at a word boundary that is
    /// one of the recognised top-level keywords, or a `#`-prefixed
    /// preprocessor directive. Used to capture a proof skeleton's raw text.
    fn read_until_next_top_level(&mut self) -> String {
        // NOTE: the top-level `let X = ...` process definition (dispatched by
        // `theory_item`) is deliberately OMITTED here. `let` is overloaded —
        // it also begins `let`-bindings inside rules/processes — and a bare
        // `let` token can never legitimately appear inside the proof-skeleton
        // grammar this scanner captures, so the only effect of
        // adding it would be to risk truncating a capture mid-body. A top-level
        // `let` following a proof block (then needing this stop word) is
        // unattested in the corpus; keep the conservative set.
        const KW: &[&str] = &[
            "end",
            "rule",
            "lemma",
            "diffLemma",
            "restriction",
            "axiom",
            "tactic",
            "heuristic",
            "predicates",
            "predicate",
            "macros",
            "macro",
            "functions",
            "function",
            "equations",
            "builtins",
            "options",
            "process",
            "test",
            "equivLemma",
            "diffEquivLemma",
            "export",
        ];
        let mut s = String::new();
        // Track whether the previous character was an identifier char. If so,
        // we are in the middle of a word and should not match keywords here.
        let mut prev_was_ident = false;
        // Parenthesis-nesting depth of the captured text.  A top-level theory
        // item can only begin at depth 0: HS parses the proof skeleton
        // STRUCTURALLY (`proofMethod = ... solve <$> parens goal`,
        // Theory/Text/Parser/Proof.hs:76-85, see line 80), so the goal inside `solve( ... )`
        // is consumed as a `parens` unit and its interior tokens can never be
        // mistaken for a new top-level item.  Our raw-text scanner reproduces
        // that boundary rule by only testing the top-level-keyword set (`KW`,
        // which contains `test`, `rule`, `function`, `process`, ...) at
        // depth 0.  Without this guard a fact argument named after a keyword —
        // e.g. `solve( Match( test, sid ) @ #i4 )` in
        // examples/ake/bilinear/Scott.spthy — truncates the capture and
        // corrupts the following parse.
        let mut depth: i32 = 0;
        // Whether we are inside a double-quoted string, and must ignore its
        // interior for both paren-depth and keyword purposes.  Tactic filters
        // carry regex literals such as `regex "cp\("` and `regex "In_A\( 'S'"`
        // (examples/csf18-alethea/...): those `(`s are escaped regex text with
        // no matching `)`, so counting them would drive `depth` permanently
        // positive and make the scanner swallow every following item.  HS lexes
        // these as ordinary string literals (`stringLiteral`, Token.hs:366-367), so
        // their content is opaque to the surrounding grammar.  Only `"` needs
        // tracking: proof skeletons contain no double-quoted strings, and
        // single-quoted public constants (`'Init'`) never hold parens and never
        // occur at depth 0, so they need none.
        let mut in_string = false;
        // Whether the identifier at the NEXT depth-0 word boundary is a proof
        // CASE LABEL and must not be tested against `KW`.  HS parses the proof
        // skeleton structurally: `oneCase = symbol "case" *> identifier`
        // (Theory/Text/Parser/Proof.hs:98-115, see line 115; the diff variant is identical,
        // Theory/Text/Parser/Proof.hs:129-146, see line 146), so the token
        // immediately after the `case` keyword is
        // consumed as the case name and can never begin a new top-level item.
        // Case names are drawn from rule names and source-case names, so ANY
        // top-level keyword can legally appear here — e.g. a rule named `test`
        // prints as `case test`, and `test` is itself the CaseTest keyword
        // (`caseTest = CaseTest <$> (symbol "test" *> identifier)`,
        // Theory/Text/Parser/Accountability.hs:25-27, see line 26; dispatched
        // Theory/Text/Parser.hs:230-393, see line 273).
        // Without this suppression the bare `test` at depth 0 truncates the
        // capture and the main parser resumes by consuming `test` as a CaseTest
        // declaration → `expected ':'`.  This is the only in-script position
        // where a bare keyword can sit at depth 0: every proof method is a fixed
        // keyword or `solve( <goal> )` whose goal is paren-nested (depth > 0).
        let mut expect_case_name = false;
        loop {
            if self.lx.is_eof() {
                break;
            }
            if !in_string {
                // Skip whitespace and comments. Block/line comments are entirely
                // skipped by skip_ws; whitespace resets the prev-ident state.
                let pre_ws = self.lx.pos();
                self.lx.skip_ws();
                if self.lx.pos() != pre_ws {
                    // Capture skipped whitespace/comments verbatim.
                    let skipped = &self.lx.src()[pre_ws.offset..self.lx.pos().offset];
                    s.push_str(skipped);
                    prev_was_ident = false;
                }
                if self.lx.is_eof() {
                    break;
                }
                // At a word boundary AND at the top level, check for top-level
                // keywords.  Inside a parenthesised group (`solve( ... )`, a
                // function application, a tuple, ...) keyword identifiers are
                // just terms, matching HS's `parens goal`.
                if depth == 0 && !prev_was_ident {
                    if expect_case_name {
                        // This depth-0 identifier is a case label (see the
                        // `expect_case_name` note above): suppress the keyword /
                        // `#`-directive break for this one token.  The per-char
                        // append below consumes it, and `prev_was_ident` prevents
                        // any re-check mid-word.
                        expect_case_name = false;
                    } else {
                        if let Some(id) = self.peek_hyphen_identifier() {
                            if KW.contains(&id.as_str()) {
                                break;
                            }
                            // Arm case-label suppression for the NEXT identifier.
                            if id == "case" {
                                expect_case_name = true;
                            }
                        }
                        if self.lx.peek() == Some('#') {
                            let mut probe = self.lx.clone();
                            probe.bump();
                            let name = probe.ascii_alpha_run();
                            if matches!(
                                name.as_str(),
                                "ifdef" | "endif" | "else" | "define" | "include"
                            ) {
                                break;
                            }
                        }
                    }
                }
            }
            // Append next char.
            match self.lx.peek() {
                Some(c) if in_string => {
                    // Inside a double-quoted string: consume verbatim, honour
                    // `\`-escapes (so `\"` does not close and `\(` is not a
                    // paren), and close on an unescaped `"`.  Do NOT touch
                    // `depth` — string interiors are opaque.
                    if c == '\\' {
                        s.push(c);
                        self.lx.bump();
                        if let Some(c2) = self.lx.peek() {
                            s.push(c2);
                            self.lx.bump();
                        }
                    } else {
                        if c == '"' {
                            in_string = false;
                        }
                        s.push(c);
                        self.lx.bump();
                    }
                    prev_was_ident = false;
                }
                Some(c) => {
                    prev_was_ident = is_ident_char(c) || c == '-';
                    // Track parenthesis nesting so the keyword scan above only
                    // fires at the top level.  `)` is clamped at 0 so a stray
                    // unbalanced close (should not occur in a well-formed
                    // proof) cannot drive the depth negative and re-enable the
                    // scan inside a group.
                    match c {
                        '"' => in_string = true,
                        '(' => depth += 1,
                        ')' => depth = (depth - 1).max(0),
                        _ => {}
                    }
                    s.push(c);
                    self.lx.bump();
                }
                None => break,
            }
        }
        s
    }

    // -------------------- functions / equations / macros / predicates --------------------

    fn functions(&mut self) -> Result<TheoryItem, ParseError> {
        // `functions:` or `function:`
        if !self.try_kw("functions") {
            self.require_kw("function")?;
        }
        self.require_punct(":")?;
        let mut decls = Vec::new();
        let mut had_attrs;
        loop {
            let (f, attrs) = self.function_decl()?;
            had_attrs = attrs;
            decls.push(f);
            if !self.try_punct(",") {
                break;
            }
        }
        // Two of the last declaration's parsers stopped here without consuming:
        // `option [] $ list functionAttribute`
        // (Theory/Text/Parser/Signature.hs:187), unless it
        // did consume a `[…]`, and `commaSep1`'s trailing `comma`.
        self.set_item_hangover(if had_attrs {
            &["\",\""]
        } else {
            &["\"[\"", "\",\""]
        });
        Ok(TheoryItem::Functions(decls))
    }

    /// Parse `elem (, elem)* ,?` up to (and consuming) the `close` token,
    /// assuming the opening token has already been consumed. Mirrors HS
    /// `commaSep = sepEndBy comma` (Token.hs): the list may be empty and a
    /// single trailing comma before `close` is permitted.
    fn sep_end_by<T>(
        &mut self,
        close: &str,
        mut elem: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        let mut v = Vec::new();
        if !self.try_punct(close) {
            loop {
                v.push(elem(self)?);
                if !self.try_punct(",") {
                    break;
                }
                if self.peek_punct(close) {
                    break;
                }
            }
            if !self.try_punct(close) {
                // `sepEndBy`'s failed `comma` and the closing `symbol` both
                // sit at the element's stop position, merged with whatever
                // hangovers the element itself left there (a term's variable
                // and operator labels, a fact's `"["` annotation attempt) —
                // the frame of Theory/Text/Parser/Fact.hs:47's
                // `parens (commaSep pterm)` and
                // every other `commaSep`-then-close context.
                let close_label = format!("\"{close}\"");
                return Err(self.err_expect_after_term(&["\",\"", &close_label]));
            }
        }
        Ok(v)
    }

    /// The `(arity, options)` HS's `function` finds for `name` in the parse-time
    /// signature: `lookup f (S.toList (stFunSyms sign) ++ S.toList (macroNames
    /// sign))` (Theory/Text/Parser/Signature.hs:212), which takes the FIRST
    /// match — free symbols before macros.
    fn lookup_fun_options(&self, name: &str) -> Option<FunOptions> {
        self.fun_syms
            .iter()
            .chain(self.macro_syms.iter())
            .find(|(n, _)| n == name)
            .map(|(_, o)| *o)
    }

    /// HS `functionType` (Theory/Text/Parser/Signature.hs:150-161): either
    /// `/ <natural>` or a parenthesised argument-type list plus `: <type>`.
    ///
    /// `name_end` is the byte offset just past the function name's identifier
    /// characters.  `T.identifier`'s trailing `many identLetter` fails there and
    /// leaves an `Expect "letter or digit"` (from `alphaNum`, Token.hs:223-224)
    /// on the error parsec carries forward; parsec keeps that message only while
    /// nothing further is consumed, so it is merged into an error raised at
    /// exactly that offset and dropped once trailing whitespace moves past it.
    #[allow(clippy::type_complexity)]
    fn function_type(
        &mut self,
        name_end: usize,
    ) -> Result<(Vec<Option<String>>, Option<String>), ParseError> {
        if self.try_punct("/") {
            // HS `T.natural`, whose `<?> "natural"` is the only label here —
            // `symbol "/"` consumed, so the name's hangover is gone.
            let Some(k) = self.lx.natural() else {
                return Err(self.err_expect(&["natural"]));
            };
            return Ok((vec![None; k as usize], None));
        }
        if !self.try_punct("(") {
            // Both alternatives failed without consuming, so parsec unions their
            // leading labels: `opSlash`'s `symbol_ "/"` (Token.hs:634-635) and
            // `parens`' opening `(`.
            let mut labels: Vec<&str> = Vec::new();
            self.skip_ws();
            if self.lx.pos().offset == name_end {
                labels.push("letter or digit");
            }
            labels.push("\"/\"");
            labels.push("\"(\"");
            return Err(self.err_expect(&labels));
        }
        let args = self.function_arg_types()?;
        self.require_punct(":")?;
        let out_type = self.type_p()?;
        Ok((args, out_type))
    }

    /// HS `parens (commaSep typep)` (Theory/Text/Parser/Signature.hs:158) with
    /// the opening `(` already consumed, reproducing the expectation set parsec
    /// merges at the position where the list stops.
    ///
    /// `commaSep = sepEndBy comma` (Token.hs:354-355) is
    /// `sepEndBy1 p sep <|> return []`, and `sepEndBy1` is
    /// `p >>= \x -> (sep *> sepEndBy p sep) <|> return [x]`.  Every recovery is
    /// an empty alternative, so parsec merges the labels of whichever parser
    /// stopped the list into the error the closing `)` then raises:
    ///
    /// * the element ran and the separator failed → `","`, preceded by the
    ///   element's own `letter or digit` hangover when it ended on an
    ///   identifier and consumed nothing since;
    /// * the element failed (at the start, or right after a `,`) → `typep`'s
    ///   two leading labels, `"Any"` and `identifier`.
    fn function_arg_types(&mut self) -> Result<Vec<Option<String>>, ParseError> {
        let mut args: Vec<Option<String>> = Vec::new();
        // Labels of the parser that ended the list, and the offset of a live
        // identifier hangover (`None` once anything consumed past it).
        let mut hangover: Option<usize>;
        let mid: &[&str];
        match self.type_p_element() {
            None => {
                hangover = None;
                mid = TYPEP_EXPECTS;
            }
            Some((t, h)) => {
                args.push(t);
                hangover = h;
                loop {
                    if !self.try_punct(",") {
                        mid = &["\",\""];
                        break;
                    }
                    match self.type_p_element() {
                        Some((t, h)) => {
                            args.push(t);
                            hangover = h;
                        }
                        None => {
                            hangover = None;
                            mid = TYPEP_EXPECTS;
                            break;
                        }
                    }
                }
            }
        }
        self.skip_ws();
        let mut labels: Vec<&str> = Vec::new();
        if hangover == Some(self.lx.pos().offset) {
            labels.push("letter or digit");
        }
        labels.extend_from_slice(mid);
        labels.push("\")\"");
        if !self.try_punct(")") {
            return Err(self.err_expect(&labels));
        }
        Ok(args)
    }

    /// One `typep` inside an argument list, reporting the byte offset at which
    /// its `letter or digit` hangover sits (see [`Parser::function_type`]).
    ///
    /// `None` is HS's empty failure: neither alternative of
    /// `typep = (try (symbol defaultSapicTypeS) *> return Nothing) <|> Just <$>
    /// identifier` (Token.hs:472-473) consumes on failure, so the caller's
    /// `<|> return []` can recover.  `Any` matches through `symbol`, i.e.
    /// `string` rather than `identifier`, and so leaves no hangover.
    fn type_p_element(&mut self) -> Option<(Option<String>, Option<usize>)> {
        self.skip_ws();
        let start = self.lx.pos().offset;
        let id = self.lx.identifier()?;
        if id == "Any" {
            Some((None, None))
        } else {
            let end = start + id.len();
            Some((Some(id), Some(end)))
        }
    }

    /// One `functions:` entry (HS `function`,
    /// Theory/Text/Parser/Signature.hs:183-225).
    ///
    /// The `bool` of the result records whether the optional attribute list
    /// consumed a `[`; the caller needs it for the item hangover, and the two
    /// `fail`s below need it because parsec merges the `Expect "\"[\""` that
    /// `option [] $ list functionAttribute` leaves behind into them.
    fn function_decl(&mut self) -> Result<(FunctionDecl, bool), ParseError> {
        self.skip_ws();
        let name_start = self.lx.pos().offset;
        let name = self.ident()?;
        let name_end = name_start + name.len();
        let (arg_types, out_type) = self.function_type(name_end)?;
        // Optional attributes `[private, destructor, AC, NDC, NDC-diff, ...]`
        // (HS `option [] $ list functionAttribute`).
        let mut atts = Vec::new();
        let had_attrs = self.try_punct("[");
        if had_attrs {
            loop {
                self.skip_ws();
                let Some(a) = self.function_attribute() else {
                    break;
                };
                atts.push(a);
                if !self.try_punct(",") {
                    break;
                }
            }
            self.require_punct("]")?;
        }
        // HS `function` (Theory/Text/Parser/Signature.hs:183-225) folds the
        // attribute list into one
        // value per property, each defaulting to the "absent" case.
        let private = atts.contains(&FctAttr::Private);
        let destructor = atts.contains(&FctAttr::Destructor);
        let ac = atts.contains(&FctAttr::Ac);
        let ndc = atts.contains(&FctAttr::Ndc);
        let ndc_diff = atts.contains(&FctAttr::NdcDiff);
        let requested = FunOptions {
            arity: arg_types.len(),
            private,
            destructor,
            ndc,
            ndc_diff,
        };
        // Every diagnosis below is a bare `fail` after the attribute list's
        // lexeme, i.e. [`Self::err_fail`] at the post-whitespace position,
        // carrying `option`'s leftover `Expect "\"[\""` when no `[` was there.
        let fail = |p: &mut Self, msg: String| {
            let mut e = p.err_fail(msg);
            if !had_attrs {
                e.messages.push(Message::Expect("\"[\"".to_string()));
            }
            e
        };
        // Check (1), Theory/Text/Parser/Signature.hs:200-209: a name an enabled
        // `builtins:` item
        // reserved must be re-declared at EXACTLY the builtin's options tuple.
        // It runs BEFORE the general conflict check, has no `fst`/`snd`
        // exemption, and consults `stFunSyms` only — never the macro names.
        if self.reserved_builtin_names.contains(&name) {
            let builtin = self
                .fun_syms
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, o)| *o);
            if let Some(b) = builtin.filter(|b| *b != requested) {
                // `conflictingBuiltins` (Theory/Text/Parser/Signature.hs:203)
                // scans the WHOLE
                // static table, not just the builtins this theory enabled.
                let conflicting: Vec<&str> = builtin_st_fun_sym_table()
                    .iter()
                    .filter(|(_, syms)| syms.iter().any(|s| s.name == name.as_bytes()))
                    .map(|(b, _)| *b)
                    .collect();
                return Err(fail(
                    self,
                    format!(
                        "`{}` conflicts with builtin(s) {} (builtin: {}, requested: {})",
                        name,
                        show_string_list(&conflicting),
                        b.show(),
                        requested.show()
                    ),
                ));
            }
        }
        // Check (2), Theory/Text/Parser/Signature.hs:212-217: the general
        // conflict against the
        // parse-time signature, macro names included.
        if let Some(prev) = self.lookup_fun_options(&name) {
            // Theory/Text/Parser/Signature.hs:213: `fst`/`snd` may be
            // re-declared at the pair
            // projections' own shape, tested by name, arity and privacy only.
            let pair_proj = (name == "fst" || name == "snd") && requested.arity == 1 && !private;
            if prev != requested && !pair_proj {
                return Err(fail(
                    self,
                    format!(
                        "conflicting arities/options {} and {} for `{}`. Please choose a \
                         different name for this function.",
                        prev.show(),
                        requested.show(),
                        name
                    ),
                ));
            }
            if name == "fst" || name == "snd" {
                // Theory/Text/Parser/Signature.hs:217-218 returns
                // `NoEqUser (f, kp')`, i.e. the
                // EXISTING symbol's option tuple: the declared argument and
                // result types survive, but privacy, constructability and the
                // NDC state are those of `kp'`, `[AC]` is dropped, the arity
                // check never runs, and nothing is registered.  Discarding the
                // requested attributes is what keeps `functions: fst/1
                // [destructor]` printing as `function: fst (Any) : Any` in the
                // open theory's typing lines (TheoryObject.hs:820-838).
                return Ok((
                    FunctionDecl {
                        name,
                        arg_types,
                        out_type,
                        private: prev.private,
                        destructor: prev.destructor,
                        ac: false,
                        ndc: prev.ndc,
                        ndc_diff: prev.ndc_diff,
                    },
                    had_attrs,
                ));
            }
        }
        if ac {
            // HS rejects a non-binary `[AC]` symbol outright
            // (Theory/Text/Parser/Signature.hs:220)
            // in the `_` case of the conflict check, so check (2) above wins for
            // a name already in the signature.
            if requested.arity != 2 {
                return Err(fail(
                    self,
                    "conflicting arity : AC function must be binary".to_string(),
                ));
            }
            // A binary `[AC]` symbol also becomes an infix operator for the terms
            // that follow, mirroring HS's `modifyStateSig $ addFunSym (ACfctUser
            // ...)`, which likewise runs only in the `IsAC` branch.
            if !self.ac_fun_syms.contains(&name) {
                let names = Arc::make_mut(&mut self.ac_fun_syms);
                names.push(name.clone());
                names.sort();
            }
        } else {
            // HS's `NotAC` branch instead files the symbol under `stFunSyms`
            // (`addFunSym (NoEqUser ...)`, Theory/Text/Parser/Signature.hs:224),
            // a set insert.
            self.insert_fun_sym(&name, requested);
        }
        Ok((
            FunctionDecl {
                name,
                arg_types,
                out_type,
                private,
                destructor,
                ac,
                ndc,
                ndc_diff,
            },
            had_attrs,
        ))
    }

    /// One function attribute inside the `[...]` list.  Port of HS
    /// `functionAttribute` (Theory/Text/Parser/Signature.hs:164-171), whose
    /// alternatives are tried in exactly this order; `None` here is HS's failing
    /// `asum`, which ends the attribute list.
    ///
    /// `NDC-diff` must be tried BEFORE `NDC`: HS's `symbol` has no trailing word
    /// boundary, so `symbol "NDC"` would otherwise swallow the `NDC` of
    /// `NDC-diff` and leave `-diff` behind (hence the `try` in HS).  Here
    /// `try_kw` additionally refuses a keyword followed by `-`, so the order is
    /// belt-and-braces.
    fn function_attribute(&mut self) -> Option<FctAttr> {
        if self.try_kw("private") {
            Some(FctAttr::Private)
        } else if self.try_kw("destructor") {
            Some(FctAttr::Destructor)
        } else if self.try_kw("constructor") {
            Some(FctAttr::Constructor)
        } else if self.try_kw("AC") {
            Some(FctAttr::Ac)
        } else if self.try_kw("NDC-diff") {
            Some(FctAttr::NdcDiff)
        } else if self.try_kw("NDC") {
            Some(FctAttr::Ndc)
        } else {
            None
        }
    }

    /// SAPIC type: `<defaultSapicTypeS>` = `Any` placeholder, or an identifier.
    fn type_p(&mut self) -> Result<Option<String>, ParseError> {
        // HS `typep` (Token.hs:472-473): `(try (symbol defaultSapicTypeS) *>
        // return Nothing) <|> Just <$> identifier`, where `defaultSapicTypeS =
        // "Any"` (Theory/Sapic/Term.hs:94-95, see line 95). Only the literal `Any`
        // (case-sensitive) is the default placeholder; everything else is
        // `Just <ident>` — so lowercase `any` is `Just "any"`, and `*` is not a
        // valid identifier (a parse failure, matching HS).
        match self.type_p_element() {
            Some((t, _)) => Ok(t),
            None => Err(self.err_expect(TYPEP_EXPECTS)),
        }
    }

    fn equations(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("equations")?;
        // HS `equations` (Theory/Text/Parser/Signature.hs:234-239): `convergent`
        // is set only when
        // the literal `[convergent]` is present (`brackets (symbol "convergent")`);
        // an empty `[]` makes the `try` block fail (convergent=False) and the
        // subsequent `symbol "equations" *> colon` then errors on the `[`. So the
        // `convergent` keyword is required inside the brackets here.
        let convergent = if self.try_punct("[") {
            self.require_kw("convergent")?;
            self.require_punct("]")?;
            true
        } else {
            false
        };
        self.require_punct(":")?;
        let mut eqs = Vec::new();
        loop {
            // HS `equation` (Theory/Text/Parser/Signature.hs:245-246) parses both
            // operands with
            // `acterm True llitNoPub`. The `True` (eqn flag) gates multiset/
            // nat/xor/mult/exp operators (but NOT the user-defined AC operators
            // of `acterm`) — matched here by `acterm(true)`, which is what
            // `term(true)` reduces to anyway once those gates are closed.
            // `llitNoPub` (Theory/Text/Parser/Term.hs:57-58 = `asum [freshTerm
            // <$> freshName,
            // varTerm <$> msgvar]`) additionally forbids public-name literals
            // `'foo'` and nat literals `%'n'` in operands, while still allowing
            // fresh literals `~'n'` and all msgvar-sort variables (including `$x`
            // pub-sort vars, since `msgvar = sortedLVar [Fresh,Pub,Nat,Msg]`).
            // We deliberately use the public-name-allowing `acterm(true)` here:
            // accepting `'foo'`/`%'n'` is benign parser-level leniency — such
            // public/nat names are invalid in (convergent) equations and are
            // rejected during elaboration, so end-to-end `--prove` output is
            // unchanged on all valid theories.
            let lhs = self.acterm(true)?;
            // `equalSign`'s `symbol "="` merges the left operand's hangovers
            // when it fails — the frame of an arity-mismatched application
            // that backtracked to a variable (`g(x) = x` for `g/2`).
            if !self.try_punct("=") {
                return Err(self.err_expect_after_term(&["\"=\""]));
            }
            let rhs = self.acterm(true)?;
            eqs.push(Equation { lhs, rhs });
            if !self.try_punct(",") {
                break;
            }
        }
        // `commaSep1`'s trailing `comma` fails at the last right-hand side's
        // stop position, ahead of the next item's labels.
        self.set_item_hangover(&["\",\""]);
        Ok(TheoryItem::Equations { convergent, eqs })
    }

    fn macros(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("macros") {
            self.require_kw("macro")?;
        }
        self.require_punct(":")?;
        let mut ms = Vec::new();
        loop {
            let name = self.ident()?;
            // HS `when (BC.unpack op `elem` reservedBuiltins) $ error …`
            // (Theory/Text/Parser/Macro.hs:34-35): a GHC `error`, raised right
            // after the
            // identifier and BEFORE the arguments, so it wins over every later
            // failure in the macro — including a malformed argument list, and
            // the name conflict below that an enabled owning theory would
            // otherwise raise.  Independent of which builtins are enabled.
            if Self::RESERVED_BUILTINS.contains(&name.as_str()) {
                return Err(self.macro_reserved_name_error(&name));
            }
            self.require_punct("(")?;
            // HS `parens $ commaSep lvar` (Theory/Text/Parser/Macro.hs:29-49, see
            // line 36): trailing comma OK.
            let args = self.sep_end_by(")", |p| p.var_spec())?;
            // HS `unless (length args == length (nub args)) $ error …`
            // (Theory/Text/Parser/Macro.hs:37-38), the second GHC `error`: `nub`
            // compares FULL
            // `LVar`s, so name, sort and index all count — `m(x, x:pub)` and
            // `m(x.1, x)` pass, `m(x, x)` and `m(x, x:msg)` do not (a
            // prefixless binder is `LSortMsg`, Token.hs:424-433).
            if Self::has_duplicate_macro_arg(&args) {
                return Err(self.macro_duplicate_arg_error(&name));
            }
            self.require_punct("=")?;
            let body = self.term(false)?;
            // HS `macro` rejects a name the signature already carries
            // (Theory/Text/Parser/Macro.hs:43-44): `op elem map extractName
            // (S.toList
            // (userDefinedFunSyms sign) ++ map NoEqUser (S.toList (macroNames
            // sign)))` — the subterm symbols plus the enabled theories' `NoEq`
            // symbols (`noEqFunSyms`, Term/Maude/Signature.hs:157-164), the
            // user-declared `[AC]` symbols (`acUserFunSyms`), and every macro
            // registered so far (including earlier in this very `macros:`
            // list).  The check runs AFTER the body parse, so a body parse
            // error wins over the conflict.
            if self.macro_name_conflicts(&name) {
                return Err(self.macro_conflict_error(&name));
            }
            // HS `macro` registers the name under `macroNames` as
            // `(k, Private, Destructor, NotNDC)`
            // (Theory/Text/Parser/Macro.hs:46), which
            // `function`'s conflict check then sees
            // (Theory/Text/Parser/Signature.hs:212).
            Arc::make_mut(&mut self.macro_syms).push((
                name.clone(),
                FunOptions {
                    arity: args.len(),
                    private: true,
                    destructor: true,
                    ndc: false,
                    ndc_diff: false,
                },
            ));
            ms.push(Macro { name, args, body });
            if !self.try_punct(",") {
                break;
            }
        }
        // `commaSep`'s trailing `comma` fails at the last body's stop
        // position, ahead of the next item's labels — together with the
        // body term's own hangovers (see [`Parser::term_carry`]).
        self.set_item_hangover(&["\",\""]);
        Ok(TheoryItem::Macros(ms))
    }

    /// HS `reservedBuiltins` (Theory/Text/Parser/Term.hs:74-85) in its order:
    /// the builtin symbol names no macro may take, whatever the theory
    /// declares (values at Term/Term/FunctionSymbols.hs:221-243).
    const RESERVED_BUILTINS: &'static [&'static str] = &[
        "mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor",
    ];

    /// The package id GHC stamps into the `HasCallStack` frame of the `error`s
    /// `macro` raises, as the pinned oracle build prints it.  Refreshed at a
    /// submodule bump together with [`Self::MACRO_RESERVED_NAME_SITE`] and
    /// [`Self::MACRO_DUPLICATE_ARG_SITE`].
    const MACRO_ERROR_PACKAGE: &'static str = "tamarin-prover-theory-1.13.0-8wixYaxm5uHCGl2uEzaKzP";

    /// `LINE:COLUMN` of the reserved-name `error` in
    /// `src/Theory/Text/Parser/Macro.hs` — see [`Self::MACRO_ERROR_PACKAGE`].
    const MACRO_RESERVED_NAME_SITE: &'static str = "35:15";

    /// `LINE:COLUMN` of the duplicate-argument `error` in
    /// `src/Theory/Text/Parser/Macro.hs` — see [`Self::MACRO_ERROR_PACKAGE`].
    const MACRO_DUPLICATE_ARG_SITE: &'static str = "38:15";

    /// The `error, called at <…>` location the `HasCallStack` frame of
    /// `macro`'s `error` at `Macro.hs:<site>` names.
    fn macro_error_call_site(site: &str) -> String {
        format!(
            "src/Theory/Text/Parser/Macro.hs:{site} in {}:Theory.Text.Parser.Macro",
            Self::MACRO_ERROR_PACKAGE
        )
    }

    /// The `error` of Theory/Text/Parser/Macro.hs:34-35 — see [`Self::macros`].
    /// Its message is
    /// the macro name inside backticks, followed by " is a reserved function
    /// name for builtins."; `op` is a `ByteString`, so the `show op` HS
    /// interpolates wraps it in its own double quotes INSIDE those backticks.
    /// A macro name is a plain identifier, so it needs no escaping.
    fn macro_reserved_name_error(&self, name: &str) -> ParseError {
        self.err_ghc(
            format!("`\"{name}\"` is a reserved function name for builtins."),
            Self::macro_error_call_site(Self::MACRO_RESERVED_NAME_SITE),
        )
    }

    /// HS `error $ show op ++ " have two arguments with the same name."`
    /// (Theory/Text/Parser/Macro.hs:37-38) — see [`Self::macros`].  `show` on the
    /// `ByteString`
    /// name supplies the double quotes.
    fn macro_duplicate_arg_error(&self, name: &str) -> ParseError {
        self.err_ghc(
            format!("\"{name}\" have two arguments with the same name."),
            Self::macro_error_call_site(Self::MACRO_DUPLICATE_ARG_SITE),
        )
    }

    /// HS `length args /= length (nub args)`
    /// (Theory/Text/Parser/Macro.hs:37): `nub`'s `Eq LVar`
    /// compares name, sort and index together (LTerm.hs:541-542), so two
    /// arguments collide only when all three agree.  The sort is the one
    /// `lvar` gave the argument (Token.hs:409-437): an explicit prefix or
    /// suffix names it, a prefixless binder is `LSortMsg`.
    fn has_duplicate_macro_arg(args: &[VarSpec]) -> bool {
        let mut seen: Vec<(&str, u64, LSort)> = Vec::with_capacity(args.len());
        for a in args {
            let key = (a.name.as_str(), a.idx, a.sort);
            if seen.contains(&key) {
                return true;
            }
            seen.push(key);
        }
        false
    }

    /// The macro-name membership test of Theory/Text/Parser/Macro.hs:43 — see
    /// [`Self::macros`].
    /// `extractName` (Theory/Text/Parser/Macro.hs:49-50) drops the options, so
    /// only names
    /// compare; the reserved builtin names (`mun`, `em`, …) are NOT part of
    /// this set unless a theory flag contributes them (a macro so named never
    /// reaches this check — the reserved-name `error` at
    /// Theory/Text/Parser/Macro.hs:34-35 fires
    /// first).
    fn macro_name_conflicts(&self, name: &str) -> bool {
        self.fun_syms.iter().any(|(n, _)| n == name)
            || self.ac_fun_syms.iter().any(|n| n == name)
            || self.macro_syms.iter().any(|(n, _)| n == name)
            || self
                .enabled_theory_noeq_syms()
                .any(|s| s.name == name.as_bytes())
    }

    /// The parse error HS's `fail $ "Conflicting name for macro " ++ op`
    /// (Theory/Text/Parser/Macro.hs:44) surfaces: a `Message` at the position
    /// after the macro
    /// body, merged with the `expecting` labels the body parse left there —
    /// the pending `.`-index attempt of a trailing bare variable
    /// ([`Parser::var_dot_hangover`]) and one label per operator continuation
    /// an enabled `chainl1` level tried, innermost first
    /// (Theory/Text/Parser/Term.hs:176-208):
    /// the user AC symbols in reverse `stACFunSyms` order, then `^` `*`
    /// (`multterm`/`expterm`, DH), `XOR` `⊕` (`xorterm`, both `opXor`
    /// alternatives, Token.hs:555-556), `%+` (`natterm`), and `++` `+`
    /// (`msetterm`, both `opUnion` alternatives, Token.hs:551-552).
    fn macro_conflict_error(&mut self, name: &str) -> ParseError {
        let mut e = self.err_fail(format!("Conflicting name for macro {name}"));
        let mut expects: Vec<Message> = Vec::new();
        if self.var_dot_hangover {
            expects.push(Message::Expect("\".\"".to_string()));
        }
        for sym in self.ac_fun_syms.iter().rev() {
            expects.push(Message::Expect(format!("\"{sym}\"")));
        }
        let mut ops: Vec<&str> = Vec::new();
        if self.sig_enable_dh {
            ops.extend(["^", "*"]);
        }
        if self.sig_enable_xor {
            ops.extend(["XOR", "⊕"]);
        }
        if self.sig_enable_nat {
            ops.push("%+");
        }
        if self.sig_enable_mset {
            ops.extend(["++", "+"]);
        }
        expects.extend(ops.into_iter().map(|o| Message::Expect(format!("\"{o}\""))));
        // `Display` stable-sorts by constructor rank, so appending keeps the
        // `Expect`s ahead of the raw `Message` and in accumulation order.
        e.messages.extend(expects);
        e
    }

    fn predicates(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("predicates") {
            self.require_kw("predicate")?;
        }
        self.require_punct(":")?;
        let mut ps = Vec::new();
        loop {
            // HS `predicate … <?> "predicate declaration"`
            // (Theory/Text/Parser/Signature.hs:270-275):
            // `labels` rewrites a NON-consuming failure, dropping its `Expect`s
            // for the label and keeping `UnExpect`/`Message`.  Only the leading
            // `fact' lvar` can fail without consuming, and this port signals
            // that by leaving the position where the element started.
            let start = self.save();
            let f = self.fact().map_err(|mut e| {
                if self.save() == start {
                    e.messages.retain(|m| !matches!(m, Message::Expect(_)));
                    e.messages
                        .push(Message::Expect("predicate declaration".to_string()));
                }
                e
            })?;
            self.require_punct("<=>")?;
            let phi = self.formula()?;
            ps.push(Predicate {
                fact: f,
                formula: phi,
            });
            if !self.try_punct(",") {
                break;
            }
        }
        // HS folds `liftedAddPredicate` over the block AFTER `commaSep1`
        // collected every declaration (Theory/Text/Parser/Signature.hs:278-284),
        // so a collision — against an earlier block, the builtin `Smaller/2`,
        // or an earlier declaration of the same block — fails at the position
        // past the whole block, where the last formula's pending labels still
        // stand.
        for p in &ps {
            let key = (p.fact.persistent, p.fact.name.clone(), p.fact.args.len());
            if self.seen_predicates.contains(&key) {
                return Err(self.predicate_dup_fail(&p.fact));
            }
            self.seen_predicates.push(key);
        }
        Ok(TheoryItem::Predicates(ps))
    }

    /// The `duplicate predicate: <fact>` failure `liftedAddPredicate` raises
    /// (Theory/Text/Parser/Signature.hs:328-331, message rendered by
    /// Theory/Text/Parser/Exceptions.hs:43 as `prettyFact prettyLVar`): a
    /// consumed `fail` at the position past the `predicates:` block, merging
    /// the labels standing there — the last term's carried hangovers (or the
    /// bare dot-index attempt of a trailing timepoint variable, which ends no
    /// term chain), then the formula operator levels
    /// (Theory/Text/Parser/Formula.hs:82-104) and `commaSep1`'s `","`.
    fn predicate_dup_fail(&mut self, fact: &Fact) -> ParseError {
        let mut e = self.err_fail(format!("duplicate predicate: {}", pred_fact_text(fact)));
        let mut labels = self.term_carry_labels(e.offset);
        if labels.is_empty() && self.var_dot_hangover {
            // The dot-index attempt stands at the failure position only when
            // the variable was the last token consumed — a later lexeme (a
            // closing `)`, a fact's annotation bracket) moves the parse past
            // it and drops the label.
            let since_var = self
                .var_hangover_ident_end
                .map(|ie| &self.lx.src()[ie..e.offset]);
            if since_var.is_some_and(|s| remove_comments(s).chars().all(char::is_whitespace)) {
                labels.push(Message::Expect("\".\"".to_string()));
            }
        }
        for l in [
            "\"&\"", "\"∧\"", "\"|\"", "\"∨\"", "\"==>\"", "\"⇒\"", "\"<=>\"", "\"⇔\"", "\",\"",
        ] {
            labels.push(Message::Expect(l.to_string()));
        }
        for (k, l) in labels.into_iter().enumerate() {
            e.messages.insert(1 + k, l);
        }
        e
    }

    // -------------------- Restriction / axiom --------------------

    fn restriction_item(&mut self) -> Result<TheoryItem, ParseError> {
        let r = self.restriction("restriction")?;
        Ok(TheoryItem::Restriction(r))
    }

    fn legacy_axiom(&mut self) -> Result<TheoryItem, ParseError> {
        let r = self.restriction("axiom")?;
        // HS `legacyAxiom` builds the restriction through
        // `trace "Deprecation Warning: ..." Restriction <$> ...`
        // (Theory/Text/Parser/Restriction.hs:88-92).  The traced value is a
        // shared CAF, so the message reaches stderr at most once per process,
        // and it is only forced once a COMPLETE `axiom` item has been built —
        // an axiom whose formula fails to parse prints nothing.
        static AXIOM_DEPRECATION: std::sync::Once = std::sync::Once::new();
        AXIOM_DEPRECATION.call_once(|| {
            eprintln!(
                "Deprecation Warning: using 'axiom' is retired notation, replace all uses of \
                 'axiom' by 'restriction'."
            );
        });
        Ok(TheoryItem::LegacyAxiom(r))
    }

    fn restriction(&mut self, kw: &str) -> Result<Restriction, ParseError> {
        self.require_kw(kw)?;
        let name = self.ident()?;
        let mut attributes = Vec::new();
        if self.try_punct("[") {
            loop {
                self.skip_ws();
                if self.try_kw("left") {
                    attributes.push(RestrictionAttr::LeftRestriction);
                } else if self.try_kw("right") {
                    attributes.push(RestrictionAttr::RightRestriction);
                } else {
                    break;
                }
                if !self.try_punct(",") {
                    break;
                }
            }
            self.require_punct("]")?;
        }
        self.require_punct(":")?;
        let phi = self.double_quoted_formula()?;
        // HS `liftedAddRestriction` (Theory/Text/Parser.hs:129-134) runs
        // `addRestriction`'s name guard (TheoryObject.hs:453-456) on each
        // parsed `restriction`/`axiom` item.  The closing quote's lexeme left
        // no pending labels, so the frame is bare (`unexpected <tok>` plus the
        // message).  A left/right attribute marks the diff-theory shape, which
        // HS's plain `restriction` production cannot even read
        // (Theory/Text/Parser/Restriction.hs:77-80) and its diff parse routes
        // through `liftedAddRestriction'` (Theory/Text/Parser.hs:433-435,546),
        // splitting the sides instead of comparing names; the guard leaves
        // those items, and every item of a diff parse, alone.
        if !self.is_diff && attributes.is_empty() && self.seen_restriction_names.contains(&name) {
            return Err(self.item_fail(format!("duplicate restriction: {name}")));
        }
        // Feed the restriction-name set the `_restrict` guard consults
        // ([`Parser::guard_duplicate_rule`] step 1): HS `addRestriction`
        // checks new `Restr_<rule>_<i>` names against ALL restrictions,
        // user-declared ones included (TheoryObject.hs:453-456).
        self.seen_restriction_names.push(name.clone());
        Ok(Restriction {
            name,
            formula: phi,
            attributes,
        })
    }

    /// Parse a formula between literal `"` and `"`. Whitespace and comments
    /// inside (including `/* ... */` blocks containing `"`) are handled by
    /// the normal lexer's `skip_ws`. This matches Haskell's
    /// `doubleQuoted parseFormula` rather than reading a string literal and
    /// re-parsing it.
    fn double_quoted_formula(&mut self) -> Result<Formula, ParseError> {
        self.require_punct("\"")?;
        let f = self.formula()?;
        if !self.try_punct("\"") {
            return Err(self.formula_close_error());
        }
        Ok(f)
    }

    /// The frame `doubleQuoted (standardFormula …)`'s closing `symbol "\""`
    /// produces when leftover input follows a complete formula: the operator
    /// attempts of every formula level fail at the same position on the way
    /// out — `chainl1 … opLAnd` / `opLOr`
    /// (Theory/Text/Parser/Formula.hs:82-89), `imp`'s
    /// `opImplies` and `iff`'s `opLEquiv`
    /// (Theory/Text/Parser/Formula.hs:92-104), each `symbol`
    /// leaving both of its spellings' labels — followed by the quote itself.
    /// When the formula's last atom was a fact whose annotation list was
    /// absent, its `Expect "\"[\""` (Theory/Text/Parser/Fact.hs:48) sits at the
    /// same position
    /// and was accumulated first.
    fn formula_close_error(&mut self) -> ParseError {
        self.skip_ws();
        let pos = self.lx.pos();
        let mut messages = vec![Message::SysUnExpect(self.unexpected_token())];
        if self.fact_annot_hangover == Some(pos.offset) {
            messages.push(Message::Expect("\"[\"".to_string()));
        }
        for l in [
            "\"&\"", "\"∧\"", "\"|\"", "\"∨\"", "\"==>\"", "\"⇒\"", "\"<=>\"", "\"⇔\"", "\"\"\"",
        ] {
            messages.push(Message::Expect(l.to_string()));
        }
        ParseError::at(pos, messages)
    }

    // -------------------- Rule --------------------

    fn rule_item(&mut self) -> Result<TheoryItem, ParseError> {
        // We must distinguish protocol rules from intruder rules. Intruder
        // rules use `rule (modulo AC) name: ...` — they live in the top-level
        // theory only when explicitly parsed (e.g. for a precomputed intruder
        // file).
        let r = self.parse_rule()?;
        // Dispatch on the `(modulo AC)` head alone.  Intruder-rule names
        // conventionally start with `c` or `d` (HS `intrInfo`,
        // Theory/Text/Parser/Rule.hs:163-172, see line 171,172), but that prefix
        // is not tested
        // here — the `c`/`d` split happens when the caller translates the
        // parser rule into an `IntrRuleAC`.
        if r.modulo.as_deref() == Some("AC") {
            Ok(TheoryItem::IntrRule(r))
        } else {
            // HS `addItems`'s rule alternative runs `liftedAddProtoRule` on
            // each parsed rule (Theory/Text/Parser.hs:283-285) — intruder
            // rules instead go through `addIntrRuleACs`, which `nub`-appends
            // without any name guard (OpenTheory.hs:751-753).
            self.guard_duplicate_rule(&r)?;
            Ok(TheoryItem::Rule(r))
        }
    }

    /// The name guards HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193)
    /// runs after each protocol rule parses, in HS's order:
    ///
    ///   1. each `_restrict` formula's minted `Restr_<rule>_<i>` restriction is
    ///      added first — `addRestriction` fails if a restriction with that
    ///      NAME already exists (TheoryObject.hs:453-456), so a second
    ///      `_restrict`-carrying rule with a reused name dies here
    ///      (`duplicate restriction: Restr_<rule>_1`) even when it is
    ///      byte-identical to the first;
    ///   2. then the rule itself — `addOpenProtoRule` (OpenTheory.hs:691-702)
    ///      fails only when the name is already bound to a DIFFERENT rule
    ///      (`maybe True (ru ==) $ lookupOpenProtoRule …`); an identical
    ///      duplicate passes the guard and is appended AGAIN (both copies
    ///      render), which the corpus relies on (e.g.
    ///      examples/asiaccs20-POIDC/OIDC_CodeFlow_with_ClientSecret.spthy).
    ///
    /// Both failures are `throwM` → `fail (show e)` (Token.hs:210-211) with
    /// `show (DuplicateItem …)` (Parser/Exceptions.hs:38-40), i.e. an ordinary
    /// parsec `fail` at the position where the parser stands after the rule —
    /// merging the rule's trailing `option [] $ symbol "variants" …` label
    /// exactly as [`Parser::item_hangover`] records it.
    ///
    /// Diff mode is exempt: diff theories route rules through
    /// `liftedAddDiffRule`/`addDiffRule` with a different message
    /// (`"duplicate rule or inconsistent names: …"`,
    /// Theory/Text/Parser.hs:520-522), which
    /// this port does not implement.
    ///
    /// Equality is on the parsed AST minus the `(modulo E)` head, which HS
    /// discards at parse time (`optional moduloE`, Parser/Rule.hs:100-104).
    /// HS compares rules after `liftedAddProtoRule` has appended the minted
    /// `Restr_*` actions; two same-name rules that both carry an embedded
    /// restriction die at the restriction guard above before this comparison
    /// runs, and a rule with none has no action to append, so the two
    /// comparisons agree.
    fn guard_duplicate_rule(&mut self, r: &Rule) -> Result<(), ParseError> {
        if self.is_diff {
            return Ok(());
        }
        for i in 1..=r.embedded_restrictions.len() {
            // HS `fromRuleRestriction (rname ++ "_" ++ show i)` with
            // `restrPrefix = "Restr_"` (Model/Restriction.hs:129-149).
            let rstr_name = format!("Restr_{}_{}", r.name, i);
            if self.seen_restriction_names.contains(&rstr_name) {
                return Err(self.item_fail(format!("duplicate restriction: {rstr_name}")));
            }
        }
        if let Some(first) = self.seen_rules.iter().find(|p| p.name == r.name) {
            let differs = first.attributes != r.attributes
                || first.premises != r.premises
                || first.actions != r.actions
                || first.conclusions != r.conclusions
                || first.embedded_restrictions != r.embedded_restrictions
                || first.variants != r.variants
                || first.left_right != r.left_right;
            if differs {
                // `"duplicate rule: " ++ render (prettyRuleName …)`
                // (Theory/Text/Parser/Exceptions.hs:38).  `prettyProtoRuleName` is
                // `prefixIfReserved` (Model/Rule.hs:1287-1290), which only
                // rewrites reserved names / leading `_` — both unreachable
                // here (`protoRule` rejects reserved rule names and
                // identifiers cannot start with `_`), so the name is verbatim.
                return Err(self.item_fail(format!("duplicate rule: {}", r.name)));
            }
        } else {
            self.seen_rules.push(r.clone());
        }
        for i in 1..=r.embedded_restrictions.len() {
            self.seen_restriction_names
                .push(format!("Restr_{}_{}", r.name, i));
        }
        Ok(())
    }

    /// A parsec `fail` raised at the position an item's parse just finished,
    /// merging the trailing-optional `expecting` labels the item left there
    /// ([`Parser::item_hangover`]) — for a protocol rule, `"variants"`.  The
    /// frame reads `unexpected <tok> / expecting "variants" / <msg>`, matching
    /// the oracle byte-for-byte for the duplicate-rule/-restriction guards.
    fn item_fail(&mut self, msg: String) -> ParseError {
        let mut e = self.err_fail(msg);
        if let Some((at, labels)) = self.item_hangover {
            if at == e.offset {
                for (k, l) in labels.iter().enumerate() {
                    e.messages.insert(1 + k, Message::Expect((*l).to_string()));
                }
            }
        }
        e
    }

    /// Parse the middle arrow of a rule: either the `-->` shortcut (no
    /// actions/restrictions) or `--[ .. ]->` with a `fact_or_restr` loop
    /// splitting action Facts from embedded Restrs, allowing a trailing comma
    /// before `]->` (HS `commaSep` = `sepEndBy comma`,
    /// Theory/Text/Parser/Rule.hs:205-213, see line 210).
    fn parse_actions_and_restrictions(&mut self) -> Result<(Vec<Fact>, Vec<Formula>), ParseError> {
        if self.try_punct("-->") {
            return Ok((vec![], vec![]));
        }
        self.require_punct("--[")?;
        self.parse_action_restr_list()
    }

    /// Parse the `--[ ... ]->` action/restriction body up to (and consuming)
    /// the `]->` terminator, assuming `--[` has already been consumed. Facts
    /// become actions and `_restrict(..)` become restrictions; a trailing comma
    /// before `]->` is permitted (HS `commaSep`,
    /// Theory/Text/Parser/Rule.hs:205-213, see line 210).
    fn parse_action_restr_list(&mut self) -> Result<(Vec<Fact>, Vec<Formula>), ParseError> {
        let mut acts = Vec::new();
        let mut rstrs = Vec::new();
        if !self.try_punct("]->") {
            loop {
                match self.fact_or_restr()? {
                    FactOrRestr::Fact(f) => acts.push(f),
                    FactOrRestr::Restr(phi) => rstrs.push(phi),
                }
                if !self.try_punct(",") {
                    break;
                }
                if self.peek_punct("]->") {
                    break;
                }
            }
            self.require_punct("]->")?;
        }
        Ok((acts, rstrs))
    }

    /// Parse a SAPIC channel-message argument list (shared by `in`/`out`):
    /// `(msg)` yields `(None, msg)`, `(chan, msg)` yields `(Some(chan), msg)`.
    fn parse_chan_msg(&mut self) -> Result<(Option<Term>, Term), ParseError> {
        self.require_punct("(")?;
        // Either `(msg)` or `(chan, msg)`
        let first = self.term(false)?;
        if self.try_punct(",") {
            let snd = self.term(false)?;
            self.require_punct(")")?;
            Ok((Some(first), snd))
        } else {
            self.require_punct(")")?;
            Ok((None, first))
        }
    }

    /// The `in(...)` argument list.  Unlike [`Parser::parse_chan_msg`], the
    /// MESSAGE term takes `=v` patterns and the channel does not, so the two
    /// HS alternatives (Parser/Sapic.hs:96-116) cannot fold into one parse:
    /// `try` the one-argument `(msg)` form with pattern literals first, then
    /// `(chan, msg)` with a plain channel.  When both fail, the errors merge
    /// parsec-style ([`Parser::merge_alt_errors`]).
    fn parse_in_chan_msg(&mut self) -> Result<(Option<Term>, Term), ParseError> {
        self.require_punct("(")?;
        let probe = self.save();
        let e1 = match (|| -> Result<Term, ParseError> {
            let msg = self.with_patterns(|p| p.term(false))?;
            self.require_punct(")")?;
            Ok(msg)
        })() {
            Ok(msg) => return Ok((None, msg)),
            Err(e) if e.ghc_error.is_some() => return Err(e),
            Err(e) => e,
        };
        self.restore(probe);
        (|| -> Result<(Option<Term>, Term), ParseError> {
            let chan = self.term(false)?;
            self.require_punct(",")?;
            let msg = self.with_patterns(|p| p.term(false))?;
            self.require_punct(")")?;
            Ok((Some(chan), msg))
        })()
        .map_err(|e2| Self::merge_alt_errors(e1, e2))
    }

    /// parsec `mergeError`: the failure at the further position wins; at equal
    /// positions the two message lists concatenate.  A GHC `error` in the
    /// second branch escapes unmerged.
    fn merge_alt_errors(e1: ParseError, e2: ParseError) -> ParseError {
        if e2.ghc_error.is_some() {
            return e2;
        }
        match e2.offset.cmp(&e1.offset) {
            std::cmp::Ordering::Greater => e2,
            std::cmp::Ordering::Less => e1,
            std::cmp::Ordering::Equal => {
                let mut e = e1;
                e.messages.extend(e2.messages);
                e
            }
        }
    }

    fn parse_rule(&mut self) -> Result<Rule, ParseError> {
        self.skip_ws();
        let kw_end = self.lx.pos().offset + "rule".len();
        self.require_kw("rule")?;
        let mut rule = self.rule_after_kw(kw_end)?;
        // Optional variants
        rule.variants = if self.try_kw("variants") {
            let mut vs = Vec::new();
            loop {
                let v = self.parse_rule_ac()?;
                vs.push(v);
                if !self.try_punct(",") {
                    break;
                }
            }
            vs
        } else {
            // HS `option [] $ symbol "variants" *> commaSep1 protoRuleAC`
            // (Theory/Text/Parser/Rule.hs:134) stops here without consuming,
            // leaving its
            // `Expect "\"variants\""` for the next error raised at this offset.
            // Only `protoRule` has this trailing block; `diffRule`
            // (Theory/Text/Parser/Rule.hs:120)
            // ends in an `optionMaybe (symbol "left" *> …)` instead, so a diff
            // theory's rules leave a different label that this port does not
            // track.
            if !self.is_diff {
                self.set_item_hangover(&["\"variants\""]);
            }
            vec![]
        };
        // Optional `left ... right ...` for diff rules
        if self.try_kw("left") {
            let l = self.parse_rule()?;
            self.require_kw("right")?;
            let r = self.parse_rule()?;
            rule.left_right = Some((Box::new(l), Box::new(r)));
        }
        Ok(rule)
    }

    fn parse_rule_ac(&mut self) -> Result<Rule, ParseError> {
        self.require_kw("rule")?;
        // HS `protoRuleACInfo`/`intrRule`
        // (Theory/Text/Parser/Rule.hs:137-138/157) sequence a
        // non-optional `moduloAC` here (`symbol "rule" *> moduloAC *> ...`).
        // This port relaxes that: `try_modulo` returns `None` when the
        // `(modulo AC)` head is absent and parsing proceeds. (More lenient than
        // Haskell, but still accepts all valid Haskell input.)
        self.rule_after_kw(usize::MAX)
    }

    /// The rule header and body that follow the `rule` keyword, shared by
    /// `protoRule` (Theory/Text/Parser/Rule.hs:126-135) and `protoRuleAC`
    /// (Theory/Text/Parser/Rule.hs:146-154): the optional `(modulo ...)` head,
    /// the name, the attribute list and the closing colon of `protoRuleInfo` /
    /// `protoRuleACInfo` (Theory/Text/Parser/Rule.hs:100-107 / 138-143), then
    /// `option emptySubst letBlock`, the premises, the actions and embedded
    /// restrictions, the conclusions and the `apply subst` of the bindings.
    /// `kw_end` is the offset just past the `rule` letters, which
    /// [`Self::rule_name_ident`] uses to place the `formalComment` labels.
    /// `variants` and `left_right` are empty; only `protoRule` has them, and
    /// [`Self::parse_rule`] fills them in.
    fn rule_after_kw(&mut self, kw_end: usize) -> Result<Rule, ParseError> {
        let modulo = self.try_modulo();
        let name = self.rule_name_ident(kw_end)?;
        let had_attributes = self.peek_punct("[");
        let attributes = self.rule_attributes()?;
        self.require_rule_colon(had_attributes)?;
        // Optional let block.
        let (lets, mut premises) = if self.at_keyword("let") {
            (self.let_bindings()?, self.fact_list()?)
        } else {
            (vec![], self.premises_after_absent_let()?)
        };
        // Actions / restrictions either `--[..]->` or `-->`
        let (mut actions, mut embedded_restrictions) = self.parse_actions_and_restrictions()?;
        let mut conclusions = self.fact_list()?;
        apply_let_bindings(
            &lets,
            &mut premises,
            &mut actions,
            &mut conclusions,
            &mut embedded_restrictions,
        );
        Ok(Rule {
            name,
            modulo,
            attributes,
            premises,
            actions,
            conclusions,
            embedded_restrictions,
            variants: vec![],
            left_right: None,
        })
    }

    fn try_modulo(&mut self) -> Option<String> {
        let save = self.save();
        if !self.try_punct("(") {
            return None;
        }
        if !self.try_kw("modulo") {
            self.restore(save);
            return None;
        }
        let id = match self.ident() {
            Ok(s) => s,
            Err(_) => {
                self.restore(save);
                return None;
            }
        };
        if !self.try_punct(")") {
            self.restore(save);
            return None;
        }
        Some(id)
    }

    /// The `colon` that closes a rule header (HS `protoRuleInfo` /
    /// `protoRuleACInfo`, Theory/Text/Parser/Rule.hs:100-107 / 137-145).
    ///
    /// It is preceded by `ruleAttributesp = option mempty (…list ruleAttribute)`
    /// (Theory/Text/Parser/Rule.hs:97-98).  When the attribute list is absent,
    /// `option` returns
    /// without consuming, so parsec keeps its `Expect "\"[\""` and merges it
    /// into whatever fails next — here the colon — and the frame reads
    /// `expecting "[" or ":"`.  A present `[…]` consumes, which discards that
    /// expectation and leaves `expecting ":"` alone.
    fn require_rule_colon(&mut self, had_attributes: bool) -> Result<(), ParseError> {
        if self.try_punct(":") {
            return Ok(());
        }
        if had_attributes {
            Err(self.err_expect(&["\":\""]))
        } else {
            Err(self.err_expect(&["\"[\"", "\":\""]))
        }
    }

    fn rule_attributes(&mut self) -> Result<Vec<RuleAttr>, ParseError> {
        let mut attrs = Vec::new();
        if !self.try_punct("[") {
            return Ok(attrs);
        }
        loop {
            self.skip_ws();
            // colour=, color=
            if self.try_kw("colour") || self.try_kw("color") {
                self.require_punct("=")?;
                let c = self.color_attr_value()?;
                attrs.push(RuleAttr::Color(c));
            } else if self.try_kw("process") {
                // HS `ruleAttribute` (Parser/Rule.hs:68-93, see line 72) `parseAndIgnore`s
                // `process=`: the value is parsed and DISCARDED, leaving
                // `ruleProcess = Nothing`, so a user-written `process=` is never
                // rendered.  `process=` is only emitted by HS for
                // SAPIC-translation-generated rules (via `ruleProcess`, not this
                // parser).  Mirror that: read and drop the value, push nothing.
                self.require_punct("=")?;
                let _ = self.read_balanced_token()?;
            } else if self.try_kw("no_derivcheck") {
                attrs.push(RuleAttr::NoDerivCheck);
            } else if self.try_kw("role") {
                self.require_punct("=")?;
                let s = self.string_literal_or_squoted()?;
                attrs.push(RuleAttr::Role(s));
            } else if self.try_kw("issapicrule") {
                attrs.push(RuleAttr::IsSapicRule);
            } else {
                // External attribute: x-<id> [= raw]
                let save = self.save();
                if let Some(ext) = self.lx.ext_identifier() {
                    let val = if self.try_punct("=") {
                        Some(self.read_balanced_token()?)
                    } else {
                        None
                    };
                    attrs.push(RuleAttr::External(ext, val));
                } else {
                    self.restore(save);
                    break;
                }
            }
            if !self.try_punct(",") {
                break;
            }
        }
        self.require_punct("]")?;
        Ok(attrs)
    }

    /// The value of a `color=`/`colour=` rule attribute: HS `hexColor`
    /// (Token.hs:403-406, `lexeme (singleQuoted hexCode <|> hexCode)` with
    /// `hexCode = optional (symbol "#") *> many1 hexDigit`) followed by
    /// `parseColor`'s `hexToRGB` validation (Parser/Rule.hs:81-85).
    ///
    /// `hexToRGB` (Data/Color.hs:149-155) only matches a six-character code
    /// (`[r1,r2,g1,g2,b1,b2]`, each pair read via `readHex`, so both cases
    /// are fine); anything else is `Nothing` and `parseColor` raises
    /// `fail ("Color code " ++ show hc ++ " could not be parsed to RGB")`.
    /// The accepted code is stored verbatim (quotes/`#` stripped); rendering
    /// lowercases it, matching `rgbToHex` of the parsed `RGB` value
    /// (Data/Color.hs:139-147 round-trips every 6-digit code byte-for-byte).
    ///
    /// Error shapes (oracle-pinned in `tests/hex_color.rs`):
    ///   * no code at all — the lexer alternation's merged labels at the value
    ///     position: `expecting "'", "#" or hexadecimal digit`, minus whichever
    ///     prefix tokens were already consumed;
    ///   * unquoted bad tail / closing-quote miss — `many1 hexDigit`'s pending
    ///     `hexadecimal digit` label (plus `"'"` for the quoted form) at the
    ///     offending char;
    ///   * wrong length — the `Color code …` `fail`, which merges the pending
    ///     `hexadecimal digit` label only when the code is unquoted and no
    ///     whitespace follows it (`lexeme`'s trailing `whiteSpace` consuming
    ///     anything discards the pending empty error, as does the closing
    ///     quote's `symbol`).
    ///
    /// Kept from the previous lexer-side implementation: no whitespace is
    /// skipped after the opening quote or the `#`, so `' #FF'` / `'# FF'` are
    /// rejected here though HS's `symbol`-based parser accepts them — real
    /// colour attributes are always tight (e.g. `'#111111'`).
    fn color_attr_value(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        let quoted = self.lx.eat_str("'");
        let hash = self.lx.eat_str("#");
        let mut code = String::new();
        while let Some(c) = self.lx.peek() {
            if c.is_ascii_hexdigit() {
                code.push(c);
                self.lx.bump();
            } else {
                break;
            }
        }
        if code.is_empty() {
            // `many1 hexDigit` failed at its first char; the labels of the
            // not-yet-consumed prefix alternatives merge in.
            let expects: &[&str] = if quoted {
                if hash {
                    &["hexadecimal digit"]
                } else {
                    &["\"#\"", "hexadecimal digit"]
                }
            } else if hash {
                &["hexadecimal digit"]
            } else {
                &["\"'\"", "\"#\"", "hexadecimal digit"]
            };
            return Err(self.err_expect(expects));
        }
        let mut pending_hexdigit = false;
        if quoted {
            if !self.lx.eat_str("'") {
                // Closing `symbol "'"` fails where `many1 hexDigit` stopped;
                // the pending `hexadecimal digit` label merges in first.
                return Err(self.err_expect(&["hexadecimal digit", "\"'\""]));
            }
        } else {
            pending_hexdigit = true;
        }
        // `lexeme`'s trailing whiteSpace: consuming anything discards the
        // pending `hexadecimal digit` empty error.
        let before = self.lx.pos().offset;
        self.skip_ws();
        if self.lx.pos().offset != before {
            pending_hexdigit = false;
        }
        if code.len() != 6 {
            let mut e = self.err_fail(format!("Color code \"{code}\" could not be parsed to RGB"));
            if pending_hexdigit {
                e.messages
                    .insert(1, Message::Expect("hexadecimal digit".to_string()));
            }
            return Err(e);
        }
        Ok(code)
    }

    fn string_literal_or_squoted(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        if let Some(s) = self.lx.string_literal() {
            return Ok(s);
        }
        if let Some(s) = self.lx.single_quoted() {
            return Ok(s);
        }
        Err(self.err("expected quoted string"))
    }

    /// Read an identifier or a balanced parenthesised token (for `process=...`).
    fn read_balanced_token(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        // HS `parseAndIgnore = betweenMatching (\(l,r) -> manyCharsExcept [l,r] ...)`
        // (Theory/Text/Parser/Rule.hs:69-95, see line 87). `betweenMatching`
        // (Token.hs:305-316) tries each pair in
        // `matches`, and `manyCharsExcept [l,r]` (Token.hs:320-321) consumes
        // chars until the FIRST `l` or `r` (NO nesting), after which `between`
        // requires the closing `r`. The pair set INCLUDES `('|','|')`.
        let pairs = [
            ('"', '"'),
            ('\'', '\''),
            ('(', ')'),
            ('[', ']'),
            ('{', '}'),
            ('|', '|'),
            ('<', '>'),
        ];
        if let Some(c) = self.lx.peek() {
            for (l, r) in pairs.iter() {
                if c == *l {
                    self.lx.bump();
                    let mut s = String::new();
                    loop {
                        match self.lx.peek() {
                            None => return Err(self.err("unterminated bracketed value")),
                            // Stop at the first `l` or `r` (matches
                            // `manyCharsExcept`, which does not nest); the closer
                            // `r` is then consumed by `between`.
                            Some(ch) if ch == *r || ch == *l => {
                                if ch != *r {
                                    return Err(self.err("unterminated bracketed value"));
                                }
                                self.lx.bump();
                                break;
                            }
                            Some(ch) => {
                                s.push(ch);
                                self.lx.bump();
                            }
                        }
                    }
                    self.skip_ws();
                    return Ok(s);
                }
            }
        }
        // Otherwise, read a single identifier-or-number token.
        let id = self.ident()?;
        Ok(id)
    }

    /// The left side of one `let` definition — HS `sortedLVar` under
    /// `genericletBlock` (Theory/Text/Parser/Let.hs:24-31): an indexed
    /// identifier with an optional sort prefix or `:sort` suffix, never an
    /// application or a compound term.  HS's sort list here is `[LSortMsg,
    /// LSortNat]`. `Ok(None)` means no variable starts here, which ends the
    /// definition list.
    fn let_binder(&mut self) -> Result<Option<VarSpec>, ParseError> {
        let start = self.save();
        let Some(v) = self.try_var_spec()? else {
            return Ok(None);
        };
        let v = self.attach_sort_suffix(v)?;
        if !matches!(v.sort, LSort::Msg | LSort::Nat) {
            self.restore(start);
            return Err(self.err_expect(&["identifier", "\"%\""]));
        }
        self.note_var_dot_hangover(&v);
        Ok(Some(v))
    }

    /// HS `letBlock` (Theory/Text/Parser/Let.hs:28-35): a sequence of
    /// `sortedLVar [LSortMsg, LSortNat] <* equalSign` definitions closed by
    /// `in`, folded into an `LNSubst`.  The left side is a VARIABLE, so a
    /// bare identifier that names an arity-0 function symbol binds the
    /// like-named variable and leaves the body's `nullaryApp` constant alone.
    fn let_bindings(&mut self) -> Result<Vec<(Term, Term)>, ParseError> {
        self.require_kw("let")?;
        let mut bs = Vec::new();
        loop {
            self.skip_ws();
            if self.at_keyword("in") {
                break;
            }
            let lhs = match self.let_binder()? {
                Some(v) => Term::Var(v),
                None => break,
            };
            self.require_punct("=")?;
            let rhs = self.term(false)?;
            bs.push((lhs, rhs));
        }
        if bs.is_empty() {
            return Err(self.err_expect(&["identifier", "\"%\""]));
        }
        self.require_kw("in")?;
        Ok(bs)
    }

    /// The rule-name `identifier`, with the parsec frame HS leaves when it is
    /// missing.  `moduloE`'s failed `option` probe puts `Expect "\"(\""`
    /// ahead of `identifier` at the name position
    /// (Theory/Text/Parser/Rule.hs:127-131, via
    /// `protoRuleInfo`); and when the failure sits DIRECTLY after the `rule`
    /// letters (`kw_end_offset`), the item alternation's `formalComment`
    /// retry — `try (many1 letter <* string "{*")` (Token.hs:377-378) —
    /// re-consumes them and fails at the same offset, so its
    /// `letter`/`"{*"` labels merge behind (bare `rule` at EOF, `rule!x`).
    /// Callers outside the top-level item alternation (variants sub-rules)
    /// pass `usize::MAX`: no formalComment alternative exists there.
    fn rule_name_ident(&mut self, kw_end_offset: usize) -> Result<String, ParseError> {
        if let Some(id) = self.lx.identifier() {
            return Ok(id);
        }
        if let Some(e) = self.err_reserved_word() {
            return Err(e);
        }
        let mut e = self.err_expect(&["\"(\"", "identifier"]);
        if e.offset == kw_end_offset {
            e.messages.push(Message::Expect("letter".to_string()));
            e.messages.push(Message::Expect("\"{*\"".to_string()));
        }
        Err(e)
    }

    /// The premise [`Parser::fact_list`] of a rule whose optional `let` block
    /// is absent.  HS sequences `option emptySubst letBlock` before
    /// `genericRule` (Theory/Text/Parser/Rule.hs:131, :151): the failed
    /// non-consuming `letBlock`
    /// leaves `Expect "\"let\""` at the probe offset, and a premise-`[`
    /// failure at that SAME offset merges the two — `expecting "let" or "["`
    /// (parsec merge is position-gated, so a failure deeper inside the list
    /// keeps its own labels).
    fn premises_after_absent_let(&mut self) -> Result<Vec<Fact>, ParseError> {
        self.skip_ws();
        let probe_offset = self.lx.pos().offset;
        self.fact_list().map_err(|mut e| {
            if e.offset == probe_offset {
                let at = usize::from(matches!(e.messages.first(), Some(Message::SysUnExpect(_))));
                e.messages
                    .insert(at, Message::Expect("\"let\"".to_string()));
            }
            e
        })
    }

    fn fact_list(&mut self) -> Result<Vec<Fact>, ParseError> {
        self.require_punct("[")?;
        // HS `list (fact ...)` (Theory/Text/Parser/Rule.hs:205-213, see line
        // 207,212) = `brackets . commaSep`
        // (Token.hs:362-363) with `commaSep = sepEndBy comma`: the list may
        // be empty and a trailing comma before `]` is OK.
        self.sep_end_by("]", |p| p.fact())
    }

    fn fact_or_restr(&mut self) -> Result<FactOrRestr, ParseError> {
        // `_restrict(formula)` or fact.
        if self.try_kw("_restrict") {
            self.require_punct("(")?;
            let phi = self.formula()?;
            self.require_punct(")")?;
            Ok(FactOrRestr::Restr(phi))
        } else {
            Ok(FactOrRestr::Fact(self.fact()?))
        }
    }

    // -------------------- Lemma --------------------

    fn lemma_item(&mut self) -> Result<TheoryItem, ParseError> {
        // HS `protoLemma` captures `start <- getInput` BEFORE `symbol "lemma"`;
        // the enclosing item loop has already consumed leading whitespace, so
        // the cursor sits exactly at `lemma` here (`Theory/Text/Parser/Lemma.hs:78-88, see line 80`).
        let start = self.lx.pos().offset;
        // Look ahead to decide between a normal lemma and an accountability lemma.
        // Accountability lemmas have the body `accounts for [..]` after the name.
        self.require_kw("lemma")?;
        let _ = self.try_modulo();
        let name = self.ident()?;
        let attrs = self.lemma_attributes()?;
        self.require_punct(":")?;

        // Detect accountability: `<test_idents> accounts for "phi"`
        let snap = self.save();
        if let Some(acc) = self.try_acc_lemma_body(&name, &attrs)? {
            return Ok(TheoryItem::AccLemma(acc));
        }
        self.restore(snap);

        // Trace quantifier
        let trace_quantifier = if self.try_kw("all-traces") {
            TraceQuantifier::AllTraces
        } else if self.try_kw("exists-trace") {
            TraceQuantifier::ExistsTrace
        } else {
            TraceQuantifier::AllTraces
        };
        let formula = self.double_quoted_formula()?;
        let proof = self.try_proof_skeleton()?;
        // HS `end <- getInput` after the proof skeleton; `inputString =
        // removeComments $ take (length start - length end) start`
        // (`Theory/Text/Parser/Lemma.hs:86-87`).  The closing-quote lexeme and
        // `try_proof_skeleton` have already consumed trailing whitespace and
        // comments, so `end` sits at the next top-level token — exactly HS's.
        let end = self.lx.pos().offset;
        let plaintext = remove_comments(&self.lx.src()[start..end]);
        if proof.is_none() {
            // An absent proof leaves the unmatched skeleton alternatives'
            // labels standing at the item's end position — HS
            // `startProofSkeleton <|> pure (unproven ())`
            // (Theory/Text/Parser/Lemma.hs:85) with the alternatives `SOLVED` /
            // `by` (Theory/Text/Parser/Proof.hs:99-115) and the `proofMethod`
            // list (Theory/Text/Parser/Proof.hs:76-85) — where a following
            // same-position failure merges them in ahead of its own.
            self.set_item_hangover(&[
                "\"SOLVED\"",
                "\"by\"",
                "\"sorry\"",
                "\"simplify\"",
                "\"solve\"",
                "\"contradiction\"",
                "\"induction\"",
                "\"INVALIDATED\"",
                "\"UNFINISHABLE\"",
            ]);
        }
        // HS `liftedAddLemma` (Theory/Text/Parser.hs:280-282) runs `addLemma`'s
        // name guard (TheoryObject.hs:462-465) on each parsed lemma;
        // accountability lemmas are TranslationItems, which `lookupLemma`
        // (TheoryObject.hs:675-676) does not see, so they neither feed nor hit
        // this set. A diff parse routes sided lemmas through
        // `liftedAddLemma'` (Theory/Text/Parser.hs:438,532), whose per-side
        // stores enforce their own duplicate guards. In a regular parse,
        // `left`/`right` are ordinary attributes and `liftedAddLemma` still
        // checks the shared lemma namespace.
        if !self.is_diff {
            if self.seen_lemma_names.iter().any(|n| n == &name) {
                return Err(self.item_fail(format!("duplicate lemma: {name}")));
            }
            self.seen_lemma_names.push(name.clone());
        }
        Ok(TheoryItem::Lemma(Lemma {
            name,
            attributes: attrs,
            trace_quantifier,
            formula,
            proof,
            plaintext,
        }))
    }

    fn try_acc_lemma_body(
        &mut self,
        name: &str,
        attrs: &[LemmaAttr],
    ) -> Result<Option<AccLemma>, ParseError> {
        // Pattern: `<id1, id2, ...> (accounts|account) for "phi"`
        let save = self.save();
        let mut idents = Vec::new();
        loop {
            self.skip_ws();
            let probe = self.save();
            if let Some(id) = self.lx.peek_identifier() {
                if id == "accounts" || id == "account" {
                    break;
                }
                let _ = self.ident();
                idents.push(id);
                if !self.try_punct(",") {
                    break;
                }
            } else {
                self.restore(probe);
                break;
            }
        }
        // HS `lemmaAcc` (Theory/Text/Parser/Accountability.hs:30-39, see line 36)
        // uses `commaSep1 $ identifier`,
        // requiring at least one case-test identifier before `accounts for`.
        // Since the whole `lemmaAcc` is `try`-wrapped, an empty list backtracks
        // and the caller reparses as a normal lemma — so fall back here too.
        if idents.is_empty() {
            self.restore(save);
            return Ok(None);
        }
        if !(self.try_kw("accounts") || self.try_kw("account")) {
            self.restore(save);
            return Ok(None);
        }
        self.require_kw("for")?;
        let formula = self.double_quoted_formula()?;
        Ok(Some(AccLemma {
            name: name.to_string(),
            attributes: attrs.to_vec(),
            formula,
            case_test_idents: idents,
        }))
    }

    fn diff_lemma_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("diffLemma")?;
        let name = self.ident()?;
        let attributes = self.lemma_attributes()?;
        self.require_punct(":")?;
        let proof = self.try_diff_proof_skeleton()?;
        Ok(TheoryItem::DiffLemma(DiffLemma {
            name,
            attributes,
            proof,
        }))
    }

    fn case_test_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("test")?;
        let name = self.ident()?;
        self.require_punct(":")?;
        let formula = self.double_quoted_formula()?;
        Ok(TheoryItem::CaseTest(CaseTest { name, formula }))
    }

    fn lemma_attributes(&mut self) -> Result<Vec<LemmaAttr>, ParseError> {
        let mut attrs = Vec::new();
        if !self.try_punct("[") {
            return Ok(attrs);
        }
        loop {
            self.skip_ws();
            if self.try_kw("typing") || self.try_kw("sources") {
                attrs.push(LemmaAttr::Sources);
            } else if self.try_kw("reuse") {
                attrs.push(LemmaAttr::Reuse);
            } else if self.try_kw("diff_reuse") {
                attrs.push(LemmaAttr::DiffReuse);
            } else if self.try_kw("use_induction") {
                attrs.push(LemmaAttr::UseInduction);
            } else if self.try_kw("hide_lemma") {
                self.require_punct("=")?;
                let id = self.ident()?;
                attrs.push(LemmaAttr::HideLemma(id));
            } else if self.try_kw("heuristic") {
                self.require_punct("=")?;
                let raw = self.read_until_attribute_end();
                attrs.push(LemmaAttr::Heuristic(raw));
            } else if self.try_kw("output") {
                self.require_punct("=")?;
                self.require_punct("[")?;
                // HS `list constructorp` (Theory/Text/Parser/Lemma.hs:39-53, see
                // line 49) = `brackets . commaSep`:
                // trailing comma before `]` is permitted.
                let outs = self.sep_end_by("]", |p| p.ident())?;
                attrs.push(LemmaAttr::Output(outs));
            } else if self.try_kw("left") {
                attrs.push(LemmaAttr::Left);
            } else if self.try_kw("right") {
                attrs.push(LemmaAttr::Right);
            } else {
                // HS `lemmaAttribute` (Theory/Text/Parser/Lemma.hs:39-53) is a
                // closed `asum` of the
                // recognised attributes with no catch-all; an unknown attribute
                // makes `list (lemmaAttribute ...)` fail and `protoLemma`'s outer
                // `try` backtrack into a load error. An empty read here means we
                // are at `]` (empty list) or a trailing `,`, both of which are
                // permitted by `commaSep` — so break in that case, otherwise
                // reject the unknown attribute to match Haskell.
                let raw = self.read_until_attribute_end();
                if raw.is_empty() {
                    break;
                }
                return Err(self.err(format!("unknown lemma attribute: {raw}")));
            }
            if !self.try_punct(",") {
                break;
            }
        }
        self.require_punct("]")?;
        Ok(attrs)
    }

    fn read_until_attribute_end(&mut self) -> String {
        let mut s = String::new();
        let mut depth = 0i32;
        loop {
            match self.lx.peek() {
                None => break,
                Some(']') if depth == 0 => break,
                Some(',') if depth == 0 => break,
                Some(c @ ('[' | '(' | '{')) => {
                    depth += 1;
                    s.push(c);
                    self.lx.bump();
                }
                Some(c @ (']' | ')' | '}')) => {
                    depth -= 1;
                    s.push(c);
                    self.lx.bump();
                }
                Some(c) => {
                    s.push(c);
                    self.lx.bump();
                }
            }
        }
        s.trim().to_string()
    }

    fn try_proof_skeleton(&mut self) -> Result<Option<ProofSkeleton>, ParseError> {
        // Proofs in `.spthy` files start with one of a known set of proof
        // method tokens. We treat the proof as raw text up to the next
        // top-level keyword. If no proof tokens appear, return None.
        self.skip_ws();
        let save = self.save();
        // First-token set that can START a stored proof skeleton, matching HS.
        // This gate is for `lemma_item`'s regular proof grammar:
        //   - regular `proofMethod` (Theory/Text/Parser/Proof.hs:77-85): sorry,
        //     simplify, solve,
        //     contradiction, induction, INVALIDATED, UNFINISHABLE
        //   - regular skeleton extras (Theory/Text/Parser/Proof.hs:99-115):
        //     `by` (finalProof),
        //     `SOLVED` (solvedProof)
        // `case`/`next`/`qed` are intentionally absent: they only appear INSIDE
        // an interProof block, never as a proof body's first token. `rule` is
        // excluded (a bare `rule:` is a rule declaration; only the hyphenated
        // `rule-equivalence` is a proof method).
        let proof_starters = [
            // regular proofMethod
            "sorry",
            "simplify",
            "solve",
            "contradiction",
            "induction",
            "INVALIDATED",
            "UNFINISHABLE",
            // regular skeleton extras
            "by",
            "SOLVED",
        ];
        // Check for hyphenated proof identifiers.
        let probe = self.peek_hyphen_identifier();
        let starts = match probe {
            Some(id) => proof_starters.contains(&id.as_str()),
            None => false,
        };
        if !starts {
            self.restore(save);
            return Ok(None);
        }
        let proof_start = self.lx.pos();
        let raw = self.read_until_next_top_level();
        // Structured parse of `raw`.  Mirrors HS's `startProofSkeleton`
        // (Theory/Text/Parser/Proof.hs:90-95) which calls `proofSkeleton`
        // (Theory/Text/Parser/Proof.hs:98-115) — a recursive descent over
        // `simplify | solve(...) | induction | by <method> | SOLVED`
        // with `case <name> ... next ... qed` blocks.  We parse over
        // the captured raw text rather than the original lexer so the
        // top-level boundary detection (`read_until_next_top_level`)
        // controls termination.
        //
        let tree = parse_proof_tree(&raw, self).map_err(|e| {
            let rel_offset = offset_at_line_col(&raw, e.line, e.col);
            ParseError::at(
                Pos {
                    offset: proof_start.offset + rel_offset,
                    line: proof_start.line + e.line - 1,
                    col: if e.line == 1 {
                        proof_start.col + e.col - 1
                    } else {
                        e.col
                    },
                },
                vec![Message::Message(e.msg)],
            )
        })?;
        Ok(Some(ProofSkeleton {
            raw,
            tree: Some(tree),
        }))
    }

    /// Capture and validate HS's separate diff-proof grammar. The regular
    /// replay AST has no diff methods, so a valid diff proof intentionally
    /// retains only its raw text.
    fn try_diff_proof_skeleton(&mut self) -> Result<Option<ProofSkeleton>, ParseError> {
        self.skip_ws();
        let save = self.save();
        let starters = [
            "sorry",
            "rule-equivalence",
            "backward-search",
            "step",
            "ATTACK",
            "UNFINISHABLEdiff",
            "by",
            "MIRRORED",
        ];
        let starts = self
            .peek_hyphen_identifier()
            .is_some_and(|id| starters.contains(&id.as_str()));
        if !starts {
            self.restore(save);
            return Ok(None);
        }
        let proof_start = self.lx.pos();
        let raw = self.read_until_next_top_level();
        validate_diff_proof_tree(&raw, self).map_err(|e| {
            let rel_offset = offset_at_line_col(&raw, e.line, e.col);
            ParseError::at(
                Pos {
                    offset: proof_start.offset + rel_offset,
                    line: proof_start.line + e.line - 1,
                    col: if e.line == 1 {
                        proof_start.col + e.col - 1
                    } else {
                        e.col
                    },
                },
                vec![Message::Message(e.msg)],
            )
        })?;
        Ok(Some(ProofSkeleton { raw, tree: None }))
    }

    /// Peek a possibly-hyphenated identifier without consuming.
    fn peek_hyphen_identifier(&mut self) -> Option<String> {
        let save = self.save();
        self.lx.skip_ws();
        let mut s = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphabetic() => {
                s.push(c);
                self.lx.bump();
            }
            _ => {
                self.restore(save);
                return None;
            }
        }
        loop {
            match self.lx.peek() {
                Some(c) if is_ident_char(c) => {
                    s.push(c);
                    self.lx.bump();
                }
                _ if self.at_hyphen_join() => {
                    self.lx.bump();
                    s.push('-');
                }
                _ => break,
            }
        }
        self.restore(save);
        Some(s)
    }

    // -------------------- Top-level process / processDef --------------------

    fn toplevel_process(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("process")?;
        self.require_punct(":")?;
        let p = self.process()?;
        Ok(TheoryItem::TopLevelProcess(p))
    }

    fn process_def(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("let")?;
        let name = self.ident()?;
        let vars = if self.try_punct("(") {
            // HS `parens $ commaSep sapicvar` (Theory/Text/Parser/Sapic.hs:64-72,
            // see line 69): trailing comma OK.
            // `sapicvar`, so a `:` here types the parameter (see
            // [`Parser::sapic_var_types`]).
            let r = self.with_sapic_var_types(|p| p.sep_end_by(")", |p| p.var_spec()));
            Some(r?)
        } else {
            None
        };
        self.require_punct("=")?;
        let body = self.process()?;
        Ok(TheoryItem::ProcessDef(ProcessDef { name, vars, body }))
    }

    fn equiv_lemma(&mut self, diff: bool) -> Result<TheoryItem, ParseError> {
        if diff {
            self.require_kw("diffEquivLemma")?;
        } else {
            self.require_kw("equivLemma")?;
        }
        self.require_punct(":")?;
        if diff {
            // HS `diffEquivLemma` turns the signature's diff bit on right after
            // the colon and leaves it on for the rest of the parse
            // (Theory/Text/Parser/Sapic.hs:211-217, see line 215).
            self.enable_diff = true;
        }
        let p1 = self.process()?;
        if diff {
            Ok(TheoryItem::DiffEquivLemma(p1))
        } else {
            let p2 = self.process()?;
            Ok(TheoryItem::EquivLemma(p1, p2))
        }
    }

    fn export_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("export")?;
        let tag = self.ident()?;
        self.require_punct(":")?;
        // Export bodies use the strict `bodyChar` grammar (Parser/Signature.hs:297-302),
        // NOT the general string-literal escape decoding.
        let body = self
            .lx
            .export_body()
            .ok_or_else(|| self.err("expected export body string"))?;
        Ok(TheoryItem::Export { tag, body })
    }

    // =========================================================================
    // Process parser (SAPIC)
    // =========================================================================

    /// Run `f` with [`Parser::sapic_var_types`] on, restoring the previous
    /// value afterwards — the HS `sapicvar` regions.
    fn with_sapic_var_types<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = self.sapic_var_types;
        self.sapic_var_types = true;
        let r = f(self);
        self.sapic_var_types = saved;
        r
    }

    /// Run `f` with [`Parser::allow_pat`] on, restoring the previous value
    /// afterwards — the HS pattern-literal regions.
    fn with_patterns<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = self.allow_pat;
        self.allow_pat = true;
        let r = f(self);
        self.allow_pat = saved;
        r
    }

    /// One process-`let` binding — HS `definition = sapicpatternterm <*
    /// equalSign <*> sapicterm` (Let.hs:23-26): only the pattern side takes
    /// `=v` patterns.
    fn let_definition(&mut self) -> Result<(Term, Term), ParseError> {
        let pat = self.with_patterns(|p| p.term(false))?;
        self.require_punct("=")?;
        let val = self.term(false)?;
        Ok((pat, val))
    }

    /// A SAPIC process.  Every variable inside is HS `sapicvar`, so a trailing
    /// `:` names a type rather than a sort — see [`Parser::sapic_var_types`].
    fn process(&mut self) -> Result<Process, ParseError> {
        self.with_sapic_var_types(|p| p.process_body())
    }

    /// Left-associative parallel / NDC composition.
    fn process_body(&mut self) -> Result<Process, ParseError> {
        self.chainl1(
            |p| p.action_process(),
            |p| {
                p.skip_ws();
                if p.try_punct("||") {
                    Some(ProcessComb::Parallel)
                } else if p.lx.peek() == Some('|') && p.lx.peek2() != Some('|') {
                    // Single `|` parallel
                    p.lx.bump();
                    p.skip_ws();
                    Some(ProcessComb::Parallel)
                } else if p.try_punct("+") {
                    Some(ProcessComb::Ndc)
                } else {
                    None
                }
            },
            |comb, left, right| Process::Comb {
                comb,
                left: Box::new(left),
                right: Box::new(right),
            },
        )
    }

    fn action_process(&mut self) -> Result<Process, ParseError> {
        self.skip_ws();
        // Replication
        if self.try_punct("!") {
            let p = self.process()?;
            return Ok(Process::Replication(Box::new(p)));
        }
        if self.try_kw("lookup") {
            let t = self.term(false)?;
            self.require_kw("as")?;
            let v = self.var_spec()?;
            self.require_kw("in")?;
            let p = self.process()?;
            let q = self.else_process()?;
            return Ok(Process::Comb {
                comb: ProcessComb::Lookup(t, v),
                left: Box::new(p),
                right: Box::new(q),
            });
        }
        if self.try_kw("if") {
            // Try equality: t = t else formula
            let cond = match self.attempt(|p| {
                let t1 = p.term(false)?;
                p.require_punct("=")?;
                let t2 = p.term(false)?;
                Ok(Condition::Eq(t1, t2))
            }) {
                Some(c) => c,
                None => Condition::Formula(self.formula()?),
            };
            self.require_kw("then")?;
            let p = self.process()?;
            let q = self.else_process()?;
            return Ok(Process::Comb {
                comb: ProcessComb::Cond(cond),
                left: Box::new(p),
                right: Box::new(q),
            });
        }
        if self.try_kw("let") {
            // `let pat = t [, pat = t]* in p` or with newline-separated
            // bindings (Tamarin's `genericletBlock = many1 definition` has no
            // separator between bindings).
            // HS `genericletBlock = many1 definition` (Let.hs:23-26, see line 24) with
            // `definition = sapicpatternterm <* equalSign <*> sapicterm`. There
            // is no separator between bindings; `many1` greedily reparses a
            // `definition` and backtracks when one fails to parse. We mirror that
            // by attempting another `(pat = val)` binding and restoring on
            // failure.
            let mut bindings: Vec<(Term, Term)> = Vec::new();
            // First binding is required.
            bindings.push(self.let_definition()?);
            loop {
                let _ = self.try_punct(",");
                self.skip_ws();
                if self.at_keyword("in") {
                    break;
                }
                // Try to parse one more binding; backtrack if it doesn't parse
                // (matching `many1`'s greedy-with-backtrack behaviour).
                match self.attempt(|p| p.let_definition()) {
                    Some(b) => bindings.push(b),
                    None => break,
                }
            }
            self.require_kw("in")?;
            let p = self.process()?;
            let q = self.else_process()?;
            // Right-fold the bindings into nested Let combinators.
            let mut acc = p;
            for (pat, val) in bindings.into_iter().rev() {
                acc = Process::Comb {
                    comb: ProcessComb::Let { pat, value: val },
                    left: Box::new(acc),
                    right: Box::new(q.clone()),
                };
            }
            return Ok(acc);
        }
        // null process
        if self.try_punct("0") {
            return Ok(Process::Null);
        }
        // Parenthesised process — possibly with `@ term` annotation.
        if self.try_punct("(") {
            let p = self.process()?;
            self.require_punct(")")?;
            if self.try_punct("@") {
                let m = self.term(false)?;
                return Ok(Process::AtAnnotation(Box::new(p), m));
            }
            return Ok(p);
        }
        // Sapic action: new / insert / delete / in / out / lock / unlock / event / msr
        let save = self.save();
        if let Some(act) = self.try_sapic_action()? {
            // Optional `; rest` (sequencing)
            let body = if self.try_punct(";") {
                self.action_process()?
            } else {
                Process::Null
            };
            return Ok(Process::Action {
                action: act,
                body: Box::new(body),
            });
        }
        self.restore(save);
        // Process call by name: ident or ident(args)
        let save2 = self.save();
        if let Some(id) = self.lx.identifier() {
            // Heuristic: if followed by `(`, parse as call args.
            let args = if self.try_punct("(") {
                // HS `parens $ commaSep (msetterm ...)`
                // (Theory/Text/Parser/Sapic.hs:224-312, see line 296):
                // trailing comma before `)` is permitted.
                self.sep_end_by(")", |p| p.term(false))?
            } else {
                vec![]
            };
            return Ok(Process::Call { name: id, args });
        }
        self.restore(save2);
        Err(self.err("expected process"))
    }

    fn else_process(&mut self) -> Result<Process, ParseError> {
        if self.try_kw("else") {
            self.process()
        } else {
            Ok(Process::Null)
        }
    }

    fn try_sapic_action(&mut self) -> Result<Option<SapicAction>, ParseError> {
        self.skip_ws();
        let save = self.save();
        if self.try_kw("new") {
            let v = self.var_spec()?;
            return Ok(Some(SapicAction::New(v)));
        }
        if self.try_kw("insert") {
            let t1 = self.term(false)?;
            self.require_punct(",")?;
            let t2 = self.term(false)?;
            return Ok(Some(SapicAction::Insert(t1, t2)));
        }
        if self.try_kw("delete") {
            let t = self.term(false)?;
            return Ok(Some(SapicAction::Delete(t)));
        }
        if self.try_kw("in") {
            let (chan, msg) = self.parse_in_chan_msg()?;
            return Ok(Some(SapicAction::ChIn { chan, msg }));
        }
        if self.try_kw("out") {
            let (chan, msg) = self.parse_chan_msg()?;
            return Ok(Some(SapicAction::ChOut { chan, msg }));
        }
        if self.try_kw("lock") {
            let t = self.term(false)?;
            return Ok(Some(SapicAction::Lock(t)));
        }
        if self.try_kw("unlock") {
            let t = self.term(false)?;
            return Ok(Some(SapicAction::Unlock(t)));
        }
        if self.try_kw("event") {
            let f = self.fact()?;
            return Ok(Some(SapicAction::Event(f)));
        }
        // Embedded MSR: `[..] --[..]-> [..]`.  HS parses it via `genericRule
        // sapicpatternvar …` (Parser/Sapic.hs:155), so the whole rule — every
        // fact row and the `_restrict` formulas — is ONE pattern-literal
        // region, shared with the plain-rule arrow alternation.
        if self.lx.peek() == Some('[') {
            return self.with_patterns(|p| {
                let prems = p.fact_list()?;
                if !p.peek_punct("-->") && !p.peek_punct("--[") {
                    p.restore(save);
                    return Ok(None);
                }
                let (acts, restrs) = p.parse_actions_and_restrictions()?;
                let concs = p.fact_list()?;
                Ok(Some(SapicAction::Msr {
                    prems,
                    acts,
                    concs,
                    restrictions: restrs,
                }))
            });
        }
        self.restore(save);
        Ok(None)
    }

    // =========================================================================
    // Facts
    // =========================================================================

    fn fact(&mut self) -> Result<Fact, ParseError> {
        self.skip_ws();
        let persistent = self.try_punct("!");
        let before_ident = self.save();
        let name = self.ident()?;
        if !name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            // HS `fact'` (Theory/Text/Parser/Fact.hs:39-50, see line 46):
            // `fail "facts must start
            // with upper-case letters"` immediately after `identifier`.  The
            // identifier lexeme leaves a pending empty error where its `many
            // identLetter` stopped — `SysUnExpect` of the next char plus
            // `alphaNum`'s `Expect "letter or digit"` — which merges into the
            // fail ONLY when the lexeme's trailing whiteSpace consumed nothing;
            // any whitespace/comment after the name discards the label (the
            // consumed whiteSpace resets the pending error, and its own stop
            // re-fills just the `SysUnExpect`).  Replay the lexeme to find the
            // identifier's end, since `Lexer::identifier` has already skipped
            // the trailing whitespace.
            let after = self.save();
            self.restore(before_ident);
            self.skip_ws();
            for _ in name.chars() {
                self.lx.bump();
            }
            let ident_end = self.lx.pos().offset;
            self.restore(after);
            let mut e = self.err_fail("facts must start with upper-case letters");
            if ident_end == after.offset {
                e.messages
                    .insert(1, Message::Expect("letter or digit".to_string()));
            }
            return Err(e);
        }
        self.require_punct("(")?;
        // HS `parens (commaSep pterm)` (Theory/Text/Parser/Fact.hs:39-63, see
        // line 47): trailing comma OK.
        let args = self.sep_end_by(")", |p| p.term(false))?;
        let mut annotations = Vec::new();
        // `option [] $ list factAnnotation` (Theory/Text/Parser/Fact.hs:48): when
        // no annotation
        // list follows, the failed `[` attempt leaves its label at the
        // position after the closing `)` lexeme — merged into a consumed
        // failure raised exactly there (e.g. a formula's closing quote,
        // [`Self::formula_close_error`]).
        self.skip_ws();
        let annot_attempt = self.lx.pos().offset;
        self.fact_annot_hangover = if self.peek_punct("[") {
            None
        } else {
            Some(annot_attempt)
        };
        if self.try_punct("[") && !self.try_punct("]") {
            loop {
                // HS `factAnnotation` (Theory/Text/Parser/Fact.hs:31-36):
                // SolveFirst is
                // `opUnion`, and `opUnion = symbol_ "++" <|> symbol_ "+"`
                // (Token.hs:551-552) — so `++` is accepted as well as `+`
                // (try `++` first, then `+`). SolveLast is `opMinus` (`-`),
                // NoSources is `no_precomp`.
                if self.try_punct("++") || self.try_punct("+") {
                    annotations.push(FactAnnotation::SolveFirst);
                } else if self.try_punct("-") {
                    annotations.push(FactAnnotation::SolveLast);
                } else if self.try_kw("no_precomp") {
                    annotations.push(FactAnnotation::NoSources);
                } else {
                    break;
                }
                if !self.try_punct(",") {
                    break;
                }
            }
            self.require_punct("]")?;
        }
        // HS-faithful parse-time canonicalisation, mirroring
        // `Theory.Text.Parser.Fact.mkProtoFact`
        // (Theory/Text/Parser/Fact.hs:56-63) combined with
        // `factTagMultiplicity` (Model/Fact.hs:382-388) and `factTagName`
        // (Model/Fact.hs:535-545).  Any fact whose name uppercases to one of
        // the reserved special names becomes that special fact, which:
        //   * fixes the CANONICAL name (KU/KD/Ded/Fr/In/Out),
        //   * fixes the multiplicity from the tag (KU and KD are Persistent;
        //     everything else here is Linear), discarding the user-written `!`,
        //   * enforces arity one (`singleTerm`) — a parse `fail` on mismatch,
        //   * drops annotations for all special facts except IN
        //     (`inFactAnn ann` keeps them; outFact/kuFact/kdFact/dedLogFact/
        //     freshFact take no annotations),
        //   * rejects `!Fr(...)` ("fresh facts cannot be persistent").
        // Because HS wraps the whole `fact'` body in `try`, a `fail` here
        // backtracks; in rule context this surfaces as a hard load error,
        // and in formula context the alternative (term atom) is tried.  We
        // mirror that by returning `Err` from `fact()`.
        let upper = name.to_ascii_uppercase();
        // (canonical name, persistent, keep-annotations)
        let canonical: Option<(&str, bool, bool)> = match upper.as_str() {
            "OUT" => Some(("Out", false, false)),
            "IN" => Some(("In", false, true)),
            "KU" => Some(("KU", true, false)),
            "KD" => Some(("KD", true, false)),
            "DED" => Some(("Ded", false, false)),
            "FR" => Some(("Fr", false, false)),
            _ => None,
        };
        if let Some((cname, cpersistent, keep_ann)) = canonical {
            // `!Fr(...)` is a parse error (Theory/Text/Parser/Fact.hs:39-63, see
            // line 45).
            if upper == "FR" && persistent {
                return Err(self.err("fresh facts cannot be persistent"));
            }
            // `singleTerm`: special facts have arity one
            // (Theory/Text/Parser/Fact.hs:52-54).
            if args.len() != 1 {
                return Err(self.err(format!(
                    "fact '{}' used with arity {} instead of arity one",
                    name,
                    args.len()
                )));
            }
            return Ok(Fact {
                persistent: cpersistent,
                name: cname.to_string(),
                args,
                annotations: if keep_ann { annotations } else { Vec::new() },
            });
        }
        Ok(Fact {
            persistent,
            name,
            args,
            annotations,
        })
    }

    // =========================================================================
    // Formulas
    // =========================================================================

    fn formula(&mut self) -> Result<Formula, ParseError> {
        self.iff()
    }

    fn iff(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.implies()?;
        if self.try_punct("<=>") || self.try_punct("⇔") {
            let rhs = self.implies()?;
            Ok(Formula::Iff(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn implies(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.disjuncts()?;
        if self.try_punct("==>") || self.try_punct("⇒") {
            let rhs = self.implies()?;
            Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn disjuncts(&mut self) -> Result<Formula, ParseError> {
        self.chainl1(
            |p| p.conjuncts(),
            // `|` is also process parallel — but inside formulas it's OR.
            |p| (p.try_punct("|") || p.try_punct("∨")).then_some(()),
            |(), lhs, rhs| Formula::Or(Box::new(lhs), Box::new(rhs)),
        )
    }

    fn conjuncts(&mut self) -> Result<Formula, ParseError> {
        self.chainl1(
            |p| p.negation(),
            |p| (p.try_punct("&") || p.try_punct("∧")).then_some(()),
            |(), lhs, rhs| Formula::And(Box::new(lhs), Box::new(rhs)),
        )
    }

    fn negation(&mut self) -> Result<Formula, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.fatom()?;
            Ok(Formula::Not(Box::new(f)))
        } else {
            self.fatom()
        }
    }

    /// `nodevarTerm = lit . Var <$> nodep` (Theory/Text/Parser/Formula.hs:59):
    /// a variable in a timepoint position takes `LSortNode` from its
    /// position, since `nodevar` is the only parser that reads there
    /// (Token.hs:443-448).  `nodevar` accepts `#name`, a bare name and
    /// `name:node`, and fails on any other spelling.  It reads the bare name
    /// with `indexedIdentifier` (Token.hs:445-447), which never consults the
    /// signature, so a name that is also an arity-0 symbol is a timepoint
    /// variable here rather than the constant `nullaryApp` builds for it
    /// elsewhere (Theory/Text/Parser/Term.hs:158-163) — the zero-argument
    /// application arm below. Callers that must enforce `nodevarTerm` syntax
    /// validate the parsed shape with [`Self::node_operand`] first.
    fn node_sorted(t: Term) -> Term {
        match t {
            Term::Var(mut v) => {
                v.sort = LSort::Node;
                Term::Var(v)
            }
            Term::App(name, args) if args.is_empty() => Term::Var(VarSpec {
                name,
                idx: 0,
                sort: LSort::Node,
                typ: None,
            }),
            other => other,
        }
    }

    /// Accept the shapes HS `nodevarTerm` can read after a relational
    /// alternative backtracks: a node/bare variable, or a bare identifier
    /// that the ordinary term parser had resolved as a nullary symbol.
    fn node_operand(t: Term) -> Option<Term> {
        match t {
            Term::Var(v) if matches!(v.sort, LSort::Msg | LSort::Node) => {
                Some(Self::node_sorted(Term::Var(v)))
            }
            Term::App(_, ref args) if args.is_empty() => Some(Self::node_sorted(t)),
            _ => None,
        }
    }

    fn fatom(&mut self) -> Result<Formula, ParseError> {
        self.skip_ws();
        if self.try_kw("F") || self.try_punct("⊥") {
            return Ok(Formula::False);
        }
        if self.try_kw("T") || self.try_punct("⊤") {
            return Ok(Formula::True);
        }
        // Quantifiers: All / ∀ / Ex / ∃
        if self.try_kw("All") || self.try_punct("∀") {
            let vs = self.quantifier_binders()?;
            let f = self.iff()?;
            return Ok(Formula::Forall(vs, Box::new(f)));
        }
        if self.try_kw("Ex") || self.try_punct("∃") {
            let vs = self.quantifier_binders()?;
            let f = self.iff()?;
            return Ok(Formula::Exists(vs, Box::new(f)));
        }
        // Parenthesised formula — backtrack to term-relational on failure,
        // since e.g. `(a+z) = b` should parse as a relational equality atom
        // whose LHS happens to be a parenthesised term.
        if self.lx.peek() == Some('(') {
            let save_p = self.save();
            self.lx.bump();
            self.skip_ws();
            if let Ok(f) = self.iff() {
                if self.try_punct(")") {
                    return Ok(f);
                }
            }
            self.restore(save_p);
        }
        // Atom: try last(t), action f@t, equality, less, subterm, smaller, predicate
        if self.try_kw("last") {
            self.require_punct("(")?;
            let t = self.term(false)?;
            self.require_punct(")")?;
            return Ok(Formula::Atom(Atom::Last(Self::node_sorted(t))));
        }
        // Try fact@t (action atom)
        let save_f = self.save();
        if let Ok(f) = self.fact() {
            if self.try_punct("@") {
                let t = self.term(false)?;
                return Ok(Formula::Atom(Atom::Action(f, Self::node_sorted(t))));
            }
            // HS `blatom` (Theory/Text/Parser/Formula.hs:45-57) tries the
            // term-relational atoms
            // (Subterm/Less/smallerp/EqE, alts 3-6, all `try`-guarded) BEFORE
            // the bare-fact `Pred` alternative (alt 7). So a name like `Foo(x)`
            // that is also a function symbol must be re-parsed as a term when a
            // relational operator follows. A genuine predicate atom is never
            // followed by such an operator, so this only diverts on what HS
            // already treats as a term relation.
            if !self.peek_atom_relop() {
                // Predicate atom (no @, no following relational operator)
                return Ok(Formula::Atom(Atom::Pred(f)));
            }
        }
        self.restore(save_f);
        // Try term-level atom: t = t / t < t / t << t / t (<) t
        let lhs = self.term(false)?;
        if self.try_punct("=") {
            let rhs = self.term(false)?;
            // `blatom`'s "term equality" alternative reads both operands with
            // `msgvar`, which rejects a node variable, so an equality whose
            // left operand is one is the LAST alternative, "node equality"
            // (Theory/Text/Parser/Formula.hs:51,56): `nodevarTerm` on both
            // sides, which reads a bare right operand as a timepoint.
            if matches!(&lhs, Term::Var(v) if v.sort == LSort::Node)
                || matches!(&rhs, Term::Var(v) if v.sort == LSort::Node)
            {
                let lhs = Self::node_operand(lhs)
                    .ok_or_else(|| self.err("expected node variable before `=`"))?;
                let rhs = Self::node_operand(rhs)
                    .ok_or_else(|| self.err("expected node variable after `=`"))?;
                return Ok(Formula::Atom(Atom::Eq(lhs, rhs)));
            }
            return Ok(Formula::Atom(Atom::Eq(lhs, rhs)));
        }
        if self.try_punct("<<") || self.try_punct("⊏") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Subterm(lhs, rhs)));
        }
        if self.try_punct("(<)") {
            if !self.sig_enable_mset {
                return Err(
                    self.err("Need builtins: multiset to use multiset comparison operator.")
                );
            }
            let rhs = self.term(false)?;
            // HS `smallerp` (Theory/Text/Parser/Formula.hs:30-38): the multiset
            // comparison operator `a (<) b` desugars DIRECTLY into the built-in
            // `Smaller` predicate fact at PARSE time —
            //   `(Syntactic . Pred) $ protoFact Linear "Smaller" [a,b]`.
            // There is no dedicated `(<)` atom downstream in HS; the whole
            // pipeline (condition rendering, the `if Smaller(..)_<idx>` rule
            // name, the restriction expansion via the built-in predicate, and
            // the AC-sorted union rendering) flows from this being a `Smaller`
            // predicate atom.  We mirror that exactly.
            let fact = Fact {
                persistent: false,
                name: "Smaller".to_string(),
                args: vec![lhs, rhs],
                annotations: Vec::new(),
            };
            return Ok(Formula::Atom(Atom::Pred(fact)));
        }
        if self.try_punct("<") {
            // HS `blatom` (Theory/Text/Parser/Formula.hs:44-60, see line 49)
            // restricts both operands of `<` to
            // node/timepoint variables: `Less <$> try (nodevarTerm <* opLess)
            // <*> nodevarTerm`. We parse terms first so the earlier atom
            // alternatives can share this prefix, then validate the two
            // operands against exactly the shapes `nodevarTerm` accepts.
            let rhs = self.term(false)?;
            let lhs = Self::node_operand(lhs)
                .ok_or_else(|| self.err("expected node variable before `<`"))?;
            let rhs = Self::node_operand(rhs)
                .ok_or_else(|| self.err("expected node variable after `<`"))?;
            return Ok(Formula::Atom(Atom::Less(lhs, rhs)));
        }
        // No relational operator follows the term.  HS `blatom`'s remaining
        // alternatives (Theory/Text/Parser/Formula.hs:45-57): the `Pred` fact
        // (alt 7 — reachable
        // here when `peek_atom_relop` diverted a fact whose relop turned out
        // to belong AFTER it, e.g. `P3(x) = y` with `P3` not a function), then
        // the UN-try'd node-equality `nodevarTerm <* opEqual` (alt 8), whose
        // consumed failure aborts the whole formula parse and is the frame
        // the user sees.
        let after_lhs = self.save();
        self.restore(save_f);
        if let Ok(f) = self.fact() {
            return Ok(Formula::Atom(Atom::Pred(f)));
        }
        self.restore(save_f);
        Err(self.formula_atom_tail_error(save_f, after_lhs))
    }

    /// The error HS's formula-atom alternation reports once every `blatom`
    /// alternative has failed for the atom that starts at `atom_start`
    /// (Theory/Text/Parser/Formula.hs:44-60).
    ///
    /// The last alternative, `EqE <$> (nodevarTerm <* opEqual) <*> …`, is not
    /// `try`-wrapped: when `nodevar` (Token.hs:443-447 — a `#`-prefixed or
    /// bare `indexedIdentifier`) can consume the atom's head, `opEqual`'s
    /// failure right after it is a CONSUMED error, which parsec's `<|>` does
    /// not merge away — it aborts the alternation and every accumulated label
    /// of the earlier alternatives is discarded.  The frame is the identifier
    /// lexeme's hangovers plus `"="`, at the position right after the name —
    /// even when the failed atom continued past it (`g(x) @ #i` errors at the
    /// `(`).
    ///
    /// When `nodevar` cannot consume anything (a non-identifier head such as
    /// `'a' @ …`), every alternative failed EMPTY and the merged error keeps
    /// only the furthest-position labels: the `<?>` relabels of the two (three
    /// with multiset) `try`-wrapped relational alternatives that consumed the
    /// term and failed where the relational operator was expected —
    /// `"subterm predicate"`, `"multiset comparisson"` (sic, only when the
    /// multiset signature bit is on — `smallerp` fails early otherwise) and
    /// `"term equality"`.
    fn formula_atom_tail_error(&mut self, atom_start: Pos, after_lhs: Pos) -> ParseError {
        self.restore(atom_start);
        self.skip_ws();
        if self.lx.peek() == Some('#') {
            self.lx.bump();
        }
        let pre_ident = self.save();
        if let Some(id) = self.lx.identifier() {
            let ident_end = self.ident_end_from(pre_ident, &id);
            self.try_dot_index();
            let idx_spent = self.dot_index_consumed;
            self.skip_ws();
            let pos = self.lx.pos();
            let mut messages = vec![Message::SysUnExpect(self.unexpected_token())];
            if ident_end == pos.offset {
                messages.push(Message::Expect("letter or digit".to_string()));
            }
            if !idx_spent {
                messages.push(Message::Expect("\".\"".to_string()));
            }
            messages.push(Message::Expect("\"=\"".to_string()));
            return ParseError::at(pos, messages);
        }
        self.restore(after_lhs);
        let mut labels: Vec<&str> = vec!["subterm predicate"];
        if self.sig_enable_mset {
            labels.push("multiset comparisson");
        }
        labels.push("term equality");
        self.err_expect(&labels)
    }

    // =========================================================================
    // Terms
    // =========================================================================

    /// Top-level term parser.  `eqn` indicates we're inside an `equations:`
    /// block, which closes the builtin algebraic operators (`++`, `%+`, `⊕`,
    /// `*`, `^`) that the signature bits would otherwise open; the
    /// user-declared `[AC]` infix operators of [`Self::acterm`] stay open, as
    /// in HS's `acterm True llitNoPub`.
    fn term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.tupleterm(eqn)
    }

    /// HS `tupleterm`'s `chainr1 (msetterm …) (… <$ comma)`
    /// (Theory/Text/Parser/Term.hs:211-212)
    /// with its comma chain unreachable at this level: a comma-grouped
    /// sequence only ever occurs inside `<...>` or `f{...}`, where
    /// [`Self::tuple_contents`] folds it into the right-associative pair.  So
    /// outside those brackets `tupleterm` is exactly `msetterm`.
    fn tupleterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.msetterm(eqn)
    }

    /// Parse a comma-separated term sequence and fold into a right-assoc
    /// pair (or single term). Used inside `<...>` and `f{...}`.
    fn tuple_contents(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut items = Vec::new();
        loop {
            let t = self.msetterm(eqn)?;
            items.push(t);
            if !self.try_punct(",") {
                break;
            }
        }
        if items.len() == 1 {
            Ok(items.into_iter().next().unwrap())
        } else {
            Ok(Term::Pair(items))
        }
    }

    /// [`Self::chainl1`]'s fold for the infix term operators.
    fn bin_op_term(op: BinOp, lhs: Term, rhs: Term) -> Term {
        Term::BinOp(op, Box::new(lhs), Box::new(rhs))
    }

    fn msetterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let lhs = self.msetterm_inner(eqn)?;
        // The outermost chain level finishing records the carried error the
        // enclosing grammar merges into a failure raised right here (see
        // [`Parser::term_carry`]).
        self.finish_term_carry(eqn);
        Ok(lhs)
    }

    /// HS `msetterm` (Theory/Text/Parser/Term.hs:195-200): the union level runs
    /// only under `enableMSet && not eqn`, otherwise the parser drops straight
    /// to [`Self::natterm`] and `++`/`+` are not term operators at all.
    fn msetterm_inner(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.sig_enable_mset || eqn {
            return self.natterm(eqn);
        }
        self.chainl1(
            |p| p.natterm(eqn),
            |p| {
                p.skip_ws();
                // `++` or `+` (as multiset union); careful with `+` for NDC
                // and `%+` for nat plus, which are handled separately.
                if p.lx.rest().starts_with("++") {
                    p.lx.bump();
                    p.lx.bump();
                    p.skip_ws();
                    Some(BinOp::Union)
                } else if p.lx.rest().starts_with('+') && !p.lx.rest().starts_with("+>") {
                    // Avoid `+` that's part of process NDC. At term level
                    // we always treat `+` as union.
                    p.lx.bump();
                    p.skip_ws();
                    Some(BinOp::Union)
                } else {
                    None
                }
            },
            Self::bin_op_term,
        )
    }

    /// HS `natterm` (Theory/Text/Parser/Term.hs:203-208): `%+` needs
    /// `enableNat && not eqn`.
    fn natterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.sig_enable_nat || eqn {
            return self.xorterm(eqn);
        }
        self.chainl1(
            |p| p.xorterm(eqn),
            |p| p.try_punct("%+").then_some(BinOp::NatPlus),
            Self::bin_op_term,
        )
    }

    /// HS `xorterm` (Theory/Text/Parser/Term.hs:187-192): `XOR`/`⊕` need
    /// `enableXor && not eqn`.
    fn xorterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.sig_enable_xor || eqn {
            return self.multterm(eqn);
        }
        self.chainl1(
            |p| p.multterm(eqn),
            |p| (p.try_kw("XOR") || p.try_punct("⊕")).then_some(BinOp::Xor),
            Self::bin_op_term,
        )
    }

    /// HS `multterm` (Theory/Text/Parser/Term.hs:179-185): without
    /// `enableDH && not eqn` the parser skips BOTH this level and
    /// [`Self::expterm`], so neither `*` nor `^` is a term operator.
    fn multterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.sig_enable_dh || eqn {
            return self.acterm(eqn);
        }
        self.chainl1(
            |p| p.expterm(eqn),
            |p| {
                p.skip_ws();
                // Multiplication is `*`, except for the `*}` that closes a
                // formal comment.
                if p.lx.peek() == Some('*') && p.lx.peek2() != Some('}') {
                    p.lx.bump();
                    p.skip_ws();
                    Some(BinOp::Mult)
                } else {
                    None
                }
            },
            Self::bin_op_term,
        )
    }

    /// HS `expterm` is "a left-associative sequence of exponentiations"
    /// (`chainl1`, Parser/Term.hs:174-176).
    fn expterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.chainl1(
            |p| p.acterm(eqn),
            |p| p.try_punct("^").then_some(BinOp::Exp),
            Self::bin_op_term,
        )
    }

    /// A left-associative sequence of user-defined AC operators — the infix
    /// notation `t1 f t2` for a binary symbol declared `f/2 [AC]`.
    ///
    /// Port of HS `acterm` (Theory/Text/Parser/Term.hs:165-174):
    /// ```haskell
    /// acterm eqn plit = do
    ///     acsyms <- stACFunSyms . sig <$> getState
    ///     parseACSym $ S.toList acsyms
    ///   where
    ///     parseACSym [] = term eqn plit
    ///     parseACSym (op:ops) = chainl1 (parseACSym ops) ((\a b -> fAppACfct op [a,b]) <$ opAC op)
    /// ```
    /// One `chainl1` level per declared AC symbol, nested in
    /// `stACFunSyms`/`ac_fun_syms` order, so a later symbol in that
    /// order binds tighter than an earlier one; the innermost level is a single
    /// atomic term (HS `term`, here [`Self::atom_term`]).  The `eqn` flag is
    /// only passed down: AC operators ARE accepted inside `equations:`, which is
    /// how equational theories over AC symbols are written.
    fn acterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let t = self.ac_chain(0, eqn)?;
        // `equations:` parses its operands with `acterm` directly, so this is
        // the outermost chain level there — record the carried error (inside a
        // larger chain the enclosing `msetterm` re-records the same thing).
        self.finish_term_carry(eqn);
        Ok(t)
    }

    /// The `parseACSym` recursion of [`Self::acterm`]: the `chainl1` level for
    /// `ac_fun_syms[level]`, or the atomic-term base case once the list is
    /// exhausted.
    ///
    /// The infix spelling is recorded as [`BinOp::AcFct`], never `Term::App`:
    /// HS `acterm` builds `fAppACfct op [a,b]` — the AC symbol — even when the
    /// same name is ALSO a `NoEq` symbol of the signature, whereas the PREFIX
    /// spelling of such a dual-declared name resolves through `lookupArity` to
    /// the `NoEq` symbol (its `lookup` list sorts every `NoEqUser` before
    /// every `ACfctUser`, Theory/Text/Parser/Term.hs:62-72,
    /// Term/Term/FunctionSymbols.hs:146-147).  The AST node therefore has to
    /// carry which spelling was written for the readers to resolve it.
    fn ac_chain(&mut self, level: usize, eqn: bool) -> Result<Term, ParseError> {
        let Some(op) = self.ac_fun_syms.get(level).cloned() else {
            return self.atom_term(eqn);
        };
        self.chainl1(
            |p| p.ac_chain(level + 1, eqn),
            // HS `opAC (op, _) = symbol_ (BC.unpack op)`, i.e. the symbol's own
            // name as a plain token.  `try_kw` adds a word boundary that HS's
            // `symbol` lacks, so HS would also accept the name as a PREFIX of
            // the following token (`f(x) fg(y)` parsing as `f(f(x), g(y))` for
            // an AC symbol `f`); such input is not valid syntax in any theory
            // and errors here instead.
            |p| p.try_kw(&op).then(|| BinOp::AcFct(intern_ac_name(&op))),
            Self::bin_op_term,
        )
    }

    /// One atomic term, maintaining [`Parser::var_dot_hangover`]: the variable
    /// return sites inside [`Self::atom_term_inner`] set it via
    /// [`Self::note_var_dot_hangover`], and every atom whose LAST lexeme is not
    /// the variable's identifier clears it here.  `AlgApp` and `PatMatch` are
    /// transparent — their rightmost lexeme belongs to the sub-atom that
    /// already maintained the flag (HS `binaryAlgApp`'s trailing `arg2 <- term
    /// eqn plit`, Theory/Text/Parser/Term.hs:109-121).
    fn atom_term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let t = self.atom_term_inner(eqn)?;
        if !matches!(t, Term::Var(_) | Term::AlgApp(..) | Term::PatMatch(_)) {
            self.var_dot_hangover = false;
        }
        Ok(t)
    }

    /// Whether the variable just consumed ended on a plain `indexedIdentifier`
    /// lexeme: no explicit `.<index>` (`option 0 (try (dot *> natural))`,
    /// Token.hs:395-400), no `:sort` suffix (`sortedLVar`'s suffix arm ends in
    /// `symbol_ (sortSuffix s)`, Token.hs:409-421) and no SAPIC `:type`
    /// annotation.  That is the shape [`Self::bare_ident_term`] reads as an
    /// arity-0 symbol's constant, and the shape that leaves the
    /// `Expect "\".\""` hangover behind.
    fn is_plain_indexed_identifier(&self, v: &VarSpec) -> bool {
        !self.dot_index_consumed && !self.sort_suffix_consumed && v.typ.is_none()
    }

    /// Set [`Parser::var_dot_hangover`] for the variable atom just consumed.
    ///
    /// HS leaves the `Expect "\".\""` at the current position iff the
    /// variable's LAST lexeme was its `identifier`: the lexeme is a plain
    /// `indexedIdentifier` ([`Self::is_plain_indexed_identifier`]) and the
    /// name is not one `nullaryApp` claims instead of `plit` — an arity-0
    /// symbol of `funSyms ∪ macroNames`, matched by `symbol`, not
    /// `indexedIdentifier` (Theory/Text/Parser/Term.hs:148,158-163).  Every
    /// variable parse runs [`Self::try_dot_index`] right after its
    /// identifier, so [`Parser::dot_index_consumed`] is the just-parsed
    /// variable's at this point.
    fn note_var_dot_hangover(&mut self, v: &VarSpec) {
        self.var_dot_hangover =
            self.is_plain_indexed_identifier(v) && !self.is_nullary_sym(&v.name);
        // Where this variable's `letter or digit` identifier hangover sits —
        // recorded by the identifier-consuming site that just ran (see
        // [`Parser::last_ident_end`]) and only meaningful alongside the dot
        // hangover (both are the tail of the same `indexedIdentifier` lexeme).
        self.var_hangover_ident_end = if self.var_dot_hangover {
            self.last_ident_end
        } else {
            None
        };
    }

    /// What HS `lookupArity` (Theory/Text/Parser/Term.hs:62-72) resolves a
    /// prefix-application head to.
    ///
    /// Its `lookup` list is `map extractName (S.toList (userDefinedFunSyms
    /// maudeSig) ++ map NoEqUser (S.toList (macroNames maudeSig) ++
    /// [(emapSymString, (2,Public,Constructor,NotNDC))]))` and `lookup` takes
    /// the FIRST name match, so:
    ///
    ///   * every `NoEqUser` outranks every `ACfctUser` (`UserDefinedSym`'s
    ///     derived `Ord` ranks constructors in declaration order,
    ///     Term/Term/FunctionSymbols.hs:146-147) — a dual-declared name
    ///     resolves NoEq;
    ///   * among same-name `NoEqUser` entries the set order picks the smallest
    ///     `(arity, priv, constr, ndc)` tuple ([`FunOptions::ord_key`]);
    ///   * `userDefinedFunSyms` is built from the FULL `funSyms`
    ///     (Term/Maude/Signature.hs:157-164), so the enabled theories' `NoEq`
    ///     symbols ([`Self::enabled_theory_noeq_syms`]) participate;
    ///   * macros come after the function symbols, and `em` is ALWAYS present
    ///     at arity 2 (even without bilinear-pairing), appended last.
    ///
    /// `Some(NoEq)`'s applications are arity-checked
    /// (`Theory/Text/Parser/Term.hs:97-100`);
    /// `Some(Ac)`'s are not (the check is gated on `NotAC`).  `None` is HS's
    /// `fail "unknown operator ..."`, which the try-wrapped application
    /// converts into a backtrack.
    fn lookup_arity(&self, op: &str) -> Option<ArityRes> {
        let mut best: Option<FunOptions> = None;
        let mut consider = |o: FunOptions| {
            if best.map_or(true, |b: FunOptions| o.ord_key() < b.ord_key()) {
                best = Some(o);
            }
        };
        for (n, o) in self.fun_syms.iter() {
            if n == op {
                consider(*o);
            }
        }
        for s in self.enabled_theory_noeq_syms() {
            if s.name == op.as_bytes() {
                consider(FunOptions::of_no_eq(s));
            }
        }
        if let Some(opts) = best {
            return Some(ArityRes::NoEq { opts });
        }
        if self.ac_fun_syms.iter().any(|n| n == op) {
            return Some(ArityRes::Ac);
        }
        if let Some((_, o)) = self.macro_syms.iter().find(|(n, _)| n == op) {
            return Some(ArityRes::NoEq { opts: *o });
        }
        if op == "em" {
            // The appended `(emapSymString, (2,Public,Constructor,NotNDC))`
            // row: `naryOpApp` special-cases the NAME into `fAppC EMap`
            // (Theory/Text/Parser/Term.hs:102-103), which the readers resolve
            // from the `em`
            // application node; the arity check runs like any NoEq's.
            return Some(ArityRes::NoEq {
                opts: FunOptions::plain(2),
            });
        }
        None
    }

    /// Whether `name` is an arity-0 symbol HS `nullaryApp`
    /// (Theory/Text/Parser/Term.hs:158-163)
    /// parses via `symbol` — searched over `funSyms maudeSig` (the subterm
    /// signature plus the enabled theories' symbols) and `macroNames`.
    fn is_nullary_sym(&self, name: &str) -> bool {
        self.fun_syms
            .iter()
            .chain(self.macro_syms.iter())
            .any(|(n, o)| n == name && o.arity == 0)
            || self
                .enabled_theory_noeq_syms()
                .any(|s| s.name == name.as_bytes() && s.arity == 0)
    }

    /// The theory-level `NoEq` symbols the enabled signature bits fold into
    /// `funSyms` — see [`TheoryNoEqSyms`].
    fn enabled_theory_noeq_syms(&self) -> impl Iterator<Item = &'static NoEqSym> {
        let syms = theory_noeq_syms();
        [
            (self.sig_enable_dh, &syms.dh),
            (self.sig_enable_bp, &syms.bp),
            (self.sig_enable_xor, &syms.xor),
            (self.sig_enable_nat, &syms.nat),
        ]
        .into_iter()
        .filter(|(enabled, _)| *enabled)
        .flat_map(|(_, syms)| syms.iter())
    }

    /// One atomic term.
    fn atom_term_inner(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.skip_ws();
        // SAPIC pattern-match prefix `=v` — legal only in pattern positions
        // ([`Parser::allow_pat`]).  Elsewhere no term alternative starts with
        // `=`, so the character falls through to the no-alternative error,
        // matching HS where the literal parser there has no `=` branch.
        if self.allow_pat && self.lx.peek() == Some('=') {
            // Avoid consuming `=` if it's the start of an operator like `==>`,
            // `=>`, or `==`.
            let r = self.lx.rest();
            if !r.starts_with("==") && !r.starts_with("=>") {
                self.lx.bump();
                self.skip_ws();
                // HS `sapicpatternvar` (Token.hs:512-519): after the `=` comes
                // `sapicvar` — a VARIABLE, never a general term.  `=h(x)`
                // parses as the match-var `h`, and the `(` then breaks the
                // enclosing grammar through the variable's hangover labels.
                let inner = self.pattern_var_atom()?;
                return Ok(Term::PatMatch(Box::new(inner)));
            }
        }
        // Parens for grouping
        if self.try_punct("(") {
            let t = self.msetterm(eqn)?;
            // `(` … `)` is grouping only: Tamarin spells pairs `<a, b>`, so a
            // comma is not accepted here — HS `parens (msetterm eqn plit)`
            // (Theory/Text/Parser/Term.hs:141), whose closing `symbol ")"`
            // merges the term's
            // hangovers when it fails.
            if !self.try_punct(")") {
                return Err(self.err_expect_after_term(&["\")\""]));
            }
            // The atom's last lexeme is the `)`, even when the grouped term
            // collapses to a bare variable node.
            self.var_dot_hangover = false;
            return Ok(t);
        }
        // Pair `<a, b, ...>` (right-associative). The `<<` subterm and
        // `<=>` iff operators only appear at formula level — at term level a
        // bare `<` always opens a tuple. We do refuse `<-` (process arrow).
        if self.lx.peek() == Some('<') {
            let r = self.lx.rest();
            if !r.starts_with("<-") {
                self.lx.bump(); // consume '<'
                self.skip_ws();
                // HS `pairing = angled (tupleterm eqn plit)`
                // (Theory/Text/Parser/Term.hs:157) with
                // `tupleterm = chainr1 (msetterm ...) (... <$ comma)`
                // (Theory/Text/Parser/Term.hs:211-212). `chainr1` requires >=1
                // operand, so [`Self::tuple_contents`] always reads one: an
                // empty `<>` fails to parse (matching HS, where no other
                // `term` alternative starts with `<`), and a singleton `<a>`
                // collapses to `a`.
                let t = self.tuple_contents(eqn)?;
                // `chainr1`'s failed `comma` and `angled`'s closing `symbol
                // ">"` both sit at the last operand's stop position, merged
                // with its hangovers.
                if !self.try_punct(">") {
                    return Err(self.err_expect_after_term(&["\",\"", "\">\""]));
                }
                // The atom's last lexeme is the `>`, even when a singleton
                // `<a>` collapses to its operand's node.
                self.var_dot_hangover = false;
                return Ok(t);
            }
        }
        // Special tokens
        if self.try_kw("DH_neutral") {
            return Ok(Term::DhNeutral);
        }
        if self.try_punct("1:nat") {
            if !self.sig_enable_nat {
                return Err(
                    self.err("natural-number literal 1:nat requires the natural-numbers builtin")
                );
            }
            return Ok(Term::NatOne);
        }
        if self.try_punct("%1") {
            if !self.sig_enable_nat {
                return Err(
                    self.err("natural-number literal %1 requires the natural-numbers builtin")
                );
            }
            return Ok(Term::NatOne);
        }
        // `1` only valid when DH is enabled; we accept it always at parse level.
        // Divergence from HS, benign on the corpus: HS `term`
        // (Theory/Text/Parser/Term.hs:137-163, see line 149) tries
        // `symbol "1"` before the identifier path, and `symbol`/`T.symbol`
        // (Token.hs:272-273, see line 273) has NO trailing word boundary, so HS splits the leading
        // `1` off `1abc`/`12` (yielding fAppOne, leaving `abc`/`2`, which then
        // fails as a stray token). Note HS identifiers CAN start with a digit
        // (Token.hs:214-230, see line 223 `identStart = alphaNum`), so a bare `2` is the variable
        // `2`. The word-boundary guard below only diverges on a `1` immediately
        // followed by an alphanumeric/`_` (e.g. `1abc`, `12`) — inputs that are
        // never valid message terms and never appear in any .spthy, so accepted
        // valid output is identical; only the parse-error location differs.
        {
            let save = self.save();
            self.skip_ws();
            if self.lx.peek() == Some('1') {
                let mut probe = self.lx.clone();
                probe.bump();
                let next = probe.peek();
                if next.map_or(true, |c| !c.is_alphanumeric() && c != '_') {
                    self.lx.bump();
                    self.skip_ws();
                    return Ok(Term::NumberOne);
                }
            }
            self.restore(save);
        }
        // Sigil-prefixed variables: ~x, $x, #x, %x.
        if let Some(c @ ('~' | '$' | '#')) = self.lx.peek() {
            // Could be a fresh-name literal `~'n'` or `%'n'` — handled below.
            let mut probe = self.lx.clone();
            probe.bump();
            if c == '~' && probe.peek() == Some('\'') {
                self.lx.bump();
                let s = self
                    .lx
                    .single_quoted()
                    .ok_or_else(|| self.err("bad fresh literal"))?;
                return Ok(Term::FreshLit(s));
            }
            // Otherwise: variable.
            if let Some(v) = self.try_var_spec()? {
                let v = self.attach_sort_suffix(v)?;
                self.note_var_dot_hangover(&v);
                return Ok(Term::Var(v));
            }
        }
        if self.lx.peek() == Some('%') {
            // %'n' / %x — distinguish. (`%1` is already handled above via the
            // `try_punct("%1")` token match.)
            let mut probe = self.lx.clone();
            probe.bump();
            match probe.peek() {
                Some('\'') => {
                    if !self.sig_enable_nat {
                        return Err(self.err("nat names require the natural-numbers builtin"));
                    }
                    self.lx.bump();
                    let s = self
                        .lx
                        .single_quoted()
                        .ok_or_else(|| self.err("bad nat literal"))?;
                    return Ok(Term::NatLit(s));
                }
                Some(c) if c.is_ascii_alphabetic() => {
                    if !self.sig_enable_nat {
                        return Err(
                            self.err("nat-sorted variables require the natural-numbers builtin")
                        );
                    }
                    if let Some(v) = self.try_var_spec()? {
                        let v = self.attach_sort_suffix(v)?;
                        self.note_var_dot_hangover(&v);
                        return Ok(Term::Var(v));
                    }
                }
                _ => {}
            }
        }
        // Literal `'foo'` is a public name term.
        if self.lx.peek() == Some('\'') {
            let s = self
                .lx
                .single_quoted()
                .ok_or_else(|| self.err("bad public literal"))?;
            return Ok(Term::PubLit(s));
        }
        // diff(a, b) — HS `diffOp = symbol "diff" *> parens ...`
        // (Theory/Text/Parser/Term.hs:123-135, see line 125).
        // `diff` is a reserved name (Token.hs:214-230, see line 225) so it is NOT an identifier and
        // must be matched as a keyword here, BEFORE the identifier path. The
        // word-boundary check in `peek_symbol` keeps `diffuse(...)` an identifier
        // (function application), matching HS where `naryOpApp` handles it.
        if self.lx.peek_symbol("diff") {
            // Step over the keyword by hand rather than via `symbol`: the two
            // parsec frames that can surface below sit at *different* positions,
            // one before and one after the lexeme's trailing whitespace.
            self.skip_ws();
            for _ in 0.."diff".len() {
                self.lx.bump();
            }
            let after_word = self.lx.pos();
            self.skip_ws();
            if self.lx.peek() == Some('(') {
                self.lx.bump();
                // HS `parens (commaSep (msetterm eqn plit))`, and `commaSep = flip
                // sepEndBy comma` (Token.hs:353-355) admits an empty list and a
                // trailing comma — so the parse itself accepts any argument count
                // and only the `fail` below constrains it.
                let mut ts = Vec::new();
                loop {
                    self.skip_ws();
                    if self.lx.peek() == Some(')') {
                        break;
                    }
                    ts.push(self.msetterm(eqn)?);
                    if !self.try_punct(",") {
                        break;
                    }
                }
                self.require_punct(")")?;
                // `diffOp`'s three `fail`s, in HS's order
                // (Theory/Text/Parser/Term.hs:126-132): the
                // first one that fires is the one the user sees, so an argument
                // count other than 2 hides both of the others.  Each is a bare
                // `fail` after the closing-paren lexeme, hence [`Self::err_fail`]
                // at the post-whitespace position, relabelled `term` by the
                // enclosing `<?>`.
                if ts.len() != 2 {
                    return Err(self.err_fail_labelled(
                        "the diff operator requires exactly 2 arguments",
                        "term",
                    ));
                }
                if eqn {
                    return Err(
                        self.err_fail_labelled("diff operator not allowed in equations", "term")
                    );
                }
                if !self.enable_diff {
                    return Err(self
                        .err_fail_labelled("diff operator found, but flag diff not set", "term"));
                }
                let mut args = ts.into_iter();
                let a = args.next().unwrap();
                let b = args.next().unwrap();
                return Ok(Term::Diff(Box::new(a), Box::new(b)));
            }
            // `diff` not followed by `(`: `diffOp`'s `parens` fails, and no other
            // `term` alternative can take a reserved word.  Two parsec errors land
            // here, both relabelled `term` by the enclosing `<?>`: `identifier`'s
            // reserved-word `UnExpect` at `after_word` (Token.hs:393-394), and the
            // `SysUnExpect` of `parens`' `symbol "("` at the position `symbol
            // "diff"`'s trailing whitespace reached.  `mergeError` keeps the later
            // of the two, or concatenates them when no whitespace separates them.
            let pos = self.lx.pos();
            let mut messages = vec![
                Message::SysUnExpect(self.unexpected_token()),
                Message::Expect("term".to_string()),
            ];
            if pos.offset == after_word.offset {
                messages.push(Message::UnExpect("reserved word \"diff\"".to_string()));
            }
            return Err(ParseError::at(pos, messages));
        }
        // Identifier — could be: function application f(...), algebraic
        // application f{a}b, sort-suffixed var x:msg, or a bare variable /
        // nullary function.
        let save_id = self.save();
        if let Some(id) = self.lx.identifier() {
            // HS `naryOpApp`/`binaryAlgApp` reject a reserved builtin name in
            // an `equations:` context with a GHC `error`
            // (Theory/Text/Parser/Term.hs:90-92,
            // 111-113) right after the identifier — BEFORE looking at what
            // follows, so even a bare `exp` inside an equation aborts.  The
            // exception escapes every enclosing `try`; only `naryOpApp`'s
            // call site (Term.hs:92:9) can surface, since `application` tries
            // it first for every identifier.
            if eqn && Self::RESERVED_BUILTINS.contains(&id.as_str()) {
                return Err(self.err_ghc(
                    format!("`\"{id}\"` is a reserved function name for builtins."),
                    Self::term_reserved_name_call_site(),
                ));
            }
            self.last_ident_end = Some(self.ident_end_from(save_id, &id));
            self.skip_ws();
            if self.lx.peek() == Some('(') {
                // Look one token ahead inside `(`: if it's `<)` (the multiset
                // less-than operator at process level), this isn't a
                // function call but the `(<)` token. Defer to the variable
                // path so the `(<)` check above the term parser can see it.
                let probe = self.save();
                self.lx.bump();
                let is_lessmset = self.lx.peek() == Some('<') && {
                    let mut p2 = self.lx.clone();
                    p2.bump();
                    p2.peek() == Some(')')
                };
                self.restore(probe);
                if is_lessmset {
                    return self.bare_ident_term(id);
                }
                if self.resolve_prefix_apps {
                    // HS resolves the head through `lookupArity` and parses
                    // the arity the lookup returned (`naryOpApp`,
                    // Theory/Text/Parser/Term.hs:88-105).  On ANY failure —
                    // unknown operator,
                    // arity mismatch, or a malformed argument list — the
                    // try-wrapped application backtracks wholesale and the
                    // name reparses as `plit`'s variable below; the next
                    // token then breaks the enclosing grammar, which is where
                    // the user-visible frame comes from.  Only the GHC
                    // `error`s escape.
                    if let Some(res) = self.lookup_arity(&id) {
                        let save_app = self.save();
                        match self.prefix_app_args(&id, res, eqn) {
                            Ok(t) => return Ok(t),
                            Err(e) if e.ghc_error.is_some() => return Err(e),
                            Err(_) => self.restore(save_app),
                        }
                    }
                } else {
                    // Structural mode ([`parse_formula_str`],
                    // [`parse_intruder_rules`]): accept any application shape,
                    // strictly comma-separated, and leave the head for the
                    // caller to resolve.
                    self.lx.bump();
                    self.skip_ws();
                    let mut ts = Vec::new();
                    if !self.try_punct(")") {
                        loop {
                            let t = self.msetterm(eqn)?;
                            ts.push(t);
                            if !self.try_punct(",") {
                                break;
                            }
                        }
                        self.require_punct(")")?;
                    }
                    return Ok(Term::App(id, ts));
                }
            } else if self.lx.peek() == Some('{') {
                if self.resolve_prefix_apps {
                    // HS `binaryAlgApp` (Theory/Text/Parser/Term.hs:109-121): same
                    // lookup, arity
                    // fixed at 2, same wholesale backtrack on failure.
                    if let Some(res) = self.lookup_arity(&id) {
                        let save_app = self.save();
                        match self.binary_alg_app(&id, res, eqn) {
                            Ok(t) => return Ok(t),
                            Err(e) if e.ghc_error.is_some() => return Err(e),
                            Err(_) => self.restore(save_app),
                        }
                    }
                } else {
                    self.lx.bump();
                    self.skip_ws();
                    let arg1 = self.tuple_contents(eqn)?;
                    self.require_punct("}")?;
                    let arg2 = self.atom_term(eqn)?;
                    return Ok(Term::AlgApp(id, Box::new(arg1), Box::new(arg2)));
                }
            }
            // Bare identifier: message-sorted variable. Optionally with index `.<n>`
            // (only consumes `.` if followed by a digit) and optionally with
            // sort suffix `:msg|pub|fresh|node|nat` or a SAPIC type annotation.
            // Also the landing site of the application backtracks above, where
            // HS's `plit` reparses the name (leaving the following `(`/`{` for
            // the enclosing grammar to choke on).  A failed application parse
            // may have clobbered `last_ident_end` with a nested argument's, so
            // re-record this name's for `note_var_dot_hangover`.
            self.last_ident_end = Some(self.ident_end_from(save_id, &id));
            return self.bare_ident_term(id);
        }
        self.restore(save_id);
        Err(self.err("expected term"))
    }

    /// The term a BARE identifier (no sigil) denotes once its optional
    /// `.<index>` and `:sort` / `:type` suffix are read.
    ///
    /// HS's `term` tries `nullaryApp` ahead of the literal parser
    /// (Theory/Text/Parser/Term.hs:139-153,158-163): an identifier that is an
    /// arity-0 symbol of `funSyms maudeSig ∪ macroNames maudeSig` is the
    /// application `fApp fs []`, whatever a same-named binder is in scope.
    /// `nullaryApp` matches through `symbol`, which has no word boundary, so
    /// HS claims the name and leaves the rest of the lexeme behind: `c.1`,
    /// `c:msg` and a SAPIC `c:ty` are the constant `c` followed by input the
    /// enclosing parser rejects.  This parser claims the name only when the
    /// whole lexeme is it, and reads those three as variables instead.  A
    /// claimed name is the symbol's lexeme rather than an
    /// `indexedIdentifier`, so it leaves neither of the variable hangovers
    /// [`Parser::note_var_dot_hangover`] records.
    fn bare_ident_term(&mut self, id: String) -> Result<Term, ParseError> {
        let idx = self.try_dot_index();
        let v = VarSpec {
            name: id,
            idx,
            sort: LSort::Msg,
            typ: None,
        };
        let v = self.attach_sort_suffix(v)?;
        self.note_var_dot_hangover(&v);
        if self.is_plain_indexed_identifier(&v) && self.is_nullary_sym(&v.name) {
            return Ok(Term::App(v.name, Vec::new()));
        }
        Ok(Term::Var(v))
    }

    /// The variable after a pattern `=` — HS `sapicvar` via `sapicpatternvar`
    /// (Token.hs:506-519): a sorted variable with an optional `.idx` index and
    /// `:type` annotation, never an application, literal, or compound term.
    ///
    /// On a non-variable the failure carries
    /// [`SORTED_LVAR_NO_SUFFIX_EXPECTS`], as the pinned oracle prints for
    /// `in(c, =<x, y>)`:
    /// `unexpected "<" / expecting "$", "~", identifier, "#" or "%"`.
    fn pattern_var_atom(&mut self) -> Result<Term, ParseError> {
        if let Some(v) = self.try_var_spec()? {
            let v = self.attach_sort_suffix(v)?;
            self.note_var_dot_hangover(&v);
            return Ok(Term::Var(v));
        }
        Err(self.err_expect(SORTED_LVAR_NO_SUFFIX_EXPECTS))
    }

    /// `LINE:COLUMN` of `naryOpApp`'s reserved-name `error` in
    /// `src/Theory/Text/Parser/Term.hs` — see [`Self::MACRO_ERROR_PACKAGE`].
    const TERM_RESERVED_NAME_SITE: &'static str = "92:9";

    /// The `error, called at <…>` location of `naryOpApp`'s reserved-name
    /// rejection as the pinned oracle build prints it — same package id as
    /// `macro`'s errors.
    fn term_reserved_name_call_site() -> String {
        format!(
            "src/Theory/Text/Parser/Term.hs:{} in {}:Theory.Text.Parser.Term",
            Self::TERM_RESERVED_NAME_SITE,
            Self::MACRO_ERROR_PACKAGE
        )
    }

    /// HS `naryOpApp`'s argument parse after `lookupArity` succeeded
    /// (Theory/Text/Parser/Term.hs:93-105), starting at the opening `(`:
    ///
    /// ```haskell
    /// ts <- parens $ if k == 1 then return <$> tupleterm eqn plit
    ///                          else commaSep (msetterm eqn plit)
    /// when (acstate == NotAC && (k /= k')) $ fail "operator `…' has arity …"
    /// ```
    ///
    /// So an arity-1 symbol takes ONE `tupleterm` — surplus commas fold into
    /// a right-associative pair (`h(a, b)` is `h(<a, b>)`) and a trailing
    /// comma is a parse failure — while any other arity takes `commaSep`
    /// (`sepEndBy`, Token.hs:353-355: empty list and trailing comma both OK)
    /// followed by the `NotAC`-gated arity check.  An `IsAC` head accepts any
    /// count: `fAppAC` flattens ≥2 arguments (built here as the same nested
    /// [`BinOp::AcFct`] the infix spelling produces), collapses a singleton to
    /// its argument (`fAppAC _ [a] = a`, Term/Term/Raw.hs:118-121), and
    /// `fAppAC _ []` is a GHC `error` the empty argument list only triggers
    /// once the theory pipeline forces the term — kept as an `App` node here
    /// (`scripts/divergence_fixtures/ac_prefix_arities.spthy`).
    ///
    /// Every `Err` return is discarded by the caller's backtrack, mirroring
    /// the enclosing `try` — the messages never surface.
    fn prefix_app_args(&mut self, id: &str, res: ArityRes, eqn: bool) -> Result<Term, ParseError> {
        self.lx.bump(); // the '(' the caller peeked
        self.skip_ws();
        match res {
            ArityRes::NoEq {
                opts: FunOptions { arity: 1, .. },
            } => {
                let arg = self.tuple_contents(eqn)?;
                self.require_punct(")")?;
                Ok(Term::App(id.to_string(), vec![arg]))
            }
            ArityRes::NoEq { opts } => {
                let arity = opts.arity;
                let ts = self.sep_end_by(")", |p| p.msetterm(eqn))?;
                if ts.len() != arity {
                    return Err(self.err(format!(
                        "operator `{id}' has arity {arity}, but here it is used with arity {}",
                        ts.len()
                    )));
                }
                if res.is_dh_exp(id) {
                    let mut it = ts.into_iter();
                    let a = it.next().expect("arity 2 checked above");
                    let b = it.next().expect("arity 2 checked above");
                    return Ok(Term::BinOp(BinOp::Exp, Box::new(a), Box::new(b)));
                }
                Ok(Term::App(id.to_string(), ts))
            }
            ArityRes::Ac => {
                let ts = self.sep_end_by(")", |p| p.msetterm(eqn))?;
                Ok(self.ac_prefix_app(id, ts))
            }
        }
    }

    /// The argument list of a prefix application whose head the signature
    /// declares `[AC]`, as the term HS `naryOpApp` builds for it: `fAppAC
    /// (ACfct ...) ts` (Theory/Text/Parser/Term.hs:105), which the AST spells
    /// as a left-folded chain of [`BinOp::AcFct`].  A single argument is the
    /// term itself, as `fAppAC` over a one-element list flattens to it
    /// (`fAppAC _ [a] = a`, Term/Term/Raw.hs:121), and an empty list leaves
    /// the plain application.
    fn ac_prefix_app(&mut self, id: &str, ts: Vec<Term>) -> Term {
        let sym = intern_ac_name(id);
        let mut it = ts.into_iter();
        match (it.next(), it.next()) {
            (None, _) => Term::App(id.to_string(), Vec::new()),
            (Some(a), None) => {
                // The collapsed term IS the argument, but the atom's last
                // lexeme is this application's `)` — no variable hangover
                // survives even when the argument was one.
                self.var_dot_hangover = false;
                self.var_hangover_ident_end = None;
                a
            }
            (Some(a), Some(b)) => {
                let mut t = Term::BinOp(BinOp::AcFct(sym), Box::new(a), Box::new(b));
                for x in it {
                    t = Term::BinOp(BinOp::AcFct(sym), Box::new(t), Box::new(x));
                }
                t
            }
        }
    }

    /// HS `binaryAlgApp` (Theory/Text/Parser/Term.hs:109-121) after
    /// `lookupArity` succeeded,
    /// starting at the opening `{`: `op{t1}t2` parses `braced (tupleterm …)`
    /// then a trailing atom (`term eqn plit`), requires arity 2 (`fail`
    /// otherwise — discarded by the caller's backtrack), and builds
    /// `fAppNoEq`/`fAppAC` by the head's AC state.  There is no `em` special
    /// case here (`naryOpApp`'s Theory/Text/Parser/Term.hs:103 is prefix-only).
    fn binary_alg_app(&mut self, id: &str, res: ArityRes, eqn: bool) -> Result<Term, ParseError> {
        self.lx.bump(); // the '{' the caller peeked
        self.skip_ws();
        let arg1 = self.tuple_contents(eqn)?;
        self.require_punct("}")?;
        let arg2 = self.atom_term(eqn)?;
        match res {
            ArityRes::Ac => Ok(Term::BinOp(
                BinOp::AcFct(intern_ac_name(id)),
                Box::new(arg1),
                Box::new(arg2),
            )),
            ArityRes::NoEq {
                opts: FunOptions { arity: 2, .. },
            } => {
                if res.is_dh_exp(id) {
                    return Ok(Term::BinOp(BinOp::Exp, Box::new(arg1), Box::new(arg2)));
                }
                Ok(Term::AlgApp(id.to_string(), Box::new(arg1), Box::new(arg2)))
            }
            ArityRes::NoEq { .. } => {
                Err(self
                    .err("only operators of arity 2 can be written using the `op{t1}t2' notation"))
            }
        }
    }

    /// HS `sortedLVar`'s suffix arm: `indexedIdentifier <* colon` followed by
    /// one `sortSuffix`, returning `LVar n s i` with `s` the suffix's sort —
    /// the same plain `LVar` the sigil arms build (Token.hs:409-433).
    fn attach_sort_suffix(&mut self, mut v: VarSpec) -> Result<VarSpec, ParseError> {
        // Suffix syntax: `<id>:msg`, `:pub`, `:fresh`, `:node`, `:nat`.
        self.sort_suffix_consumed = false;
        let save = self.save();
        if self.try_punct(":") {
            // Inside a SAPIC process every variable comes from HS `sapicvar =
            // lvarNoSuffix; option Nothing (colon *> typep)` (Token.hs:506-510).
            // `lvarNoSuffix` (Token.hs:502-503) is `sortedLVarNoSuffix
            // [minBound..]` (Token.hs:486-501), which offers PREFIX sorts only, so a
            // colon there always introduces a SAPIC TYPE — `x:nat` is the
            // msg-sorted `x` typed `"nat"`, not a nat-sorted variable — and
            // `typep`'s `Any` is the untyped placeholder (Token.hs:472-473).
            if self.sapic_var_types {
                match self.type_p_element() {
                    Some((t, _)) => v.typ = t,
                    None => self.restore(save),
                }
                return Ok(v);
            }
            // Distinguish suffix sort vs SAPIC type annotation.
            let snap = self.save();
            for (kw, sort) in [
                ("msg", LSort::Msg),
                ("pub", LSort::Pub),
                ("fresh", LSort::Fresh),
                ("node", LSort::Node),
                ("nat", LSort::Nat),
            ] {
                if self.try_kw(kw) {
                    if sort == LSort::Nat && !self.sig_enable_nat {
                        return Err(
                            self.err("nat-sorted variables require the natural-numbers builtin")
                        );
                    }
                    v.sort = sort;
                    self.sort_suffix_consumed = true;
                    return Ok(v);
                }
            }
            // Else SAPIC type annotation.
            self.restore(snap);
            if let Some(t) = self.lx.identifier() {
                v.typ = Some(t);
                return Ok(v);
            }
            self.restore(save);
        }
        Ok(v)
    }

    /// Parse a variable specification. Returns None if no var sigil/identifier
    /// is present.
    fn try_var_spec(&mut self) -> Result<Option<VarSpec>, ParseError> {
        self.skip_ws();
        let save = self.save();
        let sort = match self.lx.peek() {
            Some('~') => {
                self.lx.bump();
                LSort::Fresh
            }
            Some('$') => {
                self.lx.bump();
                LSort::Pub
            }
            Some('#') => {
                self.lx.bump();
                LSort::Node
            }
            Some('%') => {
                // Could be `%1` (nat one) or `%'n'` (nat name lit) or `%x` (nat var).
                let mut probe = self.lx.clone();
                probe.bump();
                match probe.peek() {
                    Some('\'') | Some('1') => return Ok(None), // handled by literal/atom path
                    Some(c) if c.is_ascii_alphabetic() => {
                        if !self.sig_enable_nat {
                            return Err(self
                                .err("nat-sorted variables require the natural-numbers builtin"));
                        }
                        self.lx.bump();
                        LSort::Nat
                    }
                    _ => {
                        return Ok(None);
                    }
                }
            }
            // HS `sortedLVar`'s `mkPrefixParser LSortMsg` arm is the bare
            // `LSortMsg -> pure ()` case (Token.hs:424-426): a prefixless
            // identifier is message-sorted.
            Some(c) if c.is_alphabetic() => LSort::Msg,
            _ => return Ok(None),
        };
        let pre_ident = self.save();
        let id = match self.lx.identifier() {
            Some(s) => s,
            None => {
                self.restore(save);
                return Ok(None);
            }
        };
        self.last_ident_end = Some(self.ident_end_from(pre_ident, &id));
        let idx = self.try_dot_index();
        Ok(Some(VarSpec {
            name: id,
            idx,
            sort,
            typ: None,
        }))
    }

    fn var_spec(&mut self) -> Result<VarSpec, ParseError> {
        let v = self
            .try_var_spec()?
            .ok_or_else(|| self.err("expected variable"))?;
        // Allow `: msg | pub | fresh | node | nat` sort suffix or a SAPIC
        // type annotation after the variable.
        self.attach_sort_suffix(v)
    }

    /// Parse a quantifier's binder list (`All`/`Ex` share this): a sequence of
    /// variables terminated by `.`, which is consumed.  HS
    /// `quantification`'s `many1 (try varp <|> nodep)` with `varp = msgvar`,
    /// `nodep = nodevar` (Theory/Text/Parser/Formula.hs:64-77, see line 75,
    /// Token.hs:440-447): a prefixless binder is `LSortMsg`
    /// (Token.hs:440-441 into 409-433, see line 426), and an explicit
    /// `$`/`~`/`#`/`%` sigil or `:sort` suffix names the sort — which is what
    /// [`Self::var_spec`] builds.
    fn quantifier_binders(&mut self) -> Result<Vec<VarSpec>, ParseError> {
        let mut vs = Vec::new();
        loop {
            self.skip_ws();
            if self.lx.peek() == Some('.') {
                break;
            }
            let v = self.var_spec()?;
            vs.push(v);
        }
        self.require_punct(".")?;
        Ok(vs)
    }

    /// Consume `.<digit>+` as a variable index, otherwise leave input
    /// alone. Used so that `x.` (in quantifier lists, function arity slashes,
    /// etc.) doesn't accidentally swallow the trailing dot.
    fn try_dot_index(&mut self) -> u64 {
        let save = self.save();
        // Records whether the attempt was spent (see
        // [`Parser::dot_index_consumed`]); every early-out below leaves it
        // pending.
        self.dot_index_consumed = false;
        // Don't skip whitespace — `.` must be immediately after the identifier
        // for it to be an index. (Tamarin's `indexedIdentifier` matches
        // `dot *> natural`, but the dot follows the lexeme without an
        // intervening token break.)
        if self.lx.peek() != Some('.') {
            return 0;
        }
        self.lx.bump();
        // After the dot we accept digits with no intervening whitespace.
        match self.lx.peek() {
            Some(c) if c.is_ascii_digit() => match self.lx.natural() {
                Some(n) => {
                    self.dot_index_consumed = true;
                    n
                }
                None => {
                    self.restore(save);
                    0
                }
            },
            _ => {
                self.restore(save);
                0
            }
        }
    }

    // =========================================================================
    // Flag formulas (for #ifdef)
    // =========================================================================

    fn flag_disjuncts(&mut self) -> Result<FlagFormula, ParseError> {
        self.chainl1(
            |p| p.flag_conjuncts(),
            |p| (p.try_punct("|") || p.try_punct("∨")).then_some(()),
            |(), lhs, rhs| FlagFormula::Or(Box::new(lhs), Box::new(rhs)),
        )
    }

    fn flag_conjuncts(&mut self) -> Result<FlagFormula, ParseError> {
        self.chainl1(
            |p| p.flag_negation(),
            |p| (p.try_punct("&") || p.try_punct("∧")).then_some(()),
            |(), lhs, rhs| FlagFormula::And(Box::new(lhs), Box::new(rhs)),
        )
    }

    fn flag_negation(&mut self) -> Result<FlagFormula, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.flag_atom()?;
            Ok(FlagFormula::Not(Box::new(f)))
        } else {
            self.flag_atom()
        }
    }

    fn flag_atom(&mut self) -> Result<FlagFormula, ParseError> {
        if self.try_punct("(") {
            let f = self.flag_disjuncts()?;
            self.require_punct(")")?;
            return Ok(f);
        }
        let id = self.ident()?;
        Ok(FlagFormula::Atom(id))
    }

    // =========================================================================
    // Proof goals
    // =========================================================================

    /// Parse the goal inside a stored `solve( ... )` step.  HS `goal`
    /// (Theory/Text/Parser/Proof.hs:38-72):
    ///
    /// ```haskell
    /// goal = asum
    ///     [ stSplitGoal, premiseGoal, actionGoal
    ///     , chainGoal, disjSplitGoal, eqSplitGoal ]
    /// ```
    ///
    /// Each of the first four alternatives wraps only its LEADING operator in
    /// a `try`, so once that operator is read the alternative is committed and
    /// a failure after it fails the whole goal; [`Parser::attempt`] is that
    /// `try` and the `?` after each call is that commitment.  `disjSplitGoal`
    /// backtracks on its own because HS's `plainFormula`
    /// (Theory/Text/Parser/Formula.hs:112-117) is `try`-wrapped whole, and
    /// `eqSplitGoal` is `try $ do ...`.
    ///
    /// The equation split is hoisted above the disjunction, which accepts the
    /// same language: HS reaches `eqSplitGoal` only because `disjSplitGoal`
    /// fails on `splitEqs(N)`, and the keyword form does not depend on how
    /// [`Parser::formula`] reads a lower-case predicate-shaped atom.
    fn goal(&mut self) -> Result<GoalSpec, ParseError> {
        if let Some(g) = self.subterm_goal()? {
            return Ok(g);
        }
        if let Some(g) = self.premise_goal()? {
            return Ok(g);
        }
        if let Some(g) = self.action_goal()? {
            return Ok(g);
        }
        if let Some(g) = self.chain_goal()? {
            return Ok(g);
        }
        if let Some(g) = self.attempt(|p| p.eq_split_goal()) {
            return Ok(g);
        }
        self.disj_split_goal()
    }

    /// HS `try` over `f`: on failure the input is restored and nothing is
    /// reported, so the caller can offer another alternative.
    fn attempt<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, ParseError>) -> Option<T> {
        let save = self.save();
        match f(self) {
            Ok(v) => Some(v),
            Err(_) => {
                self.restore(save);
                None
            }
        }
    }

    /// The `try (head <* sep) *> tail` shape of `stSplitGoal`, `premiseGoal`,
    /// `actionGoal` and `chainGoal` (Theory/Text/Parser/Proof.hs:49-68):
    /// `head` reads the goal's first operand AND its separator under one
    /// `try`, so failing either restores the input and yields `None` for
    /// [`Self::goal`] to move on to the next alternative, while `tail` reads
    /// the rest outside the `try`, where a failure is the whole goal's.
    fn goal_after<H>(
        &mut self,
        head: impl FnOnce(&mut Self) -> Result<H, ParseError>,
        tail: impl FnOnce(&mut Self, H) -> Result<GoalSpec, ParseError>,
    ) -> Result<Option<GoalSpec>, ParseError> {
        match self.attempt(head) {
            Some(h) => tail(self, h).map(Some),
            None => Ok(None),
        }
    }

    /// HS `disjSplitGoal` (Theory/Text/Parser/Proof.hs:61):
    /// `(DisjG . Disj) <$> sepBy1 guardedFormula (symbol "∥")`.  A disjunct is
    /// a `plainFormula`; the `formulaToGuarded` half of `guardedFormula`
    /// (Theory/Text/Parser/Formula.hs:122-127) runs in
    /// `tamarin_theory::elaborate::goal_from_parsed`.
    fn disj_split_goal(&mut self) -> Result<GoalSpec, ParseError> {
        let mut alts = vec![self.formula()?];
        while self.try_punct("\u{2225}") {
            alts.push(self.formula()?);
        }
        Ok(GoalSpec::Disj(alts))
    }

    /// HS `stSplitGoal` (Theory/Text/Parser/Proof.hs:63-68): two
    /// `msetterm False (vlit msgvar)` terms around `opSubterm`
    /// (`<<` or `⊏`, Token.hs:574-576), the first of them under the `try`.
    fn subterm_goal(&mut self) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            |p| {
                let t = p.msetterm(false)?;
                if !p.try_punct("<<") && !p.try_punct("\u{228F}") {
                    return Err(p.err("expected `⊏`"));
                }
                Ok(t)
            },
            |p, small| Ok(GoalSpec::Subterm(small, p.msetterm(false)?)),
        )
    }

    /// HS `premiseGoal` (Theory/Text/Parser/Proof.hs:54-57): a `fact llit`
    /// followed by `opRequires` (`▶` and a subscript natural,
    /// Token.hs:618-619), both under the `try`, then a `nodevar`.
    fn premise_goal(&mut self) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            |p| {
                let fa = p.fact()?;
                p.skip_ws();
                if !p.lx.eat_str("\u{25B6}") {
                    return Err(p.err("expected `▶`"));
                }
                let v =
                    p.lx.natural_subscript()
                        .ok_or_else(|| p.err("expected a subscript premise index"))?;
                Ok((fa, v))
            },
            |p, (fa, v)| Ok(GoalSpec::Premise((p.nodevar()?, v), fa)),
        )
    }

    /// HS `actionGoal` (Theory/Text/Parser/Proof.hs:49-52): a `fact llit`
    /// followed by `opAt` (`@`, Token.hs:566-568) under the `try`, then a
    /// `nodevar`.
    fn action_goal(&mut self) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            |p| {
                let fa = p.fact()?;
                if !p.try_punct("@") {
                    return Err(p.err("expected `@`"));
                }
                Ok(fa)
            },
            |p, fa| Ok(GoalSpec::Action(p.nodevar()?, fa)),
        )
    }

    /// HS `chainGoal` (Theory/Text/Parser/Proof.hs:59): a `nodeConc` and
    /// `opChain` (`~~>`, Token.hs:621-623) under the `try`, then a `nodePrem`.
    /// Each endpoint is `parens ((,) <$> nodevar <*> (comma *> natural))`
    /// (Theory/Text/Parser/Proof.hs:28-36).
    fn chain_goal(&mut self) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            |p| {
                let conc = p.node_idx_pair()?;
                if !p.try_punct("~~>") {
                    return Err(p.err("expected `~~>`"));
                }
                Ok(conc)
            },
            |p, conc| Ok(GoalSpec::Chain(conc, p.node_idx_pair()?)),
        )
    }

    /// HS `nodePrem`/`nodeConc` (Theory/Text/Parser/Proof.hs:28-36):
    /// `parens ((,) <$> nodevar <*> (comma *> natural))`.
    fn node_idx_pair(&mut self) -> Result<(VarSpec, u64), ParseError> {
        self.require_punct("(")?;
        let v = self.nodevar()?;
        self.require_punct(",")?;
        let n = self
            .lx
            .natural()
            .ok_or_else(|| self.err("expected a node index"))?;
        self.require_punct(")")?;
        Ok((v, n))
    }

    /// HS `eqSplitGoal` (Theory/Text/Parser/Proof.hs:70-72):
    /// `symbol_ "splitEqs"` then `parens natural`.
    fn eq_split_goal(&mut self) -> Result<GoalSpec, ParseError> {
        if !self.try_kw("splitEqs") {
            return Err(self.err("expected `splitEqs`"));
        }
        self.require_punct("(")?;
        let n = self
            .lx
            .natural()
            .ok_or_else(|| self.err("expected a split id"))?;
        self.require_punct(")")?;
        Ok(GoalSpec::Split(n as i64))
    }

    /// Parse a timepoint variable.  HS `nodevar` (Token.hs:443-448) is
    /// `sortedLVar [LSortNode]` — the `#x` prefix or the `x:node` suffix —
    /// or a bare `indexedIdentifier` stamped `LSortNode`.  A `$`/`~`/`%`
    /// sigil, a different sort suffix and a SAPIC type annotation are all
    /// outside that language.
    fn nodevar(&mut self) -> Result<VarSpec, ParseError> {
        let save = self.save();
        let v = self.var_spec()?;
        // `sortedLVar [LSortNode]` is the `#x` sigil and the `x:node` suffix;
        // the second alternative reads a bare `indexedIdentifier`, which
        // [`Parser::try_var_spec`] stamps `LSort::Msg` with no suffix consumed.
        let is_node = v.sort == LSort::Node
            || (v.sort == LSort::Msg && !self.sort_suffix_consumed && v.typ.is_none());
        if !is_node {
            self.restore(save);
            return Err(self.err("expected a timepoint variable"));
        }
        Ok(VarSpec {
            name: v.name,
            idx: v.idx,
            sort: LSort::Node,
            typ: None,
        })
    }

    fn eval_flagformula(&self, f: &FlagFormula) -> bool {
        match f {
            FlagFormula::Atom(s) => self.flags.contains(s),
            FlagFormula::Not(g) => !self.eval_flagformula(g),
            FlagFormula::And(a, b) => self.eval_flagformula(a) && self.eval_flagformula(b),
            FlagFormula::Or(a, b) => self.eval_flagformula(a) || self.eval_flagformula(b),
        }
    }
}

// =============================================================================
// `let` inlining
// =============================================================================

/// Substitute a rule's `let` bindings into its body — HS
/// `apply subst (ps0,as0,cs0,rs0)` (Theory/Text/Parser/Rule.hs:119, 133, 153).
///
/// `letBlock` folds the bindings with `foldr1 compose` over singleton
/// substitutions (Theory/Text/Parser/Let.hs:35) and `compose s1 s2` has the
/// effect of `s1(s2(t))` (Term/Substitution/SubstVFree.hs:186-191), so the
/// bindings apply in REVERSE source order.  A binding's right-hand side is
/// therefore rewritten by the bindings that precede it (`let a = ~k  b = h(a)`
/// puts `h(~k)` in the body), while a reference to a LATER binding survives as
/// a free variable (`let a = h(b)  b = ~k` puts `h(b)` in the body).
fn apply_let_bindings(
    bindings: &[(Term, Term)],
    premises: &mut [Fact],
    actions: &mut [Fact],
    conclusions: &mut [Fact],
    restrictions: &mut [Formula],
) {
    for (var, value) in bindings.iter().rev() {
        for f in premises
            .iter_mut()
            .chain(actions.iter_mut())
            .chain(conclusions.iter_mut())
        {
            subst_let_fact(f, var, value);
        }
        for phi in restrictions.iter_mut() {
            subst_let_formula(phi, var, value);
        }
    }
}

fn subst_let_fact(f: &mut Fact, key: &Term, val: &Term) {
    for a in f.args.iter_mut() {
        *a = subst_let_term(a, key, val);
    }
}

fn subst_let_term(t: &Term, key: &Term, val: &Term) -> Term {
    if t == key {
        return val.clone();
    }
    match t {
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter().map(|a| subst_let_term(a, key, val)).collect(),
        ),
        Term::AlgApp(name, a, b) => Term::AlgApp(
            name.clone(),
            Box::new(subst_let_term(a, key, val)),
            Box::new(subst_let_term(b, key, val)),
        ),
        Term::Pair(args) => Term::Pair(args.iter().map(|a| subst_let_term(a, key, val)).collect()),
        Term::Diff(a, b) => Term::Diff(
            Box::new(subst_let_term(a, key, val)),
            Box::new(subst_let_term(b, key, val)),
        ),
        Term::BinOp(op, a, b) => Term::BinOp(
            *op,
            Box::new(subst_let_term(a, key, val)),
            Box::new(subst_let_term(b, key, val)),
        ),
        Term::PatMatch(a) => Term::PatMatch(Box::new(subst_let_term(a, key, val))),
        Term::Var(_)
        | Term::PubLit(_)
        | Term::FreshLit(_)
        | Term::NatLit(_)
        | Term::Number(_)
        | Term::NumberOne
        | Term::NatOne
        | Term::DhNeutral => t.clone(),
    }
}

fn subst_let_formula(phi: &mut Formula, key: &Term, val: &Term) {
    match phi {
        Formula::False | Formula::True => {}
        Formula::Atom(a) => subst_let_atom(a, key, val),
        Formula::Not(p) => subst_let_formula(p, key, val),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
            subst_let_formula(a, key, val);
            subst_let_formula(b, key, val);
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            let Term::Var(key_var) = key else {
                subst_let_formula(body, key, val);
                return;
            };
            // A rule-let substitution is a free-variable substitution. A
            // quantifier for its domain shadows every occurrence below it.
            if vars.contains(key_var) {
                return;
            }

            // Parser formulas still carry named variables. Alpha-rename any
            // binder that occurs free in the replacement before descending,
            // otherwise `let x = y in Ex y. ...x...` captures the inserted y.
            let mut replacement_vars = Vec::new();
            collect_term_vars(val, &mut replacement_vars);
            let mut used_vars = replacement_vars.clone();
            collect_formula_vars(body, &mut used_vars);
            for var in vars.iter() {
                if !used_vars.contains(var) {
                    used_vars.push(var.clone());
                }
            }
            if !used_vars.contains(key_var) {
                used_vars.push(key_var.clone());
            }
            for var in vars.iter_mut() {
                if replacement_vars.contains(var) {
                    let old = var.clone();
                    let fresh = fresh_formula_var(&used_vars, &old);
                    rename_bound_formula(body, &old, &fresh);
                    used_vars.push(fresh.clone());
                    *var = fresh;
                }
            }
            subst_let_formula(body, key, val);
        }
    }
}

fn collect_term_vars(term: &Term, out: &mut Vec<VarSpec>) {
    match term {
        Term::Var(v) => {
            if !out.contains(v) {
                out.push(v.clone());
            }
        }
        Term::App(_, args) | Term::Pair(args) => {
            for arg in args {
                collect_term_vars(arg, out);
            }
        }
        Term::AlgApp(_, a, b) | Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        Term::PatMatch(t) => collect_term_vars(t, out),
        Term::PubLit(_)
        | Term::FreshLit(_)
        | Term::NatLit(_)
        | Term::Number(_)
        | Term::NumberOne
        | Term::NatOne
        | Term::DhNeutral => {}
    }
}

fn collect_formula_vars(formula: &Formula, out: &mut Vec<VarSpec>) {
    match formula {
        Formula::False | Formula::True => {}
        Formula::Atom(atom) => collect_atom_vars(atom, out),
        Formula::Not(body) => collect_formula_vars(body, out),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
            collect_formula_vars(a, out);
            collect_formula_vars(b, out);
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            for var in vars {
                if !out.contains(var) {
                    out.push(var.clone());
                }
            }
            collect_formula_vars(body, out);
        }
    }
}

fn collect_atom_vars(atom: &Atom, out: &mut Vec<VarSpec>) {
    match atom {
        Atom::Eq(a, b) | Atom::Less(a, b) | Atom::LessMset(a, b) | Atom::Subterm(a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        Atom::Action(fact, node) => {
            for arg in &fact.args {
                collect_term_vars(arg, out);
            }
            collect_term_vars(node, out);
        }
        Atom::Last(node) => collect_term_vars(node, out),
        Atom::Pred(fact) => {
            for arg in &fact.args {
                collect_term_vars(arg, out);
            }
        }
    }
}

fn fresh_formula_var(used: &[VarSpec], old: &VarSpec) -> VarSpec {
    let mut fresh = old.clone();
    fresh.idx = used
        .iter()
        .filter(|v| v.name == old.name && v.sort == old.sort)
        .map(|v| v.idx)
        .max()
        .unwrap_or(old.idx)
        .saturating_add(1);
    while used.contains(&fresh) {
        fresh.idx = fresh.idx.saturating_add(1);
    }
    fresh
}

/// Rename occurrences bound by the current quantifier. A nested quantifier
/// for the same variable starts a new scope and stops the traversal there.
fn rename_bound_formula(formula: &mut Formula, old: &VarSpec, new: &VarSpec) {
    match formula {
        Formula::False | Formula::True => {}
        Formula::Atom(atom) => rename_atom_var(atom, old, new),
        Formula::Not(body) => rename_bound_formula(body, old, new),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
            rename_bound_formula(a, old, new);
            rename_bound_formula(b, old, new);
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            if !vars.contains(old) {
                rename_bound_formula(body, old, new);
            }
        }
    }
}

fn rename_atom_var(atom: &mut Atom, old: &VarSpec, new: &VarSpec) {
    match atom {
        Atom::Eq(a, b) | Atom::Less(a, b) | Atom::LessMset(a, b) | Atom::Subterm(a, b) => {
            rename_term_var(a, old, new);
            rename_term_var(b, old, new);
        }
        Atom::Action(fact, node) => {
            for arg in &mut fact.args {
                rename_term_var(arg, old, new);
            }
            rename_term_var(node, old, new);
        }
        Atom::Last(node) => rename_term_var(node, old, new),
        Atom::Pred(fact) => {
            for arg in &mut fact.args {
                rename_term_var(arg, old, new);
            }
        }
    }
}

fn rename_term_var(term: &mut Term, old: &VarSpec, new: &VarSpec) {
    match term {
        Term::Var(v) if v == old => *v = new.clone(),
        Term::App(_, args) | Term::Pair(args) => {
            for arg in args {
                rename_term_var(arg, old, new);
            }
        }
        Term::AlgApp(_, a, b) | Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            rename_term_var(a, old, new);
            rename_term_var(b, old, new);
        }
        Term::PatMatch(t) => rename_term_var(t, old, new),
        Term::Var(_)
        | Term::PubLit(_)
        | Term::FreshLit(_)
        | Term::NatLit(_)
        | Term::Number(_)
        | Term::NumberOne
        | Term::NatOne
        | Term::DhNeutral => {}
    }
}

fn subst_let_atom(a: &mut Atom, key: &Term, val: &Term) {
    match a {
        Atom::Eq(x, y) | Atom::Less(x, y) | Atom::LessMset(x, y) | Atom::Subterm(x, y) => {
            *x = subst_let_term(x, key, val);
            *y = subst_let_term(y, key, val);
        }
        Atom::Action(f, t) => {
            subst_let_fact(f, key, val);
            *t = subst_let_term(t, key, val);
        }
        Atom::Last(t) => *t = subst_let_term(t, key, val),
        Atom::Pred(f) => subst_let_fact(f, key, val),
    }
}

#[derive(Debug)]
enum BranchEnd {
    Else,
    Endif,
    Eof,
}

/// One attribute of a `functions:` declaration.  Mirrors HS `FctAttr`
/// (`Privacy Privacy | Constructability Constructability | ACstate ACstate |
/// NDCstate NDCstate`, Term/Term/FunctionSymbols.hs:128-129) restricted to the
/// six values the surface syntax can produce.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FctAttr {
    /// `private` (HS `Privacy Private`)
    Private,
    /// `destructor` (HS `Constructability Destructor`)
    Destructor,
    /// `constructor` (HS `Constructability Constructor`) — the default, so it is
    /// collected but never inspected.
    Constructor,
    /// `AC` (HS `ACstate IsAC`)
    Ac,
    /// `NDC` (HS `NDCstate IsNDC`)
    Ndc,
    /// `NDC-diff` (HS `NDCstate IsNDCDiff`)
    NdcDiff,
}

#[derive(Debug)]
enum FactOrRestr {
    Fact(Fact),
    Restr(Formula),
}

// =============================================================================
// String-form formula parsing (lemmas and restrictions store the formula as
// a quoted string)
// =============================================================================

/// Parse a standalone formula from its source text into the AST [`Formula`].
///
/// Lemmas and restrictions store their formula as a quoted string; this is the
/// entry point used to recover the AST from that text.  Errors on any trailing
/// input after the formula.
///
/// `msig` is the signature the text was rendered against, seeded as HS
/// `parseString` seeds one (Theory/Text/Parser/Token.hs:250-258): it supplies
/// the `[AC]` symbols' infix spelling, the arity-0 constants `nullaryApp`
/// claims, and the enable bits that open the algebraic term levels, so text
/// rendered from a theory reparses under that theory's operators.
pub fn parse_formula_str(s: &str, msig: &MaudeSig) -> Result<Formula, ParseError> {
    let mut p = Parser::new(s, &[], false);
    p.seed_signature(msig);
    // Rendered formula text carries applications of symbols this fresh
    // parser has no declarations for — accept them structurally.
    p.resolve_prefix_apps = false;
    let f = p.formula()?;
    p.skip_ws();
    if !p.lx.is_eof() {
        return Err(p.err("trailing garbage in formula string"));
    }
    Ok(f)
}

/// Parse the `( <goal> )` of a stored `solve` step at the head of `s`, and
/// report the byte offset just past its closing `)`.
///
/// HS reads the step as `symbol "solve" *> parens goal`
/// (Theory/Text/Parser/Proof.hs:80), one parser over one input; the offset
/// lets the proof-skeleton parser resume where this one stopped.
///
/// `parent` is the parser the stored text came out of, whose symbol state
/// [`Parser::seed_from`] copies: HS's proof parser runs inside the theory
/// parser and reads its `stSig` (Theory/Text/Parser/Proof.hs:38-72), so an
/// application head in the goal resolves through `lookupArity`
/// (Theory/Text/Parser/Term.hs:88-105) against the theory's symbols exactly
/// as one in a rule does.
pub(crate) fn parse_parens_goal(
    s: &str,
    parent: &Parser<'_>,
) -> Result<(GoalSpec, usize), ParseError> {
    let mut p = Parser::new(s, &[], false);
    p.seed_from(parent);
    p.require_punct("(")?;
    let g = p.goal()?;
    p.skip_ws();
    if !p.lx.eat_str(")") {
        return Err(p.err("expected `)` after the goal"));
    }
    Ok((g, p.lx.pos().offset))
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
