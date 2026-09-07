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
use crate::lexer::{is_ident_char, Lexer, Pos, RESERVED_NAMES};
use crate::parse_error::{
    bound_owned_text, bounded_diagnostic_text, DiagnosticInfo, IllegalDiffReason, ParseContext,
    ParseErrorKind, MAX_DIAGNOSTIC_MESSAGE_CHARS, MAX_DIAGNOSTIC_NAME_CHARS,
};
use crate::proof_tree::{parse_proof_tree, validate_diff_proof_tree};

// =============================================================================
// Errors
// =============================================================================

/// Details belonging to one failed parse, never combined across alternatives.
#[derive(Debug)]
pub(crate) enum ErrorDetails {
    Expected {
        expected: String,
        found: Option<char>,
    },
    Custom(String),
}

/// A parser failure with a compact semantic classification and source span.
///
/// Callers use structured accessors such as [`ParseError::kind`],
/// [`ParseError::span`], and [`ParseError::diagnostic_notes`].
/// [`std::fmt::Display`] renders the same details as [`ParseError::render_plain`].
/// Individual diagnostic strings are limited to 512 characters.
#[derive(Debug)]
pub struct ParseError {
    pub(crate) pos: Pos,
    /// Source name, supplied by the caller or an included file.
    pub(crate) source: String,
    pub(crate) details: Option<ErrorDetails>,
    /// Structured classification, source spans, and related declarations.
    /// Ordinary syntax failures leave this unallocated.
    pub(crate) diagnostic: Option<Box<DiagnosticInfo>>,
}

impl ParseError {
    pub(crate) fn at(pos: Pos) -> Self {
        Self {
            pos,
            source: String::new(),
            details: None,
            diagnostic: None,
        }
    }

    pub(crate) fn custom(pos: Pos, mut cause: String) -> Self {
        bound_owned_text(&mut cause, MAX_DIAGNOSTIC_MESSAGE_CHARS);
        Self {
            details: Some(ErrorDetails::Custom(cause)),
            ..Self::at(pos)
        }
    }

    pub(crate) fn expected(pos: Pos, expected: impl Into<String>, found: Option<char>) -> Self {
        let mut expected = expected.into();
        bound_owned_text(&mut expected, MAX_DIAGNOSTIC_MESSAGE_CHARS);
        Self {
            details: Some(ErrorDetails::Expected { expected, found }),
            ..Self::at(pos)
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.render_plain())
    }
}

impl std::error::Error for ParseError {}

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

fn diagnostic_lexeme(text: &str) -> String {
    bounded_diagnostic_text(text, MAX_DIAGNOSTIC_NAME_CHARS)
}

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
    p.theory()
}

/// Parse a diff theory, enabling both the `diff(a, b)` term and the diff-only
/// top-level namespaces. This is the syntax-level counterpart of HS
/// `parseOpenDiffTheoryString` (`Theory/Text/Parser.hs:84-86`).
pub fn parse_diff_theory(input: &str, flags: &[&str]) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, true);
    p.theory()
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
    p.theory()
}

/// Like [`parse_diff_theory`], but resolves includes relative to `base_dir`.
pub fn parse_diff_theory_with_base(
    input: &str,
    flags: &[&str],
    base_dir: Option<PathBuf>,
) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, true);
    p.base_dir = base_dir;
    p.theory()
}

/// One parser-selected source input and the path it must have when staged
/// beside the root theory. `None` denotes an absolute input outside that tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputAlias {
    pub physical: PathBuf,
    pub staged: Option<PathBuf>,
}

/// Parse a theory while recording the root and every active include. This is
/// the dependency authority for cache keys and web staging: inactive branches,
/// comments and text after `end` are interpreted by the real grammar rather
/// than a second scanner.
pub fn parse_theory_with_manifest(
    input: &str,
    flags: &[&str],
    root: PathBuf,
    is_diff: bool,
) -> Result<(Theory, Vec<InputAlias>), ParseError> {
    let staged = root.file_name().map(PathBuf::from);
    let inputs = vec![InputAlias {
        physical: root.clone(),
        staged: staged.clone(),
    }];
    let mut parser = Parser::new(input, flags, is_diff);
    parser.base_dir = root.parent().map(PathBuf::from);
    parser.source_file = Some(root);
    parser.staged_file = staged;
    parser.state.input_aliases = inputs;
    parser.state.emit_warnings = false;
    let theory = parser.theory()?;
    Ok((theory, parser.state.input_aliases))
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
    let result = (|| {
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
    })();
    p.lx.finish(result)
}

/// Strip `//` line comments and `/* */` block comments from a lemma's verbatim
/// source span, used to populate `ast::Lemma::plaintext`.  Faithful port of HS
/// `removeComments` / `removeCommentBlock` (`Theory/Text/Parser/Lemma.hs:62-74`),
/// including the newline-swallowing behaviour that HS relies on: a `\n`
/// immediately preceding a comment is consumed with the comment, and a block
/// comment's closing `*/\n` consumes the trailing newline.  This determines the
/// textarea's `rows` count in the web Edit form (HS `textHeight = 2 + number of
/// '\n'`), so it must match char-for-char.
pub(crate) fn remove_comments(mut source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    while let Some((start, line_comment)) =
        source
            .match_indices('/')
            .find_map(|(start, _)| match source.as_bytes().get(start + 1) {
                Some(b'/') => Some((start, true)),
                Some(b'*') => Some((start, false)),
                _ => None,
            })
    {
        let prefix = &source[..start];
        out.push_str(prefix.strip_suffix('\n').unwrap_or(prefix));
        source = &source[start + 2..];
        source = if line_comment {
            source.find('\n').map_or("", |end| &source[end..])
        } else {
            source.find("*/").map_or("", |end| {
                let tail = &source[end + 2..];
                tail.strip_prefix('\n').unwrap_or(tail)
            })
        };
    }
    out.push_str(source);
    out
}

// =============================================================================
// Parser state
// =============================================================================

/// Numeric declarations defer their placeholder allocation until validation.
enum FunctionArgs {
    Untyped {
        arity: usize,
        position: Pos,
        len: usize,
    },
    Typed(Vec<Option<String>>),
}

/// The `(arity, Privacy, Constructability, NDCstate)` options tuple HS carries
/// per free function symbol (HS `NoEqSym`, Term/Term/FunctionSymbols.hs:132).
///
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
}

fn function_option_difference(previous: FunOptions, requested: FunOptions) -> String {
    let mut differences = Vec::new();
    if previous.arity != requested.arity {
        differences.push(format!(
            "arity {} requested, previously {}",
            requested.arity, previous.arity
        ));
    }
    for (name, before, after) in [
        ("private", previous.private, requested.private),
        ("destructor", previous.destructor, requested.destructor),
        ("NDC", previous.ndc, requested.ndc),
        ("NDC-diff", previous.ndc_diff, requested.ndc_diff),
    ] {
        if before != after {
            differences.push(format!(
                "{name} {}",
                if after { "added" } else { "removed" }
            ));
        }
    }
    differences.join(", ")
}

/// The `MaudeSig` each `builtins:` name enables, in HS's `builtinsNames` order
/// (Theory/Text/Parser/Signature.hs:78-86, whose tail is `builtinsDiffNames`,
/// Theory/Text/Parser/Signature.hs:58-76) — the order `builtinReservedNames`
/// (Theory/Text/Parser/Signature.hs:178-181) is built in.
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

fn is_builtin_name(name: &str) -> bool {
    name == "reliable-channel" || BUILTIN_MAUDE_SIG_NAMES.contains(&name)
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

/// Parser state inherited by an included file and returned to its parent.
/// Lexer position, source identity, and term state remain file-local on
/// [`Parser`]. Keeping the inherited state in one value makes that boundary
/// structural instead of maintaining a parallel field list.
struct ParserState {
    #[allow(clippy::disallowed_types)]
    flags: HashSet<String>,
    enable_diff: bool,
    input_aliases: Vec<InputAlias>,
    emit_warnings: bool,
    ac_fun_syms: Arc<Vec<String>>,
    fun_syms: Arc<Vec<(String, FunOptions)>>,
    macro_syms: Arc<Vec<(String, FunOptions)>>,
    reserved_builtin_names: Vec<String>,
    sig_enable_dh: bool,
    sig_enable_bp: bool,
    sig_enable_xor: bool,
    sig_enable_mset: bool,
    sig_enable_nat: bool,
    seen_rules: Vec<Rule>,
    seen_restriction_names: Vec<String>,
    seen_lemma_names: Vec<String>,
    seen_diff_left_lemma_names: Vec<String>,
    seen_diff_right_lemma_names: Vec<String>,
    seen_diff_lemma_names: Vec<String>,
    seen_predicates: Vec<(bool, String, usize)>,
}

struct FunctionSite {
    name: String,
    options: FunOptions,
    span: std::ops::Range<usize>,
    builtin: bool,
}

pub struct Parser<'a> {
    lx: Lexer<'a>,
    // These positions belong to this parser's source, not the shared include state.
    function_sites: Vec<FunctionSite>,
    named_sites: std::collections::BTreeMap<(&'static str, String), std::ops::Range<usize>>,
    state: ParserState,
    /// Whether we're parsing a diff theory. Set only from the `Parser::new`
    /// argument supplied by the caller and echoed into `Theory::is_diff`.
    is_diff: bool,
    /// Directory of the file currently being parsed (`takeDirectory inFile0` in
    /// HS).  `#include "file"` resolves relative to this; `None` (no source
    /// file) means includes are taken verbatim, mirroring HS's `Nothing` case.
    base_dir: Option<PathBuf>,
    /// Exact included fragment currently being parsed. Root entry points only
    /// receive a base directory, so `None` there falls back to the loader's
    /// source filename during elaboration.
    source_file: Option<PathBuf>,
    /// Staged spelling of [`Self::source_file`] relative to the root input.
    staged_file: Option<PathBuf>,
    /// Set by every successful variable parse; only consulted for variable operands.
    /// Formula alternatives need not restore it: the next variable overwrites it.
    sort_suffix_consumed: bool,
    /// Whether prefix applications resolve through [`Self::lookup_arity`]
    /// (HS `naryOpApp`/`binaryAlgApp`, Theory/Text/Parser/Term.hs:88-121).  True
    /// for theory parsing and for [`parse_parens_goal`], which runs inside the
    /// theory parser's symbol state; [`parse_formula_str`] and
    /// [`parse_intruder_rules`] clear it because they re-parse RENDERED text
    /// whose heads their callers resolve, where every application must be
    /// accepted structurally.
    resolve_prefix_apps: bool,
    /// Grammar-owned list closers; never scan ahead to guess delimiter ownership.
    list_closers: Vec<char>,
    /// Whether a `:` after a variable names a SAPIC TYPE rather than a sort
    /// suffix.  Set while parsing a SAPIC process (and a process definition's
    /// parameter list), where HS uses `sapicvar` — `lvarNoSuffix` plus an
    /// optional type (defaulting node-sorted variables to `node`) — instead of the
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
            function_sites: Vec::new(),
            named_sites: std::collections::BTreeMap::new(),
            state: ParserState {
                enable_diff: is_diff || flags_set.contains("diff"),
                flags: flags_set,
                input_aliases: Vec::new(),
                emit_warnings: true,
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
                seen_rules: Vec::new(),
                seen_restriction_names: Vec::new(),
                seen_lemma_names: Vec::new(),
                seen_diff_left_lemma_names: Vec::new(),
                seen_diff_right_lemma_names: Vec::new(),
                seen_diff_lemma_names: Vec::new(),
                seen_predicates: vec![(false, "Smaller".to_string(), 2)],
            },
            is_diff,
            base_dir: None,
            source_file: None,
            staged_file: None,
            sort_suffix_consumed: false,
            resolve_prefix_apps: true,
            list_closers: Vec::new(),
            sapic_var_types: false,
            allow_pat: false,
        }
    }

    /// Exchange the parse state that an included fragment inherits and
    /// returns. File-local lexer and term state deliberately stay
    /// with each parser.
    fn swap_include_state(&mut self, other: &mut Parser<'_>) {
        std::mem::swap(&mut self.state, &mut other.state);
    }

    // -------- Error helpers --------

    /// Report a custom cause at the current parse position.
    fn err(&self, msg: impl Into<String>) -> ParseError {
        ParseError::custom(self.lx.pos(), msg.into())
    }

    /// A semantic error keeps parse progress separate from its primary label.
    fn semantic_error(&self, kind: ParseErrorKind, position: Pos, len: usize) -> ParseError {
        ParseError::at(self.lx.pos())
            .with_kind(kind)
            .with_location(position, len)
    }

    /// Report expected constructs at the next token, consuming leading whitespace/comments.
    fn err_expect(&mut self, expected: impl Into<String>) -> ParseError {
        self.skip_ws();
        self.err_expect_here(expected)
    }

    /// Report an expectation without advancing past the failure position.
    fn err_expect_here(&self, expected: impl Into<String>) -> ParseError {
        ParseError::expected(self.lx.pos(), expected, self.lx.peek())
    }

    fn in_context<T>(
        &mut self,
        context: ParseContext,
        parse: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        parse(self).map_err(|error| error.with_context(context))
    }

    fn item_position_error(&mut self) -> ParseError {
        self.skip_ws();
        let start = self.save();
        if self.lx.peek().is_some_and(|c| c.is_alphabetic()) {
            let (item, len) = self.diagnostic_item();
            return self.semantic_error(
                ParseErrorKind::UnknownItem {
                    item,
                    context: ParseContext::TheoryItem,
                },
                start,
                len,
            );
        }
        self.err_expect("theory item, \"end\"")
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
        loop {
            let Some(o) = op(self) else { break };
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
            Err(self.err_expect(label))
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
            Err(self.err_expect(label))
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

    fn ident(&mut self) -> Result<String, ParseError> {
        if let Some(id) = self.lx.identifier() {
            return Ok(id);
        }
        if let Some(e) = self.err_reserved_word() {
            return Err(e);
        }
        Err(self.err_expect_here("identifier"))
    }

    /// Diagnose a reserved identifier without rescanning or moving the lexer.
    fn err_reserved_word(&mut self) -> Option<ParseError> {
        self.skip_ws();
        let start = self.save();
        let word = RESERVED_NAMES.into_iter().find(|word| {
            self.lx
                .rest()
                .strip_prefix(word)
                .is_some_and(|rest| !rest.chars().next().is_some_and(is_ident_char))
        })?;
        // Keep parse progress distinct from the keyword's primary source span.
        let progress = Pos {
            offset: start.offset + word.len(),
            col: start.col + word.len() as u32,
            ..start
        };
        Some(
            ParseError::at(progress)
                .with_kind(ParseErrorKind::ReservedKeyword {
                    keyword: word.into(),
                })
                .with_location(start, word.len()),
        )
    }

    fn string_literal(&mut self) -> Result<String, ParseError> {
        self.string_literal_spanned().map(|(text, _)| text)
    }

    fn string_literal_spanned(&mut self) -> Result<(String, std::ops::Range<usize>), ParseError> {
        self.skip_ws();
        let opening = self.save();
        self.lx
            .string_literal_spanned()
            .map_err(|failure| self.quoted_error(opening, failure, "a valid string literal"))
    }

    fn quoted_error(
        &self,
        opening: Pos,
        failure: crate::lexer::QuotedError,
        expected: &str,
    ) -> ParseError {
        let found = self.lx.src()[failure.position.offset..].chars().next();
        let error = ParseError::expected(failure.position, expected, found);
        if failure.unterminated {
            error.with_kind(ParseErrorKind::UnclosedDelimiter {
                opening: '"',
                opening_span: opening.offset..opening.offset + 1,
                closing: '"',
            })
        } else {
            error
        }
    }

    // =========================================================================
    // Top-level theory
    // =========================================================================

    pub fn theory(&mut self) -> Result<Theory, ParseError> {
        let result = self.theory_inner();
        self.lx
            .finish(result)
            .map_err(|error| self.with_arity_site(error))
    }

    fn theory_inner(&mut self) -> Result<Theory, ParseError> {
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
            return Err(self.err_expect("configuration or begin"));
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

    /// Parse a flat item stream, evaluating conditionals with an explicit stack.
    /// Active syntax owns comments and item contents; inactive text is opaque.
    fn theory_items_until_end(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        let mut items = Vec::new();
        // Each frame holds the parent's activity and whether #else has occurred.
        let mut branches: Vec<(bool, bool)> = Vec::new();
        let mut active = true;
        loop {
            if active {
                self.skip_ws();
            } else {
                while self
                    .lx
                    .peek()
                    .is_some_and(|c| c != '\n' && c.is_whitespace())
                {
                    self.lx.bump();
                }
            }
            if let Some(directive) = self.conditional_directive() {
                match directive {
                    "ifdef" => {
                        let condition = self
                            .consume_conditional("ifdef")?
                            .expect("ifdef has a condition");
                        branches.push((active, false));
                        active &= condition;
                    }
                    "else" => {
                        let Some((parent_active, seen_else)) = branches.last_mut() else {
                            break;
                        };
                        if *seen_else {
                            return Err(self.err_expect_here("\"#endif\""));
                        }
                        self.consume_conditional("else")?;
                        *seen_else = true;
                        active = *parent_active && !active;
                    }
                    "endif" => {
                        let Some((parent_active, _)) = branches.pop() else {
                            break;
                        };
                        self.consume_conditional("endif")?;
                        active = parent_active;
                    }
                    _ => unreachable!("only conditional keywords are recognized"),
                }
                continue;
            }
            if self.lx.is_eof() {
                break;
            }
            if !active {
                while let Some(c) = self.lx.bump() {
                    if c == '\n' {
                        break;
                    }
                }
                continue;
            }
            if self.at_keyword("end") {
                break;
            }
            // Expand directives here so every consumer sees the same flat item stream.
            let save = self.save();
            if self.lx.eat_str("#") {
                let directive = self.lx.ascii_alpha_run();
                match directive.as_str() {
                    "ifdef" | "else" | "endif" => {
                        return Err(ParseError::expected(
                            save,
                            "a standalone conditional directive line",
                            Some('#'),
                        )
                        .with_context(ParseContext::Theory));
                    }
                    "include" => items.extend(self.expand_include()?),
                    "define" => {
                        let id = self.ident()?;
                        self.state.flags.insert(id);
                    }
                    other => {
                        return Err(self.err(format!("unknown preprocessor directive `#{other}`")))
                    }
                }
                continue;
            }
            let item = self.theory_item()?;
            items.push(item);
        }
        if !branches.is_empty() {
            return Err(self.err_expect_here("\"#endif\""));
        }
        Ok(items)
    }

    fn theory_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.skip_ws();

        // Try formal comment first (header `{* body *}`)
        let save = self.save();
        if let Some((h, b)) = self.lx.formal_comment() {
            return Ok(TheoryItem::FormalComment { header: h, body: b });
        }
        self.restore(save);

        // Try keyword-led items in priority order.
        if self.at_keyword("builtins") {
            return self.in_context(ParseContext::Builtin, Self::builtins);
        }
        if self.at_keyword("options") {
            return self.in_context(ParseContext::Options, Self::options);
        }
        if self.at_keyword("functions") || self.at_keyword("function") {
            return self.in_context(ParseContext::FunctionDeclaration, Self::functions);
        }
        if self.at_keyword("equations") {
            return self.in_context(ParseContext::Equation, Self::equations);
        }
        if self.at_keyword("macros") || self.at_keyword("macro") {
            return self.in_context(ParseContext::Macro, Self::macros);
        }
        if self.at_keyword("predicates") || self.at_keyword("predicate") {
            return self.in_context(ParseContext::Predicate, Self::predicates);
        }
        if self.at_keyword("heuristic") {
            return self.in_context(ParseContext::Heuristic, Self::heuristic);
        }
        if self.at_keyword("tactic") {
            return self.in_context(ParseContext::Tactic, Self::tactic);
        }
        if self.at_keyword("restriction") {
            return self.in_context(ParseContext::Restriction, Self::restriction_item);
        }
        if self.at_keyword("axiom") {
            return self.in_context(ParseContext::Restriction, Self::legacy_axiom);
        }
        if self.at_keyword("rule") {
            return self.in_context(ParseContext::Rule, Self::rule_item);
        }
        if self.at_keyword("lemma") {
            return self.in_context(ParseContext::Lemma, Self::lemma_item);
        }
        if self.at_keyword("diffLemma") {
            return self.in_context(ParseContext::Lemma, Self::diff_lemma_item);
        }
        if self.at_keyword("test") {
            return self.in_context(ParseContext::CaseTest, Self::case_test_item);
        }
        if self.at_keyword("equivLemma") {
            return self.in_context(ParseContext::Lemma, |parser| parser.equiv_lemma(false));
        }
        if self.at_keyword("diffEquivLemma") {
            return self.in_context(ParseContext::Lemma, |parser| parser.equiv_lemma(true));
        }
        if self.at_keyword("export") {
            return self.in_context(ParseContext::Export, Self::export_item);
        }
        if self.at_keyword("process") {
            return self.in_context(ParseContext::Process, Self::toplevel_process);
        }
        if self.at_keyword("let") {
            return self.in_context(ParseContext::Process, Self::process_def);
        }

        // Accountability: `lemma X [accountability_attrs] ...` is matched by lemma_item.
        // A lemmaAcc requires >=1 case-test ident before `accounts for` (HS
        // `commaSep1`, Theory/Text/Parser/Accountability.hs:30-39, see line 36);
        // the zero-ident form falls back to
        // a normal lemma.

        Err(self.item_position_error())
    }

    // -------------------- Preprocessor --------------------

    /// Expand an already-consumed `#include` keyword and its following path into the
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
    /// The double-quoted path is consumed here; the path is
    /// resolved against `self.base_dir` (HS `takeDirectory inFile0`); the file
    /// is read and its header-less fragment parsed by [`parse_include_fragment`]
    /// — which threads parser state both ways (signature / known funcs / flags),
    /// matching HS's `getState`/`putState` round-trip and `sig st'` merge.
    fn expand_include(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        self.in_context(ParseContext::Include, Self::expand_include_inner)
    }

    fn expand_include_inner(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        self.skip_ws();
        let path_start = self.save();
        let (raw_path, path_span) = self.string_literal_spanned()?;

        // HS `filePathParser`: resolve relative to the including file's dir when
        // we know it (`Just s -> s </> path`), else verbatim (`Nothing`).
        let resolved: PathBuf = match &self.base_dir {
            Some(dir) => dir.join(&raw_path),
            None => PathBuf::from(&raw_path),
        };
        let staged = if PathBuf::from(&raw_path).is_absolute() {
            None
        } else {
            self.staged_file.as_ref().map(|source| {
                source
                    .parent()
                    .unwrap_or_else(|| std::path::Path::new(""))
                    .join(&raw_path)
            })
        };
        self.state.input_aliases.push(InputAlias {
            physical: resolved.clone(),
            staged: staged.clone(),
        });

        let content = std::fs::read_to_string(&resolved).map_err(|e| {
            self.semantic_error(
                ParseErrorKind::IncludeIo {
                    path: resolved.display().to_string(),
                    reason: e.to_string(),
                },
                path_start,
                path_span.len(),
            )
        })?;

        // Nested includes in the fragment resolve relative to ITS directory
        // (HS recurses: `takeDirectory filepath`).
        let sub_base = resolved.parent().map(|p| p.to_path_buf());
        let source_name = resolved.display().to_string();
        self.parse_include_fragment(&content, sub_base, resolved, staged)
            .map_err(|e| e.with_source_text(source_name, content))
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
        source_file: PathBuf,
        staged_file: Option<PathBuf>,
    ) -> Result<Vec<TheoryItem>, ParseError> {
        let mut sub = Parser::new(content, &[], self.is_diff);
        // Thread parser state IN (HS `getState` before `parseFileWState`).
        self.swap_include_state(&mut sub);
        sub.base_dir = sub_base;
        sub.source_file = Some(source_file);
        sub.staged_file = staged_file;

        // Parse the header-less item stream: same loop as a theory body, but it
        // terminates at EOF (there is no `end` keyword in a fragment).
        let result = (|| {
            let items = sub.theory_items_until_end()?;
            sub.skip_ws();
            if !sub.lx.is_eof() {
                return Err(sub
                    .err_expect_here("end of included file")
                    .with_context(ParseContext::Include));
            }
            Ok(items)
        })();

        let result = sub
            .lx
            .finish(result)
            .map_err(|error| sub.with_arity_site(error));
        // Annotate while the included signature is still available, then
        // thread parser state BACK (HS `putState st'` + `sig st'` merge).
        self.swap_include_state(&mut sub);
        result
    }

    /// A conditional keyword at the start of a physical line, after indentation.
    /// Indexed node names such as `#endif.0` are ordinary tokens.
    fn conditional_directive(&self) -> Option<&'static str> {
        let rest = self.lx.rest().strip_prefix('#')?;
        let directive = ["ifdef", "else", "endif"].into_iter().find(|directive| {
            rest.strip_prefix(directive).is_some_and(|tail| {
                !tail
                    .chars()
                    .next()
                    .is_some_and(|c| is_ident_char(c) || c == '.')
            })
        })?;
        let before = &self.lx.src()[..self.save().offset];
        before
            .rsplit('\n')
            .next()
            .unwrap()
            .chars()
            .all(char::is_whitespace)
            .then_some(directive)
    }

    /// Parse only the directive's physical line, leaving the next line untouched.
    /// The caller has recognized the directive without consuming it.
    fn consume_conditional(&mut self, expected: &str) -> Result<Option<bool>, ParseError> {
        self.lx.eat_str(&format!("#{expected}"));
        let payload_start = self.save();
        let line_len = self.lx.rest().find('\n').unwrap_or(self.lx.rest().len());
        let mut line = Parser::new(&self.lx.rest()[..line_len], &[], false);
        let result = (|| {
            let condition = if expected == "ifdef" {
                Some(line.flag_disjuncts(&self.state.flags)?)
            } else {
                None
            };
            line.skip_ws();
            if !line.lx.is_eof() {
                return Err(line.err_expect_here("end of conditional directive line"));
            }
            Ok(condition)
        })();
        let condition = line
            .lx
            .finish(result)
            .map_err(|error| error.shifted(payload_start, self.lx.src()))?;
        while let Some(c) = self.lx.bump() {
            if c == '\n' {
                break;
            }
        }
        Ok(condition)
    }

    // -------------------- Builtins / options / heuristic / tactic --------------------

    fn builtins(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("builtins")?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            self.skip_ws();
            let (name, name_start, name_len) = self.hyphen_identifier_spanned()?;
            if !is_builtin_name(&name) {
                let diagnostic_name = diagnostic_lexeme(&name);
                return Err(self.semantic_error(
                    ParseErrorKind::UnknownItem {
                        item: diagnostic_name,
                        context: ParseContext::Builtin,
                    },
                    name_start,
                    name_len,
                ));
            }
            // HS `builtinTheory = asum $ map (try . extendSig) builtinsNames`
            // (Theory/Text/Parser/Signature.hs:139): `extendSig` runs per name,
            // right after its
            // `symbol`, so a conflict is diagnosed against the signature the
            // EARLIER names in the same list already merged, at the position
            // that name's lexeme reached.
            let introduced: Vec<_> = builtin_st_fun_syms(&name)
                .unwrap_or(&[])
                .iter()
                .filter(|sym| {
                    !self.state.fun_syms.iter().any(|(n, options)| {
                        n.as_bytes() == sym.name && *options == FunOptions::of_no_eq(sym)
                    })
                })
                .collect();
            self.enable_builtin(&name).map_err(|error| {
                error
                    .with_kind(ParseErrorKind::ConflictingDeclaration {
                        name: name.clone(),
                        context: ParseContext::Builtin,
                    })
                    .with_location(name_start, name_len)
            })?;
            for sym in introduced {
                self.function_sites.push(FunctionSite {
                    name: sym_name(sym).to_string(),
                    options: FunOptions::of_no_eq(sym),
                    span: name_start.offset..name_start.offset + name_len,
                    builtin: true,
                });
            }
            names.push(name);
            if !self.try_punct(",") {
                break;
            }
        }
        // `commaSep1`'s trailing `comma` (Token.hs:353-355) fails here.
        self.skip_ws();
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
    /// symbol. Names outside HS's table are rejected by [`Self::builtins`]
    /// before this function is called.
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
            "diffie-hellman" => self.state.sig_enable_dh = true,
            // `maudeSig` sets `enableDH = enableDH || enableBP`
            // (Term/Maude/Signature.hs:110-112).
            "bilinear-pairing" => {
                self.state.sig_enable_bp = true;
                self.state.sig_enable_dh = true;
            }
            "xor" => self.state.sig_enable_xor = true,
            "multiset" => self.state.sig_enable_mset = true,
            "natural-numbers" => self.state.sig_enable_nat = true,
            _ => {}
        }
        if !self.is_diff {
            // `functionConflicts` (Theory/Text/Parser/Signature.hs:110-115): a
            // name the builtin
            // brings that the signature already carries at a DIFFERENT options
            // tuple.  `dest-pairing` is exempt — it is expected to replace the
            // seeded `fst`/`snd` constructors with their destructor variants.
            if name != "dest-pairing"
                && let Some((conflict, options)) = syms.iter().find_map(|symbol| {
                    let want = FunOptions::of_no_eq(symbol);
                    self.state
                        .fun_syms
                        .iter()
                        .find(|(n, options)| n.as_bytes() == symbol.name && *options != want)
                        .map(|(_, options)| (sym_name(symbol), *options))
                })
            {
                let error = self.err(format!(
                        "Builtin `{name}` conflicts with function `{conflict}`: different arity or function options"
                    ));
                return Err(self.with_function_site(error, conflict, options));
            }
            // Functions are checked before macros; dest-pairing only exempts functions.
            if let Some(conflict) = syms.iter().find_map(|symbol| {
                let want = FunOptions::of_no_eq(symbol);
                self.state
                    .macro_syms
                    .iter()
                    .find(|(n, _)| n.as_bytes() == symbol.name)
                    .filter(|(_, options)| *options != want)
                    .map(|_| sym_name(symbol))
            }) {
                return Err(self.err(format!(
                    "Builtin `{name}` conflicts with macro `{conflict}`"
                )));
            }
            self.state
                .reserved_builtin_names
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
                Arc::make_mut(&mut self.state.fun_syms)
                    .retain(|(n, o)| !(n == fname && *o == evicted));
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
            .state
            .fun_syms
            .binary_search_by(|(n, o)| (n.as_bytes(), o.ord_key()).cmp(&key))
        {
            Ok(_) => {}
            Err(idx) => {
                Arc::make_mut(&mut self.state.fun_syms).insert(idx, (name.to_string(), opts))
            }
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
        Arc::make_mut(&mut self.state.fun_syms).clear();
        for f in &sig.st_fun_syms {
            self.insert_fun_sym(&String::from_utf8_lossy(f.name), FunOptions::of_no_eq(f));
        }
        self.state.ac_fun_syms = Arc::new(
            sig.st_ac_fun_syms
                .iter()
                .map(|a| String::from_utf8_lossy(a.name).into_owned())
                .collect(),
        );
        let ac_fun_syms = Arc::make_mut(&mut self.state.ac_fun_syms);
        ac_fun_syms.sort();
        ac_fun_syms.dedup();
        self.state.macro_syms = Arc::new(
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
        self.state.sig_enable_dh = sig.enable_dh || sig.enable_bp;
        self.state.sig_enable_bp = sig.enable_bp;
        self.state.sig_enable_xor = sig.enable_xor;
        self.state.sig_enable_mset = sig.enable_mset;
        self.state.sig_enable_nat = sig.enable_nat;
    }

    /// Copy the symbol state a sub-parser reads from the parser whose text
    /// carried it.  HS runs a nested parse in the enclosing parser's state,
    /// which supplies `acterm` the INFIX spelling of the user-declared `[AC]`
    /// symbols (Theory/Text/Parser/Term.hs:166-172), `nullaryApp` the arity-0
    /// constants (Theory/Text/Parser/Term.hs:158-163) and `diff` its gate.
    fn seed_from(&mut self, parent: &Parser<'_>) {
        self.state.fun_syms = parent.state.fun_syms.clone();
        self.state.ac_fun_syms = parent.state.ac_fun_syms.clone();
        self.state.macro_syms = parent.state.macro_syms.clone();
        self.state.sig_enable_dh = parent.state.sig_enable_dh;
        self.state.sig_enable_bp = parent.state.sig_enable_bp;
        self.state.sig_enable_xor = parent.state.sig_enable_xor;
        self.state.sig_enable_mset = parent.state.sig_enable_mset;
        self.state.sig_enable_nat = parent.state.sig_enable_nat;
        self.state.enable_diff = parent.state.enable_diff;
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
    fn hyphen_identifier_spanned(&mut self) -> Result<(String, Pos, usize), ParseError> {
        self.skip_ws();
        let start = self.save();
        let mut s = self.ident()?;
        let mut end = start.offset + s.len();
        while self.at_hyphen_join() {
            self.lx.bump(); // consume `-`
            s.push('-');
            let segment_start = self.save();
            let id = self.ident()?;
            end = segment_start.offset + id.len();
            s.push_str(&id);
        }
        Ok((s, start, end - start.offset))
    }

    fn options(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("options")?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            let mut found = None;
            for option in DeclarableOption::ALL {
                // HS uses `symbol`, not `reserved`, here: a valid option is
                // accepted as a prefix and any suffix is diagnosed by the
                // enclosing top-level parser.
                if self.try_punct(option.as_str()) {
                    found = Some(option.as_str().to_string());
                    break;
                }
            }
            let Some(name) = found else {
                return Err(self.err_expect("theory option"));
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
        Ok(TheoryItem::Heuristic {
            raw: raw.trim().to_string(),
            source_file: self
                .source_file
                .as_ref()
                .map(|path| path.to_string_lossy().into_owned()),
        })
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
            let word = self.lx.ascii_alpha_run();
            if word.is_empty() {
                return Err(self.err_expect("letter"));
            }
            self.skip_ws();
            let allowed = if self.is_diff { "sScC" } else { "sSpPcCiI" };
            if word.chars().count() != 1 || !allowed.contains(&word) {
                // HS feeds this word to the partial `stringToGoalRanking` and
                // aborts. Reject the same invalid declaration as a structured
                // parse error instead of reproducing that runtime crash.
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
            return Err(self.err_expect("tactic selector with a quoted argument"));
        }
        Ok(PrioBlock { ranking, selectors })
    }

    fn tactic_disjunction(&mut self) -> Result<Option<SelectorExpr>, ParseError> {
        let Some(mut expr) = self.tactic_conjunction()? else {
            return Ok(None);
        };
        while self.try_punct("|") || self.try_punct("∨") {
            let Some(right) = self.tactic_conjunction()? else {
                return Err(self.err_expect_here("tactic selector after disjunction"));
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
                return Err(self.err_expect_here("tactic selector after conjunction"));
            };
            expr = SelectorExpr::And(Box::new(expr), Box::new(right));
        }
        Ok(Some(expr))
    }

    fn tactic_negation(&mut self) -> Result<Option<SelectorExpr>, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let Some(expr) = self.tactic_function()? else {
                return Err(self.err_expect_here("tactic selector after negation"));
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
            "let",
        ];
        let start = self.lx.pos().offset;
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
        // Parentheses and keywords inside a public literal are data, not proof
        // structure. Track the single-quoted literal explicitly so a `)` or a
        // word such as `rule` cannot corrupt the depth-zero boundary scan.
        let mut in_public_literal = false;
        loop {
            if self.lx.is_eof() {
                break;
            }
            if in_public_literal {
                let Some(c) = self.lx.peek() else {
                    break;
                };
                self.lx.bump();
                // Tamarin public literals have no escape syntax: a backslash
                // is ordinary data and every quote closes the literal.
                if c == '\'' {
                    in_public_literal = false;
                }
                prev_was_ident = false;
                continue;
            }
            // Skip whitespace and comments. Block/line comments are entirely
            // skipped by skip_ws; whitespace resets the prev-ident state.
            let pre_ws = self.lx.pos();
            self.lx.skip_ws();
            if self.lx.pos() != pre_ws {
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
                        if KW.contains(&id) {
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
            // Advance past the next character.
            match self.lx.peek() {
                Some(c) => {
                    prev_was_ident = is_ident_char(c) || c == '-';
                    // Track parenthesis nesting so the keyword scan above only
                    // fires at the top level.  `)` is clamped at 0 so a stray
                    // unbalanced close (should not occur in a well-formed
                    // proof) cannot drive the depth negative and re-enable the
                    // scan inside a group.
                    match c {
                        '(' => depth += 1,
                        ')' => depth = (depth - 1).max(0),
                        '\'' => in_public_literal = true,
                        _ => {}
                    }
                    self.lx.bump();
                    if c == '\'' {
                        // Like single_quoted, consume the opening quote's
                        // trailing whitespace/comments before the literal body.
                        self.lx.skip_ws();
                    }
                }
                None => break,
            }
        }
        self.lx.src()[start..self.lx.pos().offset].to_owned()
    }

    // -------------------- functions / equations / macros / predicates --------------------

    fn functions(&mut self) -> Result<TheoryItem, ParseError> {
        // `functions:` or `function:`
        if !self.try_kw("functions") {
            self.require_kw("function")?;
        }
        self.require_punct(":")?;
        let mut decls = Vec::new();
        loop {
            let f = self.function_decl()?;
            decls.push(f);
            if !self.try_punct(",") {
                break;
            }
        }
        self.skip_ws();
        Ok(TheoryItem::Functions(decls))
    }

    /// Parse `elem (, elem)* ,?` up to (and consuming) the `close` token,
    /// assuming the opening token has already been consumed. Mirrors HS
    /// `commaSep = sepEndBy comma` (Token.hs): the list may be empty and a
    /// single trailing comma before `close` is permitted.
    fn sep_end_by<T>(
        &mut self,
        opening: Pos,
        close: &str,
        elem: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        let close_char = close.chars().next().expect("non-empty closing delimiter");
        self.list_closers.push(close_char);
        let result = self.sep_end_by_inner(opening, close, elem);
        self.list_closers.pop();
        result
    }

    fn sep_end_by_inner<T>(
        &mut self,
        opening: Pos,
        close: &str,
        mut elem: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        let mut v = Vec::new();
        if !self.try_punct(close) {
            loop {
                self.skip_ws();
                let missing_delimiter = self.at_unclosed_list_boundary(close);
                match elem(self) {
                    Ok(value) => v.push(value),
                    Err(mut error) => {
                        if missing_delimiter {
                            Self::mark_unclosed_delimiter(&mut error, opening, close);
                        }
                        return Err(error);
                    }
                }
                if !self.try_punct(",") {
                    break;
                }
                if self.peek_punct(close) {
                    break;
                }
            }
            if !self.try_punct(close) {
                self.skip_ws();
                let unclosed = self.at_unclosed_list_boundary(close);
                let mut error = self.err_expect(format!("\",\", \"{close}\""));
                if unclosed {
                    Self::mark_unclosed_delimiter(&mut error, opening, close);
                }
                return Err(error);
            }
        }
        Ok(v)
    }

    fn at_unclosed_list_boundary(&self, close: &str) -> bool {
        match self.lx.peek() {
            None => true,
            Some(c) if close.starts_with(c) => true,
            Some(c) => self
                .list_closers
                .get(..self.list_closers.len().saturating_sub(1))
                .is_some_and(|outer| outer.contains(&c)),
        }
    }

    fn mark_unclosed_delimiter(error: &mut ParseError, opening: Pos, close: &str) {
        let (opening_char, closing_char) = match close {
            ")" => ('(', ')'),
            "]" => ('[', ']'),
            _ => unreachable!("unsupported list delimiter: {close}"),
        };
        error.set_kind(ParseErrorKind::UnclosedDelimiter {
            opening: opening_char,
            opening_span: opening.offset..opening.offset.saturating_add(opening_char.len_utf8()),
            closing: closing_char,
        });
    }

    /// The `(arity, options)` HS's `function` finds for `name` in the parse-time
    /// signature: `lookup f (S.toList (stFunSyms sign) ++ S.toList (macroNames
    /// sign))` (Theory/Text/Parser/Signature.hs:212), which takes the FIRST
    /// match — free symbols before macros.
    fn lookup_fun_options(&self, name: &str) -> Option<FunOptions> {
        self.state
            .fun_syms
            .iter()
            .chain(self.state.macro_syms.iter())
            .find(|(n, _)| n == name)
            .map(|(_, o)| *o)
    }

    /// A numeric arity or a parenthesized argument-type list and result type.
    fn function_type(&mut self) -> Result<(FunctionArgs, Option<String>), ParseError> {
        if self.try_punct("/") {
            let position = self.save();
            let len = self
                .lx
                .rest()
                .bytes()
                .take_while(u8::is_ascii_digit)
                .count();
            let Some(k) = self.lx.natural() else {
                return Err(self.err_expect("natural"));
            };
            let arity = usize::try_from(k).map_err(|_| {
                self.err("function arity is too large for this platform")
                    .with_location(position, len)
            })?;
            return Ok((
                FunctionArgs::Untyped {
                    arity,
                    position,
                    len,
                },
                None,
            ));
        }
        self.skip_ws();
        let opening = self.save();
        if !self.try_punct("(") {
            return Err(self.err_expect("\"/\", \"(\""));
        }
        let args = self.sep_end_by(opening, ")", Self::type_p)?;
        self.require_punct(":")?;
        let out_type = self.type_p()?;
        Ok((FunctionArgs::Typed(args), out_type))
    }

    fn materialize_function_args(
        &self,
        args: FunctionArgs,
    ) -> Result<Vec<Option<String>>, ParseError> {
        match args {
            FunctionArgs::Typed(types) => Ok(types),
            FunctionArgs::Untyped {
                arity,
                position,
                len,
            } => {
                let mut types = Vec::new();
                types.try_reserve_exact(arity).map_err(|e| {
                    self.err(format!(
                        "cannot allocate arguments for function arity {arity}: {e}"
                    ))
                    .with_location(position, len)
                })?;
                types.resize(arity, None);
                Ok(types)
            }
        }
    }

    /// `Any` denotes an unspecified type; other identifiers name a type.
    fn type_p_element(&mut self) -> Option<Option<String>> {
        let id = self.lx.identifier()?;
        Some((id != "Any").then_some(id))
    }

    fn function_decl(&mut self) -> Result<FunctionDecl, ParseError> {
        self.skip_ws();
        let name_pos = self.lx.pos();
        let name_start = name_pos.offset;
        let name = self.ident()?;
        let name_end = name_start + name.len();
        let (args, out_type) = self.function_type()?;
        let arity = match &args {
            FunctionArgs::Untyped { arity, .. } => *arity,
            FunctionArgs::Typed(types) => types.len(),
        };
        // Optional attributes `[private, destructor, AC, NDC, NDC-diff, ...]`
        // (HS `option [] $ list functionAttribute`).
        let mut atts = Vec::new();
        if self.try_punct("[") {
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
            arity,
            private,
            destructor,
            ndc,
            ndc_diff,
        };
        // Check (1), Theory/Text/Parser/Signature.hs:200-209: a name an enabled
        // `builtins:` item
        // reserved must be re-declared at EXACTLY the builtin's options tuple.
        // It runs BEFORE the general conflict check, has no `fst`/`snd`
        // exemption, and consults `stFunSyms` only — never the macro names.
        if self.state.reserved_builtin_names.contains(&name) {
            let builtin = self
                .state
                .fun_syms
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, o)| *o);
            if let Some(b) = builtin.filter(|b| *b != requested) {
                let diagnostic_name = diagnostic_lexeme(&name);
                let error = self
                    .err(format!(
                        "`{diagnostic_name}` conflicts with its builtin declaration: {}",
                        function_option_difference(b, requested)
                    ))
                    .with_kind(ParseErrorKind::ConflictingDeclaration {
                        name: diagnostic_name,
                        context: ParseContext::FunctionDeclaration,
                    })
                    .with_location(name_pos, name.len());
                return Err(self.with_function_site(error, &name, b));
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
                let diagnostic_name = diagnostic_lexeme(&name);
                let error = self
                    .err(format!(
                        "`{diagnostic_name}` conflicts with its previous declaration: {}",
                        function_option_difference(prev, requested)
                    ))
                    .with_kind(ParseErrorKind::ConflictingDeclaration {
                        name: diagnostic_name,
                        context: ParseContext::FunctionDeclaration,
                    })
                    .with_location(name_pos, name.len());
                return Err(self.with_function_site(error, &name, prev));
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
                return Ok(FunctionDecl {
                    name,
                    arg_types: self.materialize_function_args(args)?,
                    out_type,
                    private: prev.private,
                    destructor: prev.destructor,
                    ac: false,
                    ndc: prev.ndc,
                    ndc_diff: prev.ndc_diff,
                });
            }
        }
        let new_symbol = !self
            .state
            .fun_syms
            .iter()
            .any(|(n, opts)| n == &name && *opts == requested);
        // HS rejects a non-binary `[AC]` symbol outright
        // (Theory/Text/Parser/Signature.hs:220)
        // in the `_` case of the conflict check, so check (2) above wins for
        // a name already in the signature.
        if ac && requested.arity != 2 {
            self.skip_ws();
            let error = self.semantic_error(
                ParseErrorKind::NonBinaryAcFunction {
                    name: diagnostic_lexeme(&name),
                    arity: requested.arity,
                },
                name_pos,
                name.len(),
            );
            return Err(error);
        }
        let arg_types = self.materialize_function_args(args)?;
        if ac {
            // A binary `[AC]` symbol also becomes an infix operator for the terms
            // that follow, mirroring HS's `modifyStateSig $ addFunSym (ACfctUser
            // ...)`, which likewise runs only in the `IsAC` branch.
            if !self.state.ac_fun_syms.contains(&name) {
                let names = Arc::make_mut(&mut self.state.ac_fun_syms);
                names.push(name.clone());
                names.sort();
            }
        } else {
            // HS's `NotAC` branch instead files the symbol under `stFunSyms`
            // (`addFunSym (NoEqUser ...)`, Theory/Text/Parser/Signature.hs:224),
            // a set insert.
            self.insert_fun_sym(&name, requested);
        }
        if !ac && new_symbol {
            self.function_sites.push(FunctionSite {
                name: name.clone(),
                options: requested,
                span: name_pos.offset..name_end,
                builtin: false,
            });
        }
        Ok(FunctionDecl {
            name,
            arg_types,
            out_type,
            private,
            destructor,
            ac,
            ndc,
            ndc_diff,
        })
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
            Some(t) => Ok(t),
            None => Err(self.err_expect("type")),
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
            if !self.try_punct("=") {
                return Err(self.err_expect("\"=\""));
            }
            let rhs = self.acterm(true)?;
            eqs.push(Equation { lhs, rhs });
            if !self.try_punct(",") {
                break;
            }
        }
        // `commaSep1`'s trailing `comma` fails at the last right-hand side's
        // stop position, ahead of the next item's labels.
        self.skip_ws();
        Ok(TheoryItem::Equations { convergent, eqs })
    }

    fn macros(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("macros") {
            self.require_kw("macro")?;
        }
        self.require_punct(":")?;
        let mut ms = Vec::new();
        loop {
            self.skip_ws();
            let name_start = self.save();
            let name = self.ident()?;
            // HS `when (BC.unpack op `elem` reservedBuiltins) $ error …`
            // (Theory/Text/Parser/Macro.hs:34-35): a GHC `error`, raised right
            // after the
            // identifier and BEFORE the arguments, so it wins over every later
            // failure in the macro — including a malformed argument list, and
            // the name conflict below that an enabled owning theory would
            // otherwise raise.  Independent of which builtins are enabled.
            if Self::RESERVED_BUILTINS.contains(&name.as_str()) {
                let diagnostic_name = diagnostic_lexeme(&name);
                return Err(self.semantic_error(
                    ParseErrorKind::ReservedBuiltin {
                        name: diagnostic_name,
                        context: ParseContext::Macro,
                    },
                    name_start,
                    name.len(),
                ));
            }
            let opening = self.save();
            self.require_punct("(")?;
            // HS `parens $ commaSep lvar` (Theory/Text/Parser/Macro.hs:29-49, see
            // line 36): trailing comma OK.
            let mut arg_positions = Vec::new();
            let args = self.sep_end_by(opening, ")", |parser| {
                let (argument, position) = parser.var_spec_spanned()?;
                arg_positions.push(position);
                Ok(argument)
            })?;
            // HS `unless (length args == length (nub args)) $ error …`
            // (Theory/Text/Parser/Macro.hs:37-38), the second GHC `error`: `nub`
            // compares FULL
            // `LVar`s, so name, sort and index all count — `m(x, x:pub)` and
            // `m(x.1, x)` pass, `m(x, x)` and `m(x, x:msg)` do not (a
            // prefixless binder is `LSortMsg`, Token.hs:424-433).
            if let Some((index, argument)) = Self::duplicate_macro_arg(&args) {
                return Err(self.semantic_error(
                    ParseErrorKind::DuplicateMacroArgument {
                        argument: diagnostic_lexeme(&argument.name),
                    },
                    arg_positions[index],
                    argument.name.len(),
                ));
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
                let diagnostic_name = diagnostic_lexeme(&name);
                return Err(self.semantic_error(
                    ParseErrorKind::ConflictingDeclaration {
                        name: diagnostic_name,
                        context: ParseContext::Macro,
                    },
                    name_start,
                    name.len(),
                ));
            }
            // HS `macro` registers the name under `macroNames` as
            // `(k, Private, Destructor, NotNDC)`
            // (Theory/Text/Parser/Macro.hs:46), which
            // `function`'s conflict check then sees
            // (Theory/Text/Parser/Signature.hs:212).
            Arc::make_mut(&mut self.state.macro_syms).push((
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
        self.skip_ws();
        Ok(TheoryItem::Macros(ms))
    }

    /// HS `reservedBuiltins` (Theory/Text/Parser/Term.hs:74-85) in its order:
    /// the builtin symbol names no macro may take, whatever the theory
    /// declares (values at Term/Term/FunctionSymbols.hs:221-243).
    const RESERVED_BUILTINS: &'static [&'static str] = &[
        "mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor",
    ];

    /// HS `length args /= length (nub args)`
    /// (Theory/Text/Parser/Macro.hs:37): `nub`'s `Eq LVar`
    /// compares name, sort and index together (LTerm.hs:541-542), so two
    /// arguments collide only when all three agree.  The sort is the one
    /// `lvar` gave the argument (Token.hs:409-437): an explicit prefix or
    /// suffix names it, a prefixless binder is `LSortMsg`.
    fn duplicate_macro_arg(args: &[VarSpec]) -> Option<(usize, &VarSpec)> {
        let mut seen: Vec<(&str, u64, LSort)> = Vec::with_capacity(args.len());
        for (index, a) in args.iter().enumerate() {
            let key = (a.name.as_str(), a.idx, a.sort);
            if seen.contains(&key) {
                return Some((index, a));
            }
            seen.push(key);
        }
        None
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
        self.state.fun_syms.iter().any(|(n, _)| n == name)
            || self.state.ac_fun_syms.iter().any(|n| n == name)
            || self.state.macro_syms.iter().any(|(n, _)| n == name)
            || self
                .enabled_theory_noeq_syms()
                .any(|s| s.name == name.as_bytes())
    }

    fn predicates(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("predicates") {
            self.require_kw("predicate")?;
        }
        self.require_punct(":")?;
        let mut ps = Vec::new();
        loop {
            let (f, name_start) = self.in_context(ParseContext::Predicate, Self::fact_located)?;
            self.require_punct("<=>")?;
            let phi = self.formula()?;
            ps.push((
                Predicate {
                    fact: f,
                    formula: phi,
                },
                name_start,
            ));
            if !self.try_punct(",") {
                break;
            }
        }
        // HS folds `liftedAddPredicate` over the block AFTER `commaSep1`
        // collected every declaration (Theory/Text/Parser/Signature.hs:278-284),
        // so a collision — against an earlier block, the builtin `Smaller/2`,
        // or an earlier declaration of the same block — fails at the position
        // after parsing the whole block.
        for (p, name_start) in &ps {
            let key = (p.fact.persistent, p.fact.name.clone(), p.fact.args.len());
            if self.state.seen_predicates.contains(&key) {
                let name = diagnostic_lexeme(&p.fact.name);
                return Err(self.semantic_error(
                    ParseErrorKind::DuplicateDeclaration {
                        name,
                        context: ParseContext::Predicate,
                    },
                    *name_start,
                    p.fact.name.len(),
                ));
            }
            self.state.seen_predicates.push(key);
        }
        Ok(TheoryItem::Predicates(
            ps.into_iter().map(|(p, _)| p).collect(),
        ))
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
        if self.state.emit_warnings {
            AXIOM_DEPRECATION.call_once(|| {
                eprintln!(
                    "Deprecation Warning: using 'axiom' is retired notation, replace all uses of \
                     'axiom' by 'restriction'."
                );
            });
        }
        Ok(TheoryItem::LegacyAxiom(r))
    }

    fn restriction(&mut self, kw: &str) -> Result<Restriction, ParseError> {
        self.require_kw(kw)?;
        self.skip_ws();
        let name_start = self.save();
        let name = self.ident()?;
        let name_len = name.len();
        let mut attributes = Vec::new();
        if self.try_punct("[") {
            loop {
                self.skip_ws();
                let attribute_start = self.save();
                if self.try_kw("left") {
                    attributes.push(RestrictionAttr::LeftRestriction);
                } else if self.try_kw("right") {
                    attributes.push(RestrictionAttr::RightRestriction);
                } else {
                    if !self.peek_punct("]") {
                        let (item, item_len) = self.diagnostic_item();
                        return Err(self.semantic_error(
                            ParseErrorKind::UnknownItem {
                                item: item.clone(),
                                context: ParseContext::RestrictionAttribute,
                            },
                            attribute_start,
                            item_len,
                        ));
                    }
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
        // parsed `restriction`/`axiom` item. A left/right attribute marks the
        // diff-theory shape, which
        // HS's plain `restriction` production cannot even read
        // (Theory/Text/Parser/Restriction.hs:77-80) and its diff parse routes
        // through `liftedAddRestriction'` (Theory/Text/Parser.hs:433-435,546),
        // splitting the sides instead of comparing names; the guard leaves
        // those items, and every item of a diff parse, alone.
        if !self.is_diff
            && attributes.is_empty()
            && self.state.seen_restriction_names.contains(&name)
        {
            return Err(self.duplicate_declaration(
                "restriction",
                name,
                ParseContext::Restriction,
                name_start,
                name_len,
            ));
        }
        // Feed the restriction-name set the `_restrict` guard consults
        // ([`Parser::guard_duplicate_rule`] step 1): HS `addRestriction`
        // checks new `Restr_<rule>_<i>` names against ALL restrictions,
        // user-declared ones included (TheoryObject.hs:453-456).
        self.state.seen_restriction_names.push(name.clone());
        if !self.is_diff {
            self.named_sites
                .entry(("restriction", name.clone()))
                .or_insert(name_start.offset..name_start.offset + name_len);
        }
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
            return Err(self.err_expect("closing quote or formula operator"));
        }
        Ok(f)
    }

    // -------------------- Rule --------------------

    fn rule_item(&mut self) -> Result<TheoryItem, ParseError> {
        // We must distinguish protocol rules from intruder rules. Intruder
        // rules use `rule (modulo AC) name: ...` — they live in the top-level
        // theory only when explicitly parsed (e.g. for a precomputed intruder
        // file).
        let (r, name_start) = self.parse_rule_located()?;
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
            self.guard_duplicate_rule(&r, name_start)?;
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
    fn guard_duplicate_rule(&mut self, r: &Rule, name_start: Pos) -> Result<(), ParseError> {
        if self.is_diff {
            return Ok(());
        }
        for i in 1..=r.embedded_restrictions.len() {
            // HS `fromRuleRestriction (rname ++ "_" ++ show i)` with
            // `restrPrefix = "Restr_"` (Model/Restriction.hs:129-149).
            let rstr_name = format!("Restr_{}_{}", r.name, i);
            if self.state.seen_restriction_names.contains(&rstr_name) {
                return Err(self.duplicate_declaration(
                    "restriction",
                    rstr_name,
                    ParseContext::Restriction,
                    name_start,
                    r.name.len(),
                ));
            }
        }
        if let Some(first) = self.state.seen_rules.iter().find(|p| p.name == r.name) {
            let differs = first.attributes != r.attributes
                || first.premises != r.premises
                || first.actions != r.actions
                || first.conclusions != r.conclusions
                || first.embedded_restrictions != r.embedded_restrictions
                || first.variants != r.variants
                || first.left_right != r.left_right;
            if differs {
                let diagnostic_name = diagnostic_lexeme(&r.name);
                return Err(self.semantic_error(
                    ParseErrorKind::ConflictingDeclaration {
                        name: diagnostic_name,
                        context: ParseContext::Rule,
                    },
                    name_start,
                    r.name.len(),
                ));
            }
        } else {
            self.state.seen_rules.push(r.clone());
        }
        for i in 1..=r.embedded_restrictions.len() {
            self.state
                .seen_restriction_names
                .push(format!("Restr_{}_{}", r.name, i));
        }
        Ok(())
    }

    fn with_function_site(&self, error: ParseError, name: &str, options: FunOptions) -> ParseError {
        let site = self
            .function_sites
            .iter()
            .rev()
            .find(|site| site.name == name && site.options == options);
        match site {
            Some(site) => error.with_related_span(
                site.span.clone(),
                if site.builtin {
                    "function introduced by this builtin"
                } else {
                    "function declared here"
                },
            ),
            None => error,
        }
    }

    fn with_arity_site(&self, error: ParseError) -> ParseError {
        // Included-file errors already carry their own source and labels.
        if error.source_text().is_some()
            || !matches!(error.kind(), ParseErrorKind::WrongFunctionArity { .. })
        {
            return error;
        }
        let Some(name) = self.lx.src().get(error.span()) else {
            return error;
        };
        match self.lookup_arity(name) {
            Some(ArityRes::NoEq { opts }) => self.with_function_site(error, name, opts),
            _ => error,
        }
    }

    fn duplicate_declaration(
        &mut self,
        label: &str,
        name: String,
        context: ParseContext,
        position: Pos,
        span_len: usize,
    ) -> ParseError {
        let site = self.named_sites.get(&(label, name.clone())).cloned();
        let name = diagnostic_lexeme(&name);
        self.skip_ws();
        let error = self.semantic_error(
            ParseErrorKind::DuplicateDeclaration { name, context },
            position,
            span_len,
        );
        match site {
            Some(span) => error.with_related_span(span, "first declaration is here"),
            None => error,
        }
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
    /// `(chan, msg)` with a plain channel. When both fail, select one complete
    /// diagnostic with [`Parser::select_alt_error`].
    fn parse_in_chan_msg(&mut self) -> Result<(Option<Term>, Term), ParseError> {
        self.require_punct("(")?;
        let probe = self.save();
        let message = (|| -> Result<Term, ParseError> {
            let msg = self.with_patterns(|p| p.term(false))?;
            self.require_punct(")")?;
            Ok(msg)
        })();
        // Retain consumed comment failures before the next alternative rewinds.
        let e1 = match self.lx.finish(message) {
            Ok(msg) => return Ok((None, msg)),
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
        .map_err(|e2| Self::select_alt_error(e1, e2))
    }

    /// Keep the furthest failure intact, preserving grammar order on ties.
    /// A structured cause can still belong to an unrelated speculative alternative.
    fn select_alt_error(e1: ParseError, e2: ParseError) -> ParseError {
        if e2.pos.offset > e1.pos.offset {
            e2
        } else {
            e1
        }
    }

    fn parse_rule(&mut self) -> Result<Rule, ParseError> {
        self.parse_rule_located().map(|(rule, _)| rule)
    }

    fn parse_rule_located(&mut self) -> Result<(Rule, Pos), ParseError> {
        self.in_context(ParseContext::Rule, Self::parse_rule_located_inner)
    }

    fn parse_rule_located_inner(&mut self) -> Result<(Rule, Pos), ParseError> {
        self.skip_ws();
        self.require_kw("rule")?;
        let (mut rule, name_start) = self.rule_after_kw()?;
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
            if !self.is_diff {
                self.skip_ws();
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
        Ok((rule, name_start))
    }

    fn parse_rule_ac(&mut self) -> Result<Rule, ParseError> {
        self.require_kw("rule")?;
        // HS `protoRuleACInfo`/`intrRule`
        // (Theory/Text/Parser/Rule.hs:137-138/157) sequence a
        // non-optional `moduloAC` here (`symbol "rule" *> moduloAC *> ...`).
        // This port relaxes that: `try_modulo` returns `None` when the
        // `(modulo AC)` head is absent and parsing proceeds. (More lenient than
        // Haskell, but still accepts all valid Haskell input.)
        self.in_context(ParseContext::Rule, |parser| {
            parser.rule_after_kw().map(|(rule, _)| rule)
        })
    }

    /// The rule header and body that follow the `rule` keyword, shared by
    /// `protoRule` (Theory/Text/Parser/Rule.hs:126-135) and `protoRuleAC`
    /// (Theory/Text/Parser/Rule.hs:146-154): the optional `(modulo ...)` head,
    /// the name, the attribute list and the closing colon of `protoRuleInfo` /
    /// `protoRuleACInfo` (Theory/Text/Parser/Rule.hs:100-107 / 138-143), then
    /// `option emptySubst letBlock`, the premises, the actions and embedded
    /// restrictions, the conclusions and the `apply subst` of the bindings.
    /// `variants` and `left_right` are empty; only `protoRule` has them, and
    /// [`Self::parse_rule`] fills them in.
    fn rule_after_kw(&mut self) -> Result<(Rule, Pos), ParseError> {
        let modulo = self.try_modulo();
        self.skip_ws();
        let name_start = self.save();
        let name = self.ident()?;
        let attributes = self.rule_attributes()?;
        self.require_punct(":")?;
        // Optional let block.
        let lets = if self.at_keyword("let") {
            self.let_bindings()?
        } else {
            vec![]
        };
        let mut premises = self.fact_list()?;
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
        Ok((
            Rule {
                name,
                modulo,
                attributes,
                premises,
                actions,
                conclusions,
                embedded_restrictions,
                variants: vec![],
                left_right: None,
            },
            name_start,
        ))
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
                let _ = self.read_attribute_token()?;
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
                        Some(self.read_attribute_token()?)
                    } else {
                        None
                    };
                    attrs.push(RuleAttr::External(ext, val));
                } else {
                    self.restore(save);
                    if !self.peek_punct("]") {
                        let (item, item_len) = self.diagnostic_item();
                        return Err(self.semantic_error(
                            ParseErrorKind::UnknownItem {
                                item: item.clone(),
                                context: ParseContext::RuleAttribute,
                            },
                            save,
                            item_len,
                        ));
                    }
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
    /// Kept from the previous lexer-side implementation: no whitespace is
    /// skipped after the opening quote or the `#`, so `' #FF'` / `'# FF'` are
    /// rejected here though HS's `symbol`-based parser accepts them — real
    /// colour attributes are always tight (e.g. `'#111111'`).
    fn color_attr_value(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        let quoted = self.lx.eat_str("'");
        self.lx.eat_str("#");
        let code_start = self.save();
        while let Some(c) = self.lx.peek() {
            if c.is_ascii_hexdigit() {
                self.lx.bump();
            } else {
                break;
            }
        }
        let code_len = self.lx.pos().offset - code_start.offset;
        if code_len == 0 {
            return Err(self.err_expect("hexadecimal digit"));
        }
        if quoted && !self.lx.eat_str("'") {
            return Err(self.err_expect("closing single quote"));
        }
        self.skip_ws();
        if code_len != 6 {
            return Err(self.semantic_error(
                ParseErrorKind::MalformedHexColor {
                    reason: format!("expected exactly 6 hexadecimal digits, found {code_len}"),
                },
                code_start,
                code_len,
            ));
        }
        Ok(self.lx.src()[code_start.offset..code_start.offset + code_len].to_owned())
    }

    fn single_quoted(&mut self, expected: &str) -> Result<String, ParseError> {
        let result = self.lx.single_quoted().map_err(|position| {
            ParseError::expected(
                position,
                expected,
                self.lx.src()[position.offset..].chars().next(),
            )
        });
        // Publish consumed comments before enclosing alternatives rewind.
        self.lx.finish(result)
    }

    fn string_literal_or_squoted(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        if self.lx.peek() == Some('"') {
            self.string_literal()
        } else {
            self.single_quoted("a valid single-quoted string")
        }
    }

    /// Read an identifier or a single-level delimited attribute value.
    fn read_attribute_token(&mut self) -> Result<String, ParseError> {
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
                    let opening = self.save();
                    self.lx.bump();
                    let start = self.save().offset;
                    while self.lx.peek().is_some_and(|ch| ch != *l && ch != *r) {
                        self.lx.bump();
                    }
                    let end = self.save().offset;
                    if !self.lx.eat(*r) {
                        let error = self.err_expect_here(format!("{r:?}"));
                        return Err(if self.lx.is_eof() {
                            error.with_kind(ParseErrorKind::UnclosedDelimiter {
                                opening: *l,
                                opening_span: opening.offset..opening.offset + 1,
                                closing: *r,
                            })
                        } else {
                            error
                        });
                    }
                    self.skip_ws();
                    return Ok(self.lx.src()[start..end].to_owned());
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
            return Err(self.err_expect("identifier, \"%\""));
        }

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
            return Err(self.err_expect("identifier, \"%\""));
        }
        self.require_kw("in")?;
        Ok(bs)
    }

    fn fact_list(&mut self) -> Result<Vec<Fact>, ParseError> {
        self.skip_ws();
        let opening = self.save();
        self.require_punct("[")?;
        // HS `list (fact ...)` (Theory/Text/Parser/Rule.hs:205-213, see line
        // 207,212) = `brackets . commaSep`
        // (Token.hs:362-363) with `commaSep = sepEndBy comma`: the list may
        // be empty and a trailing comma before `]` is OK.
        self.sep_end_by(opening, "]", |p| p.fact())
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
        self.skip_ws();
        let name_start = self.save();
        let name = self.ident()?;
        let name_len = name.len();
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
            self.skip_ws();
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
        if self.is_diff {
            let left = attrs.contains(&LemmaAttr::Left);
            let right = attrs.contains(&LemmaAttr::Right);
            let duplicate = if left {
                self.state.seen_diff_left_lemma_names.contains(&name)
            } else if right {
                self.state.seen_diff_right_lemma_names.contains(&name)
            } else {
                self.state.seen_diff_right_lemma_names.contains(&name)
                    || self.state.seen_diff_left_lemma_names.contains(&name)
            };
            if duplicate {
                let namespace = if left {
                    "left lemma"
                } else if right || self.state.seen_diff_right_lemma_names.contains(&name) {
                    "right lemma"
                } else {
                    "left lemma"
                };
                let site = self.named_sites.get(&(namespace, name.clone())).cloned();
                let error = self.duplicate_declaration(
                    "lemma",
                    name,
                    ParseContext::Lemma,
                    name_start,
                    name_len,
                );
                return Err(match site {
                    Some(span) => error.with_related_span(span, "first declaration is here"),
                    None => error,
                });
            }
            if left {
                self.state.seen_diff_left_lemma_names.push(name.clone());
            } else if right {
                self.state.seen_diff_right_lemma_names.push(name.clone());
            } else {
                self.state.seen_diff_right_lemma_names.push(name.clone());
                self.state.seen_diff_left_lemma_names.push(name.clone());
            }

            for (namespace, active) in [("left lemma", left || !right), ("right lemma", !left)] {
                if active {
                    self.named_sites
                        .entry((namespace, name.clone()))
                        .or_insert(name_start.offset..name_start.offset + name_len);
                }
            }
        } else {
            if self.state.seen_lemma_names.iter().any(|n| n == &name) {
                return Err(self.duplicate_declaration(
                    "lemma",
                    name,
                    ParseContext::Lemma,
                    name_start,
                    name_len,
                ));
            }
            self.state.seen_lemma_names.push(name.clone());
            self.named_sites
                .entry(("lemma", name.clone()))
                .or_insert(name_start.offset..name_start.offset + name_len);
        }
        Ok(TheoryItem::Lemma(Lemma {
            name,
            source_file: self
                .source_file
                .as_ref()
                .map(|path| path.to_string_lossy().into_owned()),
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
            source_file: self
                .source_file
                .as_ref()
                .map(|path| path.to_string_lossy().into_owned()),
            attributes: attrs.to_vec(),
            formula,
            case_test_idents: idents,
        }))
    }

    fn diff_lemma_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("diffLemma")?;
        self.skip_ws();
        let name_start = self.save();
        let name = self.ident()?;
        let name_len = name.len();
        let attributes = self.lemma_attributes()?;
        self.require_punct(":")?;
        let proof = self.try_diff_proof_skeleton()?;
        if self.state.seen_diff_lemma_names.contains(&name) {
            return Err(self.duplicate_declaration(
                "Diff Lemma",
                name,
                ParseContext::Lemma,
                name_start,
                name_len,
            ));
        }
        self.state.seen_diff_lemma_names.push(name.clone());
        self.named_sites
            .entry(("Diff Lemma", name.clone()))
            .or_insert(name_start.offset..name_start.offset + name_len);
        Ok(TheoryItem::DiffLemma(DiffLemma {
            name,
            source_file: self
                .source_file
                .as_ref()
                .map(|path| path.to_string_lossy().into_owned()),
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
            let attribute_start = self.save();
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
                self.skip_ws();
                let opening = self.save();
                self.require_punct("[")?;
                // HS `list constructorp` (Theory/Text/Parser/Lemma.hs:39-53, see
                // line 49) = `brackets . commaSep`:
                // trailing comma before `]` is permitted.
                let outs = self.sep_end_by(opening, "]", |p| p.ident())?;
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
                let token_len = raw
                    .char_indices()
                    .take_while(|(_, c)| is_ident_char(*c) || *c == '-')
                    .map(|(offset, c)| offset + c.len_utf8())
                    .last()
                    .unwrap_or_else(|| raw.chars().next().map_or(0, char::len_utf8));
                let item = diagnostic_lexeme(&raw[..token_len]);
                return Err(self.semantic_error(
                    ParseErrorKind::UnknownItem {
                        item,
                        context: ParseContext::LemmaAttribute,
                    },
                    attribute_start,
                    token_len,
                ));
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
            Some(id) => proof_starters.contains(&id),
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
        let tree = parse_proof_tree(&raw, self)
            .map_err(|error| error.shifted(proof_start, self.lx.src()))?;
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
            .is_some_and(|id| starters.contains(&id));
        if !starts {
            self.restore(save);
            return Ok(None);
        }
        let proof_start = self.lx.pos();
        let raw = self.read_until_next_top_level();
        validate_diff_proof_tree(&raw, self)
            .map_err(|error| error.shifted(proof_start, self.lx.src()))?;
        Ok(Some(ProofSkeleton { raw, tree: None }))
    }

    /// Peek a possibly-hyphenated identifier without consuming.
    fn peek_hyphen_identifier(&mut self) -> Option<&'a str> {
        let save = self.save();
        self.lx.skip_ws();
        let start = self.lx.pos().offset;
        match self.lx.peek() {
            Some(c) if c.is_alphabetic() => {
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
                    self.lx.bump();
                }
                _ if self.at_hyphen_join() => {
                    self.lx.bump();
                }
                _ => break,
            }
        }
        let end = self.lx.pos().offset;
        self.restore(save);
        Some(&self.lx.src()[start..end])
    }

    /// Describe the next token for a semantic diagnostic while retaining its
    /// actual source width.
    fn diagnostic_item(&mut self) -> (String, usize) {
        if let Some(item) = self.peek_hyphen_identifier() {
            let len = item.len();
            return (diagnostic_lexeme(item), len);
        }
        self.skip_ws();
        match self.lx.peek() {
            Some(c) => (c.to_string(), c.len_utf8()),
            None => (String::new(), 0),
        }
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
        self.skip_ws();
        let opening = self.save();
        let vars = if self.try_punct("(") {
            // HS `parens $ commaSep sapicvar` (Theory/Text/Parser/Sapic.hs:64-72,
            // see line 69): trailing comma OK.
            // `sapicvar`, so a `:` here types the parameter (see
            // [`Parser::sapic_var_types`]).
            let r = self.with_sapic_var_types(|p| p.sep_end_by(opening, ")", |p| p.var_spec()));
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
            self.state.enable_diff = true;
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
        let opening = self.save();
        let body = self
            .lx
            .export_body()
            .map_err(|failure| self.quoted_error(opening, failure, "a valid export body string"))?;
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
        self.in_context(ParseContext::Process, |parser| {
            parser.with_sapic_var_types(|parser| parser.process_body())
        })
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
            self.skip_ws();
            let opening = self.save();
            let args = if self.try_punct("(") {
                // HS `parens $ commaSep (msetterm ...)`
                // (Theory/Text/Parser/Sapic.hs:224-312, see line 296):
                // trailing comma before `)` is permitted.
                self.sep_end_by(opening, ")", |p| p.term(false))?
            } else {
                vec![]
            };
            return Ok(Process::Call { name: id, args });
        }
        self.restore(save2);
        Err(self.err_expect_here("process"))
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
        self.fact_located().map(|(fact, _)| fact)
    }

    fn fact_located(&mut self) -> Result<(Fact, Pos), ParseError> {
        self.skip_ws();
        let persistent = self.try_punct("!");
        let name_start = self.save();
        let name = self.ident()?;
        if !name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            self.skip_ws();
            let len = name.len();
            return Err(self.semantic_error(
                ParseErrorKind::InvalidFactName { name },
                name_start,
                len,
            ));
        }
        self.skip_ws();
        let opening = self.save();
        self.require_punct("(")?;
        // HS `parens (commaSep pterm)` (Theory/Text/Parser/Fact.hs:39-63, see
        // line 47): trailing comma OK.
        let args = self.sep_end_by(opening, ")", |p| p.term(false))?;
        let mut annotations = Vec::new();
        self.skip_ws();
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
        // (canonical name, persistent, keep-annotations)
        let canonical = [
            ("Out", false, false),
            ("In", false, true),
            ("KU", true, false),
            ("KD", true, false),
            ("Ded", false, false),
            ("Fr", false, false),
        ]
        .into_iter()
        .find(|(canonical, _, _)| name.eq_ignore_ascii_case(canonical));
        if let Some((cname, cpersistent, keep_ann)) = canonical {
            // `!Fr(...)` is a parse error (Theory/Text/Parser/Fact.hs:39-63, see
            // line 45).
            if cname == "Fr" && persistent {
                return Err(self.semantic_error(
                    ParseErrorKind::PersistentFreshFact,
                    name_start,
                    name.len(),
                ));
            }
            // `singleTerm`: special facts have arity one
            // (Theory/Text/Parser/Fact.hs:52-54).
            if args.len() != 1 {
                let diagnostic_name = diagnostic_lexeme(&name);
                return Err(self.semantic_error(
                    ParseErrorKind::FactArity {
                        name: diagnostic_name,
                        arity: args.len(),
                    },
                    name_start,
                    name.len(),
                ));
            }
            return Ok((
                Fact {
                    persistent: cpersistent,
                    name: cname.to_string(),
                    args,
                    annotations: if keep_ann { annotations } else { Vec::new() },
                },
                name_start,
            ));
        }
        Ok((
            Fact {
                persistent,
                name,
                args,
                annotations,
            },
            name_start,
        ))
    }

    // =========================================================================
    // Formulas
    // =========================================================================

    fn formula(&mut self) -> Result<Formula, ParseError> {
        self.in_context(ParseContext::Formula, Self::iff)
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

    /// Accept a node/bare variable or a bare identifier resolved as a nullary symbol.
    fn node_operand(t: Term, explicit_sort: bool) -> Option<Term> {
        match t {
            Term::Var(v) if v.sort == LSort::Node || (v.sort == LSort::Msg && !explicit_sort) => {
                Some(Self::node_sorted(Term::Var(v)))
            }
            Term::App(_, ref args) if args.is_empty() => Some(Self::node_sorted(t)),
            _ => None,
        }
    }

    /// A successful predicate/group cannot be used as a term operand. Only
    /// an actual term or relation operator makes the failed relational parse
    /// relevant; a closer, comment or unrelated token keeps its own error.
    fn at_term_continuation(&mut self) -> bool {
        let lexer = self.lx.clone();
        self.skip_ws();
        let rest = self.lx.rest();
        let relation = rest.starts_with("<<")
            || rest.starts_with('⊏')
            || rest.starts_with("(<)")
            || rest
                .strip_prefix('=')
                .is_some_and(|r| !r.starts_with(['=', '>']))
            || rest
                .strip_prefix('<')
                .is_some_and(|r| !r.starts_with(['=', '-']));
        let continuation = relation
            || [
                (self.state.sig_enable_dh, BinOp::Exp),
                (self.state.sig_enable_dh, BinOp::Mult),
                (self.state.sig_enable_mset, BinOp::Union),
                (self.state.sig_enable_xor, BinOp::Xor),
                (self.state.sig_enable_nat, BinOp::NatPlus),
            ]
            .into_iter()
            .any(|(enabled, op)| enabled && self.try_term_operator(op).is_some())
            || {
                let symbols = self.state.ac_fun_syms.clone();
                symbols.iter().any(|name| self.try_kw(name))
            };
        self.lx = lexer;
        continuation
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
        // Try a complete atom before grouping a formula. A grouped term can
        // continue through any of the term grammar's operators before reaching
        // its relation, so inspecting just the next operator is insufficient.
        let start = self.lx.clone();
        let atom = self.formula_atom();
        // Capture lexer diagnostics as well as grammar errors before restoring.
        let atom_error = match self.lx.finish(atom) {
            Ok(formula) => return Ok(formula),
            Err(error) => error,
        };
        self.lx = start;
        if self.try_punct("(") {
            let formula = match self.iff() {
                Ok(formula) => formula,
                Err(error) => return Err(Self::select_alt_error(atom_error, error)),
            };
            // Prefer the formula's closer on ties. A relational parse that
            // progressed further can still explain a truncated formula prefix
            // (for example, `F` parsed as false before an application).
            if let Err(error) = self.require_punct(")") {
                return Err(Self::select_alt_error(error, atom_error));
            }
            if self.at_term_continuation() {
                return Err(atom_error);
            }
            return Ok(formula);
        }
        Err(atom_error)
    }

    fn formula_atom(&mut self) -> Result<Formula, ParseError> {
        // Atom: try last(t), action f@t, equality, less, subterm, smaller, predicate
        if self.try_kw("last") {
            self.require_punct("(")?;
            let t = self.term(false)?;
            self.require_punct(")")?;
            return Ok(Formula::Atom(Atom::Last(Self::node_sorted(t))));
        }
        // An action commits after @. A bare fact remains a candidate until
        // the complete relational-term alternative has been tried.
        let start = self.lx.clone();
        let fact = match self.fact() {
            Ok(fact) if self.try_punct("@") => {
                let node = self.term(false)?;
                return Ok(Formula::Atom(Atom::Action(fact, Self::node_sorted(node))));
            }
            result => result,
        };
        let fact_end = self.lx.clone();
        self.lx = start;
        let relation = self.relational_atom();
        let term_error = match self.lx.finish(relation) {
            Ok(formula) => return Ok(formula),
            Err(error) => error,
        };
        self.lx = fact_end;
        match fact {
            Ok(_) if self.at_term_continuation() => Err(term_error),
            Ok(fact) => Ok(Formula::Atom(Atom::Pred(fact))),
            // On ties, an application error is more useful than a rejected
            // lowercase fact head. Deeper fact errors still retain their cause.
            Err(fact_error) => Err(Self::select_alt_error(term_error, fact_error)),
        }
    }

    fn relational_atom(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.term(false)?;
        let lhs_explicit_sort = self.sort_suffix_consumed;
        if self.try_punct("=") {
            let rhs = self.term(false)?;
            let rhs_explicit_sort = self.sort_suffix_consumed;
            // `blatom`'s "term equality" alternative reads both operands with
            // `msgvar`, which rejects a node variable, so an equality whose
            // left operand is one is the LAST alternative, "node equality"
            // (Theory/Text/Parser/Formula.hs:51,56): `nodevarTerm` on both
            // sides, which reads a bare right operand as a timepoint.
            if matches!(&lhs, Term::Var(v) if v.sort == LSort::Node) {
                let rhs = Self::node_operand(rhs, rhs_explicit_sort)
                    .ok_or_else(|| self.err("expected node variable after `=`"))?;
                return Ok(Formula::Atom(Atom::Eq(lhs, rhs)));
            }
            if matches!(&rhs, Term::Var(v) if v.sort == LSort::Node) {
                return Err(self.err("expected message term after `=`"));
            }
            return Ok(Formula::Atom(Atom::Eq(lhs, rhs)));
        }
        if self.try_punct("<<") || self.try_punct("⊏") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Subterm(lhs, rhs)));
        }
        if self.try_punct("(<)") {
            if !self.state.sig_enable_mset {
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
            let rhs_explicit_sort = self.sort_suffix_consumed;
            let lhs = Self::node_operand(lhs, lhs_explicit_sort)
                .ok_or_else(|| self.err("expected node variable before `<`"))?;
            let rhs = Self::node_operand(rhs, rhs_explicit_sort)
                .ok_or_else(|| self.err("expected node variable after `<`"))?;
            return Ok(Formula::Atom(Atom::Less(lhs, rhs)));
        }
        Err(self.err_expect("term relation"))
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

    /// Shared token recognition for term parsing and ambiguous formula operands.
    /// Callers select the operator levels enabled by the current signature.
    fn try_term_operator(&mut self, op: BinOp) -> Option<BinOp> {
        self.skip_ws();
        let matched = match op {
            BinOp::Exp => self.try_punct("^"),
            BinOp::Mult => {
                // `*}` closes a formal comment, rather than multiplying.
                self.lx.peek2() != Some('}') && self.try_punct("*")
            }
            BinOp::Union => {
                // `+>` belongs to process syntax, not multiset union.
                !self.lx.rest().starts_with("+>") && (self.try_punct("++") || self.try_punct("+"))
            }
            BinOp::Xor => self.try_kw("XOR") || self.try_punct("⊕"),
            BinOp::NatPlus => self.try_punct("%+"),
            BinOp::AcFct(name) => self.try_kw(name),
        };
        matched.then_some(op)
    }

    /// HS `msetterm` (Theory/Text/Parser/Term.hs:195-200): the union level runs
    /// only under `enableMSet && not eqn`, otherwise the parser drops straight
    /// to [`Self::natterm`] and `++`/`+` are not term operators at all.
    fn msetterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let term = if !self.state.sig_enable_mset || eqn {
            self.natterm(eqn)?
        } else {
            self.chainl1(
                |p| p.natterm(eqn),
                |p| p.try_term_operator(BinOp::Union),
                Self::bin_op_term,
            )?
        };
        self.skip_ws();
        Ok(term)
    }

    /// HS `natterm` (Theory/Text/Parser/Term.hs:203-208): `%+` needs
    /// `enableNat && not eqn`.
    fn natterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.state.sig_enable_nat || eqn {
            return self.xorterm(eqn);
        }
        self.chainl1(
            |p| p.xorterm(eqn),
            |p| p.try_term_operator(BinOp::NatPlus),
            Self::bin_op_term,
        )
    }

    /// HS `xorterm` (Theory/Text/Parser/Term.hs:187-192): `XOR`/`⊕` need
    /// `enableXor && not eqn`.
    fn xorterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.state.sig_enable_xor || eqn {
            return self.multterm(eqn);
        }
        self.chainl1(
            |p| p.multterm(eqn),
            |p| p.try_term_operator(BinOp::Xor),
            Self::bin_op_term,
        )
    }

    /// HS `multterm` (Theory/Text/Parser/Term.hs:179-185): without
    /// `enableDH && not eqn` the parser skips BOTH this level and
    /// [`Self::expterm`], so neither `*` nor `^` is a term operator.
    fn multterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if !self.state.sig_enable_dh || eqn {
            return self.acterm(eqn);
        }
        self.chainl1(
            |p| p.expterm(eqn),
            |p| p.try_term_operator(BinOp::Mult),
            Self::bin_op_term,
        )
    }

    /// HS `expterm` is "a left-associative sequence of exponentiations"
    /// (`chainl1`, Parser/Term.hs:174-176).
    fn expterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.chainl1(
            |p| p.acterm(eqn),
            |p| p.try_term_operator(BinOp::Exp),
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
        self.skip_ws();
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
        if level >= self.state.ac_fun_syms.len() {
            return self.atom_term(eqn);
        }
        let symbols = Arc::clone(&self.state.ac_fun_syms);
        let op = &symbols[level];
        self.chainl1(
            |p| p.ac_chain(level + 1, eqn),
            // HS `opAC (op, _) = symbol_ (BC.unpack op)`, i.e. the symbol's own
            // name as a plain token.  `try_kw` adds a word boundary that HS's
            // `symbol` lacks, so HS would also accept the name as a PREFIX of
            // the following token (`f(x) fg(y)` parsing as `f(f(x), g(y))` for
            // an AC symbol `f`); such input is not valid syntax in any theory
            // and errors here instead.
            |p| {
                p.try_kw(op)
                    .then(|| BinOp::AcFct(tamarin_term::intern::intern_str(op)))
            },
            Self::bin_op_term,
        )
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
            if best.is_none_or(|b: FunOptions| o.ord_key() < b.ord_key()) {
                best = Some(o);
            }
        };
        for (n, o) in self.state.fun_syms.iter() {
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
        if self.state.ac_fun_syms.iter().any(|n| n == op) {
            return Some(ArityRes::Ac);
        }
        if let Some((_, o)) = self.state.macro_syms.iter().find(|(n, _)| n == op) {
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
        self.state
            .fun_syms
            .iter()
            .chain(self.state.macro_syms.iter())
            .any(|(n, o)| n == name && o.arity == 0)
            || self
                .enabled_theory_noeq_syms()
                .any(|s| s.name == name.as_bytes() && s.arity == 0)
    }

    /// The theory-level `NoEq` symbols the enabled signature bits fold into
    /// `funSyms` — see [`TheoryNoEqSyms`].
    fn enabled_theory_noeq_syms(&self) -> impl Iterator<Item = &'static NoEqSym> + use<> {
        let syms = theory_noeq_syms();
        [
            (self.state.sig_enable_dh, &syms.dh),
            (self.state.sig_enable_bp, &syms.bp),
            (self.state.sig_enable_xor, &syms.xor),
            (self.state.sig_enable_nat, &syms.nat),
        ]
        .into_iter()
        .filter(|(enabled, _)| *enabled)
        .flat_map(|(_, syms)| syms.iter())
    }

    /// One atomic term.
    fn atom_term(&mut self, eqn: bool) -> Result<Term, ParseError> {
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
                let inner = self.pattern_var_atom()?;
                return Ok(Term::PatMatch(Box::new(inner)));
            }
        }
        // Parens for grouping
        if self.try_punct("(") {
            let t = self.msetterm(eqn)?;
            if !self.try_punct(")") {
                return Err(self.err_expect("\")\""));
            }

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
                if !self.try_punct(">") {
                    return Err(self.err_expect("\",\", \">\""));
                }

                return Ok(t);
            }
        }
        // Special tokens
        if self.lx.try_symbol("DH_neutral") {
            return Ok(Term::DhNeutral);
        }
        let literal_start = self.save();
        if self.lx.try_symbol("1:nat") {
            if !self.state.sig_enable_nat {
                return Err(self
                    .err("natural-number literal 1:nat requires the natural-numbers builtin")
                    .with_location(literal_start, 5));
            }
            return Ok(Term::NatOne);
        }
        if self.lx.try_symbol("%1") {
            if !self.state.sig_enable_nat {
                return Err(self
                    .err("natural-number literal %1 requires the natural-numbers builtin")
                    .with_location(literal_start, 2));
            }
            return Ok(Term::NatOne);
        }
        // Fixed literals use the identifier boundary of upstream's
        // `reserved`, so `1abc` remains one identifier rather than `1` plus
        // trailing garbage.
        if self.lx.try_symbol("1") {
            return Ok(Term::NumberOne);
        }
        // Sigil-prefixed variables: ~x, $x, #x, %x.
        if let Some(c @ ('~' | '$' | '#')) = self.lx.peek() {
            // Could be a fresh-name literal `~'n'` or `%'n'` — handled below.
            let mut probe = self.lx.clone();
            probe.bump();
            if c == '~' && probe.peek() == Some('\'') {
                self.lx.bump();
                let s = self.single_quoted("a valid fresh literal")?;
                return Ok(Term::FreshLit(s));
            }
            // Otherwise: variable.
            if let Some(v) = self.try_var_spec()? {
                let v = self.attach_sort_suffix(v)?;
                return Ok(Term::Var(v));
            }
        }
        if self.lx.peek() == Some('%') {
            // Exact `%1` was handled above; quoted names are literals and all
            // other forms use the shared variable parser (including `%12`).
            if self.lx.rest().starts_with("%'") {
                self.lx.bump();
                if !self.state.sig_enable_nat {
                    return Err(self
                        .err("nat names requires the natural-numbers builtin")
                        .with_location(literal_start, 1));
                }
                let s = self.single_quoted("a valid natural-number literal")?;
                return Ok(Term::NatLit(s));
            }
            if let Some(v) = self.try_var_spec()? {
                let v = self.attach_sort_suffix(v)?;
                return Ok(Term::Var(v));
            }
        }
        // Literal `'foo'` is a public name term.
        if self.lx.peek() == Some('\'') {
            let s = self.single_quoted("a valid public literal")?;
            return Ok(Term::PubLit(s));
        }
        // diff(a, b) — HS `diffOp = symbol "diff" *> parens ...`
        // (Theory/Text/Parser/Term.hs:123-135, see line 125).
        // `diff` is a reserved name (Token.hs:214-230, see line 225) so it is NOT an identifier and
        // must be matched as a keyword here, BEFORE the identifier path. The
        // word-boundary check in `peek_symbol` keeps `diffuse(...)` an identifier
        // (function application), matching HS where `naryOpApp` handles it.
        let diff_start = self.save();
        if self.try_kw("diff") {
            let opening = self.save();
            self.require_punct("(")?;
            let ts = self.sep_end_by(opening, ")", |p| p.msetterm(eqn))?;
            // Preserve validation order: arity, equation context, then diff mode.
            if ts.len() != 2 {
                return Err(self.semantic_error(
                    ParseErrorKind::WrongFunctionArity {
                        name: "diff".into(),
                        declared: 2,
                        used: ts.len(),
                    },
                    diff_start,
                    "diff".len(),
                ));
            }
            if eqn {
                return Err(self.semantic_error(
                    ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::InEquation),
                    diff_start,
                    "diff".len(),
                ));
            }
            if !self.state.enable_diff {
                return Err(self.semantic_error(
                    ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::DiffModeDisabled),
                    diff_start,
                    "diff".len(),
                ));
            }
            let mut args = ts.into_iter();
            let a = args.next().unwrap();
            let b = args.next().unwrap();
            return Ok(Term::Diff(Box::new(a), Box::new(b)));
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
            // error propagates directly out of the equation parser.
            if eqn && Self::RESERVED_BUILTINS.contains(&id.as_str()) {
                let diagnostic_name = diagnostic_lexeme(&id);
                return Err(self.semantic_error(
                    ParseErrorKind::ReservedBuiltin {
                        name: diagnostic_name,
                        context: ParseContext::Term,
                    },
                    save_id,
                    id.len(),
                ));
            }

            self.skip_ws();
            let opening = match self.lx.peek() {
                // `(<)` belongs to the enclosing multiset comparison, not an application.
                Some('(') if !self.lx.rest().starts_with("(<)") => '(',
                Some('{') => '{',
                _ => return self.bare_ident_term(id),
            };
            if self.resolve_prefix_apps {
                let res = self.lookup_arity(&id).ok_or_else(|| {
                    self.semantic_error(
                        ParseErrorKind::UndeclaredFunction {
                            name: diagnostic_lexeme(&id),
                        },
                        save_id,
                        id.len(),
                    )
                })?;
                return if opening == '(' {
                    self.prefix_app_args(id, res, eqn, save_id)
                } else {
                    self.binary_alg_app(id, res, eqn, save_id)
                };
            }
            // Structural mode leaves resolution to the caller. Its prefix
            // argument list is strictly comma-separated (no trailing comma).
            self.lx.bump();
            self.skip_ws();
            if opening == '(' {
                let mut ts = Vec::new();
                if !self.try_punct(")") {
                    loop {
                        ts.push(self.msetterm(eqn)?);
                        if !self.try_punct(",") {
                            break;
                        }
                    }
                    self.require_punct(")")?;
                }
                return Ok(Term::App(id, ts));
            }
            let arg1 = self.tuple_contents(eqn)?;
            self.require_punct("}")?;
            let arg2 = self.atom_term(eqn)?;
            return Ok(Term::AlgApp(id, Box::new(arg1), Box::new(arg2)));
        }
        self.restore(save_id);
        Err(self.err_expect("term").with_context(ParseContext::Term))
    }

    /// The term a BARE identifier (no sigil) denotes once its optional
    /// `.<index>` and `:sort` / `:type` suffix are read.
    ///
    /// HS's `term` tries `nullaryApp` ahead of the literal parser
    /// (Theory/Text/Parser/Term.hs:139-153,158-163): an identifier that is an
    /// arity-0 symbol of `funSyms maudeSig ∪ macroNames maudeSig` is the
    /// application `fApp fs []`, whatever a same-named binder is in scope.
    /// Current upstream reads a complete identifier before resolving a
    /// nullary symbol, so a symbol named `c` cannot accidentally claim the
    /// prefix of `cx`. Dot indices and type/sort suffixes are not identifier
    /// characters, however: a declared `c/0` claims the `c` in `c.1` or
    /// `c:msg`, leaving the suffix for the enclosing parser to reject.
    fn bare_ident_term(&mut self, id: String) -> Result<Term, ParseError> {
        if self.is_nullary_sym(&id) {
            return Ok(Term::App(id, Vec::new()));
        }
        let idx = self.try_dot_index();
        let v = VarSpec {
            name: id,
            idx,
            sort: LSort::Msg,
            typ: None,
        };
        let v = self.attach_sort_suffix(v)?;
        Ok(Term::Var(v))
    }

    /// The variable after a pattern `=` — HS `sapicvar` via `sapicpatternvar`
    /// (Token.hs:506-519): a sorted variable with an optional `.idx` index and
    /// `:type` annotation, never an application, literal, or compound term.
    fn pattern_var_atom(&mut self) -> Result<Term, ParseError> {
        if let Some(v) = self.try_var_spec()? {
            let v = self.attach_sort_suffix(v)?;
            return Ok(Term::Var(v));
        }
        Err(self.err_expect("pattern variable"))
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
    /// Failures are returned directly so diagnostics identify the malformed
    /// application rather than a later token after Haskell-style backtracking.
    fn prefix_app_args(
        &mut self,
        id: String,
        res: ArityRes,
        eqn: bool,
        head: Pos,
    ) -> Result<Term, ParseError> {
        let opening = self.save();
        self.lx.bump(); // the '(' the caller peeked
        self.skip_ws();
        match res {
            ArityRes::NoEq {
                opts: FunOptions { arity: 1, .. },
            } => {
                let arg = self.tuple_contents(eqn)?;
                self.require_punct(")")?;
                Ok(Term::App(id, vec![arg]))
            }
            ArityRes::NoEq { opts } => {
                let arity = opts.arity;
                let ts = self.sep_end_by(opening, ")", |p| p.msetterm(eqn))?;
                if ts.len() != arity {
                    let diagnostic_name = diagnostic_lexeme(&id);
                    return Err(self.semantic_error(
                        ParseErrorKind::WrongFunctionArity {
                            name: diagnostic_name,
                            declared: arity,
                            used: ts.len(),
                        },
                        head,
                        id.len(),
                    ));
                }
                if res.is_dh_exp(&id) {
                    let mut it = ts.into_iter();
                    let a = it.next().expect("arity 2 checked above");
                    let b = it.next().expect("arity 2 checked above");
                    return Ok(Term::BinOp(BinOp::Exp, Box::new(a), Box::new(b)));
                }
                Ok(Term::App(id, ts))
            }
            ArityRes::Ac => {
                let ts = self.sep_end_by(opening, ")", |p| p.msetterm(eqn))?;
                Ok(Self::ac_prefix_app(id, ts))
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
    fn ac_prefix_app(id: String, ts: Vec<Term>) -> Term {
        let sym = tamarin_term::intern::intern_str(&id);
        let mut it = ts.into_iter();
        match (it.next(), it.next()) {
            (None, _) => Term::App(id, Vec::new()),
            (Some(a), None) => a,
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
    /// then a trailing atom (`term eqn plit`), requires arity 2, and builds
    /// `fAppNoEq`/`fAppAC` by the head's AC state.  There is no `em` special
    /// case here (`naryOpApp`'s Theory/Text/Parser/Term.hs:103 is prefix-only).
    fn binary_alg_app(
        &mut self,
        id: String,
        res: ArityRes,
        eqn: bool,
        head: Pos,
    ) -> Result<Term, ParseError> {
        self.lx.bump(); // the '{' the caller peeked
        self.skip_ws();
        let arg1 = self.tuple_contents(eqn)?;
        self.require_punct("}")?;
        let arg2 = self.atom_term(eqn)?;
        match res {
            ArityRes::Ac => Ok(Term::BinOp(
                BinOp::AcFct(tamarin_term::intern::intern_str(&id)),
                Box::new(arg1),
                Box::new(arg2),
            )),
            ArityRes::NoEq {
                opts: FunOptions { arity: 2, .. },
            } => {
                if res.is_dh_exp(&id) {
                    return Ok(Term::BinOp(BinOp::Exp, Box::new(arg1), Box::new(arg2)));
                }
                Ok(Term::AlgApp(id, Box::new(arg1), Box::new(arg2)))
            }
            ArityRes::NoEq { opts } => {
                let diagnostic_name = diagnostic_lexeme(&id);
                Err(self.semantic_error(
                    ParseErrorKind::WrongFunctionArity {
                        name: diagnostic_name,
                        declared: opts.arity,
                        used: 2,
                    },
                    head,
                    id.len(),
                ))
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
            // lvarNoSuffix` plus an optional type (Token.hs).
            // `lvarNoSuffix` (Token.hs:502-503) is `sortedLVarNoSuffix
            // [minBound..]` (Token.hs:486-501), which offers PREFIX sorts only, so a
            // colon there always introduces a SAPIC TYPE — `x:nat` is the
            // msg-sorted `x` typed `"nat"`, not a nat-sorted variable — and
            // `typep`'s `Any` is the untyped placeholder (Token.hs:472-473).
            if self.sapic_var_types {
                match self.type_p_element() {
                    Some(t) => v.typ = t,
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
                    if sort == LSort::Nat && !self.state.sig_enable_nat {
                        return Err(self
                            .err("nat-sorted variables requires the natural-numbers builtin")
                            .with_location(snap, kw.len()));
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
        if self.sapic_var_types && v.sort == LSort::Node {
            v.typ = Some("node".to_string());
        }
        Ok(v)
    }

    /// Parse a variable specification. Returns None if no var sigil/identifier
    /// is present.
    fn try_var_spec(&mut self) -> Result<Option<VarSpec>, ParseError> {
        Ok(self.try_var_spec_spanned()?.map(|(variable, _)| variable))
    }

    fn try_var_spec_spanned(&mut self) -> Result<Option<(VarSpec, Pos)>, ParseError> {
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
                // An exact `%1` has already been consumed as nat one. A leading
                // quote is a nat literal; every alphanumeric start, including
                // `%12`, begins a nat-sorted variable upstream.
                let mut probe = self.lx.clone();
                probe.bump();
                match probe.peek() {
                    Some('\'') => return Ok(None), // handled by the literal/atom path
                    Some(c) if c.is_alphanumeric() => {
                        if !self.state.sig_enable_nat {
                            self.lx.bump();
                            return Err(self
                                .err("nat-sorted variables requires the natural-numbers builtin")
                                .with_location(save, 1));
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
        let (id, name_start) = match self.lx.identifier_spanned() {
            Some(result) => result,
            None => {
                self.restore(save);
                return Ok(None);
            }
        };

        let idx = self.try_dot_index();
        Ok(Some((
            VarSpec {
                name: id,
                idx,
                sort,
                typ: None,
            },
            name_start,
        )))
    }

    fn var_spec(&mut self) -> Result<VarSpec, ParseError> {
        self.var_spec_spanned().map(|(variable, _)| variable)
    }

    fn var_spec_spanned(&mut self) -> Result<(VarSpec, Pos), ParseError> {
        let (variable, position) = self
            .try_var_spec_spanned()?
            .ok_or_else(|| self.err_expect_here("variable"))?;
        // Allow `: msg | pub | fresh | node | nat` sort suffix or a SAPIC
        // type annotation after the variable.
        self.attach_sort_suffix(variable)
            .map(|variable| (variable, position))
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
                Some(n) => n,
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

    #[allow(clippy::disallowed_types)]
    fn flag_disjuncts(&mut self, flags: &HashSet<String>) -> Result<bool, ParseError> {
        self.chainl1(
            |p| p.flag_conjuncts(flags),
            |p| (p.try_punct("|") || p.try_punct("∨")).then_some(()),
            |(), lhs, rhs| lhs || rhs,
        )
    }

    #[allow(clippy::disallowed_types)]
    fn flag_conjuncts(&mut self, flags: &HashSet<String>) -> Result<bool, ParseError> {
        self.chainl1(
            |p| p.flag_negation(flags),
            |p| (p.try_punct("&") || p.try_punct("∧")).then_some(()),
            |(), lhs, rhs| lhs && rhs,
        )
    }

    #[allow(clippy::disallowed_types)]
    fn flag_negation(&mut self, flags: &HashSet<String>) -> Result<bool, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.flag_atom(flags)?;
            Ok(!f)
        } else {
            self.flag_atom(flags)
        }
    }

    #[allow(clippy::disallowed_types)]
    fn flag_atom(&mut self, flags: &HashSet<String>) -> Result<bool, ParseError> {
        if self.try_punct("(") {
            let f = self.flag_disjuncts(flags)?;
            self.require_punct(")")?;
            return Ok(f);
        }
        let id = self.ident()?;
        Ok(flags.contains(&id))
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
    /// The first four HS alternatives backtrack over their leading operand and
    /// complete separator (including a premise index), then commit to the tail.
    /// The two fact alternatives share a head here; [`Parser::goal_after`]
    /// preserves commitment while retaining failed heads for error selection.
    /// `disjSplitGoal` backtracks on its own because HS's `plainFormula`
    /// (Theory/Text/Parser/Formula.hs:112-117) is `try`-wrapped whole, and
    /// `eqSplitGoal` is `try $ do ...`.
    ///
    /// The equation split is hoisted above the disjunction, which accepts the
    /// same language: HS reaches `eqSplitGoal` only because `disjSplitGoal`
    /// fails on `splitEqs(N)`, and the keyword form does not depend on how
    /// [`Parser::formula`] reads a lower-case predicate-shaped atom.
    fn goal(&mut self) -> Result<GoalSpec, ParseError> {
        let mut head_error = None;
        for parse in [Self::subterm_goal, Self::fact_goal, Self::chain_goal] {
            if let Some(goal) = parse(self, &mut head_error)? {
                return Ok(goal);
            }
        }
        let save = self.save();
        let error = match self.eq_split_goal() {
            Ok(goal) => return Ok(goal),
            Err(error) => error,
        };
        self.restore(save);
        let error = match head_error {
            Some(head_error) => Self::select_alt_error(head_error, error),
            None => error,
        };
        self.disj_split_goal()
            .and_then(|goal| {
                // A formula prefix is not a complete solve goal. Include the
                // enclosing closer in failure selection so an earlier head's
                // useful error survives a shorter, partial formula parse.
                if self.lx.peek_symbol(")") {
                    Ok(goal)
                } else {
                    Err(self.err_expect_here("`)` after the goal"))
                }
            })
            .map_err(|alternate| Self::select_alt_error(error, alternate))
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
    /// `try`, so failing either restores the input and retains the error for
    /// [`Self::goal`] to compare if later alternatives fail, while `tail` reads
    /// the rest outside the `try`, where a failure is the whole goal's.
    fn goal_after<H>(
        &mut self,
        head_error: &mut Option<ParseError>,
        head: impl FnOnce(&mut Self) -> Result<H, ParseError>,
        tail: impl FnOnce(&mut Self, H) -> Result<GoalSpec, ParseError>,
    ) -> Result<Option<GoalSpec>, ParseError> {
        let save = self.save();
        let result = head(self);
        match self.lx.finish(result) {
            Ok(h) => tail(self, h).map(Some),
            Err(error) => {
                self.restore(save);
                *head_error = Some(match head_error.take() {
                    Some(previous) => Self::select_alt_error(previous, error),
                    None => error,
                });
                Ok(None)
            }
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
    fn subterm_goal(
        &mut self,
        head_error: &mut Option<ParseError>,
    ) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            head_error,
            |p| {
                let t = p.msetterm(false)?;
                if !p.try_punct("<<") && !p.try_punct("\u{228F}") {
                    return Err(p.err_expect_here("`⊏`"));
                }
                Ok(t)
            },
            |p, small| Ok(GoalSpec::Subterm(small, p.msetterm(false)?)),
        )
    }

    /// HS `premiseGoal` (Theory/Text/Parser/Proof.hs:54-57) and `actionGoal`
    /// (Theory/Text/Parser/Proof.hs:49-52) share `fact llit`. Select `opRequires`
    /// (`▶` plus a subscript natural, Token.hs:618-619) or `opAt` (`@`,
    /// Token.hs:566-568) after parsing the fact once. The complete separator,
    /// including a premise index, remains under `try`; node-variable failures commit.
    fn fact_goal(
        &mut self,
        head_error: &mut Option<ParseError>,
    ) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            head_error,
            |p| {
                let fact = p.fact()?;
                p.skip_ws();
                let premise = if p.lx.eat_str("▶") {
                    Some(
                        p.lx.natural_subscript()
                            .ok_or_else(|| p.err_expect_here("a subscript premise index"))?,
                    )
                } else if p.try_punct("@") {
                    None
                } else {
                    return Err(p.err_expect_here("`▶` or `@`"));
                };
                Ok((fact, premise))
            },
            |p, (fact, premise)| {
                let node = p.nodevar()?;
                Ok(match premise {
                    Some(index) => GoalSpec::Premise((node, index), fact),
                    None => GoalSpec::Action(node, fact),
                })
            },
        )
    }

    /// HS `chainGoal` (Theory/Text/Parser/Proof.hs:59): a `nodeConc` and
    /// `opChain` (`~~>`, Token.hs:621-623) under the `try`, then a `nodePrem`.
    /// Each endpoint is `parens ((,) <$> nodevar <*> (comma *> natural))`
    /// (Theory/Text/Parser/Proof.hs:28-36).
    fn chain_goal(
        &mut self,
        head_error: &mut Option<ParseError>,
    ) -> Result<Option<GoalSpec>, ParseError> {
        self.goal_after(
            head_error,
            |p| {
                let conc = p.node_idx_pair()?;
                if !p.try_punct("~~>") {
                    return Err(p.err_expect_here("`~~>`"));
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
            .ok_or_else(|| self.err_expect_here("a node index"))?;
        self.require_punct(")")?;
        Ok((v, n))
    }

    /// HS `eqSplitGoal` (Theory/Text/Parser/Proof.hs:70-72):
    /// `symbol_ "splitEqs"` then `parens natural`.
    fn eq_split_goal(&mut self) -> Result<GoalSpec, ParseError> {
        if !self.try_kw("splitEqs") {
            return Err(self.err_expect_here("`splitEqs`"));
        }
        self.require_punct("(")?;
        let n = self
            .lx
            .natural()
            .ok_or_else(|| self.err_expect_here("a split id"))?;
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
    // Search from zero so an existing u64::MAX index cannot pin the search.
    // A finite in-memory list cannot occupy every u64 index.
    fresh.idx = 0;
    // Rule-formula elaboration erases type annotations from variable identity.
    while used
        .iter()
        .any(|v| v.name == fresh.name && v.sort == fresh.sort && v.idx == fresh.idx)
    {
        fresh.idx += 1;
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
    let result = (|| {
        let f = p.formula()?;
        p.skip_ws();
        if !p.lx.is_eof() {
            return Err(p
                .err_expect_here("end of formula")
                .with_context(ParseContext::Formula));
        }
        Ok(f)
    })();
    p.lx.finish(result)
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
    let result = (|| {
        p.require_punct("(")?;
        let g = p.goal()?;
        p.skip_ws();
        if !p.lx.eat_str(")") {
            return Err(p.err_expect_here("`)` after the goal"));
        }
        Ok((g, p.lx.pos().offset))
    })();
    p.lx.finish(result)
        .map_err(|error| error.with_context(ParseContext::Proof))
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
