// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rkunnema, charlie-j, kevinmorio, yavivanov, felixlinker,
//   BTom-GH, PhilipLukertWork, jWoc, ValentinYuri, jdreier, beschmi,
//   rsasse, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Term/Raw.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Sapic/Term.hs,
//   lib/theory/src/Theory/Text/Parser.hs,
//   lib/theory/src/Theory/Text/Parser/Accountability.hs,
//   lib/theory/src/Theory/Text/Parser/Formula.hs,
//   lib/theory/src/Theory/Text/Parser/Lemma.hs,
//   lib/theory/src/Theory/Text/Parser/Let.hs,
//   lib/theory/src/Theory/Text/Parser/Macro.hs,
//   lib/theory/src/Theory/Text/Parser/Proof.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Sapic.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Recursive-descent parser for `.spthy` files.

// flag-name set import; membership dedup only;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
use std::collections::HashSet;
use std::path::PathBuf;

use crate::ast::*;
use crate::lexer::{is_ident_char, Lexer, Pos};
use crate::proof_tree::parse_proof_tree;

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub line: u32,
    pub col: u32,
    pub start: usize,
    pub end: usize,
}

impl Location {
    pub fn location_of<S>(word: &Option<S>, pos: Pos) -> Location
    where
        S: AsRef<str>,
    {
        Location {
            line: pos.line,
            col: pos.col,
            start: pos.offset,
            end: pos.offset + word.as_ref().map_or(0, |s| s.as_ref().len()),
        }
    }
}

impl From<Pos> for Location {
    fn from(pos: Pos) -> Self {
        Location {
            line: pos.line,
            col: pos.col,
            start: pos.offset - 1,
            end: pos.offset,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ParseError {
    UnexpectedKeyword {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedTheoryItem {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedPunctuation {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedStringLiteral {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedIdentifier {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedNaturalNumber {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    UnknownPreprocessorDirective {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedPreprocessorDirective {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedHexColor {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedQuotedString {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    UnterminatedDelimiter {
        opening: String,
        opening_at: Location,
        found: Option<String>,
        found_at: Location,
        expected: Vec<String>,
    },
    UnknownRuleAttribute {
        attribute: String,
        at: Location,
    },
    UnknownLemmaAttribute {
        attribute: String,
        at: Location,
    },
    ExpectedExportBodyString {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedProcess {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    FactNameMustStartWithUppercase {
        name: String,
        at: Location,
    },
    FreshFactCannotBePersistent {
        at: Location,
    },
    FactArityMismatch {
        name: String,
        arity: usize,
        at: Location,
    },
    ExpectedFormulaAtom {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    BadFreshLiteral {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    BadNatLiteral {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    BadPublicLiteral {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedTerm {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ExpectedVariable {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    UnexpectedTrailingInput {
        context: String,
        found: String,
        at: Location,
    },
    IoError {
        path: String,
        message: String,
        at: Location,
    },
    TrailingGarbageInFormulaString {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    TrailingGarbageInTermString {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
}

#[derive(Debug, Clone)]
pub struct ParseErrorLabel {
    pub at: Location,
    pub message: String,
    pub is_primary: bool,
}

impl ParseError {
    /// Add an expected item to the error's `expected` list, if it has one.
    fn add_expected(&mut self, exp: String) {
        match self {
            ParseError::UnexpectedKeyword { expected, .. }
            | ParseError::ExpectedTheoryItem { expected, .. }
            | ParseError::ExpectedPunctuation { expected, .. }
            | ParseError::ExpectedStringLiteral { expected, .. }
            | ParseError::ExpectedIdentifier { expected, .. }
            | ParseError::ExpectedNaturalNumber { expected, .. }
            | ParseError::UnknownPreprocessorDirective { expected, .. }
            | ParseError::ExpectedPreprocessorDirective { expected, .. }
            | ParseError::ExpectedHexColor { expected, .. }
            | ParseError::ExpectedQuotedString { expected, .. }
            | ParseError::ExpectedExportBodyString { expected, .. }
            | ParseError::ExpectedProcess { expected, .. }
            | ParseError::ExpectedFormulaAtom { expected, .. }
            | ParseError::BadFreshLiteral { expected, .. }
            | ParseError::BadNatLiteral { expected, .. }
            | ParseError::BadPublicLiteral { expected, .. }
            | ParseError::ExpectedTerm { expected, .. }
            | ParseError::ExpectedVariable { expected, .. }
            | ParseError::TrailingGarbageInFormulaString { expected, .. }
            | ParseError::TrailingGarbageInTermString { expected, .. }
            | ParseError::UnterminatedDelimiter { expected, .. } => {
                if !expected.contains(&exp) {
                    expected.push(exp);
                }
            }
            // Explicity match to force compile-time error for new variants
            ParseError::UnknownLemmaAttribute { .. }
            | ParseError::FactNameMustStartWithUppercase { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::FactArityMismatch { .. }
            | ParseError::UnexpectedTrailingInput { .. }
            | ParseError::UnknownRuleAttribute { .. }
            | ParseError::IoError { .. } => {}
        }
    }

    pub fn location(&self) -> &Location {
        match self {
            ParseError::UnexpectedKeyword { at, .. }
            | ParseError::ExpectedTheoryItem { at, .. }
            | ParseError::ExpectedPunctuation { at, .. }
            | ParseError::ExpectedStringLiteral { at, .. }
            | ParseError::ExpectedIdentifier { at, .. }
            | ParseError::ExpectedNaturalNumber { at, .. }
            | ParseError::UnknownPreprocessorDirective { at, .. }
            | ParseError::ExpectedPreprocessorDirective { at, .. }
            | ParseError::ExpectedHexColor { at, .. }
            | ParseError::ExpectedQuotedString { at, .. }
            | ParseError::UnknownLemmaAttribute { at, .. }
            | ParseError::ExpectedExportBodyString { at, .. }
            | ParseError::ExpectedProcess { at, .. }
            | ParseError::FactNameMustStartWithUppercase { at, .. }
            | ParseError::FreshFactCannotBePersistent { at }
            | ParseError::FactArityMismatch { at, .. }
            | ParseError::ExpectedFormulaAtom { at, .. }
            | ParseError::BadFreshLiteral { at, .. }
            | ParseError::BadNatLiteral { at, .. }
            | ParseError::BadPublicLiteral { at, .. }
            | ParseError::ExpectedTerm { at, .. }
            | ParseError::ExpectedVariable { at, .. }
            | ParseError::UnexpectedTrailingInput { at, .. }
            | ParseError::IoError { at, .. }
            | ParseError::TrailingGarbageInFormulaString { at, .. }
            | ParseError::TrailingGarbageInTermString { at, .. }
            | ParseError::UnknownRuleAttribute { at, .. }
            | ParseError::UnterminatedDelimiter { found_at: at, .. } => at,
        }
    }

    fn into_found(self) -> Option<String> {
        match self {
            ParseError::UnexpectedKeyword { found, .. }
            | ParseError::ExpectedTheoryItem { found, .. }
            | ParseError::ExpectedPunctuation { found, .. }
            | ParseError::ExpectedStringLiteral { found, .. }
            | ParseError::ExpectedIdentifier { found, .. }
            | ParseError::ExpectedNaturalNumber { found, .. }
            | ParseError::UnknownPreprocessorDirective { found, .. }
            | ParseError::ExpectedPreprocessorDirective { found, .. }
            | ParseError::ExpectedHexColor { found, .. }
            | ParseError::ExpectedQuotedString { found, .. }
            | ParseError::ExpectedExportBodyString { found, .. }
            | ParseError::ExpectedProcess { found, .. }
            | ParseError::ExpectedFormulaAtom { found, .. }
            | ParseError::BadFreshLiteral { found, .. }
            | ParseError::BadNatLiteral { found, .. }
            | ParseError::BadPublicLiteral { found, .. }
            | ParseError::ExpectedTerm { found, .. }
            | ParseError::ExpectedVariable { found, .. }
            | ParseError::TrailingGarbageInFormulaString { found, .. }
            | ParseError::TrailingGarbageInTermString { found, .. }
            | ParseError::UnterminatedDelimiter { found, .. } => found,
            ParseError::UnknownRuleAttribute { attribute, .. }
            | ParseError::UnknownLemmaAttribute { attribute, .. } => Some(attribute),
            ParseError::FactNameMustStartWithUppercase { name, .. }
            | ParseError::FactArityMismatch { name, .. }
            | ParseError::UnexpectedTrailingInput { found: name, .. } => Some(name),
            ParseError::FreshFactCannotBePersistent { .. } | ParseError::IoError { .. } => None,
        }
    }

    pub fn found(&self) -> Option<&str> {
        match self {
            ParseError::UnexpectedKeyword { found, .. }
            | ParseError::ExpectedTheoryItem { found, .. }
            | ParseError::ExpectedPunctuation { found, .. }
            | ParseError::ExpectedStringLiteral { found, .. }
            | ParseError::ExpectedIdentifier { found, .. }
            | ParseError::ExpectedNaturalNumber { found, .. }
            | ParseError::UnknownPreprocessorDirective { found, .. }
            | ParseError::ExpectedPreprocessorDirective { found, .. }
            | ParseError::ExpectedHexColor { found, .. }
            | ParseError::ExpectedQuotedString { found, .. }
            | ParseError::ExpectedExportBodyString { found, .. }
            | ParseError::ExpectedProcess { found, .. }
            | ParseError::ExpectedFormulaAtom { found, .. }
            | ParseError::BadFreshLiteral { found, .. }
            | ParseError::BadNatLiteral { found, .. }
            | ParseError::BadPublicLiteral { found, .. }
            | ParseError::ExpectedTerm { found, .. }
            | ParseError::ExpectedVariable { found, .. }
            | ParseError::TrailingGarbageInFormulaString { found, .. }
            | ParseError::TrailingGarbageInTermString { found, .. }
            | ParseError::UnterminatedDelimiter { found, .. } => found.as_deref(),
            ParseError::UnknownRuleAttribute { attribute, .. }
            | ParseError::UnknownLemmaAttribute { attribute, .. } => Some(attribute.as_str()),
            ParseError::FactNameMustStartWithUppercase { name, .. }
            | ParseError::FactArityMismatch { name, .. } => Some(name.as_str()),
            ParseError::UnexpectedTrailingInput { found, .. } => Some(found.as_str()),
            ParseError::FreshFactCannotBePersistent { .. } | ParseError::IoError { .. } => None,
        }
    }

    pub fn expected(&self) -> Option<&[String]> {
        match self {
            ParseError::UnexpectedKeyword { expected, .. }
            | ParseError::ExpectedPunctuation { expected, .. }
            | ParseError::ExpectedStringLiteral { expected, .. }
            | ParseError::ExpectedIdentifier { expected, .. }
            | ParseError::ExpectedNaturalNumber { expected, .. }
            | ParseError::UnknownPreprocessorDirective { expected, .. }
            | ParseError::ExpectedPreprocessorDirective { expected, .. }
            | ParseError::ExpectedHexColor { expected, .. }
            | ParseError::ExpectedQuotedString { expected, .. }
            | ParseError::ExpectedExportBodyString { expected, .. }
            | ParseError::ExpectedProcess { expected, .. }
            | ParseError::ExpectedFormulaAtom { expected, .. }
            | ParseError::BadFreshLiteral { expected, .. }
            | ParseError::BadNatLiteral { expected, .. }
            | ParseError::BadPublicLiteral { expected, .. }
            | ParseError::ExpectedTerm { expected, .. }
            | ParseError::ExpectedVariable { expected, .. }
            | ParseError::TrailingGarbageInFormulaString { expected, .. }
            | ParseError::TrailingGarbageInTermString { expected, .. }
            | ParseError::UnterminatedDelimiter { expected, .. } => Some(expected),
            ParseError::UnknownLemmaAttribute { .. }
            | ParseError::UnknownRuleAttribute { .. }
            | ParseError::FactNameMustStartWithUppercase { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::FactArityMismatch { .. }
            | ParseError::UnexpectedTrailingInput { .. }
            | ParseError::IoError { .. } => None,
            ParseError::ExpectedTheoryItem {
                expected, found, ..
            } => {
                todo!()
            }
        }
    }

    pub fn description(&self) -> &'static str {
        match self {
            ParseError::UnexpectedKeyword { .. } => "Unexpected keyword",
            ParseError::ExpectedTheoryItem { .. } => "Expected theory item",
            ParseError::ExpectedPunctuation { .. } => "Expected punctuation",
            ParseError::ExpectedStringLiteral { .. } => "Expected string literal",
            ParseError::ExpectedIdentifier { .. } => "Expected identifier",
            ParseError::ExpectedNaturalNumber { .. } => "Expected natural number",
            ParseError::UnknownPreprocessorDirective { .. } => "Unknown preprocessor directive",
            ParseError::ExpectedPreprocessorDirective { .. } => "Expected preprocessor directive",
            ParseError::ExpectedHexColor { .. } => "Expected hex color",
            ParseError::ExpectedQuotedString { .. } => "Expected quoted string",
            ParseError::UnterminatedDelimiter { .. } => "Unterminated delimiter",
            ParseError::UnknownLemmaAttribute { .. } => "Unknown lemma attribute",
            ParseError::ExpectedExportBodyString { .. } => "Expected export body string",
            ParseError::ExpectedProcess { .. } => "Expected process",
            ParseError::FactNameMustStartWithUppercase { .. } => {
                "Fact name must start with uppercase"
            }
            ParseError::FreshFactCannotBePersistent { .. } => "Fresh fact cannot be persistent",
            ParseError::FactArityMismatch { .. } => "Fact arity mismatch",
            ParseError::ExpectedFormulaAtom { .. } => "Expected formula atom",
            ParseError::BadFreshLiteral { .. } => "Bad fresh literal",
            ParseError::BadNatLiteral { .. } => "Bad nat literal",
            ParseError::BadPublicLiteral { .. } => "Bad public literal",
            ParseError::ExpectedTerm { .. } => "Expected term",
            ParseError::ExpectedVariable { .. } => "Expected variable",
            ParseError::UnexpectedTrailingInput { .. } => "Unexpected trailing input",
            ParseError::IoError { .. } => "I/O error",
            ParseError::TrailingGarbageInFormulaString { .. } => {
                "Trailing garbage in formula string"
            }
            ParseError::TrailingGarbageInTermString { .. } => "Trailing garbage in term string",
            ParseError::UnknownRuleAttribute { .. } => "Unknown rule attribute",
        }
    }

    pub fn labels(&self) -> Vec<ParseErrorLabel> {
        match self {
            ParseError::UnterminatedDelimiter {
                opening,
                opening_at,
                found,
                found_at,
                expected,
            } => {
                let primary_at = if found.is_some() {
                    *found_at
                } else {
                    *opening_at
                };
                vec![
                    ParseErrorLabel {
                        at: primary_at,
                        message: format!("expected closing {}", format_expected_list(expected)),
                        is_primary: true,
                    },
                    ParseErrorLabel {
                        at: *opening_at,
                        message: format!("opening `{opening}` starts here"),
                        is_primary: false,
                    },
                ]
            }
            _ => vec![ParseErrorLabel {
                at: *self.location(),
                message: self.description().to_string(),
                is_primary: true,
            }],
        }
    }

    pub fn notes(&self) -> Vec<String> {
        match self {
            ParseError::UnexpectedKeyword {
                found, expected, ..
            } => {
                vec![format_found_expected_note(
                    "keyword",
                    found.as_deref(),
                    expected,
                )]
            }
            ParseError::ExpectedTheoryItem {
                found, expected, ..
            } => {
                vec![format_found_expected_note(
                    "theory item",
                    found.as_deref(),
                    expected,
                )]
            }
            ParseError::ExpectedPunctuation {
                found, expected, ..
            }
            | ParseError::ExpectedStringLiteral {
                found, expected, ..
            }
            | ParseError::ExpectedIdentifier {
                found, expected, ..
            }
            | ParseError::ExpectedNaturalNumber {
                found, expected, ..
            }
            | ParseError::UnknownPreprocessorDirective {
                found, expected, ..
            }
            | ParseError::ExpectedPreprocessorDirective {
                found, expected, ..
            }
            | ParseError::ExpectedHexColor {
                found, expected, ..
            }
            | ParseError::ExpectedQuotedString {
                found, expected, ..
            }
            | ParseError::ExpectedExportBodyString {
                found, expected, ..
            }
            | ParseError::ExpectedProcess {
                found, expected, ..
            }
            | ParseError::ExpectedFormulaAtom {
                found, expected, ..
            }
            | ParseError::BadFreshLiteral {
                found, expected, ..
            }
            | ParseError::BadNatLiteral {
                found, expected, ..
            }
            | ParseError::BadPublicLiteral {
                found, expected, ..
            }
            | ParseError::ExpectedTerm {
                found, expected, ..
            }
            | ParseError::ExpectedVariable {
                found, expected, ..
            }
            | ParseError::TrailingGarbageInFormulaString {
                found, expected, ..
            }
            | ParseError::TrailingGarbageInTermString {
                found, expected, ..
            } => {
                vec![format_found_expected_note(
                    "token",
                    found.as_deref(),
                    expected,
                )]
            }
            ParseError::UnterminatedDelimiter {
                opening,
                opening_at,
                found,
                found_at,
                expected,
            } => {
                let mut notes = vec![format!(
                    "delimiter `{opening}` was opened at line {}, column {} and needs closing {}",
                    opening_at.line,
                    opening_at.col,
                    format_expected_list(expected)
                )];
                if let Some(found) = found {
                    notes.push(format!(
                        "encountered `{found}` at line {}, column {} before a closing delimiter",
                        found_at.line, found_at.col
                    ));
                }
                notes
            }
            ParseError::UnknownLemmaAttribute { attribute, .. } => {
                vec![format!("unknown lemma attribute `{attribute}`")]
            }
            ParseError::UnknownRuleAttribute { attribute, .. } => {
                vec![format!("unknown rule attribute `{attribute}`")]
            }
            ParseError::FactNameMustStartWithUppercase { name, .. } => {
                vec![format!(
                    "fact name `{name}` must start with an uppercase letter"
                )]
            }
            ParseError::FreshFactCannotBePersistent { .. } => {
                vec!["fresh facts (`Fr`) cannot be persistent facts".to_string()]
            }
            ParseError::FactArityMismatch { name, arity, .. } => {
                vec![format!(
                    "fact `{name}` was used with arity {arity}, but it must have arity 1"
                )]
            }
            ParseError::UnexpectedTrailingInput { context, found, .. } => {
                vec![format!("unexpected trailing token `{found}` in {context}")]
            }
            ParseError::IoError { path, message, .. } => {
                vec![format!("failed to read included file `{path}`: {message}")]
            }
        }
    }

    pub fn message(&self) -> String {
        self.description().to_string()
    }

    pub fn label_message(&self) -> String {
        self.description().to_string()
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message())
    }
}

fn format_expected_list(expected: &[String]) -> String {
    match expected.len() {
        0 => "EOF".to_string(),
        1 => format!("`{}`", expected[0]),
        2 => format!("`{}` or `{}`", expected[0], expected[1]),
        _ => {
            let mut s = String::new();
            for (idx, item) in expected.iter().enumerate() {
                if idx > 0 {
                    if idx == expected.len() - 1 {
                        s.push_str(", or ");
                    } else {
                        s.push_str(", ");
                    }
                }
                s.push('`');
                s.push_str(item);
                s.push('`');
            }
            s
        }
    }
}

fn format_found_expected_note(kind: &str, found: Option<&str>, expected: &[String]) -> String {
    match found {
        Some(found) => format!(
            "expected {kind} {}, but found `{found}`",
            format_expected_list(expected)
        ),
        None => format!("expected {kind} {}", format_expected_list(expected)),
    }
}

impl std::error::Error for ParseError {}

/// The merged `expecting` labels of the top-level item alternation, in HS's
/// exact order and spelling.  This is the base set parsec accumulates from
/// `addItems`'s `asum` (`Theory/Text/Parser.hs:243-303`) — each alternative's
/// leading `symbol`/`<?>` label — plus `letter` (from `formalComment`'s
/// `many1 letter`, `Token.hs:377-378`) and the trailing `symbol_ "end"`.
/// Captured empirically from the HS binary at a fresh item position (right
/// after `begin`, no preceding item leftover).  See §28 residue note: after
/// certain items parsec *prepends* extra merged tokens (rule → `"variants"`,
/// functions → `"["`,`","`, …) that this port does not reproduce.
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

/// Parse a theory.
///
/// NOTE: this entry point always parses a NON-diff theory. `is_diff` is
/// hardcoded to `false` and neither `flags` nor a `#define diff` preamble
/// switches into diff mode; diff-theory selection is not implemented at this
/// layer (HS derives it from `"diff" \`S.member\` flags0`).
///
/// No production caller; kept as parity/API surface.
pub fn parse_theory_or_diff(input: &str, flags: &[&str]) -> Result<Theory, ParseError> {
    parse_theory(input, flags)
}

/// Parse a stream of intruder-rule declarations of the form
///     `rule (modulo AC) <name>[<limit>]: [..] --[..]-> [..]`
/// (with no surrounding `theory ... begin ... end` wrapper).
///
/// Direct port of HS `parseIntruderRules` (Theory/Text/Parser/Rule.hs:200-204):
/// ```haskell
/// parseIntruderRules
///     :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
/// parseIntruderRules msig ctxtDesc =
///     parseString [] ctxtDesc (setState (mkStateSig msig) >> many intrRule)
///   . T.unpack . TE.decodeUtf8
/// ```
/// HS threads a `MaudeSig` through parser state so the term parser knows
/// which function symbols are builtin.  In this port the parser always
/// recognises every builtin operator at the syntax level — semantic
/// gating happens at elaboration — so the `MaudeSig` argument is
/// captured only for diagnostic context.
///
/// The bodies are parsed using the existing `parse_rule_ac` path.
/// The caller is responsible for translating the parser-AST rules into
/// `IntrRuleAC` (incl. the `c_`/`d_` name dispatch HS `intrInfo` does
/// at Rule.hs:161-169).
pub fn parse_intruder_rules(input: &str) -> Result<Vec<Rule>, ParseError> {
    let mut p = Parser::new(input, &[], false);
    let mut rules = Vec::new();
    loop {
        p.skip_ws();
        if p.lx.is_eof() {
            break;
        }
        // HS `intrRule` uses `try (symbol "rule" *> moduloAC *> intrInfo <* colon)`
        // (Rule.hs:155-169, see line 157) — i.e. requires the `rule (modulo AC) name:` head.
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
    /// Whether to enable parsing of operators that depend on builtins.
    /// We default-enable everything since this is a structural parser, so these
    /// are always `true`; they are kept as named gates for the operator-parsing
    /// sites (`!eqn && self.enable_x`) should builtin-aware gating ever be added.
    enable_dh: bool,
    enable_xor: bool,
    enable_mset: bool,
    enable_nat: bool,
    /// Directory of the file currently being parsed (`takeDirectory inFile0` in
    /// HS).  `#include "file"` resolves relative to this; `None` (no source
    /// file) means includes are taken verbatim, mirroring HS's `Nothing` case.
    base_dir: Option<PathBuf>,
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
        // Always enable parse-time recognition of the operators. The parser is
        // syntactic — semantic gating against builtin enablement happens at
        // elaboration. This follows the practice of accepting more than the
        // strict Haskell grammar at the syntax level.
        Parser {
            lx: Lexer::new(src),
            flags: flags_set,
            is_diff,
            enable_dh: true,
            enable_xor: true,
            enable_mset: true,
            enable_nat: true,
            base_dir: None,
        }
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
            let found = self.lx.peek_until_ws();
            let at = Location::location_of(&found, self.lx.pos());
            Err(ParseError::UnexpectedKeyword {
                found: found.map(|s| s.to_string()),
                expected: vec![kw.to_string()],
                at,
            })
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
            Err(self.expected_punctuation_err(vec![p]))
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
    /// (Formula.hs:45-57), where Subterm/Less/smallerp/EqE come before the
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
        self.lx
            .identifier()
            .ok_or_else(|| self.expected_identifier_err(vec!["identifier"]))
    }

    fn natural(&mut self) -> Result<u64, ParseError> {
        self.lx
            .natural()
            .ok_or_else(|| self.expected_natural_number_err(vec!["number"]))
    }

    fn string_literal(&mut self) -> Result<String, ParseError> {
        self.lx
            .string_literal()
            .ok_or_else(|| self.expected_string_literal_err(vec!["string literal"]))
    }

    fn found_token(&mut self) -> (Option<String>, Location) {
        self.found_token_until(|c| c.is_whitespace())
    }

    fn found_token_until(&mut self, f: impl FnMut(char) -> bool) -> (Option<String>, Location) {
        let saved_pos = self.lx.pos();
        self.lx.skip_ws();
        let found_pos = self.lx.pos();
        let tok = self.lx.peek_until(f).map(|s| s.to_string());
        self.lx.set_pos(saved_pos);
        let loc = Location::location_of(&tok.as_ref(), found_pos);
        (tok, loc)
    }

    fn expected_keyword_err<I, S>(&mut self, expected: I) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let (found, at) = self.found_token();
        ParseError::UnexpectedKeyword {
            found,
            expected: expected.into_iter().map(Into::into).collect(),
            at,
        }
    }

    fn expected_theory_item_err(&mut self, expected: &[&str]) -> ParseError {
        let (found, at) = self.found_token();
        ParseError::ExpectedTheoryItem {
            found,
            expected: expected.iter().map(|s| (*s).to_string()).collect(),
            at,
        }
    }

    fn expected_punctuation_err<I, S>(&mut self, expected: I) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let (found, at) = self.found_token();
        ParseError::ExpectedPunctuation {
            found,
            expected: expected.into_iter().map(Into::into).collect(),
            at,
        }
    }

    fn expected_string_literal_err<I, S>(&mut self, expected: I) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let (found, at) = self.found_token();
        ParseError::ExpectedStringLiteral {
            found,
            expected: expected.into_iter().map(Into::into).collect(),
            at,
        }
    }

    fn expected_identifier_err<I, S>(&mut self, expected: I) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let (found, at) = self.found_token();
        ParseError::ExpectedIdentifier {
            found,
            expected: expected.into_iter().map(Into::into).collect(),
            at,
        }
    }

    fn expected_natural_number_err<I, S>(&mut self, expected: I) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let (found, at) = self.found_token();
        ParseError::ExpectedNaturalNumber {
            found,
            expected: expected.into_iter().map(Into::into).collect(),
            at,
        }
    }

    fn unknown_preproc_err<I, S>(
        &mut self,
        expected: I,
        found: Option<String>,
        at: Location,
    ) -> ParseError
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        ParseError::UnknownPreprocessorDirective {
            found,
            expected: expected.into_iter().map(Into::into).collect(),
            at,
        }
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
            // symbol_ "begin"` (Parser.hs:233-238); the trailing `begin` here
            // is a plain `symbol_ "begin"`, label `"begin"`.
            self.require_punct(":")?;
            configuration = Some(self.string_literal()?);
            self.require_kw("begin")?;
        } else if !self.try_kw("begin") {
            // HS: `try (symbol "configuration" <* colon) <|> symbol "begin"
            //      <?> "configuration or begin"` (Parser.hs:230-393, see line 233) — the whole
            // choice is relabelled, so the failure Expect is the single custom
            // label, not the two quoted keywords.
            return Err(
                self.expected_keyword_err(vec!["configuration".to_string(), "begin".to_string()])
            );
        }
        let items = self.theory_items_until_end()?;
        // HS `addItems … <* symbol_ "end"` (Parser.hs:230-393, see line 240): when `end` is
        // absent the trailing-`end` failure merges with the item alternation's
        // error, so report the full item-position error rather than a bare
        // `expecting "end"`.
        if !self.try_kw("end") {
            return Err(self.expected_keyword_err(vec!["end".to_string()]));
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
                    // HS `include` (Parser.hs:323-343): consume the directive,
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
        // `commaSep1`, Accountability.hs:30-39, see line 36); the zero-ident form falls back to
        // a normal lemma.

        // No item alternative matched: reproduce parsec's merged item-position
        // error (`addItems` `asum` <* `symbol_ "end"`).
        Err(self.expected_theory_item_err(TOP_LEVEL_ITEM_EXPECTS))
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
        let pos_before_ascii = self.lx.pos();
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
            other => Err(self.unknown_preproc_err(
                vec!["define", "include", "endif", "else"],
                Some(other.to_string()),
                pos_before_ascii.into(),
            )),
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
            return Err(self.expected_keyword_err(vec!["#ifdef".to_string()]));
        }
        if self.lx.ascii_alpha_run() != "ifdef" {
            return Err(self.expected_keyword_err(vec!["#ifdef".to_string()]));
        }
        self.skip_ws();
        let cond = self.flag_disjuncts()?;
        if self.eval_flagformula(&cond) {
            let items = self.theory_items_until_end()?;
            if self.try_punct("#else") {
                // Else branch text is skipped.
                self.skip_until("#endif");
            } else if !self.try_punct("#endif") {
                return Err(
                    self.expected_keyword_err(vec!["#endif".to_string(), "#else".to_string()])
                );
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
                BranchEnd::Eof => Err(self.expected_keyword_err(vec!["#endif".to_string()])),
            }
        }
    }

    fn expand_include(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        // Consume `#include`.
        self.skip_ws();
        if !self.lx.eat_str("#include") {
            let (found, at) = self.found_token();
            return Err(ParseError::ExpectedPreprocessorDirective {
                found,
                expected: vec!["#include".to_string()],
                at,
            });
        }
        self.skip_ws();
        let raw_path = self.string_literal()?;

        // HS `filePathParser`: resolve relative to the including file's dir when
        // we know it (`Just s -> s </> path`), else verbatim (`Nothing`).
        let resolved: PathBuf = match &self.base_dir {
            Some(dir) => dir.join(&raw_path),
            None => PathBuf::from(&raw_path),
        };

        let content = std::fs::read_to_string(&resolved).map_err(|e| ParseError::IoError {
            path: resolved.display().to_string(),
            message: e.to_string(),
            at: self.lx.pos().into(),
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
        sub.base_dir = sub_base;

        // Parse the header-less item stream: same loop as a theory body, but it
        // terminates at EOF (there is no `end` keyword in a fragment).
        let items = sub.theory_items_until_end()?;
        sub.skip_ws();
        if !sub.lx.is_eof() {
            let (found, at) = sub.found_token();
            return Err(ParseError::UnexpectedTrailingInput {
                context: "included file".to_string(),
                found: found.unwrap_or_else(|| "EOF".to_string()),
                at,
            });
        }

        // Thread parser state BACK (HS `putState st'` + `sig st'` merge): pick up
        // any new flags the included file declared.
        self.flags = sub.flags;

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

    /// `<kw>: ident-with-hyphens (, ident-with-hyphens)*` (no trailing comma).
    /// Shared by the `builtins` and `options` declarations, which are identical
    /// modulo the keyword and the wrapping `TheoryItem` variant.
    fn comma_sep_hyphen_idents(&mut self, kw: &str) -> Result<Vec<String>, ParseError> {
        self.require_kw(kw)?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            names.push(self.hyphen_identifier()?);
            if !self.try_punct(",") {
                break;
            }
        }
        Ok(names)
    }

    fn builtins(&mut self) -> Result<TheoryItem, ParseError> {
        Ok(TheoryItem::Builtins(
            self.comma_sep_hyphen_idents("builtins")?,
        ))
    }

    /// Identifier that may contain hyphens (e.g. `asymmetric-encryption`,
    /// `diffie-hellman`, `dest-pairing`). Hyphens are concatenated into the
    /// returned name with no whitespace allowed across the boundary.
    fn hyphen_identifier(&mut self) -> Result<String, ParseError> {
        let mut s = self.ident()?;
        loop {
            // Look for `-<ident>` immediately after with no whitespace.
            if self.lx.peek() != Some('-') {
                break;
            }
            // We need to peek the char *after* the dash without consuming.
            let mut probe = self.lx.clone();
            probe.bump();
            match probe.peek() {
                Some(c) if c.is_alphabetic() => {
                    self.lx.bump(); // consume `-`
                    s.push('-');
                    let id = self.ident()?;
                    s.push_str(&id);
                }
                _ => break,
            }
        }
        Ok(s)
    }

    fn options(&mut self) -> Result<TheoryItem, ParseError> {
        Ok(TheoryItem::Options(
            self.comma_sep_hyphen_idents("options")?,
        ))
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
        // tactic: <name>\n  presort: ...\n  prio: ...\n  ...
        // We recognise the structure by reading until we hit an end-of-tactic
        // marker — tactics terminate when a keyword that starts a new theory
        // item appears at the top of a line. Pragmatic: read until next
        // top-level keyword.
        self.require_kw("tactic")?;
        self.require_punct(":")?;
        let name = self.ident()?;
        let raw = self.read_until_next_top_level();
        Ok(TheoryItem::Tactic(Tactic { name, raw }))
    }

    /// Read raw text until we see an identifier at a word boundary that is
    /// one of the recognised top-level keywords, or a `#`-prefixed
    /// preprocessor directive. Used for tactics, proof skeletons, etc.
    fn read_until_next_top_level(&mut self) -> String {
        // NOTE: the top-level `let X = ...` process definition (dispatched by
        // `theory_item`) is deliberately OMITTED here. `let` is overloaded —
        // it also begins `let`-bindings inside rules/processes — and a bare
        // `let` token can never legitimately appear inside the proof-skeleton
        // or tactic-body grammars this scanner captures, so the only effect of
        // adding it would be to risk truncating a capture mid-body. A top-level
        // `let` following a tactic/proof block (then needing this stop word) is
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
        // Proof.hs:129-146, see line 146), so the token immediately after the `case` keyword is
        // consumed as the case name and can never begin a new top-level item.
        // Case names are drawn from rule names and source-case names, so ANY
        // top-level keyword can legally appear here — e.g. a rule named `test`
        // prints as `case test`, and `test` is itself the CaseTest keyword
        // (`caseTest = CaseTest <$> (symbol "test" *> identifier)`,
        // Theory/Text/Parser/Accountability.hs:25-27, see line 26; dispatched Parser.hs:230-393, see line 268).
        // Without this suppression the bare `test` at depth 0 truncates the
        // capture and the main parser resumes by consuming `test` as a CaseTest
        // declaration → `expected ':'`.  This is the only in-script position
        // where a bare keyword can sit at depth 0: every proof method is a fixed
        // keyword or `solve( <goal> )` whose goal is paren-nested (depth > 0),
        // and tactic blocks (the other user of this scanner) carry only the
        // fixed keywords `presort`/`prio`/`deprio`, the fixed tactic-function
        // names, braced ranking names, and double-quoted (opaque) arguments —
        // none of which collide with `KW`.
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
        loop {
            let f = self.function_decl()?;
            decls.push(f);
            if !self.try_punct(",") {
                break;
            }
        }
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
            self.require_punct(close)?;
        }
        Ok(v)
    }

    fn function_decl(&mut self) -> Result<FunctionDecl, ParseError> {
        let name = self.ident()?;
        let (arg_types, out_type);
        if self.try_punct("/") {
            let k = self.natural()?;
            arg_types = vec![None; k as usize];
            out_type = None;
        } else {
            self.require_punct("(").map_err(|mut e| {
                // Due to the if/else the error that would surface here does not
                // report the "/" as an expected token.
                e.add_expected("/".to_string());
                e
            })?;
            // HS `parens (commaSep typep)` (Signature.hs:149-160, see line 156): `sepEndBy`
            // permits a trailing comma before `)`.
            let args = self.sep_end_by(")", |p| p.type_p())?;
            self.require_punct(":")?;
            out_type = self.type_p()?;
            arg_types = args.into_iter().collect();
        }
        // Optional attributes [private, constructor, destructor, ...]
        let mut private = false;
        let mut destructor = false;
        if self.try_punct("[") {
            loop {
                self.skip_ws();
                if self.try_kw("private") {
                    private = true;
                } else if self.try_kw("constructor") {
                } else if self.try_kw("destructor") {
                    destructor = true;
                } else {
                    break;
                }
                if !self.try_punct(",") {
                    break;
                }
            }
            self.require_punct("]")?;
        }
        Ok(FunctionDecl {
            name,
            arg_types,
            out_type,
            private,
            destructor,
        })
    }

    /// SAPIC type: `<defaultSapicTypeS>` = `Any` placeholder, or an identifier.
    fn type_p(&mut self) -> Result<Option<String>, ParseError> {
        // HS `typep` (Token.hs:472-473): `(try (symbol defaultSapicTypeS) *>
        // return Nothing) <|> Just <$> identifier`, where `defaultSapicTypeS =
        // "Any"` (Theory/Sapic/Term.hs:94-95, see line 95). Only the literal `Any`
        // (case-sensitive) is the default placeholder; everything else is
        // `Just <ident>` — so lowercase `any` is `Just "any"`, and `*` is not a
        // valid identifier (a parse failure, matching HS).
        self.skip_ws();
        let id = self.ident()?;
        if id == "Any" {
            Ok(None)
        } else {
            Ok(Some(id))
        }
    }

    fn equations(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("equations")?;
        // HS `equations` (Signature.hs:219-224): `convergent` is set only when
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
            // HS `equation` (Signature.hs:230-231) parses both operands with
            // `term llitNoPub True`. The `True` (eqn flag) gates AC/multiset/
            // nat/xor/exp operators — matched here by `term(true)`. `llitNoPub`
            // (Term.hs:53-54 = `asum [freshTerm <$> freshName, varTerm <$>
            // msgvar]`) additionally forbids public-name literals `'foo'` and
            // nat literals `%'n'` in operands, while still allowing fresh
            // literals `~'n'` and all msgvar-sort variables (including `$x`
            // pub-sort vars, since `msgvar = sortedLVar [Fresh,Pub,Nat,Msg]`).
            // We deliberately use the public-name-allowing `term(true)` here:
            // accepting `'foo'`/`%'n'` is benign parser-level leniency — such
            // public/nat names are invalid in (convergent) equations and are
            // rejected during elaboration, so end-to-end `--prove` output is
            // unchanged on all valid theories.
            let lhs = self.term(true)?;
            self.require_punct("=")?;
            let rhs = self.term(true)?;
            eqs.push(Equation { lhs, rhs });
            if !self.try_punct(",") {
                break;
            }
        }
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
            self.require_punct("(")?;
            // HS `parens $ commaSep lvar` (Macro.hs:29-49, see line 38): trailing comma OK.
            let args = self.sep_end_by(")", |p| p.var_spec())?;
            self.require_punct("=")?;
            let body = self.term(false)?;
            ms.push(Macro { name, args, body });
            if !self.try_punct(",") {
                break;
            }
        }
        Ok(TheoryItem::Macros(ms))
    }

    fn predicates(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("predicates") {
            self.require_kw("predicate")?;
        }
        self.require_punct(":")?;
        let mut ps = Vec::new();
        loop {
            let f = self.fact()?;
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
        Ok(TheoryItem::Predicates(ps))
    }

    // -------------------- Restriction / axiom --------------------

    fn restriction_item(&mut self) -> Result<TheoryItem, ParseError> {
        let r = self.restriction("restriction")?;
        Ok(TheoryItem::Restriction(r))
    }

    fn legacy_axiom(&mut self) -> Result<TheoryItem, ParseError> {
        let r = self.restriction("axiom")?;
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
        self.lx.skip_ws();
        let opening_pos = self.lx.pos();
        self.require_punct("\"")?;
        let f = self.formula()?;
        self.require_punct("\"")
            .map_err(|e| ParseError::UnterminatedDelimiter {
                opening: "\"".to_string(),
                opening_at: Location::location_of(&Some("\""), opening_pos),
                found_at: *e.location(),
                found: e.into_found(),
                expected: vec!["\"".to_string()],
            })?;
        Ok(f)
    }

    // -------------------- Rule --------------------

    fn rule_item(&mut self) -> Result<TheoryItem, ParseError> {
        // We must distinguish protocol rules from intruder rules. Intruder
        // rules use `rule (modulo AC) name: ...` — they live in the top-level
        // theory only when explicitly parsed (e.g. for a precomputed intruder
        // file).
        let r = self.parse_rule()?;
        // Tag intruder rules: their names start with `c<...>` or `d<...>`,
        // typically only when modulo == Some("AC"). We don't enforce this.
        if r.modulo.as_deref() == Some("AC") {
            Ok(TheoryItem::IntrRule(r))
        } else {
            Ok(TheoryItem::Rule(r))
        }
    }

    /// Parse the middle arrow of a rule: either the `-->` shortcut (no
    /// actions/restrictions) or `--[ .. ]->` with a `fact_or_restr` loop
    /// splitting action Facts from embedded Restrs, allowing a trailing comma
    /// before `]->` (HS `commaSep` = `sepEndBy comma`, Rule.hs:181-191, see line 186).
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
    /// before `]->` is permitted (HS `commaSep`, Rule.hs:181-191, see line 186).
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

    fn parse_rule(&mut self) -> Result<Rule, ParseError> {
        self.require_kw("rule")?;
        let modulo = self.try_modulo();
        let name = self.ident()?;
        let attributes = self.rule_attributes()?;
        self.require_punct(":")?;
        // Optional let block.
        let let_block = if self.at_keyword("let") {
            self.parse_let_block()?
        } else {
            vec![]
        };
        // Premises [..]
        let premises = self.fact_list()?;
        // Actions / restrictions either `--[..]->` or `-->`
        let (actions, embedded_restrictions) = self.parse_actions_and_restrictions()?;
        let conclusions = self.fact_list()?;
        // Optional variants
        let variants = if self.try_kw("variants") {
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
            vec![]
        };
        // Optional `left ... right ...` for diff rules
        let left_right = if self.try_kw("left") {
            let l = self.parse_rule()?;
            self.require_kw("right")?;
            let r = self.parse_rule()?;
            Some((Box::new(l), Box::new(r)))
        } else {
            None
        };
        Ok(Rule {
            name,
            modulo,
            attributes,
            let_block,
            premises,
            actions,
            conclusions,
            embedded_restrictions,
            variants,
            left_right,
        })
    }

    fn parse_rule_ac(&mut self) -> Result<Rule, ParseError> {
        self.require_kw("rule")?;
        // HS `protoRuleACInfo`/`intrRule` (Rule.hs:137-138/157) sequence a
        // non-optional `moduloAC` here (`symbol "rule" *> moduloAC *> ...`).
        // This port relaxes that: `try_modulo` returns `None` when the
        // `(modulo AC)` head is absent and parsing proceeds. (More lenient than
        // Haskell, but still accepts all valid Haskell input.)
        let modulo = self.try_modulo();
        let name = self.ident()?;
        let attributes = self.rule_attributes()?;
        self.require_punct(":")?;
        let let_block = if self.at_keyword("let") {
            self.parse_let_block()?
        } else {
            vec![]
        };
        let premises = self.fact_list()?;
        let (actions, embedded_restrictions) = self.parse_actions_and_restrictions()?;
        let conclusions = self.fact_list()?;
        Ok(Rule {
            name,
            modulo,
            attributes,
            let_block,
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
                let c = self.lx.hex_color().ok_or_else(|| {
                    let (found, at) = self.found_token();
                    ParseError::ExpectedHexColor {
                        found,
                        expected: vec!["hex color".to_string()],
                        at,
                    }
                })?;
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
                    let (found, at) =
                        self.found_token_until(|c| c == ']' || c == ',' || c.is_whitespace());
                    return Err(ParseError::UnknownRuleAttribute {
                        attribute: found.unwrap_or("EOF".to_string()),
                        at,
                    });
                }
            }
            if !self.try_punct(",") {
                break;
            }
        }
        self.require_punct("]")?;
        Ok(attrs)
    }

    fn string_literal_or_squoted(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        if let Some(s) = self.lx.string_literal() {
            return Ok(s);
        }
        if let Some(s) = self.lx.single_quoted() {
            return Ok(s);
        }
        let (found, at) = self.found_token();
        Err(ParseError::ExpectedQuotedString {
            found,
            expected: vec!["quoted string".to_string()],
            at,
        })
    }

    /// Read an identifier or a balanced parenthesised token (for `process=...`).
    fn read_balanced_token(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        // HS `parseAndIgnore = betweenMatching (\(l,r) -> manyCharsExcept [l,r] ...)`
        // (Rule.hs:68-93, see line 85). `betweenMatching` (Token.hs:305-316) tries each pair in
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
                    let opening_at = self.lx.pos().into();
                    self.lx.bump();
                    let mut s = String::new();
                    loop {
                        match self.lx.peek() {
                            None => {
                                let (found, found_at) = self.found_token();
                                return Err(ParseError::UnterminatedDelimiter {
                                    found,
                                    expected: vec![r.to_string()],
                                    opening: l.to_string(),
                                    opening_at,
                                    found_at,
                                });
                            }
                            // Stop at the first `l` or `r` (matches
                            // `manyCharsExcept`, which does not nest); the closer
                            // `r` is then consumed by `between`.
                            Some(ch) if ch == *r || ch == *l => {
                                if ch != *r {
                                    let (found, found_at) = self.found_token();
                                    return Err(ParseError::UnterminatedDelimiter {
                                        found,
                                        expected: vec![r.to_string()],
                                        opening: l.to_string(),
                                        opening_at,
                                        found_at,
                                    });
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

    fn parse_let_block(&mut self) -> Result<Vec<LetBinding>, ParseError> {
        self.require_kw("let")?;
        let mut bs = Vec::new();
        loop {
            self.skip_ws();
            if self.at_keyword("in") {
                break;
            }
            // End-of-block sentinels (defensive — the canonical terminator is
            // `in`, but malformed inputs shouldn't loop forever).
            if self.lx.peek() == Some('[')
                || self.lx.rest().starts_with("-->")
                || self.lx.rest().starts_with("--[")
            {
                break;
            }
            let lhs_save = self.save();
            let lhs = match self.term(false) {
                Ok(t) => t,
                Err(_) => {
                    self.restore(lhs_save);
                    break;
                }
            };
            if !self.try_punct("=") {
                self.restore(lhs_save);
                break;
            }
            let rhs = self.term(false)?;
            bs.push(LetBinding {
                var: lhs,
                value: rhs,
            });
        }
        // Consume the `in` terminator if present.
        let _ = self.try_kw("in");
        Ok(bs)
    }

    fn fact_list(&mut self) -> Result<Vec<Fact>, ParseError> {
        self.require_punct("[")?;
        // HS `list (fact ...)` (Rule.hs:181-191, see line 183/188) = `brackets . commaSep`
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
        Ok(TheoryItem::Lemma(Lemma {
            name,
            modulo: None,
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
        // HS `lemmaAcc` (Accountability.hs:30-39, see line 36) uses `commaSep1 $ identifier`,
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
        let proof = self.try_proof_skeleton()?;
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
                // HS `list constructorp` (Lemma.hs:39-53, see line 49) = `brackets . commaSep`:
                // trailing comma before `]` is permitted.
                let outs = self.sep_end_by("]", |p| p.ident())?;
                attrs.push(LemmaAttr::Output(outs));
            } else if self.try_kw("left") {
                attrs.push(LemmaAttr::Left);
            } else if self.try_kw("right") {
                attrs.push(LemmaAttr::Right);
            } else {
                // HS `lemmaAttribute` (Lemma.hs:39-53) is a closed `asum` of the
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
                let at = Location::location_of(&Some(&raw), self.lx.pos());
                return Err(ParseError::UnknownLemmaAttribute { attribute: raw, at });
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
                Some('[') | Some('(') | Some('{') => {
                    depth += 1;
                    s.push(self.lx.peek().unwrap());
                    self.lx.bump();
                }
                Some(']') | Some(')') | Some('}') => {
                    depth -= 1;
                    s.push(self.lx.peek().unwrap());
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
        // This gate is shared by `lemma_item` (regular proofs) and
        // `diff_lemma_item` (diff proofs), so it is the union of both:
        //   - regular `proofMethod` (Proof.hs:77-85): sorry, simplify, solve,
        //     contradiction, induction, INVALIDATED, UNFINISHABLE
        //   - regular skeleton extras (Proof.hs:99-115): `by` (finalProof),
        //     `SOLVED` (solvedProof)
        //   - diff `diffProofMethod` (Proof.hs:119-126): sorry, rule-equivalence,
        //     backward-search, step, ATTACK, UNFINISHABLEdiff
        //   - diff skeleton extras (Proof.hs:130-144): `by` (finalProof),
        //     `MIRRORED` (solvedProof)
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
            // diff proofMethod
            "rule-equivalence",
            "backward-search",
            "step",
            "ATTACK",
            "UNFINISHABLEdiff",
            // diff skeleton extras
            "MIRRORED",
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
        let raw = self.read_until_next_top_level();
        // Structured parse of `raw`.  Mirrors HS's `startProofSkeleton`
        // (Theory/Text/Parser/Proof.hs:90-95) which calls `proofSkeleton`
        // (Proof.hs:98-115) — a recursive descent over
        // `simplify | solve(...) | induction | by <method> | SOLVED`
        // with `case <name> ... next ... qed` blocks.  We parse over
        // the captured raw text rather than the original lexer so the
        // top-level boundary detection (`read_until_next_top_level`)
        // controls termination.
        //
        // If the structured parse fails we still keep the raw text,
        // and `replace_sorry_prove` will fall back to the auto-prover.
        let tree = parse_proof_tree(&raw).ok();
        Ok(Some(ProofSkeleton { raw, tree }))
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
                Some('-') => {
                    let mut probe = self.lx.clone();
                    probe.bump();
                    match probe.peek() {
                        Some(c) if c.is_alphabetic() => {
                            self.lx.bump();
                            s.push('-');
                        }
                        _ => break,
                    }
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
            // HS `parens $ commaSep sapicvar` (Sapic.hs:64-72, see line 69): trailing comma OK.
            Some(self.sep_end_by(")", |p| p.var_spec())?)
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
        // Export bodies use the strict `bodyChar` grammar (Signature.hs:282-287),
        // NOT the general string-literal escape decoding.
        let body = self.lx.export_body().ok_or_else(|| {
            let (found, at) = self.found_token();
            ParseError::ExpectedExportBodyString {
                found,
                expected: vec!["export body string".to_string()],
                at,
            }
        })?;
        Ok(TheoryItem::Export { tag, body })
    }

    // =========================================================================
    // Process parser (SAPIC)
    // =========================================================================

    fn process(&mut self) -> Result<Process, ParseError> {
        // Left-associative parallel / NDC composition.
        let mut left = self.action_process()?;
        loop {
            self.skip_ws();
            if self.try_punct("||") {
                let right = self.action_process()?;
                left = Process::Comb {
                    comb: ProcessComb::Parallel,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else if self.lx.peek() == Some('|') && self.lx.peek2() != Some('|') {
                // Single `|` parallel
                self.lx.bump();
                self.skip_ws();
                let right = self.action_process()?;
                left = Process::Comb {
                    comb: ProcessComb::Parallel,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else if self.try_punct("+") {
                let right = self.action_process()?;
                left = Process::Comb {
                    comb: ProcessComb::Ndc,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
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
            let cond_save = self.save();
            let cond = match (|| -> Result<Condition, ParseError> {
                let t1 = self.term(false)?;
                self.require_punct("=")?;
                let t2 = self.term(false)?;
                Ok(Condition::Eq(t1, t2))
            })() {
                Ok(c) => c,
                Err(_) => {
                    self.restore(cond_save);
                    let phi = self.formula()?;
                    Condition::Formula(phi)
                }
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
            {
                let pat = self.term(false)?;
                self.require_punct("=")?;
                let val = self.term(false)?;
                bindings.push((pat, val));
            }
            loop {
                let _ = self.try_punct(",");
                self.skip_ws();
                if self.at_keyword("in") {
                    break;
                }
                // Try to parse one more binding; backtrack if it doesn't parse
                // (matching `many1`'s greedy-with-backtrack behaviour).
                let probe = self.save();
                let next = (|| -> Result<(Term, Term), ParseError> {
                    let pat = self.term(false)?;
                    self.require_punct("=")?;
                    let val = self.term(false)?;
                    Ok((pat, val))
                })();
                match next {
                    Ok(b) => bindings.push(b),
                    Err(_) => {
                        self.restore(probe);
                        break;
                    }
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
                // HS `parens $ commaSep (msetterm ...)` (Sapic.hs:224-312, see line 296):
                // trailing comma before `)` is permitted.
                self.sep_end_by(")", |p| p.term(false))?
            } else {
                vec![]
            };
            return Ok(Process::Call { name: id, args });
        }
        self.restore(save2);
        let (found, at) = self.found_token();
        Err(ParseError::ExpectedProcess {
            found,
            expected: vec!["process".to_string()],
            at,
        })
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
            let (chan, msg) = self.parse_chan_msg()?;
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
        // Embedded MSR: `[..] --[..]-> [..]`
        if self.lx.peek() == Some('[') {
            let prems = self.fact_list()?;
            let (acts, restrs) = if self.try_punct("-->") {
                (vec![], vec![])
            } else if self.try_punct("--[") {
                self.parse_action_restr_list()?
            } else {
                self.restore(save);
                return Ok(None);
            };
            let concs = self.fact_list()?;
            return Ok(Some(SapicAction::Msr {
                prems,
                acts,
                concs,
                restrictions: restrs,
            }));
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
        let name_pos = self.lx.pos();
        let name = self.ident()?;
        if !name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            let at = Location::location_of(&Some(&name), name_pos);
            return Err(ParseError::FactNameMustStartWithUppercase { name, at });
        }
        self.require_punct("(")?;
        // HS `parens (commaSep pterm)` (Fact.hs:39-63, see line 47): trailing comma OK.
        let args = self.sep_end_by(")", |p| p.term(false))?;
        let mut annotations = Vec::new();
        if self.try_punct("[") && !self.try_punct("]") {
            loop {
                // HS `factAnnotation` (Fact.hs:31-36): SolveFirst is
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
        // `Theory.Text.Parser.Fact.mkProtoFact` (Fact.hs:56-63) combined with
        // `factTagMultiplicity` (Model/Fact.hs:354-360) and `factTagName`
        // (Model/Fact.hs:507-517).  Any fact whose name uppercases to one of
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
            // `!Fr(...)` is a parse error (Fact.hs:39-63, see line 45).
            if upper == "FR" && persistent {
                let at = Location::location_of(&Some(&name), name_pos);
                return Err(ParseError::FreshFactCannotBePersistent { at });
            }
            // `singleTerm`: special facts have arity one (Fact.hs:52-54).
            if args.len() != 1 {
                let at = Location::location_of(&Some(&name), name_pos);
                return Err(ParseError::FactArityMismatch {
                    name,
                    arity: args.len(),
                    at,
                });
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
        let mut lhs = self.conjuncts()?;
        loop {
            // `|` is also process parallel — but inside formulas it's OR.
            if self.try_punct("|") || self.try_punct("∨") {
                let rhs = self.conjuncts()?;
                lhs = Formula::Or(Box::new(lhs), Box::new(rhs));
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn conjuncts(&mut self) -> Result<Formula, ParseError> {
        let mut lhs = self.negation()?;
        loop {
            if self.try_punct("&") || self.try_punct("∧") {
                let rhs = self.negation()?;
                lhs = Formula::And(Box::new(lhs), Box::new(rhs));
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn negation(&mut self) -> Result<Formula, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.fatom()?;
            Ok(Formula::Not(Box::new(f)))
        } else {
            self.fatom()
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
            return Ok(Formula::Atom(Atom::Last(t)));
        }
        // Try fact@t (action atom)
        let save_f = self.save();
        if let Ok(f) = self.fact() {
            if self.try_punct("@") {
                let t = self.term(false)?;
                return Ok(Formula::Atom(Atom::Action(f, t)));
            }
            // HS `blatom` (Formula.hs:45-57) tries the term-relational atoms
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
            return Ok(Formula::Atom(Atom::Eq(lhs, rhs)));
        }
        if self.try_punct("<<") || self.try_punct("⊏") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Subterm(lhs, rhs)));
        }
        if self.try_punct("(<)") {
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
            // HS `blatom` (Formula.hs:44-60, see line 49) restricts both operands of `<` to
            // node/timepoint variables: `Less <$> try (nodevarTerm <* opLess)
            // <*> nodevarTerm`. This structural port intentionally accepts any
            // `term` on both sides (parser-level permissiveness); the sort
            // restriction is deferred to elaboration. Valid theories (which use
            // timepoint vars with `<`) parse identically.
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Less(lhs, rhs)));
        }
        let (found, at) = self.found_token();
        Err(ParseError::ExpectedFormulaAtom {
            found,
            expected: vec!["formula atom".to_string()],
            at,
        })
    }

    // =========================================================================
    // Terms
    // =========================================================================

    /// Top-level term parser. `eqn` indicates we're inside an equation
    /// (which forbids AC operators).
    fn term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.tupleterm(eqn)
    }

    /// Right-associative tuple `<a, b, c, ...>` is parsed by `pairing` —
    /// at the `term` level we handle comma-grouped sequence only inside
    /// `<...>` brackets. So `tupleterm` here is just `msetterm` plus a
    /// chain on `,` when used inside angled brackets.
    fn tupleterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        // For top-level, no comma-grouping happens unless inside <...>.
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

    fn msetterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.natterm(eqn)?;
        if !eqn && self.enable_mset {
            loop {
                self.skip_ws();
                // `++` or `+` (as multiset union); careful with `+` for NDC
                // and `%+` for nat plus, which are handled separately.
                if self.lx.rest().starts_with("++") {
                    self.lx.bump();
                    self.lx.bump();
                    self.skip_ws();
                    let rhs = self.natterm(eqn)?;
                    lhs = Term::BinOp(BinOp::Union, Box::new(lhs), Box::new(rhs));
                } else if self.lx.rest().starts_with('+') && !self.lx.rest().starts_with("+>") {
                    // Avoid `+` that's part of process NDC. At term level
                    // we always treat `+` as union.
                    self.lx.bump();
                    self.skip_ws();
                    let rhs = self.natterm(eqn)?;
                    lhs = Term::BinOp(BinOp::Union, Box::new(lhs), Box::new(rhs));
                } else {
                    break;
                }
            }
        }
        Ok(lhs)
    }

    fn natterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.xorterm(eqn)?;
        if !eqn && self.enable_nat {
            while self.try_punct("%+") {
                let rhs = self.xorterm(eqn)?;
                lhs = Term::BinOp(BinOp::NatPlus, Box::new(lhs), Box::new(rhs));
            }
        }
        Ok(lhs)
    }

    fn xorterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.multterm(eqn)?;
        if !eqn && self.enable_xor {
            while self.try_kw("XOR") || self.try_punct("⊕") {
                let rhs = self.multterm(eqn)?;
                lhs = Term::BinOp(BinOp::Xor, Box::new(lhs), Box::new(rhs));
            }
        }
        Ok(lhs)
    }

    fn multterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if eqn || !self.enable_dh {
            return self.atom_term(eqn);
        }
        let mut lhs = self.expterm(eqn)?;
        loop {
            self.skip_ws();
            // Multiplication is `*` but not `**`. Avoid consuming `*}` (formal-comment end).
            if self.lx.peek() == Some('*') && self.lx.peek2() != Some('}') {
                self.lx.bump();
                self.skip_ws();
                let rhs = self.expterm(eqn)?;
                lhs = Term::BinOp(BinOp::Mult, Box::new(lhs), Box::new(rhs));
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn expterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.atom_term(eqn)?;
        // HS `expterm` is "a left-associative sequence of exponentiations"
        // (`chainl1`, Parser/Term.hs:150-152), so build left-associative
        // `^` trees here to match.
        while self.try_punct("^") {
            let rhs = self.atom_term(eqn)?;
            lhs = Term::BinOp(BinOp::Exp, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// One atomic term.
    fn atom_term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.skip_ws();
        // SAPIC pattern-match prefix `=t` — treat as PatMatch wrapper.
        if self.lx.peek() == Some('=') {
            // Avoid consuming `=` if it's the start of an operator like `==>`,
            // `=>`, or `==`.
            let r = self.lx.rest();
            if !r.starts_with("==") && !r.starts_with("=>") {
                self.lx.bump();
                self.skip_ws();
                let inner = self.atom_term(eqn)?;
                return Ok(Term::PatMatch(Box::new(inner)));
            }
        }
        // Parens for grouping
        if self.try_punct("(") {
            let t = self.msetterm(eqn)?;
            // Allow a tuple inside () with ',' — actually Tamarin uses `<>` for
            // pairs and `()` for grouping only. So no comma inside `()`.
            self.require_punct(")")?;
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
                // HS `pairing = angled (tupleterm eqn plit)` with
                // `tupleterm = chainr1 (msetterm ...) (... <$ comma)`
                // (Term.hs:123-148, see line 142,187-188). `chainr1` requires >=1 operand, so the
                // operand loop always runs: an empty `<>` fails to parse
                // (matching HS, where no other `term` alternative starts with
                // `<`), and a singleton `<a>` collapses to `a`.
                let mut items = Vec::new();
                loop {
                    let t = self.msetterm(eqn)?;
                    items.push(t);
                    if !self.try_punct(",") {
                        break;
                    }
                }
                self.require_punct(">")?;
                if items.len() == 1 {
                    return Ok(items.into_iter().next().unwrap());
                }
                return Ok(Term::Pair(items));
            }
        }
        // Special tokens
        if self.try_kw("DH_neutral") {
            return Ok(Term::DhNeutral);
        }
        if self.try_punct("1:nat") {
            return Ok(Term::NatOne);
        }
        if self.try_punct("%1") {
            return Ok(Term::NatOne);
        }
        // `1` only valid when DH is enabled; we accept it always at parse level.
        // Divergence from HS, benign on the corpus: HS `term` (Term.hs:123-148, see line 134) tries
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
                if next.is_none_or(|c| !c.is_alphanumeric() && c != '_') {
                    self.lx.bump();
                    self.skip_ws();
                    return Ok(Term::NumberOne);
                }
            }
            self.restore(save);
        }
        // Sigil-prefixed variables: ~x, $x, #x, %x.
        if matches!(self.lx.peek(), Some('~') | Some('$') | Some('#')) {
            // Could be a fresh-name literal `~'n'` or `%'n'` — handled below.
            let c = self.lx.peek().unwrap();
            let mut probe = self.lx.clone();
            probe.bump();
            if c == '~' && probe.peek() == Some('\'') {
                self.lx.bump();
                let s = self.lx.single_quoted().ok_or_else(|| {
                    let (found, at) = self.found_token();
                    ParseError::BadFreshLiteral {
                        found,
                        expected: vec!["fresh literal".to_string()],
                        at,
                    }
                })?;
                return Ok(Term::FreshLit(s));
            }
            // Otherwise: variable.
            if let Some(v) = self.try_var_spec()? {
                let v = self.attach_sort_suffix(v)?;
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
                    self.lx.bump();
                    let s = self.lx.single_quoted().ok_or_else(|| {
                        let (found, at) = self.found_token();
                        ParseError::BadNatLiteral {
                            found,
                            expected: vec!["nat literal".to_string()],
                            at,
                        }
                    })?;
                    return Ok(Term::NatLit(s));
                }
                Some(c) if c.is_ascii_alphabetic() => {
                    if let Some(v) = self.try_var_spec()? {
                        let v = self.attach_sort_suffix(v)?;
                        return Ok(Term::Var(v));
                    }
                }
                _ => {}
            }
        }
        // Literal `'foo'` is a public name term.
        if self.lx.peek() == Some('\'') {
            let s = self.lx.single_quoted().ok_or_else(|| {
                let (found, at) = self.found_token();
                ParseError::BadPublicLiteral {
                    expected: vec!["public literal".to_string()],
                    found,
                    at,
                }
            })?;
            return Ok(Term::PubLit(s));
        }
        // diff(a, b) — HS `diffOp = symbol "diff" *> parens ...` (Term.hs:108-110).
        // `diff` is a reserved name (Token.hs:214-230, see line 225) so it is NOT an identifier and
        // must be matched as a keyword here, BEFORE the identifier path. The
        // word-boundary check in `peek_symbol` keeps `diffuse(...)` an identifier
        // (function application), matching HS where `naryOpApp` handles it.
        if self.lx.peek_symbol("diff") {
            let save_diff = self.save();
            let _ = self.lx.try_symbol("diff");
            if self.lx.peek() == Some('(') {
                self.lx.bump();
                self.skip_ws();
                let a = self.msetterm(eqn)?;
                self.require_punct(",")?;
                let b = self.msetterm(eqn)?;
                self.require_punct(")")?;
                return Ok(Term::Diff(Box::new(a), Box::new(b)));
            }
            // `diff` not followed by `(`: HS `diffOp`'s `parens` fails and there is
            // no identifier-named-`diff` fallback, so the term path moves on (and
            // ultimately fails here, as in HS).
            self.restore(save_diff);
        }
        // Identifier — could be: function application f(...), algebraic
        // application f{a}b, sort-suffixed var x:msg, or a bare variable /
        // nullary function.
        let save_id = self.save();
        if let Some(id) = self.lx.identifier() {
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
                    let idx = self.try_dot_index();
                    let v = VarSpec {
                        name: id,
                        idx,
                        sort: SortHint::Untagged,
                        typ: None,
                    };
                    let v = self.attach_sort_suffix(v)?;
                    return Ok(Term::Var(v));
                }
                self.lx.bump();
                self.skip_ws();
                let mut ts = Vec::new();
                if !self.try_punct(")") {
                    loop {
                        let t = self.msetterm(eqn)?;
                        ts.push(t);
                        // NB: HS `naryOpApp` (Term.hs:84-87) is arity-dependent —
                        // arity-1 ops parse args via `tupleterm`/`chainr1` (strict,
                        // no trailing comma), only arity≠1 via `commaSep` (trailing
                        // comma OK). This parser has no arity at this point, so we
                        // keep the strict form to avoid accepting `g(x,)` for a
                        // unary `g`, which HS rejects.
                        if !self.try_punct(",") {
                            break;
                        }
                    }
                    self.require_punct(")")?;
                }
                return Ok(Term::App(id, ts));
            }
            if self.lx.peek() == Some('{') {
                self.lx.bump();
                self.skip_ws();
                let arg1 = self.tuple_contents(eqn)?;
                self.require_punct("}")?;
                let arg2 = self.atom_term(eqn)?;
                return Ok(Term::AlgApp(id, Box::new(arg1), Box::new(arg2)));
            }
            // Bare identifier: untagged variable. Optionally with index `.<n>`
            // (only consumes `.` if followed by a digit) and optionally with
            // sort suffix `:msg|pub|fresh|node|nat` or a SAPIC type annotation.
            let idx = self.try_dot_index();
            let v = VarSpec {
                name: id,
                idx,
                sort: SortHint::Untagged,
                typ: None,
            };
            let v = self.attach_sort_suffix(v)?;
            return Ok(Term::Var(v));
        }
        self.restore(save_id);
        let (found, at) = self.found_token();
        Err(ParseError::ExpectedTerm {
            found,
            expected: vec!["term".to_string()],
            at,
        })
    }

    fn attach_sort_suffix(&mut self, mut v: VarSpec) -> Result<VarSpec, ParseError> {
        // Only sortless prefixes can have a suffix.
        // Suffix syntax: `<id>:msg`, `:pub`, `:fresh`, `:node`, `:nat`.
        let save = self.save();
        if self.try_punct(":") {
            // Distinguish suffix sort vs SAPIC type annotation.
            let snap = self.save();
            if self.try_kw("msg") {
                v.sort = SortHint::Suffix(SuffixSort::Msg);
                return Ok(v);
            }
            if self.try_kw("pub") {
                v.sort = SortHint::Suffix(SuffixSort::Pub);
                return Ok(v);
            }
            if self.try_kw("fresh") {
                v.sort = SortHint::Suffix(SuffixSort::Fresh);
                return Ok(v);
            }
            if self.try_kw("node") {
                v.sort = SortHint::Suffix(SuffixSort::Node);
                return Ok(v);
            }
            if self.try_kw("nat") {
                v.sort = SortHint::Suffix(SuffixSort::Nat);
                return Ok(v);
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
                SortHint::Fresh
            }
            Some('$') => {
                self.lx.bump();
                SortHint::Pub
            }
            Some('#') => {
                self.lx.bump();
                SortHint::Node
            }
            Some('%') => {
                // Could be `%1` (nat one) or `%'n'` (nat name lit) or `%x` (nat var).
                let mut probe = self.lx.clone();
                probe.bump();
                match probe.peek() {
                    Some('\'') | Some('1') => return Ok(None), // handled by literal/atom path
                    Some(c) if c.is_ascii_alphabetic() => {
                        self.lx.bump();
                        SortHint::Nat
                    }
                    _ => {
                        return Ok(None);
                    }
                }
            }
            Some(c) if c.is_alphabetic() => SortHint::Untagged,
            _ => return Ok(None),
        };
        let id = match self.lx.identifier() {
            Some(s) => s,
            None => {
                self.restore(save);
                return Ok(None);
            }
        };
        let idx = self.try_dot_index();
        Ok(Some(VarSpec {
            name: id,
            idx,
            sort,
            typ: None,
        }))
    }

    fn var_spec(&mut self) -> Result<VarSpec, ParseError> {
        let v = self.try_var_spec()?.ok_or_else(|| {
            let (found, at) = self.found_token();
            ParseError::ExpectedVariable {
                found,
                expected: vec!["variable".to_string()],
                at,
            }
        })?;
        // Allow `: msg | pub | fresh | node | nat` sort suffix or a SAPIC
        // type annotation after the variable.
        self.attach_sort_suffix(v)
    }

    /// Parse a quantifier binder variable (`All`/`Ex` binder list), mirroring
    /// HS `quantification`'s `many1 (try varp <|> nodep)` with `varp = msgvar`,
    /// `nodep = nodevar` (Formula.hs:64-77, see line 75, Token.hs:440-447).  `msgvar` parses a
    /// PREFIXLESS binder as `LSortMsg` (Token.hs:409-433, see line 426,441) — there is no
    /// inference step for formula binders.  RS's generic `var_spec` tags a
    /// prefixless var as `Untagged` (a placeholder it resolves later for RULE
    /// terms), which has no HS equivalent and sorts LAST under `Ord LVar`
    /// `(idx, sort, name)` (LTerm.hs:521-523).  That placeholder leaked into the
    /// guarded binding's `LSort`, flipping the display-time AC arg sort of an
    /// existential binder against a free Msg operand of equal idx (`dif++seq`
    /// → `seq++dif`), since `fAppAC`/`openGuarded` sort by that key
    /// (Term/Raw.hs:118-122, Guarded.hs:364-373, see line 367).  Pin a prefixless binder to `Msg`
    /// exactly as `msgvar` does; explicit `$`/`~`/`#`/`%`/suffix binders keep
    /// their concrete sort.
    fn quantifier_binder(&mut self) -> Result<VarSpec, ParseError> {
        let mut v = self.var_spec()?;
        if matches!(v.sort, SortHint::Untagged) {
            v.sort = SortHint::Msg;
        }
        Ok(v)
    }

    /// Parse a quantifier's binder list (`All`/`Ex` share this): a sequence of
    /// `quantifier_binder`s terminated by `.`, which is consumed.
    fn quantifier_binders(&mut self) -> Result<Vec<VarSpec>, ParseError> {
        let mut vs = Vec::new();
        loop {
            self.skip_ws();
            if self.lx.peek() == Some('.') {
                break;
            }
            let v = self.quantifier_binder()?;
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
            Some(c) if c.is_ascii_digit() => self.lx.natural().unwrap_or_else(|| {
                self.restore(save);
                0
            }),
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
        let mut lhs = self.flag_conjuncts()?;
        while self.try_punct("|") || self.try_punct("∨") {
            let rhs = self.flag_conjuncts()?;
            lhs = FlagFormula::Or(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn flag_conjuncts(&mut self) -> Result<FlagFormula, ParseError> {
        let mut lhs = self.flag_negation()?;
        while self.try_punct("&") || self.try_punct("∧") {
            let rhs = self.flag_negation()?;
            lhs = FlagFormula::And(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
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

    fn eval_flagformula(&self, f: &FlagFormula) -> bool {
        match f {
            FlagFormula::Atom(s) => self.flags.contains(s),
            FlagFormula::Not(g) => !self.eval_flagformula(g),
            FlagFormula::And(a, b) => self.eval_flagformula(a) && self.eval_flagformula(b),
            FlagFormula::Or(a, b) => self.eval_flagformula(a) || self.eval_flagformula(b),
        }
    }
}

#[derive(Debug)]
enum BranchEnd {
    Else,
    Endif,
    Eof,
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
/// input after the formula.  All algebraic operators are enabled at parse time
/// (see [`Parser::new`]); semantic gating is irrelevant here.
pub fn parse_formula_str(s: &str) -> Result<Formula, ParseError> {
    let mut p = Parser::new(s, &[], false);
    let f = p.formula()?;
    p.skip_ws();
    if !p.lx.is_eof() {
        let (found, at) = p.found_token();
        return Err(ParseError::TrailingGarbageInFormulaString {
            found,
            expected: vec!["end of input".to_string()],
            at,
        });
    }
    Ok(f)
}

/// Parse a standalone term from its source text into the AST [`Term`].
///
/// Used by the stored-proof replay matcher (`tamarin-theory::replay`) to
/// recover the structure of a `solve(...)` goal's fact arguments — which
/// the lightweight proof-tree skeleton parser captures only as raw text —
/// so they can be compared structurally (modulo variable renaming) against
/// the runtime goal terms.  All algebraic operators are enabled at parse
/// time (see [`Parser::new`]); semantic gating is irrelevant here because
/// we only need the operator/function shape.
pub fn parse_term_str(s: &str) -> Result<Term, ParseError> {
    let mut p = Parser::new(s, &[], false);
    let t = p.term(false)?;
    p.skip_ws();
    if !p.lx.is_eof() {
        let (found, at) = p.found_token();
        return Err(ParseError::TrailingGarbageInTermString {
            found,
            expected: vec!["end of input".to_string()],
            at,
        });
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formula_trailing_garbage_uses_structured_variant() {
        let e = parse_formula_str("T & F junk").unwrap_err();
        match e {
            ParseError::TrailingGarbageInFormulaString {
                found,
                expected,
                at,
            } => {
                assert_eq!(found.as_deref(), Some("junk"));
                assert_eq!(expected, vec!["end of input".to_string()]);
                assert_eq!(at.line, 1);
                assert_eq!(at.col, 7);
            }
            other => panic!("unexpected variant: {other:?}"),
        }
    }

    #[test]
    fn theory_keyword_error() {
        let e = parse_theory("theary Foo\nbegin\nend\n", &[]).unwrap_err();
        match e {
            ParseError::UnexpectedKeyword {
                found,
                expected,
                at,
            } => {
                assert_eq!(found.as_deref(), Some("theary"));
                assert_eq!(expected, vec!["\"theory\"".to_string()]);
                assert_eq!(at.line, 1);
                assert_eq!(at.col, 1);
                assert_eq!(at.start, 0);
                assert_eq!(at.end, 6);
            }
            other => panic!("unexpected variant: {other:?}"),
        }
    }

    #[test]
    fn empty_theory() {
        let s = "theory Foo begin end";
        let t = parse_theory(s, &[]).unwrap();
        assert_eq!(t.name, "Foo");
        assert!(t.items.is_empty());
    }

    #[test]
    fn theory_with_builtins() {
        let s = "theory T begin builtins: hashing, signing end";
        let t = parse_theory(s, &[]).unwrap();
        match &t.items[0] {
            TheoryItem::Builtins(v) => {
                assert_eq!(v, &vec!["hashing".to_string(), "signing".into()])
            }
            x => panic!("expected builtins, got {:?}", x),
        }
    }

    #[test]
    fn simple_rule() {
        let s = r#"
            theory T begin
              rule R: [Fr(~k)] --[ Foo(~k) ]-> [ Out(~k) ]
            end
        "#;
        let t = parse_theory(s, &[]).unwrap();
        match &t.items[0] {
            TheoryItem::Rule(r) => {
                assert_eq!(r.name, "R");
                assert_eq!(r.premises.len(), 1);
                assert_eq!(r.actions.len(), 1);
                assert_eq!(r.conclusions.len(), 1);
            }
            x => panic!("expected rule, got {:?}", x),
        }
    }

    #[test]
    fn lemma_with_quantifier() {
        let s = r#"
            theory T begin
              lemma secret: "All x #i. K(x) @ i ==> F"
            end
        "#;
        let t = parse_theory(s, &[]).unwrap();
        match &t.items[0] {
            TheoryItem::Lemma(_) => {}
            x => panic!("expected lemma, got {:?}", x),
        }
    }

    #[test]
    fn comment_handling() {
        let s = "/* outer */ theory T // line\n begin /* x /* y */ z */ end";
        let t = parse_theory(s, &[]).unwrap();
        assert_eq!(t.name, "T");
    }

    #[test]
    fn term_application() {
        let mut p = Parser::new("h(<a, b>, ~k)", &[], false);
        let t = p.term(false).unwrap();
        match t {
            Term::App(name, args) => {
                assert_eq!(name, "h");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn formula_string() {
        let f = parse_formula_str("All x. P(x) ==> Q(x)").unwrap();
        match f {
            Formula::Forall(_, _) => {}
            _ => panic!("expected Forall"),
        }
    }

    // HS `blatom` (Formula.hs:45-57) tries the term-relational atoms
    // (Subterm/Less/EqE) BEFORE the bare-fact `Pred` alternative, so an
    // uppercase function applied with a relational operator is an equality/
    // subterm atom, not a predicate. Verified against tamarin-prover 1.13.0:
    // `A(Foo(x))@i ==> Foo(x) = Foo(y)` renders `(Foo(x) = Foo(y))`.
    #[test]
    fn fatom_fact_lhs_of_relop_is_term_atom() {
        // Equality: `Foo(x) = Foo(y)` must be Atom::Eq(App,App), not Pred.
        let f = parse_formula_str("Foo(x) = Foo(y)").unwrap();
        match f {
            Formula::Atom(Atom::Eq(Term::App(l, _), Term::App(r, _))) => {
                assert_eq!(l, "Foo");
                assert_eq!(r, "Foo");
            }
            other => panic!("expected Eq(App,App), got {:?}", other),
        }
        // Subterm: `A(x) << B(y)` must be Atom::Subterm, not Pred.
        let f = parse_formula_str("A(x) << B(y)").unwrap();
        match f {
            Formula::Atom(Atom::Subterm(Term::App(l, _), Term::App(r, _))) => {
                assert_eq!(l, "A");
                assert_eq!(r, "B");
            }
            other => panic!("expected Subterm(App,App), got {:?}", other),
        }
        // A genuine predicate atom (no following relational op) stays Pred.
        let f = parse_formula_str("P(x) & Q(y)").unwrap();
        match f {
            Formula::And(a, _) => match *a {
                Formula::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
                ref other => panic!("expected Pred, got {:?}", other),
            },
            other => panic!("expected And, got {:?}", other),
        }
        // Implication after a predicate must NOT be misread as `=` (==> guard).
        let f = parse_formula_str("P(x) ==> Q(y)").unwrap();
        match f {
            Formula::Implies(a, _) => match *a {
                Formula::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
                ref other => panic!("expected Pred LHS of ==>, got {:?}", other),
            },
            other => panic!("expected Implies, got {:?}", other),
        }
    }

    // HS `typep` (Token.hs:471-473) maps only the literal `Any` to the default
    // (Nothing); lowercase `any` is `Just "any"`. Verified against
    // tamarin-prover 1.13.0: `new x:any` renders with `:any` preserved.
    #[test]
    fn type_p_only_capital_any_is_default() {
        // `functions: f(any):bitstring` — arg type must be Some("any").
        let t = parse_theory("theory T begin functions: f(any):bitstring end", &[]).unwrap();
        let decl = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Functions(ds) => ds.iter().find(|d| d.name == "f"),
                _ => None,
            })
            .expect("function f");
        assert_eq!(decl.arg_types, vec![Some("any".to_string())]);
        assert_eq!(decl.out_type, Some("bitstring".to_string()));

        // `functions: g(Any):bitstring` — capital Any is the default (None).
        let t = parse_theory("theory T begin functions: g(Any):bitstring end", &[]).unwrap();
        let decl = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Functions(ds) => ds.iter().find(|d| d.name == "g"),
                _ => None,
            })
            .expect("function g");
        assert_eq!(decl.arg_types, vec![None]);
    }

    // HS `tupleterm` uses `chainr1`, which requires >=1 operand, so `<>` fails
    // to parse and `<x>` collapses to `x`. Verified against tamarin-prover
    // 1.13.0: `A(<>)` is a parse error; `A(<x>)` renders `A( x )`.
    #[test]
    fn empty_tuple_is_error_singleton_collapses() {
        assert!(parse_term_str("<>").is_err(), "<> must be a parse error");
        // Singleton tuple collapses to the inner term.
        match parse_term_str("<x>").unwrap() {
            Term::Var(v) => assert_eq!(v.name, "x"),
            other => panic!("expected singleton to collapse to Var, got {:?}", other),
        }
        // Two-element tuple is a Pair.
        match parse_term_str("<x, y>").unwrap() {
            Term::Pair(items) => assert_eq!(items.len(), 2),
            other => panic!("expected Pair, got {:?}", other),
        }
    }

    // HS `factAnnotation` SolveFirst is `opUnion = symbol_ "++" <|> symbol_ "+"`
    // (Fact.hs:31-36, see line 32, Token.hs:551-552), so `[++]` is accepted like `[+]`.
    // Verified against tamarin-prover 1.13.0: `Foo(~k)[++]` parses and renders
    // as `[+]`.
    #[test]
    fn fact_annotation_accepts_double_plus() {
        let s = "theory T begin rule R: [ Fr(~k) ] --[ Foo(~k)[++] ]-> [ Out(~k) ] end";
        let t = parse_theory(s, &[]).unwrap();
        let rule = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Rule(r) => Some(r),
                _ => None,
            })
            .expect("rule R");
        let act = &rule.actions[0];
        assert_eq!(act.annotations, vec![FactAnnotation::SolveFirst]);
    }

    // Regression: `test` is a genuine top-level theory-item keyword (HS
    // `caseTest = CaseTest <$> (symbol "test" *> identifier)`,
    // Theory/Text/Parser/Accountability.hs:25-27, see line 26, dispatched in `addItems`,
    // Theory/Text/Parser.hs:230-393, see line 268) but is ALSO an ordinary message variable
    // name inside proof goals — e.g. `solve( Match( test, sid ) @ #i4 )` in
    // examples/ake/bilinear/Scott.spthy.  HS parses the proof skeleton
    // STRUCTURALLY (`solve <$> parens goal`, Proof.hs:76-85, see line 80), so a `test` inside
    // `solve( ... )` is a `parens`-nested term and can never begin a new
    // top-level item.  `read_until_next_top_level` reproduces that boundary
    // rule by only testing the top-level-keyword set at paren-depth 0; without
    // it the capture truncates at `test` and the following parse blows up with
    // `expected identifier`.
    #[test]
    fn proof_skeleton_not_truncated_by_keyword_fact_arg() {
        let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Match( test, sid ) @ #i4 )
    case c
    by sorry
  qed
end"#;
        let t = parse_theory(s, &[]).expect("keyword-named goal arg must parse");
        let lemmas: Vec<_> = t
            .items
            .iter()
            .filter(|it| matches!(it, TheoryItem::Lemma(_)))
            .collect();
        assert_eq!(lemmas.len(), 1, "expected exactly one lemma");
        assert!(
            !t.items
                .iter()
                .any(|it| matches!(it, TheoryItem::CaseTest(_))),
            "no CaseTest may be split out of the proof body"
        );
        let proof = match &lemmas[0] {
            TheoryItem::Lemma(l) => l.proof.as_ref().expect("lemma has a proof skeleton"),
            _ => unreachable!(),
        };
        assert!(
            proof.raw.contains("Match( test, sid )"),
            "proof raw truncated at/before `test`: {:?}",
            proof.raw
        );
        assert!(
            proof.raw.contains("qed"),
            "proof raw missing `qed`: {:?}",
            proof.raw
        );
    }

    // The paren-depth guard must cover the full spread of message-argument
    // sorts a printed goal can carry — fresh `~k`, public `$A`, nat `%n`,
    // indexed `k.1` — mixed with several bare identifiers that collide with
    // top-level keywords (`test`, `rule`, `function`).  None may truncate the
    // capture.
    #[test]
    fn proof_skeleton_captures_mixed_sorted_indexed_and_keyword_args() {
        let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Foo( ~k, $A, %n, k.1, test, rule, function ) @ #i1 )
    case c
    by sorry
  qed
end"#;
        let t = parse_theory(s, &[]).expect("mixed-arg goal must parse");
        let proof = match t
            .items
            .iter()
            .find(|it| matches!(it, TheoryItem::Lemma(_)))
            .expect("lemma")
        {
            TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
            _ => unreachable!(),
        };
        assert!(
            proof
                .raw
                .contains("Foo( ~k, $A, %n, k.1, test, rule, function )"),
            "mixed-arg goal truncated: {:?}",
            proof.raw
        );
        assert!(proof.raw.contains("qed"), "missing qed: {:?}", proof.raw);
        assert!(!t
            .items
            .iter()
            .any(|it| matches!(it, TheoryItem::CaseTest(_))));
    }

    // Dual check: the depth-0 boundary must still fire.  A genuine top-level
    // `test` CaseTest item following a proof (whose body also contains a `test`
    // goal argument) must be recognized as a CaseTest, and the proof must not
    // absorb it.
    #[test]
    fn real_casetest_after_proof_still_recognized() {
        let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Foo( test, sid ) @ #i1 )
    case c
    by sorry
  qed
  test Reachable:
    "Ex #i. Bar() @ #i"
end"#;
        let t = parse_theory(s, &[]).expect("proof followed by CaseTest must parse");
        let proof = match t
            .items
            .iter()
            .find(|it| matches!(it, TheoryItem::Lemma(_)))
            .expect("lemma")
        {
            TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
            _ => unreachable!(),
        };
        assert!(
            proof.raw.contains("Foo( test, sid )") && proof.raw.contains("qed"),
            "proof body truncated: {:?}",
            proof.raw
        );
        let ct = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::CaseTest(c) => Some(c),
                _ => None,
            })
            .expect("top-level `test` CaseTest must be recognized after the proof");
        assert_eq!(ct.name, "Reachable");
    }

    // Regression (companion to the depth guard): tactic filter regexes carry
    // ESCAPED, UNBALANCED parens inside a double-quoted string literal —
    // e.g. `regex "cp\("` and `regex "In_A\( 'S', <'codes'"` in
    // examples/csf18-alethea/....  Those `(`s are opaque regex text (HS lexes
    // the whole thing as `stringLiteral`, Token.hs:366-367); counting them as
    // grouping would keep `depth` permanently positive so the tactic capture
    // swallows every following item.  The scanner must treat double-quoted
    // string interiors as opaque.
    #[test]
    fn tactic_regex_with_unbalanced_paren_does_not_swallow_next_item() {
        let s = r#"theory T begin
  tactic: myTac
  presort: C
  prio:
    regex "In_A\( 'S', <'codes'"
  prio:
    regex "cp\("
  rule R: [ Fr(~k) ] --[ Created(~k) ]-> [ Out(~k) ]
end"#;
        let t = parse_theory(s, &[]).expect("tactic with unbalanced regex parens must parse");
        let tac = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Tactic(t) => Some(t),
                _ => None,
            })
            .expect("tactic present");
        assert!(
            tac.raw.contains(r#"regex "cp\(""#),
            "tactic body truncated: {:?}",
            tac.raw
        );
        // The `(` inside the regex string must not leak the following rule into
        // the tactic capture.
        assert!(
            !tac.raw.contains("rule R"),
            "next item leaked into tactic capture: {:?}",
            tac.raw
        );
        let rule = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Rule(r) => Some(r),
                _ => None,
            })
            .expect("rule R must remain a separate top-level item");
        assert_eq!(rule.name, "R");
    }

    // Regression: a proof CASE LABEL that collides with a top-level keyword must
    // not truncate the capture.  HS parses `oneCase = symbol "case" *> identifier`
    // (Theory/Text/Parser/Proof.hs:98-115, see line 115) structurally, so the identifier after
    // `case` is the case NAME and can be any top-level keyword — case names come
    // from rule / source-case names, and `test` is the CaseTest keyword
    // (Accountability.hs:25-27, see line 26).  A rule named `test` prints its solved case as
    // `case test` at paren-depth 0 (unlike Scott's `test` which was inside
    // `solve( ... )`), so the paren-depth guard alone does not suppress it —
    // the case-label suppression below is also needed.
    #[test]
    fn proof_case_label_named_after_keyword_does_not_truncate() {
        let s = r#"theory T begin
  lemma l:
    exists-trace "Ex x #i. Done(x) @ #i"
  simplify
  solve( A( x ) ▶₀ #i )
    case test
    SOLVED // trace found
  qed
end"#;
        let t = parse_theory(s, &[]).expect("`case test` must not truncate the proof");
        // The bare `test` case label must NOT be split off as a CaseTest item.
        assert!(
            !t.items
                .iter()
                .any(|it| matches!(it, TheoryItem::CaseTest(_))),
            "case label `test` must not become a top-level CaseTest"
        );
        let proof = match t
            .items
            .iter()
            .find(|it| matches!(it, TheoryItem::Lemma(_)))
            .expect("lemma")
        {
            TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
            _ => unreachable!(),
        };
        assert!(
            proof.raw.contains("case test"),
            "proof raw truncated at/before `case test`: {:?}",
            proof.raw
        );
        assert!(
            proof.raw.contains("SOLVED") && proof.raw.contains("qed"),
            "proof raw missing SOLVED/qed: {:?}",
            proof.raw
        );
    }

    // The suppression must fire per `case` keyword — several cases in a row, each
    // labelled after a different top-level keyword (`rule`, `lemma`, `function`),
    // separated by `next`.  None may truncate the capture, and none may be split
    // off as its own top-level item.
    #[test]
    fn multiple_case_labels_named_after_keywords_do_not_truncate() {
        let s = r#"theory T begin
  lemma l:
    all-traces "All x #i. Done(x) @ #i ==> F"
  simplify
  solve( A( x ) ▶₀ #i )
    case rule
      by sorry
    next
    case lemma
      by sorry
    next
    case function
      by sorry
  qed
end"#;
        let t = parse_theory(s, &[]).expect("keyword-named case labels must not truncate");
        // Exactly one lemma, no stray Rule/Functions items split out of the body.
        assert_eq!(
            t.items
                .iter()
                .filter(|it| matches!(it, TheoryItem::Lemma(_)))
                .count(),
            1
        );
        assert!(
            !t.items.iter().any(|it| matches!(it, TheoryItem::Rule(_))),
            "a `case rule` label must not be split into a top-level rule"
        );
        assert!(
            !t.items
                .iter()
                .any(|it| matches!(it, TheoryItem::Functions(_))),
            "a `case function` label must not be split into a top-level functions decl"
        );
        let proof = match t
            .items
            .iter()
            .find(|it| matches!(it, TheoryItem::Lemma(_)))
            .expect("lemma")
        {
            TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
            _ => unreachable!(),
        };
        for label in ["case rule", "case lemma", "case function"] {
            assert!(
                proof.raw.contains(label),
                "proof raw missing {label:?}: {:?}",
                proof.raw
            );
        }
        assert!(
            proof.raw.contains("qed"),
            "proof raw missing qed: {:?}",
            proof.raw
        );
    }

    // Dual check: the depth-0 boundary must still fire for a REAL top-level
    // keyword that is NOT a case label.  A genuine `test` CaseTest item following
    // a proof whose body contains a `case test` label must still be recognized:
    // the case-label suppression is armed only by the preceding `case` keyword and
    // is cleared after one token, so the later bare `test` still terminates the
    // capture.
    #[test]
    fn keyword_after_proof_still_terminates_capture() {
        let s = r#"theory T begin
  lemma l:
    exists-trace "Ex x #i. Done(x) @ #i"
  simplify
  solve( A( x ) ▶₀ #i )
    case test
    SOLVED
  qed
  rule two:
    [ A(x) ] --[ Done(x) ]-> [ ]
end"#;
        let t = parse_theory(s, &[]).expect("proof followed by a real rule must parse");
        let proof = match t
            .items
            .iter()
            .find(|it| matches!(it, TheoryItem::Lemma(_)))
            .expect("lemma")
        {
            TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
            _ => unreachable!(),
        };
        assert!(
            proof.raw.contains("case test") && proof.raw.contains("qed"),
            "proof body truncated: {:?}",
            proof.raw
        );
        assert!(
            !proof.raw.contains("rule two"),
            "the following rule leaked into the proof capture: {:?}",
            proof.raw
        );
        let rule = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Rule(r) => Some(r),
                _ => None,
            })
            .expect("the top-level `rule two` must remain a separate item");
        assert_eq!(rule.name, "two");
    }
}
