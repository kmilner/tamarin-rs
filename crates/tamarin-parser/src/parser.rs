// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rkunnema, charlie-j, jdreier, beschmi, BTom-GH,
//   kevinmorio, PhilipLukertWork, yavivanov, ValentinYuri, felixlinker,
//   racoucho1u, rsasse, Mathias-AURAND, jWoc, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Builtin/Signature.hs, lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Maude/Signature.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/term/src/Term/Term/Raw.hs,
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
use crate::lexer::{is_ident_char, is_reserved_name, Lexer, Pos};
use crate::proof_tree::parse_proof_tree;

pub const DUMMY_LOCATION: Location = Location {
    line: u32::MAX,
    col: u32::MAX,
    start: usize::MAX,
    end: usize::MAX,
};

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub line: u32,
    pub col: u32,
    pub start: usize,
    pub end: usize,
}

impl Location {
    pub fn location_of<S>(word: &Option<S>, pos: Pos) -> Self
    where
        S: AsRef<str>,
    {
        Self {
            line: pos.line,
            col: pos.col,
            start: pos.offset,
            end: pos.offset + word.as_ref().map_or(0, |s| s.as_ref().len()),
        }
    }

    pub fn from_positions(start: Pos, end: Pos) -> Self {
        Self {
            line: start.line,
            col: start.col,
            start: start.offset,
            end: end.offset,
        }
    }

    pub fn from_locations(start: Self, end: Self) -> Self {
        Self {
            line: start.line,
            col: start.col,
            start: start.start,
            end: end.end,
        }
    }
}

impl From<Pos> for Location {
    fn from(pos: Pos) -> Self {
        Self {
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
    DuplicateRule {
        name: String,
        first_at: Location,
        second_at: Location,
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
    UnknownAttribute {
        attribute: String,
        at: Location,
        context: String,
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
    /// Bridge for parser sites not yet converted to a dedicated variant: an
    /// expected-set failure at a location.
    Expected {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    /// Bridge for parser sites not yet converted to a dedicated variant: a
    /// preformatted message at a location.
    Custom {
        message: String,
        at: Location,
    },
    /// Bridge for the rejections HS raises as GHC `error`s inside parser
    /// actions (`macro`'s and `equations`' rejections): not a backtrackable
    /// parse failure — term-level backtracking propagates it verbatim.
    Abort {
        message: String,
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
            | ParseError::Expected { expected, .. }
            | ParseError::UnterminatedDelimiter { expected, .. } => {
                if !expected.contains(&exp) {
                    expected.push(exp);
                }
            }
            // Explicity match to force compile-time error for new variants
            ParseError::FactNameMustStartWithUppercase { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::FactArityMismatch { .. }
            | ParseError::UnexpectedTrailingInput { .. }
            | ParseError::UnknownAttribute { .. }
            | ParseError::Custom { .. }
            | ParseError::Abort { .. } => {}
            ParseError::IoError { .. } => {}
            ParseError::DuplicateRule { .. } => {}
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
            | ParseError::UnknownAttribute { at, .. }
            | ParseError::Expected { at, .. }
            | ParseError::Custom { at, .. }
            | ParseError::Abort { at, .. }
            | ParseError::UnterminatedDelimiter { found_at: at, .. } => at,
            ParseError::DuplicateRule { second_at, .. } => second_at,
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
            | ParseError::Expected { found, .. }
            | ParseError::UnterminatedDelimiter { found, .. } => found,
            ParseError::UnknownAttribute { attribute, .. } => Some(attribute),
            ParseError::FactNameMustStartWithUppercase { name, .. }
            | ParseError::FactArityMismatch { name, .. }
            | ParseError::UnexpectedTrailingInput { found: name, .. } => Some(name),
            ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::IoError { .. }
            | ParseError::Custom { .. }
            | ParseError::DuplicateRule { .. }
            | ParseError::Abort { .. } => None,
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
            | ParseError::Expected { found, .. }
            | ParseError::UnterminatedDelimiter { found, .. } => found.as_deref(),
            ParseError::UnknownAttribute { attribute, .. } => Some(attribute.as_str()),
            ParseError::FactNameMustStartWithUppercase { name, .. }
            | ParseError::FactArityMismatch { name, .. } => Some(name.as_str()),
            ParseError::UnexpectedTrailingInput { found, .. } => Some(found.as_str()),
            ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::IoError { .. }
            | ParseError::Custom { .. }
            | ParseError::DuplicateRule { .. }
            | ParseError::Abort { .. } => None,
        }
    }

    pub fn expected(&self) -> Option<Vec<String>> {
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
            | ParseError::Expected { expected, .. }
            | ParseError::UnterminatedDelimiter { expected, .. } => Some(expected.clone()),
            ParseError::FactNameMustStartWithUppercase { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::FactArityMismatch { .. }
            | ParseError::UnknownAttribute { .. }
            | ParseError::UnexpectedTrailingInput { .. }
            | ParseError::Custom { .. }
            | ParseError::Abort { .. }
            | ParseError::IoError { .. }
            | ParseError::DuplicateRule { .. } => None,
        }
        .map(|expected| match self {
            ParseError::ExpectedTheoryItem { found, .. } => {
                if let Some(found) = found {
                    let mut ranked: Vec<(usize, usize, String)> = expected
                        .into_iter()
                        .enumerate()
                        .map(|(idx, exp)| (edit_distance(found, &exp), idx, exp))
                        .collect();
                    ranked.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
                    ranked.into_iter().take(3).map(|(_, _, exp)| exp).collect()
                } else {
                    expected.into_iter().take(3).collect()
                }
            }
            _ => expected,
        })
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
            ParseError::UnknownAttribute { context, .. } => {
                // Using a string to include the context in the message
                Box::leak(format!("Unknown {} attribute", context).into_boxed_str())
            }
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
            ParseError::Expected { .. } => "Unexpected input",
            ParseError::Custom { .. } => "Parse error",
            ParseError::Abort { .. } => "Invalid input",
            ParseError::DuplicateRule { .. } => "Duplicate protocol rule",
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
            ParseError::DuplicateRule {
                name,
                first_at,
                second_at,
            } => {
                vec![
                    ParseErrorLabel {
                        at: *second_at,
                        message: format!("duplicate rule name `{name}`"),
                        is_primary: true,
                    },
                    ParseErrorLabel {
                        at: *first_at,
                        message: format!("first occurrence of rule name `{name}`"),
                        is_primary: false,
                    },
                ]
            }
            ParseError::Custom { message, at } | ParseError::Abort { message, at } => {
                vec![ParseErrorLabel {
                    at: *at,
                    message: message.clone(),
                    is_primary: true,
                }]
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
            ParseError::ExpectedTheoryItem { found, .. } => {
                // Using the function on self instead of the field computes
                // edit-distance for ExpectedTheoryItem. Not a pretty way to do this though.
                let expected = self.expected().unwrap_or_default();
                vec![format_found_expected_note(
                    "theory item",
                    found.as_deref(),
                    &expected,
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
            ParseError::UnknownAttribute {
                attribute, context, ..
            } => {
                vec![format!("unknown {context} attribute `{attribute}`")]
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
            ParseError::Expected {
                found, expected, ..
            } => {
                let list = format_expected_list(expected);
                vec![match found {
                    Some(found) => format!("expected {list}, but found `{found}`"),
                    None => format!("expected {list}"),
                }]
            }
            ParseError::Custom { message, .. } | ParseError::Abort { message, .. } => {
                vec![message.clone()]
            }
            ParseError::DuplicateRule { .. } => {
                vec!["Protocol rule names must be unique".into()]
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

fn edit_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b_chars.len()).collect();
    let mut curr = vec![0; b_chars.len() + 1];

    for (i, a_ch) in a_chars.iter().enumerate() {
        curr[0] = i + 1;
        for (j, b_ch) in b_chars.iter().enumerate() {
            let cost = if a_ch == b_ch { 0 } else { 1 };
            let del = prev[j + 1] + 1;
            let ins = curr[j] + 1;
            let sub = prev[j] + cost;
            curr[j + 1] = del.min(ins).min(sub);
        }
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[b_chars.len()]
}

impl std::error::Error for ParseError {}

/// Haskell `show :: [String] -> String`: a bracketed, comma-separated list of
/// double-quoted elements with no spaces — the rendering `function`'s and
/// `extendSig`'s diagnostics embed (Theory/Text/Parser/Signature.hs:112-119,
/// 204-207).  The elements are plain identifiers, so no escaping is needed.
fn show_string_list(items: &[&str]) -> String {
    let quoted: Vec<String> = items.iter().map(|s| format!("\"{s}\"")).collect();
    format!("[{}]", quoted.join(","))
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
/// NOTE: this entry point always parses a NON-diff theory: it delegates to
/// [`parse_theory`], which pins the parser's `is_diff` to `false`, so the
/// result never carries `Theory::is_diff` (HS derives diff-theory selection
/// from `"diff" \`S.member\` flags0`).  A `diff` entry in `flags` does still
/// set the parser's `enable_diff` bit, which is what makes the `diff(a, b)`
/// term operator legal.
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
    // HS `parseIntruderRules` seeds the parser state with the FULL enabled
    // signature (`setState (mkStateSig msig)`, TheoryLoader.hs:755-768), so
    // `lookupArity` resolves every symbol these machine-generated files use.
    // This entry point has no signature argument — the caller resolves heads
    // against `msig` afterwards (`KnownFuns`) — so accept applications
    // structurally, which admits exactly the same rules.
    p.resolve_prefix_apps = false;
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

/// The `(arity, Privacy, Constructability, NDCstate)` options tuple HS carries
/// per free function symbol (HS `NoEqSym`, Term/Term/FunctionSymbols.hs:243).
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

    /// The options of a builtin's `NoEqSym`.  Every symbol in the builtin
    /// signatures is `NotNDC` (Term/Builtin/Signature.hs:18-44,
    /// Term/Term/FunctionSymbols.hs:245-262), so only arity, privacy and
    /// constructability vary.
    fn of(sym: &BuiltinFunSym) -> Self {
        FunOptions {
            arity: sym.arity,
            private: sym.private,
            destructor: sym.destructor,
            ndc: false,
            ndc_diff: false,
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

/// One entry of a builtin's `stFunSyms` — HS `NoEqSym` restricted to the shapes
/// the builtin signatures use (all of them `NotNDC`).
///
/// Public so `tamarin-theory` can pin [`BUILTIN_ST_FUN_SYMS`] against the
/// `MaudeSig` tables it derives the very same symbols from; nothing else in the
/// port reads this type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuiltinFunSym {
    /// The symbol's name.
    pub name: &'static str,
    /// Its arity.
    pub arity: usize,
    /// HS `Privacy`: `true` is `Private`.
    pub private: bool,
    /// HS `Constructability`: `true` is `Destructor`.
    pub destructor: bool,
}

impl BuiltinFunSym {
    const fn new(name: &'static str, arity: usize, private: bool, destructor: bool) -> Self {
        BuiltinFunSym {
            name,
            arity,
            private,
            destructor,
        }
    }
}

/// The `stFunSyms` of each `builtins:` name's `MaudeSig`, i.e. the free
/// function symbols enabling that builtin adds to the parse-time signature.
///
/// Rows are in HS's `builtinsNames` order (Theory/Text/Parser/Signature.hs:
/// 78-86, whose tail is `builtinsDiffNames`, Signature.hs:57-74) — the order
/// `builtinReservedNames` (Signature.hs:174-181) is built in and therefore the
/// order `function`'s `conflictingBuiltins` list is rendered in.  Within a row
/// the symbols are in `S.toList` (ascending, raw-byte) order, matching the list
/// HS's `extendSig` iterates.
///
/// The rows whose `MaudeSig` only flips an enable flag (`diffie-hellman`,
/// `bilinear-pairing`, `multiset`, `xor`, `natural-numbers` —
/// Term/Maude/Signature.hs:191-196) contribute no symbols and reserve no names.
/// `reliable-channel` is absent on purpose: it maps to `Nothing`
/// (Signature.hs:84), so it neither merges a signature nor reserves anything.
const BUILTIN_ST_FUN_SYMS: &[(&str, &[BuiltinFunSym])] = &[
    // locationReportFunSig (Term/Builtin/Signature.hs:71-72)
    (
        "locations-report",
        &[
            BuiltinFunSym::new("check_rep", 2, false, true),
            BuiltinFunSym::new("get_rep", 1, false, true),
            BuiltinFunSym::new("rep", 2, true, false),
            BuiltinFunSym::new("report", 1, false, false),
        ],
    ),
    ("diffie-hellman", &[]),
    ("bilinear-pairing", &[]),
    ("multiset", &[]),
    ("xor", &[]),
    // symEncFunSig (Term/Builtin/Signature.hs:59-61)
    (
        "symmetric-encryption",
        &[
            BuiltinFunSym::new("sdec", 2, false, false),
            BuiltinFunSym::new("senc", 2, false, false),
        ],
    ),
    // asymEncFunSig (Term/Builtin/Signature.hs:63-65)
    (
        "asymmetric-encryption",
        &[
            BuiltinFunSym::new("adec", 2, false, false),
            BuiltinFunSym::new("aenc", 2, false, false),
            BuiltinFunSym::new("pk", 1, false, false),
        ],
    ),
    // signatureFunSig (Term/Builtin/Signature.hs:67-69)
    (
        "signing",
        &[
            BuiltinFunSym::new("pk", 1, false, false),
            BuiltinFunSym::new("sign", 2, false, false),
            BuiltinFunSym::new("true", 0, false, false),
            BuiltinFunSym::new("verify", 3, false, false),
        ],
    ),
    // pairFunDestSig (Term/Term/FunctionSymbols.hs:302-304)
    (
        "dest-pairing",
        &[
            BuiltinFunSym::new("fst", 1, false, true),
            BuiltinFunSym::new("pair", 2, false, false),
            BuiltinFunSym::new("snd", 1, false, true),
        ],
    ),
    // symEncFunDestSig (Term/Builtin/Signature.hs:83-85)
    (
        "dest-symmetric-encryption",
        &[
            BuiltinFunSym::new("sdec", 2, false, true),
            BuiltinFunSym::new("senc", 2, false, false),
        ],
    ),
    // asymEncFunDestSig (Term/Builtin/Signature.hs:87-89)
    (
        "dest-asymmetric-encryption",
        &[
            BuiltinFunSym::new("adec", 2, false, true),
            BuiltinFunSym::new("aenc", 2, false, false),
            BuiltinFunSym::new("pk", 1, false, false),
        ],
    ),
    // signatureFunDestSig (Term/Builtin/Signature.hs:91-93)
    (
        "dest-signing",
        &[
            BuiltinFunSym::new("pk", 1, false, false),
            BuiltinFunSym::new("sign", 2, false, false),
            BuiltinFunSym::new("true", 0, false, false),
            BuiltinFunSym::new("verify", 3, false, true),
        ],
    ),
    // revealSignatureFunSig (Term/Builtin/Signature.hs:71-73, see line 73)
    (
        "revealing-signing",
        &[
            BuiltinFunSym::new("getMessage", 1, false, false),
            BuiltinFunSym::new("pk", 1, false, false),
            BuiltinFunSym::new("revealSign", 2, false, false),
            BuiltinFunSym::new("revealVerify", 3, false, false),
            BuiltinFunSym::new("true", 0, false, false),
        ],
    ),
    // hashFunSig (Term/Builtin/Signature.hs:75-77)
    ("hashing", &[BuiltinFunSym::new("h", 1, false, false)]),
    ("natural-numbers", &[]),
];

/// The `stFunSyms` a `builtins:` name contributes, or `None` for a name with no
/// `MaudeSig` (`reliable-channel`) and for names this parser does not know.
///
/// Public for the `tamarin-theory` cross-check that pins
/// [`BUILTIN_ST_FUN_SYMS`] against that crate's `MaudeSig` tables.
pub fn builtin_st_fun_syms(name: &str) -> Option<&'static [BuiltinFunSym]> {
    BUILTIN_ST_FUN_SYMS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, syms)| *syms)
}

/// The names in [`BUILTIN_ST_FUN_SYMS`], in table (`builtinsNames`) order.
///
/// Public for the same `tamarin-theory` cross-check as
/// [`builtin_st_fun_syms`].
pub fn builtin_st_fun_sym_names() -> impl Iterator<Item = &'static str> {
    BUILTIN_ST_FUN_SYMS.iter().map(|(n, _)| *n)
}

/// The non-AC (`NoEq`) symbols each theory-level enable flag folds into
/// `funSyms` (Term/Maude/Signature.hs:110-125): the flags contribute whole
/// `FunSig`s, of which only the `NoEq` members reach `noEqFunSyms` and hence
/// `userDefinedFunSyms` (Term/Maude/Signature.hs:157-164) — the set the
/// macro-name conflict check searches (Theory/Text/Parser/Macro.hs:43).
/// Their AC members (`Mult`, `Xor`, `Union`, `NatPlus`) and BP's `C EMap` are
/// not `NoEq`/`ACfct` and never enter that set.
///
/// `DH_THEORY_NOEQ_SYMS` is `dhFunSig`'s `NoEq` part
/// (Term/Term/FunctionSymbols.hs:283-284), contributed when `enableDH ||
/// enableBP` (the `maudeSig` smart constructor forces `enableDH` under BP,
/// Term/Maude/Signature.hs:111-112); the rest are the `NoEq` parts of
/// `bpFunSig`, `xorFunSig` and `natFunSig`
/// (Term/Term/FunctionSymbols.hs:291-292,287-288,324-325).  Options per
/// Term/Term/FunctionSymbols.hs:245-267 (all `Public,Constructor,NotNDC`).
const DH_THEORY_NOEQ_SYMS: &[BuiltinFunSym] = &[
    BuiltinFunSym::new("exp", 2, false, false),
    BuiltinFunSym::new("inv", 1, false, false),
    BuiltinFunSym::new("one", 0, false, false),
    BuiltinFunSym::new("DH_neutral", 0, false, false),
];

/// `bpFunSig`'s `NoEq` part — see [`DH_THEORY_NOEQ_SYMS`].
const BP_THEORY_NOEQ_SYMS: &[BuiltinFunSym] = &[BuiltinFunSym::new("pmult", 2, false, false)];

/// `xorFunSig`'s `NoEq` part — see [`DH_THEORY_NOEQ_SYMS`].
const XOR_THEORY_NOEQ_SYMS: &[BuiltinFunSym] = &[BuiltinFunSym::new("zero", 0, false, false)];

/// `natFunSig`'s `NoEq` part (`natOneSym`, whose name is `tone` —
/// Term/Term/FunctionSymbols.hs:236) — see [`DH_THEORY_NOEQ_SYMS`].
const NAT_THEORY_NOEQ_SYMS: &[BuiltinFunSym] = &[BuiltinFunSym::new("tone", 0, false, false)];

/// Every `NoEq` function-symbol NAME a `builtins:` item of this name folds
/// into `funSyms`: its `stFunSyms` row plus the `NoEq` part of the
/// theory-level `FunSig`s its enable flags contribute
/// (Term/Maude/Signature.hs:110-125; the `maudeSig` smart constructor forces
/// `enableDH` under BP, Signature.hs:111-112).  These are the names
/// `lookupArity` ranks as `NoEqUser` — ahead of every `ACfctUser`
/// (Theory/Text/Parser/Term.hs:62-72) — so `crate::wf`'s printers use this to
/// classify a prefix application of a name that is also declared `[AC]`.
pub(crate) fn builtin_noeq_sym_names(builtin: &str) -> Vec<&'static str> {
    let theory: &[&[BuiltinFunSym]] = match builtin {
        "diffie-hellman" => &[DH_THEORY_NOEQ_SYMS],
        "bilinear-pairing" => &[DH_THEORY_NOEQ_SYMS, BP_THEORY_NOEQ_SYMS],
        "xor" => &[XOR_THEORY_NOEQ_SYMS],
        "natural-numbers" => &[NAT_THEORY_NOEQ_SYMS],
        _ => &[],
    };
    builtin_st_fun_syms(builtin)
        .unwrap_or(&[])
        .iter()
        .map(|s| s.name)
        .chain(theory.iter().flat_map(|syms| syms.iter().map(|s| s.name)))
        .collect()
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
    /// `NoEqUser` (or a macro name, or the appended `em` row): applications
    /// carry this arity, checked by `naryOpApp` (Term.hs:97-100).
    NoEq { arity: usize },
    /// `ACfctUser`: any argument count is accepted (`Term.hs:98` gates the
    /// check on `NotAC`) and the application builds `fAppAC (ACfct …)`.
    Ac,
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
    ac_fun_syms: Vec<String>,
    /// The free function symbols known at this point of the parse, the
    /// parse-time slice of HS's `stFunSyms . sig <$> getState` that
    /// `function`'s conflict check reads (Signature.hs:212).
    ///
    /// Seeded with `pairFunSig` (`fst/1`, `pair/2`, `snd/1`, all
    /// `Public, Constructor, NotNDC` — Term/Term/FunctionSymbols.hs:247-261) in
    /// `S.toList` order, because `parseFile` starts from `sig = pairMaudeSig`
    /// (Token.hs:260-261).  A `builtins:` item merges the row of
    /// [`BUILTIN_ST_FUN_SYMS`] it names; user `functions:` declarations add
    /// their own symbol, except `[AC]` ones (HS files those under
    /// `stACFunSyms` via `ACfctUser`, Term/Maude/Signature.hs:170-173).
    ///
    /// Held as an ordered set — ascending by name, then by
    /// [`FunOptions::ord_key`] — because HS's `lookup f (S.toList …)` takes the
    /// FIRST match, and one name can carry two entries (e.g. `builtins:
    /// symmetric-encryption, dest-symmetric-encryption` leaves both the
    /// constructor and the destructor `sdec`).
    fun_syms: Vec<(String, FunOptions)>,
    /// The macro names known at this point of the parse (HS `macroNames`),
    /// each registered as `(k, Private, Destructor, NotNDC)`
    /// (Theory/Text/Parser/Macro.hs:46).  Searched after [`Parser::fun_syms`],
    /// matching HS's `lookup f (S.toList (stFunSyms sign) ++ S.toList
    /// (macroNames sign))` (Signature.hs:212).
    macro_syms: Vec<(String, FunOptions)>,
    /// HS `reservedBuiltinNames` (Theory/Text/Parser/Token.hs parser state):
    /// the names of the `stFunSyms` of every builtin a `builtins:` item has
    /// enabled so far, appended by `extendSig` (Signature.hs:132-134).
    ///
    /// Only the non-diff `builtins` parser fills it; `diffbuiltins`
    /// (Signature.hs:141-148) merges the signature without touching it, so a
    /// diff theory reserves nothing and `function`'s builtin pre-check can
    /// never fire there.
    reserved_builtin_names: Vec<String>,
    /// The `enableDH`/`enableBP`/`enableXor`/`enableMSet`/`enableNat` bits of
    /// HS's parse-time `MaudeSig` (Term/Maude/Signature.hs:90-108), flipped by
    /// the `builtins:` names whose signatures carry only these flags
    /// (Term/Maude/Signature.hs:191-196).  Distinct from [`Parser::enable_dh`]
    /// &c., which deliberately stay `true` so the structural parser accepts
    /// every operator: these mirror the HS signature bits exactly, for the two
    /// places where that state reaches output bytes — the theory-level function
    /// symbols `userDefinedFunSyms` contributes to the macro-name conflict
    /// check (Theory/Text/Parser/Macro.hs:43 via `funSyms`,
    /// Term/Maude/Signature.hs:110-125,163-164), and the operator `expecting`
    /// labels the enabled `chainl1` levels leave in that check's parse error
    /// (Theory/Text/Parser/Term.hs:176-208).
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
    /// `Expect "\"[\""` — `option [] $ list factAnnotation` (Fact.hs:48)
    /// attempts `[` right after the closing `)` lexeme and fails there when
    /// no annotation follows.  Merged into the expected sets of failures
    /// raised at that exact offset ([`Self::err_expect_after_term`], the
    /// fact-list close of [`Self::sep_end_by`]).
    fact_annot_hangover: Option<usize>,
    /// Whether prefix applications resolve through [`Self::lookup_arity`]
    /// (HS `naryOpApp`/`binaryAlgApp`, Term.hs:88-121).  True for theory
    /// parsing; [`parse_term_str`]/[`parse_formula_str`] clear it because they
    /// re-parse RENDERED term text with no signature state, where every
    /// application must be accepted structurally.
    resolve_prefix_apps: bool,
    /// The `expecting` labels a completed top-level item leaves behind at the
    /// byte offset it stopped at, and that offset.
    ///
    /// parsec carries the error of a *consumed-ok* parse forward and merges it
    /// into whatever the continuation reports at the same position, so an
    /// item's trailing optional parsers (`option [] $ symbol "variants" …` at
    /// the end of `protoRule`, Rule.hs:134; `commaSep1`'s `comma`) prepend
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
            enable_diff: is_diff || flags_set.contains("diff"),
            flags: flags_set,
            is_diff,
            enable_dh: true,
            enable_xor: true,
            enable_mset: true,
            enable_nat: true,
            base_dir: None,
            ac_fun_syms: Vec::new(),
            fun_syms: vec![
                ("fst".to_string(), FunOptions::plain(1)),
                ("pair".to_string(), FunOptions::plain(2)),
                ("snd".to_string(), FunOptions::plain(1)),
            ],
            macro_syms: Vec::new(),
            reserved_builtin_names: Vec::new(),
            sig_enable_dh: false,
            sig_enable_bp: false,
            sig_enable_xor: false,
            sig_enable_mset: false,
            sig_enable_nat: false,
            var_dot_hangover: false,
            dot_index_consumed: false,
            last_ident_end: None,
            var_hangover_ident_end: None,
            term_carry: None,
            fact_annot_hangover: None,
            resolve_prefix_apps: true,
            item_hangover: None,
            seen_rules: Vec::new(),
            seen_restriction_names: Vec::new(),
        }
    }

    // -------- Error helpers --------

    /// A raw-message parse error at the current position (parsec `Message`).
    /// Renders as `"<path>" (line, column):\n<msg>` — the correct parsec frame
    /// with a single message line, even though the message text itself is not a
    /// `unexpected …`/`expecting …` pair.  Used by the many hand-coded error
    /// sites that do not (yet) track a parsec-style expected set.
    fn err(&self, msg: impl Into<String>) -> ParseError {
        ParseError::Custom {
            message: msg.into(),
            at: Location::from(self.lx.pos()),
        }
    }

    /// Bridge for parser sites not yet converted to a dedicated
    /// [`ParseError`] variant: an expected-set failure at the upcoming token.
    /// `expects` are label strings, already carrying any quoting (e.g.
    /// `"\"theory\""`).
    fn err_expect(&mut self, expects: &[&str]) -> ParseError {
        let (found, at) = self.found_token();
        ParseError::Expected {
            found,
            expected: expects.iter().map(|e| (*e).to_string()).collect(),
            at,
        }
    }

    /// [`Self::err`] with the position advanced to the upcoming token's
    /// start.
    fn err_fail(&mut self, msg: impl Into<String>) -> ParseError {
        self.skip_ws();
        self.err(msg)
    }

    /// The error for what HS raises as a GHC `error` inside a parser action
    /// (`macro`'s and `equations`' rejections).  Only the message is
    /// reported; the `HasCallStack` frame is not reproduced.
    fn err_ghc(&self, message: String, _call_site: String) -> ParseError {
        ParseError::Abort {
            message,
            at: Location::from(self.lx.pos()),
        }
    }

    fn err_fail_labelled(&mut self, msg: impl Into<String>, _label: &str) -> ParseError {
        self.err_fail(msg)
    }

    fn err_unterminated_delimiter(
        &self,
        opening: impl Into<String>,
        opening_at: Pos,
        found_at: Location,
        found: Option<String>,
        expected: Vec<String>,
    ) -> ParseError {
        let opening = opening.into();
        let opening_at = Location::location_of(&Some(&opening), opening_at);
        ParseError::UnterminatedDelimiter {
            opening,
            opening_at,
            found_at,
            found,
            expected,
        }
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
    /// levels of Term.hs:165-212 unwind, each level's failed operator attempt
    /// leaving its `symbol` label — innermost first: the user-defined `[AC]`
    /// operators (one level per symbol, the LAST in set order innermost —
    /// `parseACSym`, Term.hs:165-172), then `^`/`*` (DH, forced on by BP —
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
    fn term_carry_labels(&self, at: usize) -> Vec<String> {
        let Some((off, lod, dot, eqn)) = self.term_carry else {
            return Vec::new();
        };
        if off != at {
            return Vec::new();
        }
        let mut labels: Vec<String> = Vec::new();
        if lod {
            labels.push("letter or digit".to_string());
        }
        if dot {
            labels.push("\".\"".to_string());
        }
        for name in self.ac_fun_syms.iter().rev() {
            labels.push(format!("\"{name}\""));
        }
        if !eqn {
            if self.sig_enable_dh || self.sig_enable_bp {
                labels.push("\"^\"".to_string());
                labels.push("\"*\"".to_string());
            }
            if self.sig_enable_xor {
                labels.push("\"XOR\"".to_string());
                labels.push("\"⊕\"".to_string());
            }
            if self.sig_enable_nat {
                labels.push("\"%+\"".to_string());
            }
            if self.sig_enable_mset {
                labels.push("\"++\"".to_string());
                labels.push("\"+\"".to_string());
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
        let off = self.lx.pos().offset;
        let mut expected: Vec<String> = self.term_carry_labels(off);
        if self.fact_annot_hangover == Some(off) {
            expected.push("\"[\"".to_string());
        }
        expected.extend(site_labels.iter().map(|l| (*l).to_string()));
        let (found, at) = self.found_token();
        ParseError::Expected {
            found,
            expected,
            at,
        }
    }

    /// The error at a top-level *item* position when no item alternative
    /// matches: the full item-keyword set, with the suggestion machinery of
    /// [`ParseError::ExpectedTheoryItem`] picking near-misses from it.
    fn item_position_error(&mut self) -> ParseError {
        self.expected_theory_item_err(TOP_LEVEL_ITEM_EXPECTS)
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
            // self.skip_ws();
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
        if let Some(id) = self.lx.identifier() {
            return Ok(id);
        }
        if let Some(e) = self.err_reserved_word() {
            return Err(e);
        }
        Err(self.expected_identifier_err(vec!["identifier"]))
    }

    /// The rejection HS `T.identifier` (Token.hs:393-394) performs when the
    /// token here is one of the reserved names `["in","let","rule","diff"]`
    /// (Token.hs:214-230, see line 225), or `None` if it is not.
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
        Some(ParseError::Custom {
            message: format!("`{word}` is a reserved word and cannot be used as an identifier"),
            at: Location::from(pos),
        })
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
        // `commaSep1`, Accountability.hs:30-39, see line 36); the zero-ident form falls back to
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
        self.require_kw("builtins")?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            let name = self.hyphen_identifier()?;
            // HS `builtinTheory = asum $ map (try . extendSig) builtinsNames`
            // (Signature.hs:135): `extendSig` runs per name, right after its
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
    /// `extendSig` equation (Signature.hs:136-138), which only consumes the
    /// symbol.  Names outside HS's table are a parse error there and are
    /// accepted-and-ignored here, as elsewhere in this parser.
    ///
    /// `diffbuiltins` (Signature.hs:141-148), the parser a diff theory uses,
    /// merges the signature with neither check and reserves no names.
    fn enable_builtin(&mut self, name: &str) -> Result<(), ParseError> {
        let Some(syms) = builtin_st_fun_syms(name) else {
            return Ok(());
        };
        // The `MaudeSig`s of these names carry only an enable flag
        // (Term/Maude/Signature.hs:191-196); `mappend` ORs it into the
        // signature.  Recorded for both the diff and non-diff builtins parsers,
        // which merge signatures identically (Signature.hs:102-148).
        match name {
            "diffie-hellman" => self.sig_enable_dh = true,
            "bilinear-pairing" => self.sig_enable_bp = true,
            "xor" => self.sig_enable_xor = true,
            "multiset" => self.sig_enable_mset = true,
            "natural-numbers" => self.sig_enable_nat = true,
            _ => {}
        }
        if !self.is_diff {
            // `functionConflicts` (Signature.hs:107-112): a name the builtin
            // brings that the signature already carries at a DIFFERENT options
            // tuple.  `dest-pairing` is exempt — it is expected to replace the
            // seeded `fst`/`snd` constructors with their destructor variants.
            if name != "dest-pairing" {
                // The comprehension pairs every builtin symbol with every
                // signature entry of the same name, so a name carrying two
                // differing entries is listed twice.
                let mut clashes: Vec<&str> = Vec::new();
                for s in syms {
                    let want = FunOptions::of(s);
                    for (n, o) in &self.fun_syms {
                        if n == s.name && *o != want {
                            clashes.push(s.name);
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
            // `macroConflicts` (Signature.hs:114-119): the same test against
            // the macro names, with no `dest-pairing` exemption and with a
            // single `lookup` (first match) per builtin symbol.
            let mut macro_clashes: Vec<&str> = Vec::new();
            for s in syms {
                let want = FunOptions::of(s);
                if let Some((_, o)) = self.macro_syms.iter().find(|(n, _)| n == s.name) {
                    if *o != want {
                        macro_clashes.push(s.name);
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
                .extend(syms.iter().map(|s| s.name.to_string()));
        }
        // `modifyStateSig (mappend msig)`, whose `unionExceptPairSym`
        // (Term/Maude/Signature.hs:126-146) makes the pair projections
        // exclusive: whichever variant the incoming signature carries evicts
        // the other one.
        for s in syms {
            if s.name == "fst" || s.name == "snd" {
                let evicted = FunOptions {
                    destructor: !s.destructor,
                    ..FunOptions::of(s)
                };
                self.fun_syms
                    .retain(|(n, o)| !(n == s.name && *o == evicted));
            }
            self.insert_fun_sym(s.name, FunOptions::of(s));
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
            Err(idx) => self.fun_syms.insert(idx, (name.to_string(), opts)),
        }
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
        // `option [] $ list functionAttribute` (Signature.hs:186), unless it
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
        opening: (&str, Pos),
        mut elem: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        let (opening, opening_at) = opening;
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
                // the frame of Fact.hs:47's `parens (commaSep pterm)` and
                // every other `commaSep`-then-close context.
                let (found, found_at) = self.found_token();
                let e = self.err_unterminated_delimiter(
                    opening,
                    opening_at,
                    found_at,
                    found,
                    vec![close.into()],
                );
                return Err(e);
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
    /// leaves an `Expect "letter or digit"` (from `alphaNum`, Token.hs:212-213)
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

    /// HS `parens (commaSep typep)` (Theory/Text/Parser/Signature.hs:156) with
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

    /// One `functions:` entry (HS `function`, Signature.hs:183-225).
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
        // HS `function` (Signature.hs:183-225) folds the attribute list into one
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
        // lexeme, i.e. [`Self::err_fail`] at the post-whitespace position.
        let _ = had_attrs;
        let fail = |p: &mut Self, msg: String| p.err_fail(msg);
        // Check (1), Signature.hs:200-209: a name an enabled `builtins:` item
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
                // `conflictingBuiltins` (Signature.hs:203) scans the WHOLE
                // static table, not just the builtins this theory enabled.
                let conflicting: Vec<&str> = BUILTIN_ST_FUN_SYMS
                    .iter()
                    .filter(|(_, syms)| syms.iter().any(|s| s.name == name))
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
        // Check (2), Signature.hs:212-217: the general conflict against the
        // parse-time signature, macro names included.
        if let Some(prev) = self.lookup_fun_options(&name) {
            // Signature.hs:213: `fst`/`snd` may be re-declared at the pair
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
                // Signature.hs:217 returns the EXISTING symbol as a
                // `NoEqUser`: any `[AC]` attribute is dropped, the arity check
                // never runs, and nothing is registered.
                return Ok((
                    FunctionDecl {
                        name,
                        arg_types,
                        out_type,
                        private,
                        destructor,
                        ac: false,
                        ndc,
                        ndc_diff,
                    },
                    had_attrs,
                ));
            }
        }
        if ac {
            // HS rejects a non-binary `[AC]` symbol outright (Signature.hs:220)
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
                self.ac_fun_syms.push(name.clone());
                self.ac_fun_syms.sort();
            }
        } else {
            // HS's `NotAC` branch instead files the symbol under `stFunSyms`
            // (`addFunSym (NoEqUser ...)`, Signature.hs:224), a set insert.
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
        // HS `equations` (Signature.hs:234-239): `convergent` is set only when
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
            // HS `equation` (Signature.hs:245-246) parses both operands with
            // `acterm True llitNoPub`. The `True` (eqn flag) gates multiset/
            // nat/xor/mult/exp operators (but NOT the user-defined AC operators
            // of `acterm`) — matched here by `acterm(true)`, which is what
            // `term(true)` reduces to anyway once those gates are closed.
            // `llitNoPub` (Term.hs:57-58 = `asum [freshTerm <$> freshName,
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
            // (Macro.hs:34-35): a GHC `error`, raised right after the
            // identifier and BEFORE the arguments, so it wins over every later
            // failure in the macro — including a malformed argument list, and
            // the name conflict below that an enabled owning theory would
            // otherwise raise.  Independent of which builtins are enabled.
            if Self::RESERVED_BUILTINS.contains(&name.as_str()) {
                return Err(self.macro_reserved_name_error(&name));
            }
            let opening = ("(", self.lx.pos());
            self.require_punct("(")?;
            // HS `parens $ commaSep lvar` (Macro.hs:29-49, see line 36): trailing comma OK.
            let args = self.sep_end_by(")", opening, |p| p.var_spec())?;
            // HS `unless (length args == length (nub args)) $ error …`
            // (Macro.hs:37-38), the second GHC `error`: `nub` compares FULL
            // `LVar`s, so name, sort and index all count — `m(x, x:pub)` and
            // `m(x.1, x)` pass, `m(x, x)` and `m(x, x:msg)` do not (a
            // prefixless binder is `LSortMsg`, Token.hs:424-433).
            if Self::has_duplicate_macro_arg(&args) {
                return Err(self.macro_duplicate_arg_error(&name));
            }
            self.require_punct("=")?;
            let body = self.term(false)?;
            // HS `macro` rejects a name the signature already carries
            // (Macro.hs:43-44): `op elem map extractName (S.toList
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
            // `(k, Private, Destructor, NotNDC)` (Macro.hs:46), which
            // `function`'s conflict check then sees (Signature.hs:212).
            self.macro_syms.push((
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

    /// HS `reservedBuiltins` (Theory/Text/Parser/Term.hs:74-86) in its order:
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

    /// The `error` of Macro.hs:34-35 — see [`Self::macros`].  Its message is
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
    /// (Macro.hs:37-38) — see [`Self::macros`].  `show` on the `ByteString`
    /// name supplies the double quotes.
    fn macro_duplicate_arg_error(&self, name: &str) -> ParseError {
        self.err_ghc(
            format!("\"{name}\" have two arguments with the same name."),
            Self::macro_error_call_site(Self::MACRO_DUPLICATE_ARG_SITE),
        )
    }

    /// The sort HS's `lvar` (Token.hs:409-437) gives a macro argument, i.e. the
    /// `lvarSort` component of the `LVar` `nub` compares: an explicit prefix or
    /// suffix names it, and a prefixless binder is `LSortMsg`
    /// (Token.hs:424-433) — the sort [`SortHint::Untagged`] stands for here.
    fn macro_arg_sort(v: &VarSpec) -> SuffixSort {
        match v.sort {
            SortHint::Msg | SortHint::Untagged => SuffixSort::Msg,
            SortHint::Pub => SuffixSort::Pub,
            SortHint::Fresh => SuffixSort::Fresh,
            SortHint::Node => SuffixSort::Node,
            SortHint::Nat => SuffixSort::Nat,
            SortHint::Suffix(s) => s,
        }
    }

    /// HS `length args /= length (nub args)` (Macro.hs:37): `nub`'s `Eq LVar`
    /// compares name, sort and index together (LTerm.hs:541-542), so two
    /// arguments collide only when all three agree.
    fn has_duplicate_macro_arg(args: &[VarSpec]) -> bool {
        let mut seen: Vec<(&str, u64, SuffixSort)> = Vec::with_capacity(args.len());
        for a in args {
            let key = (a.name.as_str(), a.idx, Self::macro_arg_sort(a));
            if seen.contains(&key) {
                return true;
            }
            seen.push(key);
        }
        false
    }

    /// The macro-name membership test of Macro.hs:43 — see [`Self::macros`].
    /// `extractName` (Macro.hs:49-50) drops the options, so only names
    /// compare; the reserved builtin names (`mun`, `em`, …) are NOT part of
    /// this set unless a theory flag contributes them (a macro so named never
    /// reaches this check — the reserved-name `error` at Macro.hs:34-35 fires
    /// first).
    fn macro_name_conflicts(&self, name: &str) -> bool {
        self.fun_syms.iter().any(|(n, _)| n == name)
            || self.ac_fun_syms.iter().any(|n| n == name)
            || self.macro_syms.iter().any(|(n, _)| n == name)
            || self.enabled_theory_noeq_syms().any(|s| s.name == name)
    }

    /// HS's `fail $ "Conflicting name for macro " ++ op` (Macro.hs:44), at
    /// the position after the macro body.
    fn macro_conflict_error(&mut self, name: &str) -> ParseError {
        self.err_fail(format!("Conflicting name for macro {name}"))
    }

    fn predicates(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("predicates") {
            self.require_kw("predicate")?;
        }
        self.require_punct(":")?;
        let mut ps = Vec::new();
        loop {
            // HS `predicate … <?> "predicate declaration"` (Signature.hs:270-275):
            // `labels` rewrites a NON-consuming failure, dropping its `Expect`s
            // for the label and keeping `UnExpect`/`Message`.  Only the leading
            // `fact' lvar` can fail without consuming, and this port signals
            // that by leaving the position where the element started.
            let start = self.save();
            let f = match self.fact() {
                Ok(f) => f,
                Err(e) => {
                    return Err(if self.save() == start {
                        self.err_expect(&["predicate declaration"])
                    } else {
                        e
                    });
                }
            };
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
        let opening_at = self.lx.pos();
        if self.try_punct("[") {
            loop {
                self.skip_ws();
                if self.peek_punct("]") {
                    break;
                } else if self.try_kw("left") {
                    attributes.push(RestrictionAttr::LeftRestriction);
                } else if self.try_kw("right") {
                    attributes.push(RestrictionAttr::RightRestriction);
                } else {
                    let (found, found_at) =
                        self.found_token_until(|c| c.is_whitespace() || c == ']');
                    return Err(ParseError::UnknownAttribute {
                        attribute: found.unwrap_or("end of file".to_string()),
                        at: found_at,
                        context: "restriction".into(),
                    });
                }
                if !self.try_punct(",") {
                    break;
                }
            }
            self.require_punct("]").map_err(|_| {
                let (found, found_at) = self.found_token_until(|c| c.is_whitespace() || c == ']');
                self.err_unterminated_delimiter(
                    '[',
                    opening_at,
                    found_at,
                    found,
                    vec!["]".to_string(), "left".to_string(), "right".to_string()],
                )
            })?;
        }
        self.require_punct(":")?;
        let phi = self.double_quoted_formula()?;
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
        self.lx.skip_ws();
        let opening_pos = self.lx.pos();
        self.require_punct("\"")?;
        let f = self.formula()?;
        self.require_punct("\"").map_err(|e| {
            self.err_unterminated_delimiter(
                "\"",
                opening_pos,
                *e.location(),
                e.into_found(),
                vec![
                    "\"".to_string(),
                    "==>".to_string(),
                    "<=>".to_string(),
                    "&".to_string(),
                    "|".to_string(),
                ],
            )
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
        // Dispatch on the `(modulo AC)` head alone.  Intruder-rule names
        // conventionally start with `c` or `d` (HS `intrInfo`,
        // Rule.hs:155-172, see line 169-170), but that prefix is not tested
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
    /// (`"duplicate rule or inconsistent names: …"`, Parser.hs:519-522), which
    /// this port does not implement.
    ///
    /// Equality is on the parsed AST minus the `(modulo E)` head, which HS
    /// discards at parse time (`optional moduloE`, Parser/Rule.hs:100-104).
    /// Two corners are knowingly coarser than HS, which compares rules AFTER
    /// applying the `let` substitution and appending the minted `Restr_*`
    /// actions: same-name rules that differ only in `let`-bindings yet expand
    /// to the same rule reject here where HS accepts, and vice-versa shapes
    /// cannot arise (byte-identical sources always compare equal).
    fn guard_duplicate_rule(&mut self, r: &Rule) -> Result<(), ParseError> {
        if self.is_diff {
            return Ok(());
        }
        for i in 1..=r.embedded_restrictions.len() {
            // HS `fromRuleRestriction (rname ++ "_" ++ show i)` with
            // `restrPrefix = "Restr_"` (Model/Restriction.hs:129-149).
            let rstr_name = format!("Restr_{}_{}", r.name, i);
            if self.seen_restriction_names.contains(&rstr_name) {
                // TODO: Better error once we have locations for the rules inlined restrictions/actions
                return Err(self.item_fail(format!("duplicate restriction: {rstr_name}")));
            }
        }
        if let Some(first) = self.seen_rules.iter().find(|p| p.name == r.name) {
            let differs = first.attributes != r.attributes
                || first.let_block != r.let_block
                || first.premises != r.premises
                || first.actions != r.actions
                || first.conclusions != r.conclusions
                || first.embedded_restrictions != r.embedded_restrictions
                || first.variants != r.variants
                || first.left_right != r.left_right;
            if differs {
                // `"duplicate rule: " ++ render (prettyRuleName …)`
                // (Exceptions.hs:38).  `prettyProtoRuleName` is
                // `prefixIfReserved` (Model/Rule.hs:1287-1290), which only
                // rewrites reserved names / leading `_` — both unreachable
                // here (`protoRule` rejects reserved rule names and
                // identifiers cannot start with `_`), so the name is verbatim.
                let e = ParseError::DuplicateRule {
                    name: r.name.clone(),
                    first_at: first.location,
                    second_at: r.location,
                };
                return Err(e);
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

    /// A failure at the position an item's parse just finished — the
    /// duplicate-rule/-restriction guards.
    fn item_fail(&mut self, msg: String) -> ParseError {
        self.err_fail(msg)
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
        self.skip_ws();
        let start = self.lx.pos();
        let kw_end = self.lx.pos().offset + "rule".len();
        self.require_kw("rule")?;
        let modulo = self.try_modulo();
        let name = self.rule_name_ident(kw_end)?;
        let had_attributes = self.peek_punct("[");
        let attributes = self.rule_attributes()?;
        self.require_rule_colon(had_attributes)?;
        // Optional let block.
        let (let_block, premises) = if self.at_keyword("let") {
            (self.parse_let_block()?, self.fact_list()?)
        } else {
            (vec![], self.premises_after_absent_let()?)
        };
        // Actions / restrictions either `--[..]->` or `-->`
        let (actions, embedded_restrictions) = self.parse_actions_and_restrictions()?;
        let conclusions = self.fact_list()?;
        // We are not including variants and left/right variants in the location
        let end = self.lx.pos();
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
            // HS `option [] $ symbol "variants" *> commaSep1 protoRuleAC`
            // (Rule.hs:134) stops here without consuming, leaving its
            // `Expect "\"variants\""` for the next error raised at this offset.
            // Only `protoRule` has this trailing block; `diffRule` (Rule.hs:120)
            // ends in an `optionMaybe (symbol "left" *> …)` instead, so a diff
            // theory's rules leave a different label that this port does not
            // track.
            if !self.is_diff {
                self.set_item_hangover(&["\"variants\""]);
            }
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
        let location = Location::from_positions(start, end);
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
            location,
        })
    }

    fn parse_rule_ac(&mut self) -> Result<Rule, ParseError> {
        let start = self.lx.pos();
        self.require_kw("rule")?;
        // HS `protoRuleACInfo`/`intrRule` (Rule.hs:137-138/157) sequence a
        // non-optional `moduloAC` here (`symbol "rule" *> moduloAC *> ...`).
        // This port relaxes that: `try_modulo` returns `None` when the
        // `(modulo AC)` head is absent and parsing proceeds. (More lenient than
        // Haskell, but still accepts all valid Haskell input.)
        let modulo = self.try_modulo();
        let name = self.rule_name_ident(usize::MAX)?;
        let had_attributes = self.peek_punct("[");
        let attributes = self.rule_attributes()?;
        self.require_rule_colon(had_attributes)?;
        let (let_block, premises) = if self.at_keyword("let") {
            (self.parse_let_block()?, self.fact_list()?)
        } else {
            (vec![], self.premises_after_absent_let()?)
        };
        let (actions, embedded_restrictions) = self.parse_actions_and_restrictions()?;
        let conclusions = self.fact_list()?;
        let end = self.lx.pos();
        let location = Location::from_positions(start, end);
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
            location,
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
    /// `protoRuleACInfo`, Rule.hs:100-107 / 137-145).
    ///
    /// It is preceded by `ruleAttributesp = option mempty (…list ruleAttribute)`
    /// (Rule.hs:97-98).  When the attribute list is absent, `option` returns
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
        let opening_at = self.lx.pos();
        if !self.try_punct("[") {
            return Ok(attrs);
        }
        // HS `list p = brackets (commaSep p)` accepts zero attributes, so an
        // empty `[]` must not reach the attribute loop below.
        if self.try_punct("]") {
            return Ok(attrs);
        }
        loop {
            self.skip_ws();
            let start = self.save();
            // colour=, color=
            let kind: Option<RuleAttrKind> = if self.try_kw("colour") || self.try_kw("color") {
                self.require_punct("=")?;
                let c = self.color_attr_value()?;
                Some(RuleAttrKind::Color(c))
            } else if self.try_kw("process") {
                // HS `ruleAttribute` (Parser/Rule.hs:68-93, see line 72) `parseAndIgnore`s
                // `process=`: the value is parsed and DISCARDED, leaving
                // `ruleProcess = Nothing`, so a user-written `process=` is never
                // rendered.  `process=` is only emitted by HS for
                // SAPIC-translation-generated rules (via `ruleProcess`, not this
                // parser).  Mirror that: read and drop the value, push nothing.
                self.require_punct("=")?;
                let _ = self.read_balanced_token()?;
                None
            } else if self.try_kw("no_derivcheck") {
                Some(RuleAttrKind::NoDerivCheck)
            } else if self.try_kw("role") {
                self.require_punct("=")?;
                let s = self.string_literal_or_squoted()?;
                Some(RuleAttrKind::Role(s))
            } else if self.try_kw("issapicrule") {
                Some(RuleAttrKind::IsSapicRule)
            } else {
                // External attribute: x-<id> [= raw]
                if let Some(ext) = self.lx.ext_identifier() {
                    let val = if self.try_punct("=") {
                        Some(self.read_balanced_token()?)
                    } else {
                        None
                    };
                    Some(RuleAttrKind::External(ext, val))
                } else {
                    if self.peek_punct(":") || self.peek_punct("]") {
                        // Peek a ":" so that `rule name[:` fails with an unterminated
                        // delimiter error rather than an unknown attribute error.
                        // Peek a "]" so that trailing commas are allowed.
                        break;
                    }
                    let (found, at) =
                        self.found_token_until(|c| c == ']' || c == ',' || c.is_whitespace());
                    return Err(ParseError::UnknownAttribute {
                        attribute: found.unwrap_or("EOF".to_string()),
                        at,
                        context: "rule".into(),
                    });
                }
            };
            let end = self.lx.pos();
            if let Some(k) = kind {
                attrs.push(RuleAttr {
                    kind: k,
                    location: Location::from_positions(start, end),
                });
            }
            if !self.try_punct(",") {
                break;
            }
        }
        self.require_punct("]").map_err(|_| {
            let (found, found_at) = self.found_token_until(|c| c.is_whitespace() || c == ']');
            self.err_unterminated_delimiter("[", opening_at, found_at, found, vec!["]".into()])
        })?;
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
        if quoted && !self.lx.eat_str("'") {
            // Closing `'` fails where `many1 hexDigit` stopped.
            return Err(self.err_expect(&["hexadecimal digit", "\"'\""]));
        }
        self.skip_ws();
        if code.len() != 6 {
            return Err(self.err_fail(format!("Color code \"{code}\" could not be parsed to RGB")));
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

            let lhs = self.term(false)?;

            self.require_punct("=")?;

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

    /// The rule-name `identifier`, with the parsec frame HS leaves when it is
    /// missing.  `moduloE`'s failed `option` probe puts `Expect "\"(\""`
    /// ahead of `identifier` at the name position (Rule.hs:127-131, via
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
        self.skip_ws();
        let mut labels: Vec<&str> = vec!["\"(\"", "identifier"];
        if self.lx.pos().offset == kw_end_offset {
            labels.push("letter");
            labels.push("\"{*\"");
        }
        Err(self.err_expect(&labels))
    }

    /// The premise [`Parser::fact_list`] of a rule whose optional `let` block
    /// is absent.  HS sequences `option emptySubst letBlock` before
    /// `genericRule` (Rule.hs:131, :151): the failed non-consuming `letBlock`
    /// leaves `Expect "\"let\""` at the probe offset, and a premise-`[`
    /// failure at that SAME offset merges the two — `expecting "let" or "["`
    /// (parsec merge is position-gated, so a failure deeper inside the list
    /// keeps its own labels).
    fn premises_after_absent_let(&mut self) -> Result<Vec<Fact>, ParseError> {
        self.skip_ws();
        let probe_offset = self.lx.pos().offset;
        self.fact_list().map_err(|mut e| {
            if e.location().start == probe_offset {
                e.add_expected("\"let\"".to_string());
            }
            e
        })
    }

    fn fact_list(&mut self) -> Result<Vec<Fact>, ParseError> {
        let opening = ("[", self.lx.pos());
        self.require_punct("[")?;
        // HS `list (fact ...)` (Rule.hs:181-191, see line 183/188) = `brackets . commaSep`
        // (Token.hs:362-363) with `commaSep = sepEndBy comma`: the list may
        // be empty and a trailing comma before `]` is OK.
        self.sep_end_by("]", opening, |p| p.fact())
    }

    fn fact_or_restr(&mut self) -> Result<FactOrRestr, ParseError> {
        // `_restrict(formula)` or fact.
        if self.try_kw("_restrict") {
            let opening_at = self.lx.pos();
            self.require_punct("(")?;
            let phi = self.formula()?;
            self.require_punct(")").map_err(|_| {
                let (found, found_at) = self.found_token();
                self.err_unterminated_delimiter("(", opening_at, found_at, found, vec![")".into()])
            })?;
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
        self.skip_ws();
        let trace_q_pos = self.lx.pos();
        let trace_identifier = self
            .lx
            .peek_until(|c| !c.is_alphabetic() && c != '-')
            // Filter out edge case: `lx.peek_until` returns `Some("")` if
            // the first char already fulfills the stopping condition.
            .filter(|s| !s.is_empty());
        let trace_quantifier = match trace_identifier {
            Some(s) if s == "all-traces" => {
                self.lx.eat_str(s);
                TraceQuantifier::AllTraces
            }
            Some(s) if s == "exists-trace" => {
                self.lx.eat_str(s);
                TraceQuantifier::ExistsTrace
            }
            None => TraceQuantifier::AllTraces,
            Some(other) => {
                return Err(ParseError::UnexpectedKeyword {
                    found: Some(other.into()),
                    expected: vec!["all-traces".into(), "exists-trace".into()],
                    at: Location::location_of(&Some(other), trace_q_pos),
                });
            }
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
                let opening = ("[", self.lx.pos());
                self.require_punct("[")?;
                // HS `list constructorp` (Lemma.hs:39-53, see line 49) = `brackets . commaSep`:
                // trailing comma before `]` is permitted.
                let outs = self.sep_end_by("]", opening, |p| p.ident())?;
                attrs.push(LemmaAttr::Output(outs));
            } else if self.try_kw("left") {
                attrs.push(LemmaAttr::Left);
            } else if self.try_kw("right") {
                attrs.push(LemmaAttr::Right);
            } else {
                if self.peek_punct(":") || self.peek_punct("]") {
                    // Peek a ":" so that `lemma name[:` fails with an unterminated
                    // delimiter error rather than an unknown attribute error.
                    // Peek a "]" so that trailing commas are allowed.
                    break;
                }

                let (found, at) =
                    self.found_token_until(|c| c == ']' || c == ',' || c.is_whitespace());
                return Err(ParseError::UnknownAttribute {
                    attribute: found.unwrap_or("EOF".to_string()),
                    at,
                    context: "lemma".into(),
                });
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
        let opening = ("(", self.lx.pos());
        let vars = if self.try_punct("(") {
            // HS `parens $ commaSep sapicvar` (Sapic.hs:64-72, see line 69): trailing comma OK.
            Some(self.sep_end_by(")", opening, |p| p.var_spec())?)
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
            let opening = ("(", self.lx.pos());
            let args = if self.try_punct("(") {
                // HS `parens $ commaSep (msetterm ...)` (Sapic.hs:224-312, see line 296):
                // trailing comma before `)` is permitted.
                self.sep_end_by(")", opening, |p| p.term(false))?
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
        let start = self.lx.pos();
        let persistent = self.try_punct("!");
        let name_pos = self.lx.pos();
        let name = self.ident()?;
        if !name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            let at = Location::location_of(&Some(&name), name_pos);
            return Err(ParseError::FactNameMustStartWithUppercase { name, at });
        }
        let opening = ("(", self.lx.pos());
        self.require_punct("(")?;
        // HS `parens (commaSep pterm)` (Fact.hs:39-63, see line 47): trailing comma OK.
        let args = self.sep_end_by(")", opening, |p| p.term(false))?;
        let mut annotations = Vec::new();
        // `option [] $ list factAnnotation` (Fact.hs:48): when no annotation
        // list follows, the failed `[` attempt leaves its label at the
        // position after the closing `)` lexeme — merged into the expected
        // set of a failure raised exactly there.
        self.skip_ws();
        let annot_attempt = self.lx.pos().offset;
        self.fact_annot_hangover = if self.peek_punct("[") {
            None
        } else {
            Some(annot_attempt)
        };
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
        let end = self.lx.pos();
        let location = Location::from_positions(start, end);
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
                location,
            });
        }
        Ok(Fact {
            persistent,
            name,
            args,
            annotations,
            location,
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
            Ok(Formula::iff(lhs, rhs))
        } else {
            Ok(lhs)
        }
    }

    fn implies(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.disjuncts()?;
        if self.try_punct("==>") || self.try_punct("⇒") {
            let rhs = self.implies()?;
            Ok(Formula::implies(lhs, rhs))
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
                lhs = Formula::or(lhs, rhs);
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
                lhs = Formula::and(lhs, rhs);
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn negation(&mut self) -> Result<Formula, ParseError> {
        let start = self.save().into();
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.fatom()?;
            Ok(Formula::not(f, start))
        } else {
            self.fatom()
        }
    }

    fn fatom(&mut self) -> Result<Formula, ParseError> {
        self.skip_ws();
        let start = self.save();
        let kind = self.fatom_kind()?;
        let end = self.save();
        Ok(Formula::new(kind, Location::from_positions(start, end)))
    }

    fn fatom_kind(&mut self) -> Result<FormulaKind, ParseError> {
        self.skip_ws();
        if self.try_kw("F") || self.try_punct("⊥") {
            return Ok(FormulaKind::False);
        }
        if self.try_kw("T") || self.try_punct("⊤") {
            return Ok(FormulaKind::True);
        }
        // Quantifiers: All / ∀ / Ex / ∃
        if self.try_kw("All") || self.try_punct("∀") {
            let vs = self.quantifier_binders()?;
            let f = self.iff()?;
            return Ok(FormulaKind::Forall(vs, Box::new(f)));
        }
        if self.try_kw("Ex") || self.try_punct("∃") {
            let vs = self.quantifier_binders()?;
            let f = self.iff()?;
            return Ok(FormulaKind::Exists(vs, Box::new(f)));
        }
        // Parenthesised formula — backtrack to term-relational on failure,
        // since e.g. `(a+z) = b` should parse as a relational equality atom
        // whose LHS happens to be a parenthesised term.
        if self.lx.peek() == Some('(') {
            let save_p = self.save();
            self.lx.bump();
            self.skip_ws();
            // No other atom can consume a leading `(`, so this is an unterminated parenthesised formula.
            let f = self.iff()?;
            self.require_punct(")").map_err(|_| {
                let (found, found_at) = self.found_token();
                self.err_unterminated_delimiter("(", save_p, found_at, found, vec![")".to_string()])
            })?;
            return Ok(f.kind);
        }
        // Atom: try last(t), action f@t, equality, less, subterm, smaller, predicate
        if self.try_kw("last") {
            let opening_at = self.lx.pos();
            self.require_punct("(")?;
            let t = self.term(false)?;
            self.require_punct(")").map_err(|_| {
                let (found, found_at) = self.found_token();
                self.err_unterminated_delimiter(
                    "(",
                    opening_at,
                    found_at,
                    found,
                    vec![")".to_string()],
                )
            })?;
            return Ok(FormulaKind::Atom(Atom::Last(t)));
        }
        // Try fact@t (action atom)
        let save_f = self.save();
        if let Ok(f) = self.fact() {
            if self.try_punct("@") {
                let t = self.term(false)?;
                return Ok(FormulaKind::Atom(Atom::Action(f, t)));
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
                return Ok(FormulaKind::Atom(Atom::Pred(f)));
            }
        }
        self.restore(save_f);
        // Try term-level atom: t = t / t < t / t << t / t (<) t
        let start = self.save();
        let lhs = self.term(false)?;
        if self.try_punct("=") {
            let rhs = self.term(false)?;
            return Ok(FormulaKind::Atom(Atom::Eq(lhs, rhs)));
        }
        if self.try_punct("<<") || self.try_punct("⊏") {
            let rhs = self.term(false)?;
            return Ok(FormulaKind::Atom(Atom::Subterm(lhs, rhs)));
        }
        if self.try_punct("(<)") {
            let rhs = self.term(false)?;
            let end = self.save();
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
                location: Location::from_positions(start, end),
            };
            return Ok(FormulaKind::Atom(Atom::Pred(fact)));
        }
        if self.try_punct("<") {
            // HS `blatom` (Formula.hs:44-60, see line 49) restricts both operands of `<` to
            // node/timepoint variables: `Less <$> try (nodevarTerm <* opLess)
            // <*> nodevarTerm`. This structural port intentionally accepts any
            // `term` on both sides (parser-level permissiveness); the sort
            // restriction is deferred to elaboration. Valid theories (which use
            // timepoint vars with `<`) parse identically.
            let rhs = self.term(false)?;
            return Ok(FormulaKind::Atom(Atom::Less(lhs, rhs)));
        }
        // No relational operator follows the term.  HS `blatom`'s remaining
        // alternatives (Formula.hs:45-57): the `Pred` fact (alt 7 — reachable
        // here when `peek_atom_relop` diverted a fact whose relop turned out
        // to belong AFTER it, e.g. `P3(x) = y` with `P3` not a function), then
        // the UN-try'd node-equality `nodevarTerm <* opEqual` (alt 8), whose
        // consumed failure aborts the whole formula parse and is the frame
        // the user sees.
        let after_lhs = self.save();
        self.restore(save_f);
        if let Ok(f) = self.fact() {
            return Ok(FormulaKind::Atom(Atom::Pred(f)));
        }
        self.restore(save_f);
        Err(self.formula_atom_tail_error(save_f, after_lhs))
    }

    /// The error HS's formula-atom alternation reports once every `blatom`
    /// alternative has failed for the atom that starts at `atom_start`
    /// (Formula.hs:44-60).
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
            let mut labels: Vec<&str> = Vec::new();
            if ident_end == self.lx.pos().offset {
                labels.push("letter or digit");
            }
            if !idx_spent {
                labels.push("\".\"");
            }
            labels.push("\"=\"");
            return self.err_expect(&labels);
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
    /// `*`, `^`); the user-declared `[AC]` infix operators of [`Self::acterm`]
    /// stay open, as in HS's `acterm True llitNoPub`.
    fn term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.tupleterm(eqn)
    }

    /// HS `tupleterm`'s `chainr1 (msetterm …) (… <$ comma)` (Term.hs:211-212)
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

    fn msetterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let lhs = self.msetterm_inner(eqn)?;
        // The outermost chain level finishing records the carried error the
        // enclosing grammar merges into a failure raised right here (see
        // [`Parser::term_carry`]).
        self.finish_term_carry(eqn);
        Ok(lhs)
    }

    fn msetterm_inner(&mut self, eqn: bool) -> Result<Term, ParseError> {
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
            return self.acterm(eqn);
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
        let mut lhs = self.acterm(eqn)?;
        // HS `expterm` is "a left-associative sequence of exponentiations"
        // (`chainl1`, Parser/Term.hs:174-176), so build left-associative
        // `^` trees here to match.
        while self.try_punct("^") {
            let rhs = self.acterm(eqn)?;
            lhs = Term::BinOp(BinOp::Exp, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
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
        let mut lhs = self.ac_chain(level + 1, eqn)?;
        // HS `opAC (op, _) = symbol_ (BC.unpack op)`, i.e. the symbol's own name
        // as a plain token.  `try_kw` adds a word boundary that HS's `symbol`
        // lacks, so HS would also accept the name as a PREFIX of the following
        // token (`f(x) fg(y)` parsing as `f(f(x), g(y))` for an AC symbol `f`);
        // such input is not valid syntax in any theory and errors here instead.
        while self.try_kw(&op) {
            let rhs = self.ac_chain(level + 1, eqn)?;
            lhs = Term::BinOp(
                BinOp::AcFct(intern_ac_name(&op)),
                Box::new(lhs),
                Box::new(rhs),
            );
        }
        Ok(lhs)
    }

    /// One atomic term, maintaining [`Parser::var_dot_hangover`]: the variable
    /// return sites inside [`Self::atom_term_inner`] set it via
    /// [`Self::note_var_dot_hangover`], and every atom whose LAST lexeme is not
    /// the variable's identifier clears it here.  `AlgApp` and `PatMatch` are
    /// transparent — their rightmost lexeme belongs to the sub-atom that
    /// already maintained the flag (HS `binaryAlgApp`'s trailing `arg2 <- term
    /// eqn plit`, Term.hs:109-121).
    fn atom_term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let t = self.atom_term_inner(eqn)?;
        if !matches!(t, Term::Var(_) | Term::AlgApp(..) | Term::PatMatch(_)) {
            self.var_dot_hangover = false;
        }
        Ok(t)
    }

    /// Set [`Parser::var_dot_hangover`] for the variable atom just consumed.
    ///
    /// HS leaves the `Expect "\".\""` at the current position iff the
    /// variable's LAST lexeme was its `identifier` — i.e. no explicit
    /// `.<index>` was consumed (`option 0 (try (dot *> natural))`,
    /// Token.hs:395-400, whose one attempt is spent once it succeeds), no
    /// `:sort` suffix follows (`sortedLVar`'s suffix branch ends in
    /// `symbol_ (sortSuffix s)`, Token.hs:409-421), and the name is not one
    /// `nullaryApp` claims instead of `plit` — an arity-0 symbol of
    /// `funSyms ∪ macroNames`, matched by `symbol`, not `indexedIdentifier`
    /// (Term.hs:148,158-163).  The explicit-index case (including `.0`) is
    /// what [`Parser::dot_index_consumed`] records: every variable parse runs
    /// [`Self::try_dot_index`] right after its identifier, so at this point
    /// that field is the just-parsed variable's.
    fn note_var_dot_hangover(&mut self, v: &VarSpec) {
        self.var_dot_hangover = !self.dot_index_consumed
            && !matches!(v.sort, SortHint::Suffix(_))
            && v.typ.is_none()
            && !self.is_nullary_sym(&v.name);
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
    /// `Some(NoEq)`'s applications are arity-checked (`Term.hs:97-100`);
    /// `Some(Ac)`'s are not (the check is gated on `NotAC`).  `None` is HS's
    /// `fail "unknown operator ..."`, which the try-wrapped application
    /// converts into a backtrack.
    fn lookup_arity(&self, op: &str) -> Option<ArityRes> {
        let mut best: Option<(usize, u8, u8, u8)> = None;
        let mut arity = 0usize;
        for (n, o) in &self.fun_syms {
            if n == op {
                let k = o.ord_key();
                if best.is_none_or(|b| k < b) {
                    best = Some(k);
                    arity = o.arity;
                }
            }
        }
        for s in self.enabled_theory_noeq_syms() {
            if s.name == op {
                let o = FunOptions::of(s);
                let k = o.ord_key();
                if best.is_none_or(|b| k < b) {
                    best = Some(k);
                    arity = o.arity;
                }
            }
        }
        if best.is_some() {
            return Some(ArityRes::NoEq { arity });
        }
        if self.ac_fun_syms.iter().any(|n| n == op) {
            return Some(ArityRes::Ac);
        }
        if let Some((_, o)) = self.macro_syms.iter().find(|(n, _)| n == op) {
            return Some(ArityRes::NoEq { arity: o.arity });
        }
        if op == "em" {
            // The appended `(emapSymString, (2,Public,Constructor,NotNDC))`
            // row: `naryOpApp` special-cases the NAME into `fAppC EMap`
            // (Term.hs:102-103), which the readers resolve from the `em`
            // application node; the arity check runs like any NoEq's.
            return Some(ArityRes::NoEq { arity: 2 });
        }
        None
    }

    /// Whether `name` is an arity-0 symbol HS `nullaryApp` (Term.hs:158-163)
    /// parses via `symbol` — searched over `funSyms maudeSig` (the subterm
    /// signature plus the enabled theories' symbols) and `macroNames`.
    fn is_nullary_sym(&self, name: &str) -> bool {
        self.fun_syms
            .iter()
            .chain(self.macro_syms.iter())
            .any(|(n, o)| n == name && o.arity == 0)
            || self
                .enabled_theory_noeq_syms()
                .any(|s| s.name == name && s.arity == 0)
    }

    /// The theory-level `NoEq` symbols the enabled signature bits fold into
    /// `funSyms` — see [`DH_THEORY_NOEQ_SYMS`].
    fn enabled_theory_noeq_syms(&self) -> impl Iterator<Item = &'static BuiltinFunSym> {
        [
            (
                self.sig_enable_dh || self.sig_enable_bp,
                DH_THEORY_NOEQ_SYMS,
            ),
            (self.sig_enable_bp, BP_THEORY_NOEQ_SYMS),
            (self.sig_enable_xor, XOR_THEORY_NOEQ_SYMS),
            (self.sig_enable_nat, NAT_THEORY_NOEQ_SYMS),
        ]
        .into_iter()
        .filter(|(enabled, _)| *enabled)
        .flat_map(|(_, syms)| syms.iter())
    }

    /// One atomic term.
    fn atom_term_inner(&mut self, eqn: bool) -> Result<Term, ParseError> {
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
        let opening_at = self.save();
        if self.try_punct("(") {
            let t = self.msetterm(eqn)?;
            // `(` … `)` is grouping only: Tamarin spells pairs `<a, b>`, so a
            // comma is not accepted here — HS `parens (msetterm eqn plit)`
            // (Term.hs:141), whose closing `symbol ")"` merges the term's
            // hangovers when it fails.
            if !self.try_punct(")") {
                let (found, found_at) = self.found_token();
                return Err(self.err_unterminated_delimiter(
                    "(",
                    opening_at,
                    found_at,
                    found,
                    vec![")".into()],
                ));
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
            let opening_at = self.save();
            let r = self.lx.rest();
            if !r.starts_with("<-") {
                self.lx.bump(); // consume '<'
                self.skip_ws();
                // HS `pairing = angled (tupleterm eqn plit)` (Term.hs:157) with
                // `tupleterm = chainr1 (msetterm ...) (... <$ comma)`
                // (Term.hs:211-212). `chainr1` requires >=1 operand, so the
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
                // `chainr1`'s failed `comma` and `angled`'s closing `symbol
                // ">"` both sit at the last operand's stop position, merged
                // with its hangovers.
                if !self.try_punct(">") {
                    let (found, found_at) = self.found_token();
                    return Err(self.err_unterminated_delimiter(
                        "<",
                        opening_at,
                        found_at,
                        found,
                        vec!["\",\"".into(), "\">\"".into()],
                    ));
                }
                // The atom's last lexeme is the `>`, even when a singleton
                // `<a>` collapses to its operand's node.
                self.var_dot_hangover = false;
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
                        self.note_var_dot_hangover(&v);
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
        // diff(a, b) — HS `diffOp = symbol "diff" *> parens ...` (Term.hs:123-135, see line 125).
        // `diff` is a reserved name (Token.hs:214-230, see line 225) so it is NOT an identifier and
        // must be matched as a keyword here, BEFORE the identifier path. The
        // word-boundary check in `peek_symbol` keeps `diffuse(...)` an identifier
        // (function application), matching HS where `naryOpApp` handles it.
        if self.lx.peek_symbol("diff") {
            self.skip_ws();
            for _ in 0.."diff".len() {
                self.lx.bump();
            }
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
                // `diffOp`'s three `fail`s, in HS's order (Term.hs:126-132): the
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
            // `diff` not followed by `(`: no other `term` alternative can
            // accept the reserved word, so the term parse fails here.
            return Err(self.err_expect(&["term"]));
        }
        // Identifier — could be: function application f(...), algebraic
        // application f{a}b, sort-suffixed var x:msg, or a bare variable /
        // nullary function.
        let save_id = self.save();
        if let Some(id) = self.lx.identifier() {
            // HS `naryOpApp`/`binaryAlgApp` reject a reserved builtin name in
            // an `equations:` context with a GHC `error` (Term.hs:90-92,
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
            let opening_at = self.save();
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
                    self.note_var_dot_hangover(&v);
                    return Ok(Term::Var(v));
                }
                if self.resolve_prefix_apps {
                    // HS resolves the head through `lookupArity` and parses
                    // the arity the lookup returned (`naryOpApp`,
                    // Term.hs:88-105).  On ANY failure — unknown operator,
                    // arity mismatch, or a malformed argument list — the
                    // try-wrapped application backtracks wholesale and the
                    // name reparses as `plit`'s variable below; the next
                    // token then breaks the enclosing grammar, which is where
                    // the user-visible frame comes from.  Only the GHC
                    // `error`s escape.
                    if let Some(res) = self.lookup_arity(&id) {
                        let save_app = self.save();
                        // TODO: Surface the error here instead of restoring in the `Err(_)` case.
                        // TODO: Since we have already parsed a `(`, we know that parsing will fail.
                        // return self.prefix_app_args(&id, res, eqn);
                        match self.prefix_app_args(&id, res, eqn) {
                            Ok(t) => return Ok(t),
                            Err(e) if matches!(e, ParseError::Abort { .. }) => return Err(e),
                            Err(_) => self.restore(save_app),
                        }
                    }
                } else {
                    // Structural mode ([`parse_term_str`]): accept any
                    // application shape, strictly comma-separated.
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
                        self.require_punct(")").map_err(|_| {
                            let (found, found_at) = self.found_token();
                            self.err_unterminated_delimiter(
                                "(",
                                opening_at,
                                found_at,
                                found,
                                vec![")".into()],
                            )
                        })?;
                    }
                    return Ok(Term::App(id, ts));
                }
            } else {
                let opening_at = self.save();
                if self.lx.peek() == Some('{') {
                    if self.resolve_prefix_apps {
                        // HS `binaryAlgApp` (Term.hs:109-121): same lookup, arity
                        // fixed at 2, same wholesale backtrack on failure.
                        if let Some(res) = self.lookup_arity(&id) {
                            let save_app = self.save();
                            // TODO: Surface the error here instead of restoring in the `Err(_)` case.
                            // TODO: Since we have already parsed a `{`, we know that parsing will fail.
                            // return self.binary_alg_app(&id, res, eqn);
                            match self.binary_alg_app(&id, res, eqn) {
                                Ok(t) => return Ok(t),
                                Err(e) if matches!(e, ParseError::Abort { .. }) => return Err(e),
                                Err(_) => self.restore(save_app),
                            }
                        }
                    } else {
                        self.lx.bump();
                        self.skip_ws();
                        let arg1 = self.tuple_contents(eqn)?;
                        self.require_punct("}").map_err(|_| {
                            let (found, found_at) = self.found_token();
                            self.err_unterminated_delimiter(
                                "{",
                                opening_at,
                                found_at,
                                found,
                                vec!["}".into()],
                            )
                        })?;
                        let arg2 = self.atom_term(eqn)?;
                        return Ok(Term::AlgApp(id, Box::new(arg1), Box::new(arg2)));
                    }
                }
            }
            // Bare identifier: untagged variable. Optionally with index `.<n>`
            // (only consumes `.` if followed by a digit) and optionally with
            // sort suffix `:msg|pub|fresh|node|nat` or a SAPIC type annotation.
            // Also the landing site of the application backtracks above, where
            // HS's `plit` reparses the name (leaving the following `(`/`{` for
            // the enclosing grammar to choke on).  A failed application parse
            // may have clobbered `last_ident_end` with a nested argument's, so
            // re-record this name's for `note_var_dot_hangover`.
            self.last_ident_end = Some(self.ident_end_from(save_id, &id));
            let idx = self.try_dot_index();
            let v = VarSpec {
                name: id,
                idx,
                sort: SortHint::Untagged,
                typ: None,
            };
            let v = self.attach_sort_suffix(v)?;
            self.note_var_dot_hangover(&v);
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

    /// The `error, called at <…>` location of `naryOpApp`'s reserved-name
    /// rejection (Theory/Text/Parser/Term.hs:92:9) as the pinned oracle build
    /// prints it — same package id as `macro`'s errors.
    fn term_reserved_name_call_site() -> String {
        format!(
            "src/Theory/Text/Parser/Term.hs:92:9 in {}:Theory.Text.Parser.Term",
            Self::MACRO_ERROR_PACKAGE
        )
    }

    /// HS `naryOpApp`'s argument parse after `lookupArity` succeeded
    /// (Term.hs:93-105), starting at the opening `(`:
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
    /// (see the divergence note in the task fixtures).
    ///
    /// Every `Err` return is discarded by the caller's backtrack, mirroring
    /// the enclosing `try` — the messages never surface.
    fn prefix_app_args(&mut self, id: &str, res: ArityRes, eqn: bool) -> Result<Term, ParseError> {
        // the '(' the caller peeked
        let opening = ("(", self.save());
        self.lx.bump();
        self.skip_ws();
        match res {
            ArityRes::NoEq { arity: 1 } => {
                let arg = self.tuple_contents(eqn)?;
                self.require_punct(")").map_err(|_| {
                    let (found, found_at) = self.found_token();
                    self.err_unterminated_delimiter(
                        "(",
                        opening.1,
                        found_at,
                        found,
                        vec![")".into()],
                    )
                })?;
                Ok(Term::App(id.to_string(), vec![arg]))
            }
            ArityRes::NoEq { arity } => {
                let ts = self.sep_end_by(")", opening, |p| p.msetterm(eqn))?;
                if ts.len() != arity {
                    return Err(self.err(format!(
                        "operator `{id}' has arity {arity}, but here it is used with arity {}",
                        ts.len()
                    )));
                }
                Ok(Term::App(id.to_string(), ts))
            }
            ArityRes::Ac => {
                let ts = self.sep_end_by(")", opening, |p| p.msetterm(eqn))?;
                let sym = intern_ac_name(id);
                let mut it = ts.into_iter();
                match (it.next(), it.next()) {
                    (None, _) => Ok(Term::App(id.to_string(), Vec::new())),
                    (Some(a), None) => {
                        // The collapsed term IS the argument, but the atom's
                        // last lexeme is this application's `)` — no variable
                        // hangover survives even when the argument was one.
                        self.var_dot_hangover = false;
                        self.var_hangover_ident_end = None;
                        Ok(a)
                    }
                    (Some(a), Some(b)) => {
                        let mut t = Term::BinOp(BinOp::AcFct(sym), Box::new(a), Box::new(b));
                        for x in it {
                            t = Term::BinOp(BinOp::AcFct(sym), Box::new(t), Box::new(x));
                        }
                        Ok(t)
                    }
                }
            }
        }
    }

    /// HS `binaryAlgApp` (Term.hs:109-121) after `lookupArity` succeeded,
    /// starting at the opening `{`: `op{t1}t2` parses `braced (tupleterm …)`
    /// then a trailing atom (`term eqn plit`), requires arity 2 (`fail`
    /// otherwise — discarded by the caller's backtrack), and builds
    /// `fAppNoEq`/`fAppAC` by the head's AC state.  There is no `em` special
    /// case here (`naryOpApp`'s Term.hs:103 is prefix-only).
    fn binary_alg_app(&mut self, id: &str, res: ArityRes, eqn: bool) -> Result<Term, ParseError> {
        // the '{' the caller peeked
        let opening_at = self.save();
        self.lx.bump();
        self.skip_ws();
        let arg1 = self.tuple_contents(eqn)?;
        self.require_punct("}").map_err(|_| {
            let (found, found_at) = self.found_token();
            self.err_unterminated_delimiter("{", opening_at, found_at, found, vec!["}".into()])
        })?;
        let arg2 = self.atom_term(eqn)?;
        match res {
            ArityRes::Ac => Ok(Term::BinOp(
                BinOp::AcFct(intern_ac_name(id)),
                Box::new(arg1),
                Box::new(arg2),
            )),
            ArityRes::NoEq { arity: 2 } => {
                Ok(Term::AlgApp(id.to_string(), Box::new(arg1), Box::new(arg2)))
            }
            ArityRes::NoEq { .. } => {
                Err(self
                    .err("only operators of arity 2 can be written using the `op{t1}t2' notation"))
            }
        }
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
/// input after the formula.  All algebraic operators are enabled at parse time
/// (see [`Parser::new`]); semantic gating is irrelevant here.
pub fn parse_formula_str(s: &str) -> Result<Formula, ParseError> {
    let mut p = Parser::new(s, &[], false);
    // Rendered formula text carries applications of symbols this fresh
    // parser has no declarations for — accept them structurally.
    p.resolve_prefix_apps = false;
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
    // Rendered term text carries applications of symbols this fresh parser
    // has no declarations for — accept them structurally instead of
    // resolving through `lookup_arity`.
    p.resolve_prefix_apps = false;
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
#[path = "parser_tests.rs"]
mod tests;
