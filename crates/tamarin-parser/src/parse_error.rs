// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Shared locations and diagnostics for parsing `.spthy` files.

use std::borrow::Cow;

use crate::ast::*;
use crate::lexer::Pos;

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
            start: pos.offset.saturating_sub(1),
            end: pos.offset,
        }
    }
}

/// An enum to give `[ParseError]` variants context of where the error occured
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum ParseContext {
    Equation,
    Restriction,
    Macro,
    Rule,
    Lemma,
    Function,
    Builtin,
    RestrictionAttribute,
    LemmaAttribute,
    RuleAttribute,
    // Add more as necessary
}

impl ParseContext {
    pub fn as_str(&self) -> &'static str {
        match self {
            ParseContext::Equation => "equation",
            ParseContext::Macro => "macro",
            ParseContext::Rule => "rule",
            ParseContext::Lemma => "lemma",
            ParseContext::Restriction => "restriction",
            ParseContext::Function => "function",
            ParseContext::RestrictionAttribute => "restriction attribute",
            ParseContext::LemmaAttribute => "lemma attribute",
            ParseContext::RuleAttribute => "rule attribute",
            ParseContext::Builtin => "builtin",
        }
    }

    pub fn as_str_plural(&self) -> &'static str {
        match self {
            ParseContext::Equation => "equations",
            ParseContext::Macro => "macros",
            ParseContext::Rule => "rules",
            ParseContext::Lemma => "lemmas",
            ParseContext::Restriction => "restrictions",
            ParseContext::Function => "functions",
            ParseContext::RestrictionAttribute => "restriction attributes",
            ParseContext::LemmaAttribute => "lemma attributes",
            ParseContext::RuleAttribute => "rule attributes",
            ParseContext::Builtin => "builtins",
        }
    }

    pub fn as_str_with_article(&self) -> &'static str {
        match self {
            ParseContext::Equation => "an equation",
            ParseContext::Macro => "a macro",
            ParseContext::Rule => "a rule",
            ParseContext::Lemma => "a lemma",
            ParseContext::Restriction => "a restriction",
            ParseContext::Function => "a function",
            ParseContext::RestrictionAttribute => "a restriction attribute",
            ParseContext::LemmaAttribute => "a lemma attribute",
            ParseContext::RuleAttribute => "a rule attribute",
            ParseContext::Builtin => "a builtin",
        }
    }

    /// The names this context accepts, for the `expected` list of a
    /// [`ParseError::UnknownItem`].  A context that names no fixed vocabulary
    /// has no such list.
    fn expected(&self) -> Vec<&'static str> {
        match self {
            ParseContext::Builtin => BuiltinKind::iter().map(|b| b.as_str()).collect(),
            ParseContext::RestrictionAttribute => {
                RestrictionAttr::iter().map(|r| r.as_str()).collect()
            }
            ParseContext::LemmaAttribute => LemmaAttr::expected(),
            ParseContext::RuleAttribute => RuleAttr::expected(),
            ParseContext::Equation
            | ParseContext::Restriction
            | ParseContext::Macro
            | ParseContext::Rule
            | ParseContext::Lemma
            | ParseContext::Function => vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub enum ParseError {
    UsedReservedKeyword {
        found: String,
        at: Location,
        expected: Vec<String>,
    },
    IllegalDiffOperator {
        /// Was the diff flag set when parsing
        diff_set: bool,
        /// If present, the `diff` operator is not allowed in the context
        //  Currently, only used with `ParseContext::Equation`
        context: Option<ParseContext>,
        at: Location,
    },
    DuplicateMacroArg {
        arg: String,
        first_at: Location,
        second_at: Location,
    },
    UndeclaredFunction {
        name: String,
        at: Location,
    },
    UsedReservedBuiltin {
        f: String,
        at: Location,
        context: ParseContext,
    },
    MalformedHexColor {
        msg: String,
        at: Location,
    },
    FunctionUsedWithWrongArity {
        name: String,
        declared_arity: usize,
        used_arity: usize,
        declared_at: Option<Location>,
        used_at: Location,
    },
    UnexpectedKeyword {
        found: Option<String>,
        expected: Vec<String>,
        at: Location,
    },
    ConflictingDeclarations {
        name: String,
        first_context: ParseContext,
        second_context: ParseContext,
        first_at: Option<Location>,
        second_at: Location,
    },
    WrongArityforACFunctionDeclaration {
        name: String,
        found_arity: usize,
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
    UnknownItem {
        item_kind: ParseContext,
        unknown_item: String,
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
    pub(crate) fn add_expected(&mut self, exp: impl Into<String>) {
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
            | ParseError::UsedReservedKeyword { expected, .. }
            | ParseError::UnterminatedDelimiter { expected, .. } => {
                let exp = exp.into();
                if !expected.contains(&exp) {
                    expected.push(exp);
                }
            }
            // Explicity match to force compile-time error for new variants
            ParseError::IllegalDiffOperator { .. }
            | ParseError::FactNameMustStartWithUppercase { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::FactArityMismatch { .. }
            | ParseError::UnexpectedTrailingInput { .. }
            | ParseError::UnknownItem { .. }
            | ParseError::Custom { .. }
            | ParseError::ConflictingDeclarations { .. }
            | ParseError::Abort { .. }
            | ParseError::IoError { .. }
            | ParseError::UsedReservedBuiltin { .. }
            | ParseError::FunctionUsedWithWrongArity { .. }
            | ParseError::WrongArityforACFunctionDeclaration { .. }
            | ParseError::MalformedHexColor { .. }
            | ParseError::UndeclaredFunction { .. }
            | ParseError::DuplicateMacroArg { .. } => {}
        }
    }

    pub fn location(&self) -> &Location {
        match self {
            ParseError::UsedReservedKeyword { at, .. }
            | ParseError::IllegalDiffOperator { at, .. }
            | ParseError::FactNameMustStartWithUppercase { at, .. }
            | ParseError::UnexpectedKeyword { at, .. }
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
            | ParseError::UnknownItem { at, .. }
            | ParseError::Expected { at, .. }
            | ParseError::Custom { at, .. }
            | ParseError::UsedReservedBuiltin { at, .. }
            | ParseError::Abort { at, .. }
            | ParseError::UndeclaredFunction { at, .. }
            | ParseError::MalformedHexColor { at, .. }
            | ParseError::WrongArityforACFunctionDeclaration { at, .. }
            | ParseError::UnterminatedDelimiter { found_at: at, .. } => at,
            ParseError::DuplicateMacroArg { second_at, .. } => second_at,
            ParseError::ConflictingDeclarations { second_at, .. } => second_at,
            ParseError::FunctionUsedWithWrongArity { used_at, .. } => used_at,
        }
    }

    pub(crate) fn into_found(self) -> Option<String> {
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
            ParseError::UnknownItem {
                unknown_item: item, ..
            } => Some(item),
            ParseError::UsedReservedKeyword { found, .. } => Some(found),
            ParseError::FactNameMustStartWithUppercase { name, .. }
            | ParseError::FactArityMismatch { name, .. }
            | ParseError::UnexpectedTrailingInput { found: name, .. } => Some(name),
            ParseError::IllegalDiffOperator { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::IoError { .. }
            | ParseError::Custom { .. }
            | ParseError::MalformedHexColor { .. }
            | ParseError::DuplicateMacroArg { .. }
            | ParseError::WrongArityforACFunctionDeclaration { .. }
            | ParseError::UsedReservedBuiltin { .. }
            | ParseError::UndeclaredFunction { .. }
            | ParseError::ConflictingDeclarations { .. }
            | ParseError::FunctionUsedWithWrongArity { .. }
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
            ParseError::UnknownItem {
                unknown_item: item, ..
            } => Some(item.as_str()),
            ParseError::UsedReservedKeyword { found, .. } => Some(found.as_str()),
            ParseError::FactNameMustStartWithUppercase { name, .. }
            | ParseError::FactArityMismatch { name, .. } => Some(name.as_str()),
            ParseError::UnexpectedTrailingInput { found, .. } => Some(found.as_str()),
            ParseError::IllegalDiffOperator { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::IoError { .. }
            | ParseError::Custom { .. }
            | ParseError::DuplicateMacroArg { .. }
            | ParseError::WrongArityforACFunctionDeclaration { .. }
            | ParseError::MalformedHexColor { .. }
            | ParseError::FunctionUsedWithWrongArity { .. }
            | ParseError::UndeclaredFunction { .. }
            | ParseError::UsedReservedBuiltin { .. }
            | ParseError::ConflictingDeclarations { .. }
            | ParseError::Abort { .. } => None,
        }
    }

    pub fn expected(&self) -> Option<Vec<String>> {
        let raw_expected = match self {
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
            | ParseError::UsedReservedKeyword { expected, .. }
            | ParseError::Expected { expected, .. }
            | ParseError::UnterminatedDelimiter { expected, .. } => Some(expected.clone()),
            ParseError::UnknownItem {
                item_kind: kind, ..
            } => Some(kind.expected().into_iter().map(|s| s.to_string()).collect()),
            ParseError::FactNameMustStartWithUppercase { .. }
            | ParseError::IllegalDiffOperator { .. }
            | ParseError::FreshFactCannotBePersistent { .. }
            | ParseError::FactArityMismatch { .. }
            | ParseError::UnexpectedTrailingInput { .. }
            | ParseError::Custom { .. }
            | ParseError::Abort { .. }
            | ParseError::IoError { .. }
            | ParseError::DuplicateMacroArg { .. }
            | ParseError::FunctionUsedWithWrongArity { .. }
            | ParseError::MalformedHexColor { .. }
            | ParseError::WrongArityforACFunctionDeclaration { .. }
            | ParseError::UndeclaredFunction { .. }
            | ParseError::ConflictingDeclarations { .. }
            | ParseError::UsedReservedBuiltin { .. } => None,
        }?;
        // Typo suggestions: the two variants whose lists enumerate every known
        // name are ranked by edit distance to the found token and cut to the
        // closest 3.  Grammar expectation sets pass through whole, in HS's
        // order.
        match self {
            ParseError::ExpectedTheoryItem { .. } | ParseError::UnknownItem { .. } => {
                Some(match self.found() {
                    Some(found) => {
                        let mut ranked: Vec<(usize, usize, String)> = raw_expected
                            .into_iter()
                            .enumerate()
                            .map(|(idx, exp)| (edit_distance(found, &exp), idx, exp))
                            .collect();
                        ranked.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
                        ranked.into_iter().take(3).map(|(_, _, exp)| exp).collect()
                    }
                    None => raw_expected.into_iter().take(3).collect(),
                })
            }
            _ => Some(raw_expected),
        }
    }

    /// The error's headline, borrowed from the fixed table below except where
    /// the offending name is part of the message.
    pub fn description(&self) -> Cow<'static, str> {
        Cow::Borrowed(match self {
            ParseError::UsedReservedKeyword { .. } => "Used reserved keyword",
            ParseError::IllegalDiffOperator { .. } => "Illegal diff operator",
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
            ParseError::UnknownItem {
                unknown_item,
                item_kind,
                ..
            } => {
                // The offending name is part of the headline, so this one is
                // built per error rather than borrowed.
                return Cow::Owned(format!("Unknown {} `{}`", item_kind.as_str(), unknown_item));
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
            ParseError::ConflictingDeclarations { second_context, .. } => {
                return Cow::Owned(format!(
                    "Conflicting {} declaration",
                    second_context.as_str()
                ))
            }
            ParseError::WrongArityforACFunctionDeclaration { .. } => {
                "Non-binary AC function declaration"
            }
            ParseError::MalformedHexColor { .. } => "Malformed hex color",
            ParseError::FunctionUsedWithWrongArity { .. } => "Function used with wrong arity",
            ParseError::UsedReservedBuiltin { context, .. } => {
                return Cow::Owned(format!("Reserved builtin function in {}", context.as_str()))
            }
            ParseError::UndeclaredFunction { .. } => "Undeclared function",
            ParseError::DuplicateMacroArg { .. } => "Duplicate macro argument",
        })
    }

    pub fn labels(&self) -> Vec<ParseErrorLabel> {
        match self {
            ParseError::UsedReservedKeyword { found, .. } => vec![ParseErrorLabel {
                at: *self.location(),
                message: format!("Used reserved keyword `{}`", found),
                is_primary: true,
            }],
            ParseError::IllegalDiffOperator { .. } => vec![ParseErrorLabel {
                at: *self.location(),
                message: self.description().to_string(),
                is_primary: true,
            }],
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
            ParseError::DuplicateMacroArg {
                arg,
                first_at,
                second_at,
            } => {
                vec![
                    ParseErrorLabel {
                        at: *second_at,
                        message: format!("duplicate macro argument `{arg}`"),
                        is_primary: true,
                    },
                    ParseErrorLabel {
                        at: *first_at,
                        message: format!("first occurrence of argument `{arg}`"),
                        is_primary: false,
                    },
                ]
            }
            ParseError::ConflictingDeclarations {
                name,
                first_context,
                second_context,
                first_at,
                second_at,
            } => {
                let kind = second_context.as_str();
                let msg = format!("conflicting {kind} declaration for `{name}`",);
                let mut lbls = vec![ParseErrorLabel {
                    at: *second_at,
                    message: msg,
                    is_primary: true,
                }];
                if let Some(first_at) = first_at {
                    lbls.push(ParseErrorLabel {
                        at: *first_at,
                        message: format!(
                            "first declaration of `{name}` as {}",
                            first_context.as_str_with_article()
                        ),
                        is_primary: false,
                    });
                }
                lbls
            }
            ParseError::MalformedHexColor { msg, at } => {
                let lbls = vec![ParseErrorLabel {
                    at: *at,
                    message: format!("malformed hex color: {msg}"),
                    is_primary: true,
                }];
                lbls
            }
            ParseError::FunctionUsedWithWrongArity {
                name,
                declared_arity,
                used_arity,
                declared_at,
                used_at,
            } => {
                let mut lbls = vec![ParseErrorLabel {
                    at: *used_at,
                    message: format!("function `{name}` was used with arity {used_arity}, but it has arity {declared_arity}"),
                    is_primary: true,
                }];
                if let Some(declared_at) = declared_at {
                    lbls.push(ParseErrorLabel {
                        at: *declared_at,
                        message: format!("declared with arity {declared_arity} here"),
                        is_primary: false,
                    });
                }
                lbls
            }
            ParseError::UsedReservedBuiltin { f, at, context } => {
                vec![ParseErrorLabel {
                    at: *at,
                    message: format!(
                        "reserved builtin function `{f}` was used in {}",
                        context.as_str_with_article()
                    )
                    .to_string(),
                    is_primary: true,
                }]
            }
            ParseError::UndeclaredFunction { name, at } => {
                vec![ParseErrorLabel {
                    at: *at,
                    message: format!("`{name}` is not a declared function symbol"),
                    is_primary: true,
                }]
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
            ParseError::UsedReservedKeyword { found, .. } => vec![format!(
                "`{found}` is a reserved word and cannot be used as an identifier"
            )],
            ParseError::IllegalDiffOperator {
                diff_set, context, ..
            } => {
                let mut notes = vec![];
                if let Some(c) = context {
                    notes.push(format!(
                        "diff operator is not allowed in {}",
                        c.as_str_plural()
                    ));
                }
                if !*diff_set {
                    notes.push("diff operator found, but flag diff not set".to_string());
                }
                notes
            }
            ParseError::UnexpectedKeyword {
                found, expected, ..
            } => {
                vec![format_found_expected_note(
                    "keyword",
                    found.as_deref(),
                    expected,
                )]
            }
            ParseError::UndeclaredFunction { .. } => {
                vec!["functions must be declared before use".to_string()]
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
            ParseError::UnknownItem {
                unknown_item: found,
                item_kind: kind,
                ..
            } => vec![format_found_expected_note(
                kind.as_str(),
                Some(found),
                &self.expected().unwrap_or_default(),
            )],
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
            ParseError::ConflictingDeclarations { second_context, .. } => {
                let tail = match second_context {
                    ParseContext::Macro => "unique",
                    _ => "unique or consistent",
                };
                vec![format!(
                    "{} declarations must be {}",
                    second_context.as_str(),
                    tail
                )]
            }
            ParseError::WrongArityforACFunctionDeclaration { .. } => {
                vec!["AC function declarations must be binary".into()]
            }
            ParseError::MalformedHexColor { .. } => {
                vec!["Hex color literals must be in the format `#RRGGBB`".into()]
            }
            ParseError::FunctionUsedWithWrongArity { .. } => {
                vec!["Function must be used with the declared arity".into()]
            }
            ParseError::UsedReservedBuiltin { context, .. } => {
                vec![format!(
                    "Reserved builtin functions cannot be used in {}",
                    context.as_str_plural()
                )]
            }
            ParseError::DuplicateMacroArg { .. } => {
                vec!["Macro arguments must be unique".into()]
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
