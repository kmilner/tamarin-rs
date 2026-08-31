//! Structured diagnostics for `.spthy` parse failures.

use std::fmt;
use std::sync::Arc;

use crate::parser::{Message, ParseError};

/// A half-open byte range in one source file.
///
/// Spans stay parser-owned and are deliberately absent from the semantic
/// theory representation. Line and column numbers are derived from the source
/// only when a diagnostic is rendered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub(crate) fn point(offset: usize) -> Self {
        let start = u32::try_from(offset).unwrap_or(u32::MAX);
        Self { start, end: start }
    }

    pub fn as_range(self) -> std::ops::Range<usize> {
        self.start as usize..self.end as usize
    }
}

/// The grammar construct being parsed when a generic error occurred.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParseContext {
    Theory,
    TheoryItem,
    Identifier,
    FunctionDeclaration,
    Equation,
    Builtin,
    Macro,
    Rule,
    RuleAttribute,
    Restriction,
    RestrictionAttribute,
    Lemma,
    LemmaAttribute,
    Formula,
    Term,
    Process,
    Include,
}

impl ParseContext {
    pub fn description(self) -> &'static str {
        match self {
            Self::Theory => "theory",
            Self::TheoryItem => "theory item",
            Self::Identifier => "identifier",
            Self::FunctionDeclaration => "function declaration",
            Self::Equation => "equation",
            Self::Builtin => "builtin",
            Self::Macro => "macro",
            Self::Rule => "rule",
            Self::RuleAttribute => "rule attribute",
            Self::Restriction => "restriction",
            Self::RestrictionAttribute => "restriction attribute",
            Self::Lemma => "lemma",
            Self::LemmaAttribute => "lemma attribute",
            Self::Formula => "formula",
            Self::Term => "term",
            Self::Process => "process",
            Self::Include => "included file",
        }
    }
}

/// Semantic classification for failures where the parser has more useful
/// information than a generic expected-token set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseErrorKind {
    Expected {
        context: ParseContext,
    },
    ReservedKeyword {
        keyword: String,
    },
    IllegalDiffOperator {
        diff_enabled: bool,
        in_equation: bool,
    },
    DuplicateMacroArgument {
        argument: String,
    },
    UndeclaredFunction {
        name: String,
    },
    ReservedBuiltin {
        name: String,
        context: ParseContext,
    },
    MalformedHexColor {
        reason: String,
    },
    WrongFunctionArity {
        name: String,
        declared: usize,
        used: usize,
    },
    ConflictingDeclaration {
        name: String,
        context: ParseContext,
    },
    DuplicateDeclaration {
        name: String,
        context: ParseContext,
    },
    NonBinaryAcFunction {
        name: String,
        arity: usize,
    },
    UnclosedDelimiter {
        opening: String,
        opening_span: Span,
        closing: String,
    },
    UnknownItem {
        item: String,
        context: ParseContext,
    },
    InvalidFactName {
        name: String,
    },
    PersistentFreshFact,
    FactArity {
        name: String,
        arity: usize,
    },
    IncludeIo {
        path: String,
        reason: String,
    },
    Custom,
    Abort {
        message: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticLabel {
    pub span: Span,
    pub message: String,
    pub primary: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct DiagnosticSource {
    pub name: String,
    pub contents: Arc<str>,
}

impl ParseErrorKind {
    fn headline(&self) -> String {
        match self {
            Self::Expected { context } => {
                format!("Unexpected input while parsing {}", context.description())
            }
            Self::ReservedKeyword { .. } => "Reserved keyword used as an identifier".into(),
            Self::IllegalDiffOperator { .. } => "Illegal diff operator".into(),
            Self::DuplicateMacroArgument { .. } => "Duplicate macro argument".into(),
            Self::UndeclaredFunction { .. } => "Undeclared function".into(),
            Self::ReservedBuiltin { context, .. } => {
                format!("Reserved builtin used in {}", context.description())
            }
            Self::MalformedHexColor { .. } => "Malformed hex color".into(),
            Self::WrongFunctionArity { .. } => "Function used with the wrong arity".into(),
            Self::ConflictingDeclaration { context, .. } => {
                format!("Conflicting {}", context.description())
            }
            Self::DuplicateDeclaration { context, .. } => {
                format!("Duplicate {}", context.description())
            }
            Self::NonBinaryAcFunction { .. } => "Non-binary AC function declaration".into(),
            Self::UnclosedDelimiter { .. } => "Unclosed delimiter".into(),
            Self::UnknownItem { context, item } => {
                format!("Unknown {} `{item}`", context.description())
            }
            Self::InvalidFactName { .. } => "Fact name must start with uppercase".into(),
            Self::PersistentFreshFact => "Fresh fact cannot be persistent".into(),
            Self::FactArity { .. } => "Fact arity mismatch".into(),
            Self::IncludeIo { .. } => "Could not read included file".into(),
            Self::Custom => "Parser error".into(),
            Self::Abort { message } => message.clone(),
        }
    }
}

impl ParseError {
    pub(crate) fn set_kind(&mut self, kind: ParseErrorKind) {
        self.kind = kind;
    }

    pub(crate) fn with_kind(mut self, kind: ParseErrorKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn kind(&self) -> &ParseErrorKind {
        &self.kind
    }

    pub fn span(&self) -> Span {
        let mut span = self.span;
        if span.start == span.end {
            if let Some(source) = &self.diagnostic_source {
                let start = span.start as usize;
                if let Some(ch) = source.contents.get(start..).and_then(|s| s.chars().next()) {
                    span.end = span.start.saturating_add(ch.len_utf8() as u32);
                }
            }
        }
        span
    }

    /// Attach the source bytes at the API boundary. Existing include-source
    /// metadata wins, so a nested failure is never relabelled as the root file.
    pub fn with_source_text(
        mut self,
        name: impl Into<String>,
        contents: impl Into<Arc<str>>,
    ) -> Self {
        if self.diagnostic_source.is_none() {
            self.diagnostic_source = Some(DiagnosticSource {
                name: name.into(),
                contents: contents.into(),
            });
        }
        self
    }

    pub(crate) fn with_input(self, contents: &str) -> Self {
        self.with_source_text(String::new(), Arc::<str>::from(contents))
    }

    pub fn source_name(&self) -> Option<&str> {
        self.diagnostic_source
            .as_ref()
            .map(|s| s.name.as_str())
            .filter(|name| !name.is_empty())
    }

    pub fn source_text(&self) -> Option<&str> {
        self.diagnostic_source.as_ref().map(|s| s.contents.as_ref())
    }

    pub fn line_column(&self) -> (u32, u32) {
        let Some(source) = &self.diagnostic_source else {
            return (self.line, self.col);
        };
        line_column(source.contents.as_ref(), self.span.start as usize)
    }

    pub fn diagnostic_message(&self) -> String {
        if matches!(self.kind, ParseErrorKind::Custom) {
            self.messages
                .iter()
                .find_map(|message| match message {
                    Message::Message(message) => Some(message.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| self.kind.headline())
        } else {
            self.kind.headline()
        }
    }

    pub fn diagnostic_labels(&self) -> Vec<DiagnosticLabel> {
        let primary = DiagnosticLabel {
            span: self.span(),
            message: self.diagnostic_message(),
            primary: true,
        };
        match &self.kind {
            ParseErrorKind::UnclosedDelimiter {
                opening,
                opening_span,
                ..
            } => vec![
                primary,
                DiagnosticLabel {
                    span: *opening_span,
                    message: format!("`{opening}` opened here"),
                    primary: false,
                },
            ],
            _ => vec![primary],
        }
    }

    pub fn diagnostic_notes(&self) -> Vec<String> {
        let mut notes = match &self.kind {
            ParseErrorKind::ReservedKeyword { keyword } => vec![format!(
                "`{keyword}` is reserved and cannot be used as an identifier"
            )],
            ParseErrorKind::IllegalDiffOperator {
                in_equation: true, ..
            } => {
                vec!["the `diff` operator is not allowed in equations".into()]
            }
            ParseErrorKind::IllegalDiffOperator {
                diff_enabled: false,
                ..
            } => {
                vec!["the `diff` operator requires diff mode".into()]
            }
            ParseErrorKind::DuplicateMacroArgument { argument } => {
                vec![format!(
                    "macro argument `{argument}` is listed more than once"
                )]
            }
            ParseErrorKind::UndeclaredFunction { name } => {
                vec![format!("declare function `{name}` before using it")]
            }
            ParseErrorKind::ReservedBuiltin { name, .. } => {
                vec![format!("builtin function `{name}` is reserved")]
            }
            ParseErrorKind::MalformedHexColor { reason } => vec![reason.clone()],
            ParseErrorKind::WrongFunctionArity {
                name,
                declared,
                used,
            } => vec![format!(
                "`{name}` was declared with arity {declared}, but used with arity {used}"
            )],
            ParseErrorKind::ConflictingDeclaration { name, .. } => {
                vec![format!("`{name}` was already declared incompatibly")]
            }
            ParseErrorKind::DuplicateDeclaration { name, .. } => {
                vec![format!("`{name}` was already declared")]
            }
            ParseErrorKind::NonBinaryAcFunction { name, arity } => vec![format!(
                "AC function `{name}` has arity {arity}; AC functions must be binary"
            )],
            ParseErrorKind::UnclosedDelimiter { closing, .. } => {
                vec![format!("expected closing delimiter `{closing}`")]
            }
            ParseErrorKind::UnknownItem { item, .. } => {
                vec![format!("`{item}` is not valid in this context")]
            }
            ParseErrorKind::InvalidFactName { name } => vec![format!(
                "fact name `{name}` must start with an uppercase letter"
            )],
            ParseErrorKind::PersistentFreshFact => {
                vec!["the builtin `Fr` fact cannot be persistent".into()]
            }
            ParseErrorKind::FactArity { name, arity } => vec![format!(
                "fact `{name}` has arity {arity}, but this fact requires arity 1"
            )],
            ParseErrorKind::IncludeIo { path, reason } => {
                vec![format!("failed to read `{path}`: {reason}")]
            }
            ParseErrorKind::Abort { message } => {
                if message == &self.kind.headline() {
                    Vec::new()
                } else {
                    vec![message.clone()]
                }
            }
            ParseErrorKind::Custom => Vec::new(),
            ParseErrorKind::Expected { .. } | ParseErrorKind::IllegalDiffOperator { .. } => {
                Vec::new()
            }
        };

        if matches!(self.kind, ParseErrorKind::Expected { .. }) {
            let found = self.messages.iter().find_map(|message| match message {
                Message::SysUnExpect(s) | Message::UnExpect(s) if !s.is_empty() => Some(s.as_str()),
                _ => None,
            });
            let expected: Vec<&str> = self
                .messages
                .iter()
                .filter_map(|message| match message {
                    Message::Expect(s) if !s.is_empty() => Some(s.as_str()),
                    _ => None,
                })
                .collect();
            if !expected.is_empty() {
                let expected = expected.join(", ");
                notes.push(match found {
                    Some(found) => format!("expected {expected}; found {found}"),
                    None => format!("expected {expected}"),
                });
            }
        }
        notes
    }

    pub fn render_plain(&self) -> String {
        let (line, col) = self.line_column();
        let name = self.source_name().unwrap_or("<input>");
        let mut out = format!("{name}:{line}:{col}: {}", self.diagnostic_message());
        if let Some(source) = &self.diagnostic_source {
            for label in self
                .diagnostic_labels()
                .into_iter()
                .filter(|label| !label.primary)
            {
                let (line, col) = line_column(source.contents.as_ref(), label.span.start as usize);
                out.push_str(&format!(
                    "\n  = label: {name}:{line}:{col}: {}",
                    label.message
                ));
            }
        }
        for note in self.diagnostic_notes() {
            out.push_str("\n  = note: ");
            out.push_str(&note);
        }
        out
    }
}

fn line_column(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 1u32;
    let mut col = 1u32;
    for ch in source[..offset.min(source.len())].chars() {
        match ch {
            '\n' => {
                line += 1;
                col = 1;
            }
            '\t' => col += 8 - ((col - 1) % 8),
            _ => col += 1,
        }
    }
    (line, col)
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.headline())
    }
}
