//! Structured diagnostics for `.spthy` parse failures.

use std::fmt;
use std::ops::Range;

use crate::lexer::Pos;
use crate::parser::{Message, ParseError};

/// Width of the tab stops used by Parsec source positions.
pub const PARSEC_TAB_WIDTH: u32 = 8;

/// Maximum size of an identifier-like value retained in a diagnostic.
pub(crate) const MAX_DIAGNOSTIC_NAME_CHARS: usize = 80;
/// Maximum size of a free-form parser message retained in a diagnostic.
pub(crate) const MAX_DIAGNOSTIC_MESSAGE_CHARS: usize = 512;

pub(crate) fn advance_line_column(line: &mut u32, col: &mut u32, ch: char) {
    match ch {
        '\n' => {
            *line += 1;
            *col = 1;
        }
        '\t' => *col += PARSEC_TAB_WIDTH - ((*col - 1) % PARSEC_TAB_WIDTH),
        _ => *col += 1,
    }
}

pub(crate) fn bounded_diagnostic_text(text: &str, max_chars: usize) -> String {
    let mut chars = text.chars();
    let mut bounded: String = chars.by_ref().take(max_chars).collect();
    if chars.next().is_some() {
        bounded.push('…');
    }
    bounded
}

pub(crate) fn bound_owned_text(text: &mut String, max_chars: usize) {
    if let Some((end, _)) = text.char_indices().nth(max_chars) {
        text.truncate(end);
        text.push('…');
    }
}

/// The grammar construct being parsed when a generic error occurred.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParseContext {
    Theory,
    TheoryItem,
    Options,
    FunctionDeclaration,
    Equation,
    Builtin,
    Macro,
    Predicate,
    Heuristic,
    Tactic,
    Rule,
    RuleAttribute,
    Restriction,
    RestrictionAttribute,
    Lemma,
    LemmaAttribute,
    CaseTest,
    Export,
    Formula,
    Term,
    Process,
    Include,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IllegalDiffReason {
    InEquation,
    DiffModeDisabled,
}

impl ParseContext {
    pub fn description(self) -> &'static str {
        match self {
            Self::Theory => "theory",
            Self::TheoryItem => "theory item",
            Self::Options => "options",
            Self::FunctionDeclaration => "function declaration",
            Self::Equation => "equation",
            Self::Builtin => "builtin",
            Self::Macro => "macro",
            Self::Predicate => "predicate",
            Self::Heuristic => "heuristic",
            Self::Tactic => "tactic",
            Self::Rule => "rule",
            Self::RuleAttribute => "rule attribute",
            Self::Restriction => "restriction",
            Self::RestrictionAttribute => "restriction attribute",
            Self::Lemma => "lemma",
            Self::LemmaAttribute => "lemma attribute",
            Self::CaseTest => "case test",
            Self::Export => "export",
            Self::Formula => "formula",
            Self::Term => "term",
            Self::Process => "process",
            Self::Include => "included file",
        }
    }
}

/// Semantic classification for failures where the parser has more useful
/// information than a generic expected-token set.
///
/// String payloads are diagnostic excerpts rather than lossless source data:
/// identifier-like values are limited to 80 characters and free-form values
/// to 512 characters, with `…` appended when truncated. Because `…` may also
/// occur in source, consumers must treat every payload as potentially lossy.
/// The original byte extent remains available through [`ParseError::span`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseErrorKind {
    Expected {
        context: ParseContext,
    },
    ReservedKeyword {
        keyword: String,
    },
    IllegalDiffOperator(IllegalDiffReason),
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
        opening: char,
        opening_span: Range<usize>,
        closing: char,
    },
    UnclosedBlockComment {
        opening_span: Range<usize>,
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
    /// A raw parsec message. The canonical text remains in `ParseError::messages`
    /// so constructing speculative failures does not clone it into this layer.
    Custom,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticLabel {
    pub span: Range<usize>,
    pub message: String,
}

#[derive(Debug, Default)]
pub(crate) struct DiagnosticInfo {
    kind: Option<ParseErrorKind>,
    span: Option<Range<usize>>,
    location: Option<(u32, u32)>,
    source: Option<String>,
    ghc_error: Option<crate::parser::GhcError>,
    related: Option<DiagnosticLabel>,
}

impl ParseErrorKind {
    fn bound_payloads(mut self) -> Self {
        let name = match &mut self {
            Self::ReservedKeyword { keyword } => Some(keyword),
            Self::DuplicateMacroArgument { argument } => Some(argument),
            Self::UndeclaredFunction { name }
            | Self::ReservedBuiltin { name, .. }
            | Self::WrongFunctionArity { name, .. }
            | Self::ConflictingDeclaration { name, .. }
            | Self::DuplicateDeclaration { name, .. }
            | Self::NonBinaryAcFunction { name, .. }
            | Self::InvalidFactName { name }
            | Self::FactArity { name, .. } => Some(name),
            Self::UnknownItem { item, .. } => Some(item),
            _ => None,
        };
        if let Some(name) = name {
            bound_owned_text(name, MAX_DIAGNOSTIC_NAME_CHARS);
        }

        match &mut self {
            Self::MalformedHexColor { reason } => {
                bound_owned_text(reason, MAX_DIAGNOSTIC_MESSAGE_CHARS);
            }
            Self::IncludeIo { path, reason } => {
                bound_owned_text(path, MAX_DIAGNOSTIC_MESSAGE_CHARS);
                bound_owned_text(reason, MAX_DIAGNOSTIC_MESSAGE_CHARS);
            }
            _ => {}
        }
        self
    }

    fn headline(&self) -> String {
        match self {
            Self::Expected { context } => {
                format!("Unexpected input while parsing {}", context.description())
            }
            Self::ReservedKeyword { .. } => "Reserved keyword used as an identifier".into(),
            Self::IllegalDiffOperator(_) => "Illegal diff operator".into(),
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
            Self::UnclosedBlockComment { .. } => "Unclosed block comment".into(),
            Self::UnknownItem { context, item } => {
                format!("Unknown {} `{item}`", context.description())
            }
            Self::InvalidFactName { .. } => "Fact name must start with uppercase".into(),
            Self::PersistentFreshFact => "Fresh fact cannot be persistent".into(),
            Self::FactArity { .. } => "Fact arity mismatch".into(),
            Self::IncludeIo { .. } => "Could not read included file".into(),
            Self::Custom => "Parser error".into(),
        }
    }
}

impl ParseError {
    fn diagnostic_mut(&mut self) -> &mut DiagnosticInfo {
        self.diagnostic
            .get_or_insert_with(|| Box::new(DiagnosticInfo::default()))
    }

    pub(crate) fn set_kind(&mut self, kind: ParseErrorKind) {
        self.diagnostic_mut().kind = Some(kind.bound_payloads());
    }

    pub(crate) fn with_kind(mut self, kind: ParseErrorKind) -> Self {
        self.set_kind(kind);
        self
    }

    pub(crate) fn with_related_span(mut self, span: Range<usize>, message: &str) -> Self {
        self.diagnostic_mut().related = Some(DiagnosticLabel {
            span,
            message: message.into(),
        });
        self
    }

    pub(crate) fn with_ghc_error(mut self, error: crate::parser::GhcError) -> Self {
        self.diagnostic_mut().ghc_error = Some(error);
        self
    }

    pub fn kind(&self) -> &ParseErrorKind {
        static EXPECTED_THEORY: ParseErrorKind = ParseErrorKind::Expected {
            context: ParseContext::Theory,
        };
        static CUSTOM: ParseErrorKind = ParseErrorKind::Custom;

        self.diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.kind.as_ref())
            .unwrap_or_else(|| {
                if self
                    .messages
                    .iter()
                    .any(|message| matches!(message, Message::Message(_)))
                {
                    &CUSTOM
                } else {
                    &EXPECTED_THEORY
                }
            })
    }

    /// Anchor a semantic diagnostic to the token that caused it. The legacy
    /// parsec position and messages remain internally available to `Display`.
    pub(crate) fn with_location(mut self, pos: Pos, len: usize) -> Self {
        let diagnostic = self.diagnostic_mut();
        diagnostic.span = Some(pos.offset..pos.offset.saturating_add(len));
        diagnostic.location = Some((pos.line, pos.col));
        self
    }

    /// Add grammar context to an otherwise generic expected-token failure.
    /// More specific inner parsers win as the error propagates outward.
    pub(crate) fn with_context(mut self, context: ParseContext) -> Self {
        if self
            .messages
            .iter()
            .any(|message| matches!(message, Message::Message(_)))
        {
            return self;
        }
        let diagnostic = self.diagnostic_mut();
        if diagnostic.kind.is_none() {
            diagnostic.kind = Some(ParseErrorKind::Expected { context });
        }
        self
    }

    pub(crate) fn shifted(mut self, base: Pos, source: &str) -> Self {
        let relative_offset = self.pos.offset;
        self.pos.offset = relative_offset.saturating_add(base.offset);
        (self.pos.line, self.pos.col) = line_column_from(
            base.line,
            base.col,
            source
                .get(base.offset..self.pos.offset.min(source.len()))
                .unwrap_or(""),
        );
        if let Some(diagnostic) = self.diagnostic.as_mut() {
            debug_assert!(
                diagnostic.source.is_none(),
                "cannot shift an error attached to an independent source"
            );
            if let Some(label) = diagnostic.related.as_mut() {
                label.span.start = label.span.start.saturating_add(base.offset);
                label.span.end = label.span.end.saturating_add(base.offset);
            }
            if let Some(span) = diagnostic.span.as_mut() {
                span.start = span.start.saturating_add(base.offset);
                span.end = span.end.saturating_add(base.offset);
            }
            if let Some(location) = diagnostic.location.as_mut() {
                let absolute_offset = diagnostic
                    .span
                    .as_ref()
                    .map_or(self.pos.offset, |span| span.start);
                *location = line_column_from(
                    base.line,
                    base.col,
                    source
                        .get(base.offset..absolute_offset.min(source.len()))
                        .unwrap_or(""),
                );
            }
            if let Some(
                ParseErrorKind::UnclosedDelimiter { opening_span, .. }
                | ParseErrorKind::UnclosedBlockComment { opening_span },
            ) = diagnostic.kind.as_mut()
            {
                opening_span.start = opening_span.start.saturating_add(base.offset);
                opening_span.end = opening_span.end.saturating_add(base.offset);
            }
        }
        self
    }

    pub fn span(&self) -> Range<usize> {
        self.diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.span.clone())
            .unwrap_or(self.pos.offset..self.pos.offset)
    }

    fn span_with_source(&self, source: Option<&str>) -> Range<usize> {
        let mut span = self.span();
        if span.start == span.end
            && let Some(source) = source
            && let Some(ch) = source.get(span.start..).and_then(|s| s.chars().next())
        {
            span.end = span.start.saturating_add(ch.len_utf8());
        }
        span
    }

    /// Attach owned source text at the API boundary. Passing a [`String`] moves
    /// its allocation without copying its bytes.
    /// Existing include-source metadata wins, so a nested failure is never
    /// relabelled as the root file.
    pub fn with_source_text(
        mut self,
        name: impl Into<String>,
        contents: impl Into<String>,
    ) -> Self {
        let name = name.into();
        if self
            .diagnostic
            .as_ref()
            .is_some_and(|diagnostic| diagnostic.source.is_some())
        {
            if self.source.is_empty() {
                self.source = name;
            }
            return self;
        }
        if self.source.is_empty() {
            self.source = name;
        }
        self.diagnostic_mut().source = Some(contents.into());
        self
    }

    /// Attach the root source name if no more specific included-file name is
    /// already present. Repeated calls deliberately keep the first name.
    pub fn with_source(mut self, name: impl Into<String>) -> Self {
        if self.source.is_empty() {
            self.source = name.into();
        }
        self
    }

    pub fn source_name(&self) -> Option<&str> {
        (!self.source.is_empty()).then_some(self.source.as_str())
    }

    pub fn source_text(&self) -> Option<&str> {
        self.diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.source.as_ref())
            .map(|source| source.as_str())
    }

    pub fn line_column(&self) -> (u32, u32) {
        self.diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.location)
            .unwrap_or((self.pos.line, self.pos.col))
    }

    /// The upstream GHC exception represented by this failure, when parsing
    /// aborted through an `error` call rather than an ordinary parsec error.
    pub fn ghc_error(&self) -> Option<&crate::parser::GhcError> {
        self.diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.ghc_error.as_ref())
    }

    pub fn diagnostic_message(&self) -> String {
        if matches!(self.kind(), ParseErrorKind::Custom) {
            // Message order is parsec's stable merge order and therefore also
            // defines which raw failure is primary. Keep one owned copy until
            // the diagnostic is actually rendered.
            self.raw_message()
                .map(str::to_owned)
                .unwrap_or_else(|| self.kind().headline())
        } else {
            self.kind().headline()
        }
    }

    fn raw_message(&self) -> Option<&str> {
        self.messages.iter().find_map(|message| match message {
            Message::Message(message) => Some(message.as_str()),
            _ => None,
        })
    }

    pub fn diagnostic_labels(&self) -> Vec<DiagnosticLabel> {
        self.diagnostic_labels_with_source("")
    }

    /// Return renderer labels, with the primary label first and any secondary
    /// labels after it. Borrows a root source for point-span expansion when
    /// the error did not originate in an included file.
    pub fn diagnostic_labels_with_source(&self, root_source: &str) -> Vec<DiagnosticLabel> {
        let source = self.source_text().unwrap_or(root_source);
        let mut labels = vec![DiagnosticLabel {
            span: self.span_with_source(Some(source)),
            message: self.diagnostic_message(),
        }];
        if let Some(label) = self.secondary_label() {
            labels.push(label);
        }
        labels
    }

    fn secondary_label(&self) -> Option<DiagnosticLabel> {
        match self.kind() {
            ParseErrorKind::UnclosedDelimiter {
                opening,
                opening_span,
                ..
            } => Some(DiagnosticLabel {
                span: opening_span.clone(),
                message: format!("`{opening}` opened here"),
            }),
            ParseErrorKind::UnclosedBlockComment { opening_span } => Some(DiagnosticLabel {
                span: opening_span.clone(),
                message: "block comment opened here".into(),
            }),
            _ => self.diagnostic.as_ref().and_then(|d| d.related.clone()),
        }
    }

    pub fn diagnostic_notes(&self) -> Vec<String> {
        let mut notes = match self.kind() {
            ParseErrorKind::ReservedKeyword { keyword } => vec![format!(
                "`{keyword}` is reserved and cannot be used as an identifier"
            )],
            ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::InEquation) => {
                vec!["the `diff` operator is not allowed in equations".into()]
            }
            ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::DiffModeDisabled) => {
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
            ParseErrorKind::ConflictingDeclaration { name, .. } => vec![self
                .raw_message()
                .map(str::to_owned)
                .unwrap_or_else(|| format!("`{name}` was already declared incompatibly"))],
            ParseErrorKind::DuplicateDeclaration { name, .. } => {
                vec![format!("`{name}` was already declared")]
            }
            ParseErrorKind::NonBinaryAcFunction { name, arity } => vec![format!(
                "AC function `{name}` has arity {arity}; AC functions must be binary"
            )],
            ParseErrorKind::UnclosedDelimiter { closing, .. } => {
                vec![format!("expected closing delimiter `{closing}`")]
            }
            ParseErrorKind::UnclosedBlockComment { .. } => vec!["expected closing `*/`".into()],
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
            ParseErrorKind::Custom | ParseErrorKind::Expected { .. } => Vec::new(),
        };

        if matches!(self.kind(), ParseErrorKind::Expected { .. }) {
            let unexpected = |want_user| {
                self.messages.iter().find_map(|message| match message {
                    Message::UnExpect(s) if want_user && !s.is_empty() => Some(s.as_str()),
                    Message::SysUnExpect(s) if !want_user && !s.is_empty() => Some(s.as_str()),
                    _ => None,
                })
            };
            let found = unexpected(true).or_else(|| unexpected(false));
            let mut expected = Vec::new();
            for message in &self.messages {
                let Message::Expect(value) = message else {
                    continue;
                };
                if !value.is_empty() && !expected.contains(&value.as_str()) {
                    expected.push(value.as_str());
                }
            }
            if !expected.is_empty() {
                let expected = expected.join(", ");
                notes.push(match found {
                    Some(found) => format!("expected {expected}; found {found}"),
                    None => format!("expected {expected}"),
                });
            }
        }
        if self.messages_truncated {
            notes.push("additional parser messages omitted".into());
        }
        notes
    }

    pub fn render_plain(&self) -> String {
        self.render_plain_with_source("<input>", "")
    }

    /// Render a compact text diagnostic, borrowing the root source rather
    /// than requiring the error value to retain a copy of it. Included-file
    /// source attached to the error remains authoritative.
    pub fn render_plain_with_source(&self, root_name: &str, root_source: &str) -> String {
        let (line, col) = self.line_column();
        let name = self.source_name().unwrap_or(root_name);
        let mut out = format!("{name}:{line}:{col}: {}", self.diagnostic_message());
        let source = self.source_text().unwrap_or(root_source);
        if !source.is_empty()
            && let Some(label) = self.secondary_label()
        {
            let (line, col) = line_column(source, label.span.start);
            out.push_str(&format!(
                "\n  = label: {name}:{line}:{col}: {}",
                label.message
            ));
        }
        for note in self.diagnostic_notes() {
            out.push_str("\n  = note: ");
            out.push_str(&note);
        }
        out
    }
}

/// Compute Parsec-compatible one-based line and column coordinates for a byte
/// offset. Used for secondary labels and diagnostic renderer adapters.
pub fn line_column(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 1u32;
    let mut col = 1u32;
    let end = offset.min(source.len());
    for (start, ch) in source.char_indices() {
        if start + ch.len_utf8() > end {
            break;
        }
        advance_line_column(&mut line, &mut col, ch);
    }
    (line, col)
}

fn line_column_from(mut line: u32, mut col: u32, source: &str) -> (u32, u32) {
    for ch in source.chars() {
        advance_line_column(&mut line, &mut col, ch);
    }
    (line, col)
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.headline())
    }
}

#[cfg(test)]
mod tests {
    use super::line_column;

    #[test]
    fn line_column_tolerates_offsets_inside_utf8_characters() {
        assert_eq!(line_column("éx", 1), (1, 1));
        assert_eq!(line_column("éx", 2), (1, 2));
        assert_eq!(line_column("éx", 3), (1, 3));
    }
}
