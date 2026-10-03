// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Wellformedness checks over a Tamarin theory.
//!
//! Port of `Theory.Tools.Wellformedness` from
//! `lib/theory/src/Theory/Tools/Wellformedness.hs`.  Each check function
//! corresponds to a Haskell `*Report` / `*Check` function, grouped by the HS
//! family it belongs to: [`rules`] walks the rules, [`facts`] the
//! `factReports` group, [`lemmas`] the lemma annotations and the
//! `--prove`/`--lemma` arguments, [`formulas`] (with [`check_terms`]) the
//! lemma and restriction formulas, [`mult`] the multiplication restriction,
//! and [`equations`] the subterm-convergence warning.
//!
//! [`check_wellformedness`] is HS's `checkWellformedness`
//! (Wellformedness.hs): one pass over the translated theory that
//! runs the checks in the order of HS's list literal.  Both drivers — the
//! batch CLI (`run.rs`) and the web server's theory load (`theory_io.rs`) —
//! call it once, after the SAPIC and accountability translations, so the
//! rules SAPIC generated and the lemmas accountability appended are in
//! scope.  Both paths hand it the file's live Maude handle when startup
//! succeeds, which variant validation needs. Without Maude, static checks
//! remain available, but explicit variant families cannot be validated and
//! must not be admitted for later proof search.
//!
//! Every check reads the theory's items through `Theory::items`,
//! [`Theory::rules`] and [`Theory::lemmas`], which hand them out in item
//! order, and nothing in the pass reorders that list: an item's index in
//! `Theory::items` is its identity, and the report follows it.

use std::collections::BTreeSet;

use tamarin_term::maude_proc::MaudeHandle;

use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{pretty_proto_rule_name, ProtoRuleE};
use crate::theory::Theory;
use crate::tools::rule_variants::VariantsError;

pub mod check_terms;
pub mod equations;
pub mod facts;
pub mod formulas;
pub mod lemmas;
pub mod mult;
pub mod rules;
pub mod variants;

// =============================================================================
// Error type
// =============================================================================

/// A wellformedness diagnostic. `topic` matches exactly the underlined
/// header string Tamarin emits (e.g. `"Reserved names"`,
/// `"Fact arity issues"`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WfError {
    /// Short title used for grouping/ordering — matches HS's
    /// `underlineTopic` argument exactly (e.g. `"Reserved names"`).
    pub topic: String,
    /// Fully-formatted HS-style block for this entry.  When multiple
    /// `WfError`s share a topic the `format_wf_block` formatter
    /// concatenates the messages, separated by blank lines, beneath
    /// the topic header (which is part of `message`).
    pub message: String,
}

impl WfError {
    pub fn new(topic: impl Into<String>, message: impl Into<String>) -> Self {
        WfError {
            topic: topic.into(),
            message: message.into(),
        }
    }

    /// A `WfError` whose body is a ready `Doc`, framed the way
    /// `prettyWfErrorReport` frames a plain topic group:
    /// `text topic $-$ nest 2 body`, rendered into
    /// [`WfError::message`].
    pub fn block(topic: impl Into<String>, body: Doc) -> Self {
        let topic = topic.into();
        let message = Doc::text(&topic)
            .above_g(body.nest(2))
            .render_with(WF_LINE_LENGTH, WF_RIBBON);
        WfError { topic, message }
    }

    /// A block with an underlined heading, retaining the bare grouping topic.
    /// Haskell opts into `underlineTopic` per check; accountability uses plain
    /// headings and must not inherit the rule checks' formatting.
    pub fn underlined_block(topic: impl Into<String>, body: Doc) -> Self {
        let topic = topic.into();
        let message = Doc::text(underline_topic(&topic))
            .above_g(body.nest(2))
            .render_with(WF_LINE_LENGTH, WF_RIBBON);
        WfError { topic, message }
    }

    /// A `WfError` whose body is HS's `text info $-$ nest 2 (fsep $ punctuate
    /// comma cells)` paragraph fill — `unboundCheck`
    /// (Wellformedness.hs), `reservedFactNameRules'`
    /// (Wellformedness.hs) and `specialFactsUsage'`
    /// (Wellformedness.hs).
    ///
    /// HS builds such a body as ONE `Doc` and lets the layout engine break it,
    /// so a cell that overruns the ribbon does not merely get a line of its
    /// own: it breaks at its OWN `sep`/`fsep`/`fcat` points, dropping
    /// `prettyLNFact`'s closing `)` onto the next line and refilling the
    /// argument list at the `nestShort'` indent
    /// (Text/PrettyPrint/Class.hs).  `cells` are those documents —
    /// `prettyLNFact` (Theory/Model/Fact.hs) or `prettyLVar`
    /// (`prettyVarList`, TheoryObject.hs) — and the body is laid out
    /// here, into [`WfError::message`].
    ///
    /// `info` is HS's `text info`, the body's first line; the `nest 2`
    /// `prettyWfErrorReport` applies to every body of a topic group
    /// (Wellformedness.hs) is baked in, because the break decisions
    /// depend on the body's absolute column.
    pub fn filled(topic: impl Into<String>, info: impl Into<String>, cells: Vec<Doc>) -> Self {
        // HS `fsep $ punctuate comma cells` with `comma = char ','`
        // (Text/PrettyPrint/Class.hs).
        let list = hpj::fsep(hpj::punctuate(Doc::char(','), cells));
        // `above_g` is HughesPJ's `$+$`, which HS's `$-$` maps to
        // (Text/PrettyPrint/Class.hs); `info` is a single `text` (its
        // `<->` join cannot break), so it keeps its trailing spaces on the
        // line above the fill.
        let message = Doc::text(info.into())
            .above_g(list.nest(2))
            .nest(2)
            .render_with(WF_LINE_LENGTH, WF_RIBBON);
        WfError {
            topic: topic.into(),
            message,
        }
    }
}

/// `lineLength` of the style HughesPJ's `render` uses, reached from HS through
/// `addComment`'s `render` (TheoryObject.hs).
const WF_LINE_LENGTH: usize = 100;
/// `ribbonLen = round (100 / 1.5) = 67` for [`WF_LINE_LENGTH`].
const WF_RIBBON: usize = 67;

pub type WfReport = Vec<WfError>;

// =============================================================================
// The pass
// =============================================================================

/// Port of HS `checkWellformedness` (Wellformedness.hs): every
/// check of HS's list literal, run once over the TRANSLATED theory, in that
/// list's order.
///
/// HS's `incompleteMSRs :: Bool` is a literal `False` at its only call site
/// (`checkTranslatedTheory`, TheoryLoader.hs), so `factReports`' two
/// `inexistentActions` arms are unreachable and stay unported; the parameter
/// is absent here.  HS's `SignatureWithMaude` argument reaches only
/// `ruleVariantsReport`; every other check that needs the signature reads it
/// off the theory (`get (sigpMaudeSig . thySignature) thy`,
/// Wellformedness.hs), which is what
/// `thy.signature` is here.
///
/// Variant checks need a live Maude process. Without it, theories declaring
/// explicit families return an error, even if those families might be valid:
/// missing validation must not become permission to use them after recovery.
pub fn check_wellformedness(
    thy: &Theory,
    maude: Option<&MaudeHandle>,
) -> Result<WfReport, VariantsError> {
    // WF reports are plain text even when the interactive caller is building
    // an HTML document. Keep that invariant at the pass boundary so every
    // current and future sub-report is covered uniformly.
    let _plain = crate::pretty_hpj::HtmlDocGuard::disable();
    let mut variants = match maude {
        Some(maude) => variants::explicit_variants_report(thy, maude)?,
        None if thy.rules().any(|r| !r.rule_ac.is_empty()) => {
            return Err(VariantsError::MissingMaudeForExplicitVariants);
        }
        None => Vec::new(),
    };
    variants.extend(rules::rule_variants_report(thy, maude));
    let mut report = lemmas::check_if_lemmas_in_theory(thy);
    report.extend(rules::unbound_report(thy));
    report.extend(rules::fresh_names_report(thy));
    report.extend(rules::public_names_report(thy));
    report.extend(rules::rule_sorts_report(thy));
    report.extend(variants);
    report.extend(facts::fact_reports(thy));
    report.extend(formulas::formula_reports(thy));
    report.extend(lemmas::lemma_attribute_report(thy));
    report.extend(mult::mult_restricted_report(thy));
    report.extend(rules::nat_well_sorted_report(thy));
    report.extend(equations::subterm_convergence_report(&thy.signature));
    Ok(report)
}

/// The ordered set of distinct topic strings present in `report`.
pub fn topics(report: &WfReport) -> BTreeSet<String> {
    report.iter().map(|e| e.topic.clone()).collect()
}

// =============================================================================
// Helpers — rules and report formatting
// =============================================================================

/// HS `thyProtoRules` (Wellformedness.hs): the macro-applied E-rule
/// of every rule item, in item order.
fn thy_proto_rules(thy: &Theory) -> impl Iterator<Item = &ProtoRuleE> {
    thy.rules().map(|opr| &opr.rule)
}

/// HS `showRuleCaseName` (Theory/Model/Rule.hs): `render
/// . ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName`, whose
/// protocol-rule arm is all a [`ProtoRuleE`] reaches.
fn show_rule_case_name(ru: &ProtoRuleE) -> String {
    pretty_proto_rule_name(&ru.info.name).render()
}

/// HS `quote cs = '`' : cs ++ "'"` (Wellformedness.hs).
fn quote(s: &str) -> String {
    format!("`{}'", s)
}

/// Build an HS `underlineTopic` block: `"<title>\n<====>\n"` where the
/// underline matches the title length exactly (counting any trailing
/// space).  Mirrors `underlineTopic` in `Theory.Tools.Wellformedness`.
pub fn underline_topic(title: &str) -> String {
    let len = title.chars().count();
    let mut s = String::with_capacity(title.len() + len + 2);
    s.push_str(title);
    s.push('\n');
    for _ in 0..len {
        s.push('=');
    }
    s.push('\n');
    s
}

/// HS `numbered'` index width: `nWidth = length (show n)` where `n` is the
/// number of items (PrettyPrint/Class.hs).  Each index is rendered as
/// `flushRight nWidth (show i)` — i.e. left-padded with spaces to this width —
/// so a 1-of-10+ list prints ` 1.`…`10.`.
fn numbered_index_width(count: usize) -> usize {
    count.to_string().len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn block_heading_style_is_explicit() {
        let plain = WfError::block("Topic", Doc::text("body"));
        let underlined = WfError::underlined_block("Topic", Doc::text("body"));
        assert_eq!(plain.topic, underlined.topic);
        assert_eq!(plain.message, "Topic\n  body");
        assert_eq!(underlined.message, "Topic\n=====\n\n  body");
    }
}
