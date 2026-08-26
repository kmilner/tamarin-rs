// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! (Wellformedness.hs:1270-1286): one pass over the translated theory that
//! runs the checks in the order of HS's list literal.  Both drivers — the
//! batch CLI (`run.rs`) and the web server's theory load (`theory_io.rs`) —
//! call it once, after the SAPIC and accountability translations, so the
//! rules SAPIC generated and the lemmas accountability appended are in
//! scope.  The batch path additionally splices a Maude-dependent "Rule
//! variants" block into the result at HS position 6; that stays at its call
//! site, with [`AFTER_VARIANTS_TOPICS`] and [`insert_wf_before`].
//!
//! Every check reads the theory's items through `Theory::items`,
//! [`Theory::rules`] and [`Theory::lemmas`], which hand them out in item
//! order, and nothing in the pass reorders that list: an item's index in
//! `Theory::items` is its identity, and the report follows it.

use std::collections::BTreeSet;

use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{pretty_proto_rule_name, ProtoRuleE};
use crate::theory::Theory;

pub mod check_terms;
pub mod equations;
pub mod facts;
pub mod formulas;
pub mod lemmas;
pub mod mult;
pub mod rules;

// =============================================================================
// Error type
// =============================================================================

/// A wellformedness diagnostic. `topic` matches exactly the underlined
/// header string Tamarin emits (e.g. `"Reserved names"`,
/// `"Fact arity issues"`).
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
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

    /// A `WfError` whose body is HS's `text info $-$ nest 2 (fsep $ punctuate
    /// comma cells)` paragraph fill — `unboundCheck`
    /// (Wellformedness.hs:497-498), `reservedFactNameRules'`
    /// (Wellformedness.hs:546) and `specialFactsUsage'`
    /// (Wellformedness.hs:563).
    ///
    /// HS builds such a body as ONE `Doc` and lets the layout engine break it,
    /// so a cell that overruns the ribbon does not merely get a line of its
    /// own: it breaks at its OWN `sep`/`fsep`/`fcat` points, dropping
    /// `prettyLNFact`'s closing `)` onto the next line and refilling the
    /// argument list at the `nestShort'` indent
    /// (Text/PrettyPrint/Class.hs:218-223).  `cells` are those documents —
    /// `prettyLNFact` (Theory/Model/Fact.hs:567-574) or `prettyLVar`
    /// (`prettyVarList`, TheoryObject.hs:858-859) — and the body is laid out
    /// here, into [`WfError::message`].
    ///
    /// `info` is HS's `text info`, the body's first line; the `nest 2`
    /// `prettyWfErrorReport` applies to every body of a topic group
    /// (Wellformedness.hs:118-125) is baked in, because the break decisions
    /// depend on the body's absolute column.
    pub fn filled(topic: impl Into<String>, info: impl Into<String>, cells: Vec<Doc>) -> Self {
        // HS `fsep $ punctuate comma cells` with `comma = char ','`
        // (Text/PrettyPrint/Class.hs:121).
        let list = hpj::fsep(hpj::punctuate(Doc::char(','), cells));
        // `above_g` is HughesPJ's `$+$`, which HS's `$-$` maps to
        // (Text/PrettyPrint/Class.hs:180); `info` is a single `text` (its
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
/// `addComment`'s `render` (TheoryObject.hs:717-718).
pub(super) const WF_LINE_LENGTH: usize = 100;
/// `ribbonLen = round (100 / 1.5) = 67` for [`WF_LINE_LENGTH`].
pub(super) const WF_RIBBON: usize = 67;

pub type WfReport = Vec<WfError>;

// =============================================================================
// The pass
// =============================================================================

/// Port of HS `checkWellformedness` (Wellformedness.hs:1270-1286): every
/// check of HS's list literal, run once over the TRANSLATED theory, in that
/// list's order.
///
/// HS's `incompleteMSRs :: Bool` is a literal `False` at its only call site
/// (`checkTranslatedTheory`, TheoryLoader.hs:602), so `factReports`' two
/// `inexistentActions` arms are unreachable and stay unported; the parameter
/// is absent here.  HS's `SignatureWithMaude` argument reaches only
/// `ruleVariantsReport`; every other check that needs the signature reads it
/// off the theory (`get (sigpMaudeSig . thySignature) thy`,
/// Wellformedness.hs:1003, :1113, :1211-1214), which is what
/// `thy.signature.maude_sig` is here.
///
/// `ruleVariantsReport` (HS position 6) needs a live Maude process, so the
/// batch driver runs it and splices its findings into the result with
/// [`insert_wf_before`] and [`AFTER_VARIANTS_TOPICS`]; the web load path
/// produces no such block.
pub fn check_wellformedness(thy: &Theory) -> WfReport {
    let sig = &thy.signature.maude_sig;
    let mut report = lemmas::check_if_lemmas_in_theory(thy);
    report.extend(rules::unbound_report(thy));
    report.extend(rules::fresh_names_report(thy));
    report.extend(rules::public_names_report(thy));
    report.extend(rules::rule_sorts_report(thy));
    report.extend(facts::fact_reports(thy));
    report.extend(formulas::formula_reports(thy, sig));
    report.extend(lemmas::lemma_attribute_report(thy));
    report.extend(mult::mult_restricted_report(thy, sig));
    report.extend(rules::nat_well_sorted_report(thy));
    report.extend(equations::subterm_convergence_report(sig));
    report
}

/// Anchor list for the batch driver's `ruleVariantsReport` splice: every
/// topic [`check_wellformedness`] emits from a check HS runs AFTER it
/// (Wellformedness.hs:1272-1285) — the `factReports` group, `formulaReports`,
/// `lemmaAttributeReport`, `multRestrictedReport`, `natWellSortedReport` and
/// `checkEquationsSubtermConvergence`.  [`insert_wf_before`] tests membership
/// only, so the topics of the five earlier checks are absent from this list
/// and cannot act as a boundary.
pub const AFTER_VARIANTS_TOPICS: &[&str] = &[
    "Reserved names",
    "Fr facts must only use a fresh- or a msg-variable",
    "Special facts",
    "Fact capitalization issues",
    "Fact arity issues",
    "Fact multiplicity issues",
    "Facts occur in the left-hand-side but not in any right-hand-side ",
    "Quantifier sorts",
    "Formula terms",
    " Formula guardedness",
    "Lemma annotations",
    "Multiplication restriction of rules",
    "Nat Sorts",
    "Subterm Convergence Warning",
];

/// Splice `errors` into `report` immediately before the first existing entry
/// whose `topic` is one of `anchors`, or at the end if none match, preserving
/// the relative order of both the existing tail and the inserted errors.
/// No-op when `errors` is empty.
pub fn insert_wf_before(report: &mut Vec<WfError>, errors: Vec<WfError>, anchors: &[&str]) {
    if errors.is_empty() {
        return;
    }
    let insert_before = report
        .iter()
        .position(|e| anchors.contains(&e.topic.as_str()))
        .unwrap_or(report.len());
    let tail = report.split_off(insert_before);
    report.extend(errors);
    report.extend(tail);
}

/// The ordered set of distinct topic strings present in `report`.
pub fn topics(report: &WfReport) -> BTreeSet<String> {
    report.iter().map(|e| e.topic.clone()).collect()
}

// =============================================================================
// Helpers — rules and report formatting
// =============================================================================

/// HS `thyProtoRules` (Wellformedness.hs:133-134): the macro-applied E-rule
/// of every rule item, in item order.
pub(super) fn thy_proto_rules(thy: &Theory) -> impl Iterator<Item = &ProtoRuleE> {
    thy.rules().map(|opr| &opr.rule)
}

/// HS `showRuleCaseName` (Theory/Model/Rule.hs:1337-1340): `render
/// . ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName`, whose
/// protocol-rule arm is all a [`ProtoRuleE`] reaches.
pub(super) fn show_rule_case_name(ru: &ProtoRuleE) -> String {
    pretty_proto_rule_name(&ru.info.name).render()
}

/// HS `quote cs = '`' : cs ++ "'"` (Wellformedness.hs:164-165).
pub(super) fn quote(s: &str) -> String {
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

/// Assemble a topic-grouped `WfReport` from pre-built body strings (empty
/// `bodies` yields an empty report).  `underline_topic` already ends the
/// `====` rule with a newline, so the extra `\n` is HS's `$-$` blank line
/// before the bodies; the bodies are joined by the `\n  \n` that HS's
/// `nest 2 (vcat (intersperse (text "") …))` renders a blank separator line
/// as (a 2-space `nest 2`'d `text ""`).  Each body already carries its own
/// 2-space `nest 2` indent.
fn grouped_topic_block(topic: &str, bodies: Vec<String>) -> WfReport {
    if bodies.is_empty() {
        return Vec::new();
    }
    let mut msg = underline_topic(topic);
    msg.push('\n');
    msg.push_str(&bodies.join("\n  \n"));
    vec![WfError::new(topic, msg)]
}

/// HS `numbered'` index width: `nWidth = length (show n)` where `n` is the
/// number of items (PrettyPrint/Class.hs:257-258).  Each index is rendered as
/// `flushRight nWidth (show i)` — i.e. left-padded with spaces to this width —
/// so a 1-of-10+ list prints ` 1.`…`10.`.
fn numbered_index_width(count: usize) -> usize {
    count.to_string().len()
}
