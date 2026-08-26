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
//! [`check_theory`] runs the checks that read the parser AST.  The checks
//! that read the elaborated theory — the rules SAPIC generated, the lemmas
//! accountability appended, the macro- and predicate-expanded item formulas —
//! or its `MaudeSig` come from [`splice_translated_wf_reports`] and
//! [`append_subterm_convergence_report`], which insert their findings at HS's
//! check positions; see [`WF_TOPIC_ORDER`] and [`insert_wf_before`].  Both
//! drivers — the batch CLI (`run.rs`) and the web server's theory load
//! (`theory_io.rs`) — run exactly that sequence, so it lives here once.  The
//! batch path additionally splices a Maude-dependent "Rule variants" block
//! afterwards; that stays at its call site.
//!
//! The AST checks read the `LSort` the parser stamps on each variable rather
//! than a full sort assignment, so a check that needs term-level sort
//! inference (e.g. `Nat Sorts`) is one of the spliced ones.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_term::lterm::sort_prefix;
use tamarin_term::maude_sig::MaudeSig;

use crate::pretty_hpj::{self as hpj, Doc};
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
const WF_LINE_LENGTH: usize = 100;
/// `ribbonLen = round (100 / 1.5) = 67` for [`WF_LINE_LENGTH`].
const WF_RIBBON: usize = 67;

pub type WfReport = Vec<WfError>;

// =============================================================================
// Shared report ordering (batch `--prove` and web load pipelines)
// =============================================================================

/// Canonical HS wellformedness check-order (Wellformedness.hs check list).
/// Each ordered-splice call site (in the batch `run.rs` and web `theory_io.rs`
/// load pipelines) passes a SUFFIX of this list as its `anchors`: since
/// [`insert_wf_before`] only tests membership, a suffix contains exactly the
/// topics that sort AFTER the check being inserted.  One source of truth
/// avoids several in-sync literal lists that would silently mis-order a single
/// report on a typo.
pub const WF_TOPIC_ORDER: &[&str] = &[
    "Reserved names",
    "Special facts",
    "Fr facts must only use a fresh- or a msg-variable",
    "Fact arity issues",
    "Fact multiplicity issues",
    "Fact capitalization issues",
    "Facts occur in the left-hand-side but not in any right-hand-side ",
    "Unbound variables",
    "Quantifier sorts",
    "Formula terms",
    " Formula guardedness",
    "Lemma annotations",
    "Multiplication restriction of rules",
    "Nat Sorts",
    "Subterm Convergence Warning",
    "Message Derivation Checks",
    "Derivation Checks",
];

// First `WF_TOPIC_ORDER` index whose topic sorts after each splicing check.
pub const WF_AFTER_FACT_LHS: usize = 8; // "Quantifier sorts"
pub const WF_AFTER_CHECK_GUARDED: usize = 11; // "Lemma annotations"
pub const WF_AFTER_MULT_RESTRICTED: usize = 13; // "Nat Sorts"
pub const WF_AFTER_NAT_SORTED: usize = 14; // "Subterm Convergence Warning"

/// Splice `errors` into `report` immediately before the first existing entry
/// whose `topic` is one of `anchors` (its HS check-order position), or at the
/// end if none match, preserving the relative order of both the existing tail
/// and the inserted errors.  Shared by the batch (`run.rs`) and web
/// (`theory_io.rs`) ordered-splice call sites — the SAPIC unbound / lhs-rhs /
/// publicNames re-splices, formulaReports, multRestricted and ruleVariants —
/// which differ only in their `anchors` slice and the source of `errors`.
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

/// Anchor list for the SAPIC `publicNamesReport` splice (HS check index 4):
/// the variable-sorts topic, then every [`WF_TOPIC_ORDER`] topic EXCEPT
/// "Unbound variables" (HS `unboundReport` runs BEFORE `publicNames`, so its
/// entries must not act as a boundary).  publicNames therefore splices before
/// the first entry from a later check.
pub fn after_public_names_topics() -> Vec<&'static str> {
    std::iter::once("Variable with mismatching sorts or capitalization")
        .chain(
            WF_TOPIC_ORDER
                .iter()
                .copied()
                .filter(|t| *t != "Unbound variables"),
        )
        .collect()
}

/// Anchor list for the `ruleVariantsReport` splice (HS check index 6): every
/// [`WF_TOPIC_ORDER`] topic EXCEPT "Unbound variables", whose `unboundReport`
/// (index 2) runs earlier and so must not act as a boundary.  The three checks
/// between them — `freshNamesReport`, `publicNamesReport`, `ruleSortsReport` —
/// emit topics `WF_TOPIC_ORDER` does not carry, so they are already outside
/// the list.  ruleVariants therefore splices before the first `factReports`
/// entry.
pub fn after_variants_topics() -> Vec<&'static str> {
    WF_TOPIC_ORDER
        .iter()
        .copied()
        .filter(|t| *t != "Unbound variables")
        .collect()
}

/// Topics emitted by a check that runs after `unboundReport`, but which
/// [`WF_TOPIC_ORDER`] does not carry: `freshNamesReport` (HS index 3),
/// `publicNamesReport` (4), `ruleSortsReport` (5) and `ruleVariantsReport`
/// (6).
const AFTER_UNBOUND_EXTRA_TOPICS: &[&str] = &[
    "Fresh public constants",
    "Public constants with mismatching capitalization",
    "Variable with mismatching sorts or capitalization",
    "Rule has no variants",
];

/// Anchor list for the SAPIC `unboundReport` re-splice (HS check index 2):
/// every topic a LATER check emits.  `unboundReport` is the first entry of
/// `checkWellformedness`'s list past `checkIfLemmasInTheory`
/// (Wellformedness.hs:1270-1286), so the boundary set is every topic except
/// its own and those of the checks ahead of it — the `preReport` topics (SAPIC
/// process warnings, the accountability RP check) and the `--prove`/`--lemma`
/// argument check.  Their absence is what keeps the re-spliced entries behind
/// them.
pub fn after_unbound_topics() -> Vec<&'static str> {
    AFTER_UNBOUND_EXTRA_TOPICS
        .iter()
        .copied()
        .chain(
            WF_TOPIC_ORDER
                .iter()
                .copied()
                .filter(|t| *t != "Unbound variables"),
        )
        .collect()
}

/// Run every wellformedness check against the theory, held as the
/// elaborated `elab` and the parser AST `parsed`. Topics from the result
/// can be compared directly against `tamarin-prover`'s output.
pub fn check_theory(elab: &Theory, parsed: &p::Theory) -> WfReport {
    // Mirrors HS `Theory.Tools.Wellformedness.checkWellformedness`
    // (Wellformedness.hs:1270-1286) in HS check order: unbound, freshNames,
    // publicNames, ruleSorts (variable_sort_clashes), factReports,
    // formulaReports, lemmaAttribute, multRestricted, natWellSorted,
    // subtermConvergence.
    let mut report = Vec::new();
    // unboundReport — spliced by `splice_translated_wf_reports`
    // (`rules::unbound_report`, anchored by `after_unbound_topics`): it reads
    // the TRANSLATED theory's rules, so the ones SAPIC's process translation
    // generates are in scope.
    report.extend(rules::fresh_names_report(elab, parsed));
    // publicNamesReport — spliced by `splice_translated_wf_reports`
    // (`rules::translated_public_names_report`, anchored by
    // `after_public_names_topics`): it reads the TRANSLATED rules, whose
    // `process` attribute carries the constants that appear only inside a
    // SAPIC process.
    // HS `ruleSortsReport` (sortsClashCheck) runs HERE — after publicNamesReport
    // and BEFORE factReports (Wellformedness.hs:1270-1286, see line 1275/1256).  It is ported as
    // `variable_sort_clashes` ("Variable with mismatching sorts or
    // capitalization").
    report.extend(rules::variable_sort_clashes(elab, parsed));
    // ruleVariantsReport — spliced by the batch load pipeline (`run.rs`,
    // anchored by `after_variants_topics`): it needs a MaudeHandle and the
    // variant solver.
    // factReports group (Wellformedness.hs:579-583).  Its last member,
    // factLhsOccurNoRhs, is spliced by `splice_translated_wf_reports`
    // (`rules::fact_lhs_occur_no_rhs`): same reason as unboundReport above.
    report.extend(facts::fact_reports(elab, parsed));
    // formulaReports group (checkQuantifiers / checkTerms / checkGuarded) —
    // spliced by `splice_translated_wf_reports` as one interleaved per-formula
    // pass (`formulas::formula_reports`): it needs the elaborated signature's
    // irreducible funsyms and the TRANSLATED theory's formulas.
    // lemmaAttributeReport:
    report.extend(lemmas::lemma_attribute_report(elab, parsed));
    // multRestrictedReport — spliced by `splice_translated_wf_reports`
    // (`mult::mult_restricted_report`): it needs the elaborated signature's
    // irreducible funsyms and the HughesPJ rule renderer.
    // natWellSortedReport — spliced by `splice_translated_wf_reports`
    // (`rules::nat_well_sorted_report`): same reason as unboundReport above.
    // checkEquationsSubtermConvergence — appended by
    // `append_subterm_convergence_report` (`equations::subterm_convergence_report`):
    // HS reads `thyEquations = S.toList (stRules sig)`, the elaborated
    // signature's subterm-rule Set.
    report
}

/// The ordered set of distinct topic strings present in `report`.
pub fn topics(report: &WfReport) -> BTreeSet<String> {
    report.iter().map(|e| e.topic.clone()).collect()
}

// =============================================================================
// Helpers — collecting facts and variables
// =============================================================================

/// The theory's protocol rules, HS `theoryRules` (TheoryObject.hs:304-306).
/// A top-level `rule (modulo AC)` block is an intruder rule: the parser puts
/// it in the theory's intruder-rule cache (`addIntrRuleACs`,
/// Theory/Text/Parser.hs:287, OpenTheory.hs:750-751), and `theoryRules` folds
/// over the items only, so no wellformedness check reads it.
fn theory_rules(thy: &p::Theory) -> impl Iterator<Item = &p::Rule> {
    thy.items.iter().filter_map(|it| match it {
        p::TheoryItem::Rule(r) => Some(r),
        _ => None,
    })
}

fn theory_lemmas(thy: &p::Theory) -> impl Iterator<Item = &p::Lemma> {
    thy.items.iter().filter_map(|it| match it {
        p::TheoryItem::Lemma(l) => Some(l),
        _ => None,
    })
}

/// Every fact of a rule in HS `ruleFacts`' order — `concatMap (`get` ru)
/// [rPrems, rActs, rConcs]` (Wellformedness.hs:585-587).
fn rule_facts(r: &p::Rule) -> impl Iterator<Item = &p::Fact> {
    r.premises
        .iter()
        .chain(r.actions.iter())
        .chain(r.conclusions.iter())
}

/// An `LVar` as HS `show` prints it — the sort prefix, the name, and the
/// index when it is nonzero (LTerm.hs:550-557).
fn render_var(v: &p::VarSpec) -> String {
    let prefix = sort_prefix(v.sort);
    if v.idx == 0 {
        format!("{}{}", prefix, v.name)
    } else {
        format!("{}{}.{}", prefix, v.name, v.idx)
    }
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

/// The static wellformedness pass over the theory as written, before the
/// SAPIC and accountability translations extend it: clone `parsed` with
/// macros expanded — HS `thyProtoRules` (Wellformedness.hs:133-134) applies
/// `applyMacroInRule` to every rule before the checks — and run
/// [`check_theory`] on the clone.  `elab` is the elaborated theory of the
/// same source, which both drivers build before this pass runs.
///
/// The sole caller of [`crate::macro_expand::macro_expanded_clone`].
pub fn pre_translation_wf_report(elab: &Theory, parsed: &p::Theory) -> Vec<WfError> {
    let parsed_for_wf = crate::macro_expand::macro_expanded_clone(parsed);
    check_theory(elab, &parsed_for_wf)
}

/// Append the signature-driven "Subterm Convergence Warning", once
/// elaboration has produced the `MaudeSig`.  HS
/// `checkEquationsSubtermConvergence` (Wellformedness.hs:1222-1232) works on
/// `thyEquations = S.toList (stRules sig)` — the SIGNATURE's subterm-rule
/// Set, not the parser-AST `equations:` blocks — so the entry carries
/// `Ord CtxtStRule` Set order and `prettyCtxtStRule`'s width-wrap.
///
/// It is the LAST check of HS's list (Wellformedness.hs:1285) and
/// `check_theory` emits no later check's entries, so appending puts it at
/// HS's position; [`splice_translated_wf_reports`] then anchors
/// `natWellSortedReport` on it.
pub fn append_subterm_convergence_report(wf_report: &mut Vec<WfError>, maude_sig: &MaudeSig) {
    wf_report.extend(equations::subterm_convergence_report(maude_sig));
}

/// Prepend `pre` to `wf_report` — HS's `preReport ++ postReport` splice
/// (TheoryLoader.hs:487-502, see line 497).  Used for the translation
/// stage's `Sapic.checkWellformedness ++ Acc.checkWellformedness` block
/// and for batch's `checkIfLemmasInTheory` result (FIRST in HS's
/// `checkWellformedness` list, Wellformedness.hs:1272).  No-op when `pre`
/// is empty.
pub fn prepend_wf_report(wf_report: &mut Vec<WfError>, mut pre: Vec<WfError>) {
    if pre.is_empty() {
        return;
    }
    pre.extend(std::mem::take(wf_report));
    *wf_report = pre;
}

/// Run the translated-theory wellformedness checks over `elaborated` and
/// splice their findings into `wf_report`, in HS's check order.
///
/// `maude_sig` is the elaborated signature's `MaudeSig` as captured by the
/// caller before translation — the reducible/irreducible funsym
/// classification HS's `checkTerms` and `multRestrictedReport` read.
///
/// HS gates none of these checks on the theory carrying a process, and
/// neither does this pass: each of them is the ONLY source of its topics, for
/// every theory.
pub fn splice_translated_wf_reports(
    elaborated: &Theory,
    maude_sig: &MaudeSig,
    wf_report: &mut Vec<WfError>,
) {
    // Port of HS `unboundReport` (Wellformedness.hs:514-519).  It walks
    // `thyProtoRules` of the TRANSLATED theory, so a variable that is free
    // only inside a process's embedded `_restrict` — lifted into the
    // generated rule's `Restr_<rule>_<i>( … )` action, bound by no premise —
    // is reported against the generated rule.  The elaborated theory keeps
    // the user rules in source order and carries the generated ones appended
    // after them, matching HS's item order.  Position: HS check index 2, so
    // the findings splice before the first entry from a later check.
    let unbound = rules::unbound_report(elaborated);
    insert_wf_before(wf_report, unbound, &after_unbound_topics());

    // Port of HS `factLhsOccurNoRhs` (Wellformedness.hs:214-256), which
    // likewise sees the generated rules, so SAPIC-only premise facts — e.g. a
    // `Message( c, m )` consumed by an `in(c,m)` with no producing `out` —
    // are surfaced too.  Position: the factReports group (after fact_usage,
    // before formulaReports), matching HS check order.
    let lhs_rhs = rules::fact_lhs_occur_no_rhs(elaborated);
    insert_wf_before(wf_report, lhs_rhs, &WF_TOPIC_ORDER[WF_AFTER_FACT_LHS..]);

    // Port of HS `publicNamesReport` (Wellformedness.hs:485-486, over the
    // `publicNamesReport'` body at 463-483), which also runs on the TRANSLATED
    // rules.  It reads the ELABORATED rules (facts + process attribute), so a
    // constant appearing only in a generated rule's source process — e.g. `'C'`
    // in `insert <'roles', x, 'C'>` clashing with `'c'` — is surfaced,
    // attributed to the root `Init` rule exactly as HS.  Position: publicNames
    // is HS check index 4, so it splices before the first entry from a LATER
    // check — ruleSorts (HS index 5, the `variable_sort_clashes` topic) or any
    // `WF_TOPIC_ORDER` topic except "Unbound variables" (`unboundReport`, HS
    // index 2, runs BEFORE publicNames, so its entries must not act as a
    // boundary).
    let public_names = rules::translated_public_names_report(elaborated);
    insert_wf_before(wf_report, public_names, &after_public_names_topics());

    // Port of HS `formulaReports` (Wellformedness.hs:996-1015) — the whole
    // check, all three arms.  It is ONE per-formula loop, `msum
    // [checkQuantifiers, checkTerms, checkGuarded]` inside the `annFormulas`
    // walk, so its three topics interleave in item order and a topic reopens
    // after an intervening one; running the arms as separate whole-report
    // splices would instead emit one block per topic.  `formula_reports` keeps
    // HS's emission order.
    //
    // Two dependencies pin the call to this position:
    //   - the elaborated `MaudeSig`, for `checkTerms`'s
    //     reducible/irreducible funsym classification (HS
    //     `irreducibleFunSyms maudeSig`), which the parser-level
    //     `check_theory` cannot see; and
    //   - the TRANSLATED theory, because HS's single `checkWellformedness`
    //     pass runs on the `OpenTranslatedTheory` (`checkTranslatedTheory`,
    //     TheoryLoader.hs:559-565, fed by `closeTheory` at :726-728), so
    //     `annFormulas` (Wellformedness.hs:1006-1015) also covers the
    //     restrictions SAPIC's `let … else` / `if` lowering mints
    //     (`Restr_<rule>_<i>`, carrying the branch's terms verbatim — e.g. an
    //     `exp` application from `<<'a'^'b','b'>, 'c'>`) and the lemmas
    //     accountability's `translate` appends.
    //
    // Position: HS check index 8, so the findings splice before the first
    // entry from a later check (`lemmaAttributeReport` onwards).
    let formula_errors = formulas::formula_reports(elaborated, maude_sig);
    insert_wf_before(
        wf_report,
        formula_errors,
        &WF_TOPIC_ORDER[WF_AFTER_CHECK_GUARDED..],
    );

    // Port of HS `multRestrictedReport` (Wellformedness.hs:1108-1113,
    // "Multiplication restriction of rules").  Pinned here by the same two
    // dependencies as `formula_reports` above: the elaborated `MaudeSig` (HS
    // `irreducibleFunSyms $ get (sigpMaudeSig . thySignature) thy`) and the
    // TRANSLATED theory — HS's `thyProtoRules` reads the
    // `OpenTranslatedTheory`'s rule items, so SAPIC's generated rules are in
    // scope, and it must run BEFORE the no-variant rules are dropped from the
    // elaborated theory (HS closes the theory only after
    // `checkWellformedness`).
    //
    // Position: HS check index 10 — after `lemmaAttributeReport` (9), before
    // `natWellSortedReport` (11), so splice before the first entry from a
    // later check.
    let mult_errors = mult::mult_restricted_report(elaborated, maude_sig);
    insert_wf_before(
        wf_report,
        mult_errors,
        &WF_TOPIC_ORDER[WF_AFTER_MULT_RESTRICTED..],
    );

    // Port of HS `natWellSortedReport` (Wellformedness.hs:318-333), which
    // reads `thyProtoRules` of the `OpenTranslatedTheory`, so the rules
    // SAPIC's translation generates are in scope: a `%+` operand that is a
    // msg-sorted process variable (e.g. `let j:nat = i%+%1`, where the `:nat`
    // is a SAPIC TYPE and `i` stays msg-sorted) is only visible once the
    // process has become rules.  Position: HS check index 11, so the findings
    // splice before the first entry from a later check.
    let nat_errors = rules::nat_well_sorted_report(elaborated);
    insert_wf_before(
        wf_report,
        nat_errors,
        &WF_TOPIC_ORDER[WF_AFTER_NAT_SORTED..],
    );
}
