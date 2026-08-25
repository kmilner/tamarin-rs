// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The wellformedness checks HS runs on the TRANSLATED theory
//! (`checkTranslatedTheory`, TheoryLoader.hs:553-565).
//!
//! HS has ONE `checkWellformedness` pass, and it runs on the
//! `OpenTranslatedTheory` — i.e. AFTER SAPIC `translate` has injected the
//! generated rules and accountability's `translate` has appended its lemmas.
//! The port instead runs `tamarin_parser::wf::check_theory` early, on the
//! PRE-translation parser theory, because most checks need nothing else; the
//! checks collected here are the ones that must see the translated theory
//! (and, for `formula_reports` and `mult_restricted_report`, the elaborated
//! `MaudeSig` the parser cannot reach).  They read the ELABORATED theory —
//! the rules SAPIC generated, the lemmas accountability appended, and the
//! macro- and predicate-expanded item formulas — and splice in as the sole
//! producers of their topics, at HS's check positions.
//!
//! Both drivers — the batch CLI (`run.rs`) and the web server's theory load
//! (`theory_io.rs`) — run exactly this ordered sequence, so it lives here
//! once.  The batch path additionally splices a Maude-dependent "Rule
//! variants" block afterwards; that stays at its call site.
//!
//! The same two drivers also share this module's report-ASSEMBLY steps —
//! [`pre_translation_wf_report`], [`swap_subterm_convergence_report`], and
//! [`prepend_wf_report`] — so the drop/replace/prepend invariants each step
//! encodes cannot drift between the pipelines.

use tamarin_parser::ast as p;
use tamarin_parser::wf::{
    after_public_names_topics, after_unbound_topics, insert_wf_before, WfError,
    WF_AFTER_CHECK_GUARDED, WF_AFTER_FACT_LHS, WF_AFTER_MULT_RESTRICTED, WF_AFTER_NAT_SORTED,
    WF_TOPIC_ORDER,
};
use tamarin_term::maude_sig::MaudeSig;

use crate::theory::Theory;

/// The PRE-translation static wellformedness pass both drivers open with:
/// clone `parsed` with macros expanded — HS `thyProtoRules`
/// (Wellformedness.hs:133-134) applies `applyMacroInRule` to every rule
/// before the checks — run `check_theory` on the clone, and drop the
/// static "Message Derivation Checks" entry, which the dynamic,
/// Maude-backed check each driver runs later replaces.
///
/// The sole caller of [`crate::macro_expand::macro_expanded_clone`]; stage 8
/// deletes both when `check_theory`'s remaining checks move off the AST.
pub fn pre_translation_wf_report(parsed: &p::Theory) -> Vec<WfError> {
    let parsed_for_wf = crate::macro_expand::macro_expanded_clone(parsed);
    let mut report = tamarin_parser::wf::check_theory(&parsed_for_wf);
    report.retain(|e| e.topic != "Message Derivation Checks");
    report
}

/// Replace `check_theory`'s AST-level "Subterm Convergence Warning"
/// placeholder with the signature-driven version, once elaboration has
/// produced the `MaudeSig`.  HS `checkEquationsSubtermConvergence`
/// (Wellformedness.hs:1222-1232) works on `thyEquations = S.toList
/// (stRules sig)` — the SIGNATURE's subterm-rule Set, not the parser-AST
/// `equations:` blocks — so the entry carries `Ord CtxtStRule` Set order
/// and `prettyCtxtStRule`'s width-wrap, neither of which the parser-level
/// placeholder can reproduce.
pub fn swap_subterm_convergence_report(wf_report: &mut Vec<WfError>, maude_sig: &MaudeSig) {
    wf_report.retain(|e| e.topic != "Subterm Convergence Warning");
    wf_report.extend(crate::pretty_theory::subterm_convergence_report_wf(
        maude_sig,
    ));
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

/// Re-run the translated-theory wellformedness checks over `elaborated` and
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
    let unbound = crate::translated_rule_wf::unbound_report(elaborated);
    insert_wf_before(wf_report, unbound, &after_unbound_topics());

    // Port of HS `factLhsOccurNoRhs` (Wellformedness.hs:214-256), which
    // likewise sees the generated rules, so SAPIC-only premise facts — e.g. a
    // `Message( c, m )` consumed by an `in(c,m)` with no producing `out` —
    // are surfaced too.  Position: the factReports group (after fact_usage,
    // before formulaReports), matching HS check order.
    let lhs_rhs = crate::translated_rule_wf::fact_lhs_occur_no_rhs(elaborated);
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
    let public_names = crate::elaborate::translated_public_names_report(elaborated);
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
    let formula_errors = crate::formula_reports::formula_reports(elaborated, maude_sig);
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
    let mult_errors = crate::mult_restricted::mult_restricted_report(elaborated, maude_sig);
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
    let nat_errors = crate::translated_rule_wf::nat_well_sorted_report(elaborated);
    insert_wf_before(
        wf_report,
        nat_errors,
        &WF_TOPIC_ORDER[WF_AFTER_NAT_SORTED..],
    );
}
