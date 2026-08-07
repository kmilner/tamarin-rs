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
//! six checks collected here are the ones that must see the translated theory
//! (and, for three of them, the elaborated `MaudeSig` the parser cannot
//! reach), so each one's findings REPLACE the pre-translation entries of its
//! topic and are spliced back at HS's check position.
//!
//! Both drivers — the batch CLI (`run.rs`) and the web server's theory load
//! (`theory_io.rs`) — run exactly this ordered sequence, so it lives here
//! once.  The batch path additionally splices a seventh, Maude-dependent
//! "Rule variants" block afterwards; that stays at its call site.
//!
//! The `post_thy` every parser-level check reads is the translated theory with
//! macros expanded, mirroring HS `thyProtoRules` / `applyMacroInFormula`.

use tamarin_parser::ast as p;
use tamarin_parser::wf::{
    after_public_names_topics, after_unbound_topics, insert_wf_before, WfError,
    WF_AFTER_CHECK_GUARDED, WF_AFTER_FACT_LHS, WF_AFTER_MULT_RESTRICTED, WF_AFTER_NAT_SORTED,
    WF_TOPIC_ORDER,
};
use tamarin_term::maude_sig::MaudeSig;

use crate::theory::Theory;

/// Re-run the translated-theory wellformedness checks over `parsed` /
/// `elaborated` and splice their findings into `wf_report`, in HS's check
/// order.
///
/// `maude_sig` is the elaborated signature's `MaudeSig` as captured by the
/// caller before translation — the reducible/irreducible funsym
/// classification HS's `checkTerms` and `multRestrictedReport` read.
///
/// For a non-SAPIC theory the three SAPIC-gated checks are skipped and the
/// remaining three are no-ops relative to the pre-translation run (the pre-
/// and post-translation rule sets are equal).
pub fn splice_translated_wf_reports(
    parsed: &p::Theory,
    elaborated: &Theory,
    maude_sig: &MaudeSig,
    wf_report: &mut Vec<WfError>,
) {
    let post_thy = crate::macro_expand::macro_expanded_clone(parsed);
    if elaborated.is_sapic {
        // HS `unboundReport` (Wellformedness.hs:514-519) also walks
        // `thyProtoRules` of the TRANSLATED theory, so a variable that is free
        // only inside a process's embedded `_restrict` — lifted into the
        // generated rule's `Restr_<rule>_<i>( … )` action, bound by no premise
        // — is reported against the generated rule.  Replace the
        // pre-translation entries (user rules only) with the full
        // post-translation set: `post_thy` keeps the user rules in source
        // order and carries the generated ones appended after them, matching
        // HS's item order.  Position: HS check index 2, so the findings splice
        // before the first entry from a later check.
        wf_report.retain(|e| e.topic != "Unbound variables");
        let unbound = tamarin_parser::wf::unbound_report(&post_thy);
        insert_wf_before(wf_report, unbound, &after_unbound_topics());

        // HS `factLhsOccurNoRhs` likewise sees the generated rules, so
        // SAPIC-only premise facts — e.g. a `Message( c, m )` consumed by an
        // `in(c,m)` with no producing `out` — are surfaced too.  Insert at the
        // factReports position (after fact_usage, before formulaReports),
        // matching HS check order.
        let topic = "Facts occur in the left-hand-side but not in any right-hand-side ";
        wf_report.retain(|e| e.topic != topic);
        let lhs_rhs = tamarin_parser::wf::fact_lhs_occur_no_rhs(&post_thy);
        insert_wf_before(wf_report, lhs_rhs, &WF_TOPIC_ORDER[WF_AFTER_FACT_LHS..]);

        // HS `publicNamesReport` (Wellformedness.hs:463-484) also runs on the
        // TRANSLATED rules (`checkWellformedness` over the OpenTranslated
        // theory).  The parser-level `public_names_report` ran pre-translation
        // (no generated rules) and cannot see the source process a rule
        // carries as its `process=` attribute; re-run over the ELABORATED
        // rules (facts + process attribute) so a constant appearing only in
        // the process — e.g. `'C'` in `insert <'roles', x, 'C'>` clashing with
        // `'c'` — is surfaced, attributed to the root `Init` rule exactly as
        // HS.  Position: publicNames is HS check index 4, so it splices before
        // the first entry from a LATER check — ruleSorts (HS index 5, the
        // `variable_sort_clashes` topic) or any `WF_TOPIC_ORDER` topic except
        // "Unbound variables" (`unboundReport`, HS index 2, runs BEFORE
        // publicNames, so its entries must not act as a boundary).
        let caps_topic = "Public constants with mismatching capitalization";
        wf_report.retain(|e| e.topic != caps_topic);
        let public_names = crate::elaborate::sapic_public_names_report(elaborated);
        insert_wf_before(wf_report, public_names, &after_public_names_topics());
    }

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
    //     accountability's `translate` appends.  Both land in the parsed
    //     theory only after `apply_sapic` / `Acc::translate`, so the check
    //     reads `post_thy`.
    //
    // Position: HS check index 8, so the findings splice before the first
    // entry from a later check (`lemmaAttributeReport` onwards).
    let formula_errors = crate::formula_reports::formula_reports(&post_thy, maude_sig);
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

    // HS `natWellSortedReport` (Wellformedness.hs:318-333) reads
    // `thyProtoRules` of the `OpenTranslatedTheory`, so the rules SAPIC's
    // translation generates are in scope: a `%+` operand that is a msg-sorted
    // process variable (e.g. `let j:nat = i%+%1`, where the `:nat` is a SAPIC
    // TYPE and `i` stays msg-sorted) is only visible once the process has
    // become rules.  Position: HS check index 11, so the findings splice
    // before the first entry from a later check.
    if elaborated.is_sapic {
        wf_report.retain(|e| e.topic != "Nat Sorts");
        let nat_errors = tamarin_parser::wf::nat_well_sorted_report(&post_thy);
        insert_wf_before(
            wf_report,
            nat_errors,
            &WF_TOPIC_ORDER[WF_AFTER_NAT_SORTED..],
        );
    }
}
