//! wf-clean: a clean-room reimplementation of the tamarin-prover wellformedness
//! checker, derived purely from black-box oracle behavior. See
//! workspace/BEHAVIOR.md for the inferred behavioral spec.


pub mod checks;
pub mod formula;
pub mod pretty;
pub mod report;

pub use crate::ast::*;
pub use report::{
    insert_wf_before, render_report, topics, underline_topic, WfError, WfReport, SUCCESS_LINE,
};

/// Topics that follow the public-names report in the canonical order; the
/// public-names report is inserted immediately before the first of these that
/// is present in the report. (Unbound variables and Fresh public constants
/// precede the insertion point and are therefore NOT anchors.)
pub fn after_public_names_topics() -> Vec<&'static str> {
    vec![
        checks::T_SORTS,
        checks::T_RESERVED,
        checks::T_RESERVED_PREFIX,
        checks::T_FR,
        checks::T_SPECIAL,
        checks::T_ARITY,
        checks::T_MULT,
        checks::T_LHSRHS,
        checks::T_LEFT,
        checks::T_RIGHT,
        checks::T_FORMULA_TERMS,
        checks::T_GUARD,
        checks::T_LEMMA_ANNOT,
        checks::T_MULRESTRICT,
        checks::T_NAT,
        checks::T_SUBTERM,
    ]
}

/// Run every check in the oracle's report order.
pub fn check_theory(thy: &Theory) -> WfReport {
    let mut report: WfReport = Vec::new();
    // Base pipeline (public names inserted afterwards at its anchor point).
    report.extend(checks::unbound_variables(thy)); // 1
    report.extend(checks::fresh_public_constants(thy)); // 2
    report.extend(checks::mismatching_sorts(thy)); // 4
    report.extend(checks::reserved_names(thy)); // 5
    report.extend(checks::reserved_prefixes(thy)); // 6 (diff mode only)
    report.extend(checks::fr_facts(thy)); // 7
    report.extend(checks::special_facts(thy)); // 8
    report.extend(checks::fact_arity(thy)); // 9
    report.extend(checks::fact_multiplicity(thy)); // 10
    report.extend(checks::fact_lhs_occur_no_rhs(thy)); // 11
    report.extend(checks::diff_left_right(thy)); // 12, 13 (diff mode only)
    report.extend(checks::formula_terms(thy)); // 14
    report.extend(checks::formula_guardedness(thy)); // 15
    report.extend(checks::lemma_annotations(thy)); // 16
    report.extend(checks::multiplication_restriction(thy)); // 17
    report.extend(checks::nat_sorts(thy)); // 18
    report.extend(checks::subterm_convergence(thy)); // 19

    let pn = checks::public_names_report(thy); // 3
    let anchors = after_public_names_topics();
    insert_wf_before(&mut report, pn, &anchors);
    report
}

/// Secondary entry point: report any of `lemma_names` that are not declared in
/// the theory. NOTE: this entry point's exact render string could not be
/// observed through the file oracle; the set-difference logic is verified but
/// the message text is a documented gap (see BEHAVIOR.md).
pub fn check_if_lemmas_in_theory(lemma_names: &[String], thy: &Theory) -> WfReport {
    let present = checks::theory_lemma_names(thy);
    let mut out = Vec::new();
    for name in lemma_names {
        if !present.contains(name) {
            out.push(WfError::new(
                "Lemmas",
                format!("lemma `{}' referenced but not present in theory", name),
            ));
        }
    }
    out
}

// Re-export the public secondary entry points named in required_api.md.
pub use checks::{
    fact_lhs_occur_no_rhs, public_names_report, public_names_report_from_pairs,
};

pub mod order;
pub use order::*;
