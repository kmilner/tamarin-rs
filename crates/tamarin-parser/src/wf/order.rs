//! Integration adapter (workspace-authored): report-order anchor constants for
//! splicing Maude-dependent check results (checkTerms / checkGuarded / SAPIC
//! rule-variants / lhs-rhs) into the wellformedness report at their canonical
//! positions.  The topic strings and their relative order are observed report
//! behavior (see the wf module's canonical order); each `WF_AFTER_*` index is
//! the first entry whose topic sorts after that splicing check.

pub const WF_TOPIC_ORDER: &[&str] = &[
    "Reserved names",
    "Special facts",
    "Fr facts must only use a fresh- or a msg-variable",
    "Fact arity issues",
    "Fact multiplicity issues",
    "Fact capitalization issues",
    "Facts occur in the left-hand-side but not in any right-hand-side ",
    "Unbound variables",
    "Formula terms",
    " Formula guardedness",
    "Lemma annotations",
    "Multiplication restriction of rules",
    "Nat Sorts",
    "Subterm Convergence Warning",
    "Message Derivation Checks",
    "Derivation Checks",
];

pub const WF_AFTER_VARIANTS: usize = 0;
pub const WF_AFTER_FACT_LHS: usize = 8;
pub const WF_AFTER_CHECK_TERMS: usize = 9;
pub const WF_AFTER_CHECK_GUARDED: usize = 10;
