//! Skeleton port of `Theory.Tools.AbstractInterpretation` — a small
//! abstract-interpretation framework used for partial evaluation of
//! multiset-rewriting systems.
//!
//! The Haskell module exports:
//! - `interpretAbstractly`: a higher-order combinator parameterised
//!   over the unification primitive, an initial abstract state, and
//!   accessors for adding/extracting facts.
//! - `partialEvaluation`: instantiates `interpretAbstractly` with the
//!   E-unification provided by Maude.
//!
//! For the Rust port we expose `EvaluationStyle` and a generic
//! `interpret_abstractly` taking closures. The Maude-driven
//! `partial_evaluation` lands when typed-rule unification is wired
//! up.
//!
//! Not yet ported: this module is an unused placeholder. Only
//! `EvaluationStyle` is re-exported (`tools/mod.rs`); neither
//! `interpret_abstractly` nor `partial_evaluation` has a caller yet, and
//! both intentionally diverge from Haskell (the stub seeds empty-term
//! `In`/`Fresh` facts where HS uses `inFact (varTerm z)` /
//! `freshFact (varTerm z)`, and `partial_evaluation` returns its input
//! untouched). They are retained as a typed signature to fill in once the
//! typed-rule E-unification port exists; their current bodies are NOT
//! faithful ports.

use crate::fact::LNFact;
use crate::rule::ProtoRuleE;

/// How verbosely to report partial-evaluation progress.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvaluationStyle { Silent, Summary, Tracing }

/// Higher-order combinator used to build abstract interpreters over a
/// set of multiset-rewriting rules. Mirrors Haskell's
/// `interpretAbstractly`.
///
/// - `unify_fact_eqs`: solves E-unification on a list of fact
///   equalities, returning a (possibly empty) list of vfresh
///   substitutions. Implementations typically close over a Maude
///   handle.
/// - `init_state`: initial abstract state.
/// - `add_fact`: extend the state with a fact.
/// - `state_facts`: project the state to a fact list.
/// - `rules`: the rules to refine.
///
/// Unimplemented stub: rather than iterating `refineRule` to a
/// fixpoint, it seeds the state with empty-term In/Fresh facts (HS
/// uses `inFact (varTerm z)` / `freshFact (varTerm z)`) and returns a
/// single `(state, rules)` pair with the rules passed through
/// unrefined. Revisit when typed-rule unification is ported.
#[allow(dead_code)] // unused placeholder; see module-level note
pub fn interpret_abstractly<S, R, U, AddF, GetF>(
    _unify_fact_eqs: U,
    init_state: S,
    add_fact: AddF,
    state_facts: GetF,
    rules: &[R],
) -> Vec<(S, Vec<R>)>
where
    S: Clone + PartialEq,
    R: Clone,
    U: Fn(&[crate::fact::LNFact]) -> Vec<()> + Copy,
    AddF: Fn(LNFact, S) -> S + Copy,
    GetF: Fn(&S) -> Vec<LNFact> + Copy,
{
    // Without typed-rule unification we only emit the (start, rules)
    // pair and stop. A future revision will iterate `refineRule`
    // until fixpoint.
    let st = add_fact(LNFact::new(crate::fact::FactTag::Fresh, vec![]),
        add_fact(LNFact::new(crate::fact::FactTag::In, vec![]), init_state));
    let _ = state_facts;
    vec![(st, rules.to_vec())]
}

/// `partialEvaluation` placeholder. Returns the input untouched
/// until the underlying unification primitive is wired up.
#[allow(dead_code)] // unused placeholder; see module-level note
pub fn partial_evaluation(_style: EvaluationStyle, rus: &[ProtoRuleE])
    -> (Vec<LNFact>, Vec<ProtoRuleE>)
{
    (Vec::new(), rus.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluation_style_eq() {
        assert_eq!(EvaluationStyle::Silent, EvaluationStyle::Silent);
        assert_ne!(EvaluationStyle::Silent, EvaluationStyle::Summary);
    }

    #[test]
    fn partial_evaluation_passes_rules_through() {
        let (facts, rus) = partial_evaluation(EvaluationStyle::Silent, &[]);
        assert!(facts.is_empty());
        assert!(rus.is_empty());
    }
}
