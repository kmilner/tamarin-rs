// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.Solver.Simplify`: `simplifySystem` applies
//! the non-splitting CR-rules (`SIMPLIFY_PASSES`, in Haskell's non-diff
//! order) until a whole iteration changes nothing. Branch and fresh-counter
//! ownership follows `constraint/solver/BRANCHING.md`.

use crate::constraint::solver::reduction::{
    continue_in_arms, ChangeIndicator, GoalCases, Reduction, SystemBranch, SystemOutcome,
};
use crate::tools::equation_store::LNSubst;
use crate::tools::subterm_store::nat_subterm_equalities;

type Pass = fn(&mut Reduction<'_>) -> Result<SystemOutcome, crate::prove::ProveError>;

const SIMPLIFY_PASSES: &[Pass] = &[
    enforce_fresh_node_uniqueness_pass,
    enforce_kd_fact_uniqueness_pass,
    enforce_ku_action_uniqueness_pass,
    enforce_edge_uniqueness_pass,
    solve_unique_actions_pass_fan_out,
    reduce_formulas_pass,
    eval_formula_atoms_pass,
    enforce_fresh_ordering_pass,
    propagate_subterm_obvious,
    simp_injective_fact_eq_mon_pass,
    merge_last_injective_fact_nodes,
    insert_implied_formulas_pass,
];

/// Upstream aec550a2: interfering nodes at the end of an injective fact's
/// lifetime must denote the same final event, unless strict order forbids it.
fn merge_last_injective_fact_nodes(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::constraint::solver::contradictions::injective_interference_candidates;
    use crate::constraint::solver::goals::reachable_set_adj;
    use tamarin_term::rewriting::Equal;
    let Some(last) = red.sys.last_atom else {
        return Ok(SystemOutcome::Linear);
    };
    let adj = red.sys.build_always_before_adj();
    let candidates = injective_interference_candidates(red.ctx, &red.sys, &adj, |k| k == last);
    if candidates.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    let mut equations = Vec::new();
    for (_, j, k) in candidates {
        if reachable_set_adj(adj.map(), &j, false).contains(&k)
            || reachable_set_adj(adj.map(), &k, false).contains(&j)
        {
            red.mark_contradictory();
            return Ok(SystemOutcome::Contradictory);
        }
        let eq = Equal { lhs: j, rhs: k };
        if !equations.contains(&eq) {
            equations.push(eq);
        }
    }
    let result = red.solve_node_id_eqs(&equations);
    complete_solve(red, result)
}

/// The non-diff tail of HS `simplifySystem` (Simplify.hs), run once after
/// the fixpoint loop: `exploitUniqueMsgOrder`, `removeSolvedSplitGoals`,
/// `addNonInjectiveFactInstances`.
fn simp_post_loop_steps(red: &mut Reduction) -> Result<(), crate::prove::ProveError> {
    exploit_unique_msg_order(red);
    red.remove_solved_split_goals();
    add_non_injective_fact_instances(red)
}

/// Port of HS `simplifySystem` (Simplify.hs), returning every branch
/// produced by its goal and equality solves after running each to a fixpoint.
pub(crate) fn simplify_system_with_fanout(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: crate::constraint::system::System,
) -> Result<Vec<crate::constraint::system::System>, crate::prove::ProveError> {
    simplify_system_with_fanout_seeded(ctx, sys, 0)
}

/// Like [`simplify_system_with_fanout`] but continues from the producing
/// branch's fresh-counter position. `seed = 0` starts a detached reduction.
pub(crate) fn simplify_system_with_fanout_seeded(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: crate::constraint::system::System,
    seed: u64,
) -> Result<Vec<crate::constraint::system::System>, crate::prove::ProveError> {
    Ok(
        simplify_system_with_fanout_seeded_with_counters(ctx, sys, seed)?
            .into_iter()
            .map(|branch| branch.sys)
            .collect(),
    )
}

/// Counter-preserving form used by source saturation.
pub(crate) fn simplify_system_with_fanout_seeded_with_counters(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: crate::constraint::system::System,
    seed: u64,
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    use crate::constraint::solver::reduction::Reduction;
    let mut red = Reduction::new_inheriting(ctx, sys, seed);
    simplify_system_fan_out_inner_with_passes(&mut red, SIMPLIFY_PASSES)
}

/// Inner driver — mirrors the body of `simplify_system` but propagates
/// fan-out from two sources:
///   1. `solve_unique_actions_pass_fan_out` — when `solveGoal (ActionG)`
///      returns `GoalCases::Cases`.
///   2. `SystemOutcome::Cases` from any branching simplify pass.
///
/// Each branch continues with its own system and inherited FreshT counter,
/// including allocations that are no longer visible in the system.
fn simplify_system_fan_out_inner_with_passes(
    red: &mut Reduction,
    passes: &[Pass],
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    // Explicit fixpoint loop so we can break out on fan-out.
    // HS-faithful (Simplify.hs): no iteration cap — the loop
    // terminates only when a full pass reports `Unchanged`.
    loop {
        super::search::check_cancelled()?;
        red.subst_system()?;
        // Substitution is idempotent and is not one of the upstream pass
        // changes used to decide whether existential implications are stable.
        red.changed = ChangeIndicator::Unchanged;
        if let Some(branches) = continue_simplify_iteration(red, passes, 0)? {
            return Ok(branches);
        }
        if red.changed == ChangeIndicator::Unchanged {
            break;
        }
    }
    // Post-loop steps — same as `simplify_system`.
    simp_post_loop_steps(red)?;
    Ok(vec![SystemBranch {
        sys: std::mem::replace(&mut red.sys, crate::constraint::system::System::empty()),
        counter: red.fresh.next_index(),
    }])
}

/// Continue from the operation immediately after a split. Haskell's DisjT
/// resumes the lexical continuation before starting the next fixpoint
/// iteration; restarting at `substSystem` here changes both pass order and
/// fresh-allocation order.
fn continue_simplify_iteration(
    red: &mut Reduction,
    passes: &[Pass],
    mut next_pass: usize,
) -> Result<Option<Vec<SystemBranch>>, crate::prove::ProveError> {
    while let Some(pass) = passes.get(next_pass) {
        super::search::check_cancelled()?;
        let outcome = pass(red)?;
        next_pass += 1;
        let arms = match outcome {
            SystemOutcome::Linear => continue,
            SystemOutcome::Contradictory => return Ok(Some(Vec::new())),
            SystemOutcome::Cases(arms) => arms,
        };
        let changed = red.changed.or(ChangeIndicator::Changed);
        return Ok(Some(continue_simplify_branches(
            arms, red.ctx, passes, next_pass, changed,
        )?));
    }
    Ok(None)
}

fn continue_simplify_branches(
    arms: Vec<SystemBranch>,
    ctx: &crate::constraint::solver::context::ProofContext,
    passes: &[Pass],
    next_pass: usize,
    changed: ChangeIndicator,
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    let arms = arms
        .into_iter()
        .filter(|arm| !arm.sys.eq_store().is_false())
        .collect();
    continue_in_arms(ctx, arms, |branch| {
        branch.changed = changed;
        Ok(
            match continue_simplify_iteration(branch, passes, next_pass)? {
                Some(branches) => SystemOutcome::Cases(branches),
                None if branch.changed == ChangeIndicator::Changed => {
                    SystemOutcome::Cases(simplify_system_fan_out_inner_with_passes(branch, passes)?)
                }
                None => {
                    simp_post_loop_steps(branch)?;
                    SystemOutcome::Linear
                }
            },
        )
    })
}

/// `noContradictoryEqStore` after an equality solve: mark a failed solve
/// contradictory, pass every other outcome through.
fn complete_solve(
    red: &mut Reduction,
    res: std::result::Result<SystemOutcome, crate::prove::ProveError>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    let outcome = res?;
    if matches!(outcome, SystemOutcome::Contradictory) {
        red.mark_contradictory();
    }
    Ok(outcome)
}

/// HS `nonUnifiableNodes i j` (Simplify.hs, Contradictions.hs): both nodes
/// exist and their rule instances do not unify, so they are distinct in every
/// model.
pub(crate) fn non_unifiable_nodes(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    rules: &crate::constraint::system::NodeRuleMap<'_>,
    i: &crate::constraint::constraints::NodeId,
    j: &crate::constraint::constraints::NodeId,
) -> Result<bool, tamarin_term::maude_proc::MaudeError> {
    match (rules.get(i), rules.get(j)) {
        (Some(a), Some(b)) => Ok(!crate::rule::unifiable_rule_ac_insts(maude, a, b)?),
        _ => Ok(false),
    }
}

/// Direct port of Haskell `addNonInjectiveFactInstances`
/// (Simplify.hs): collects (smaller, larger) pairs from
/// `nonInjectiveFactInstances` (Simplify.hs) and inserts each as
/// `LessAtom(smaller, larger, InjectiveFacts)`.
pub(crate) fn add_non_injective_fact_instances(
    red: &mut Reduction,
) -> Result<(), crate::prove::ProveError> {
    use crate::constraint::constraints::{LessAtom, Reason};
    let pairs = non_injective_fact_instances_pairs(red)?;
    for (a, b) in pairs {
        red.insert_less(LessAtom::new(a, b, Reason::InjectiveFacts));
    }
    Ok(())
}

/// Direct port of Haskell `Simplify.nonInjectiveFactInstances`
/// (Simplify.hs) — returns the (j, i) or (k, j) less-relation
/// pairs that should be added when injective facts are duplicated
/// across the system.  Distinct from
/// `Contradictions.nonInjectiveFactInstances` (used in our
/// `contradictions::contradictions` to detect the *contradiction*
/// case): the simplify variant infers a less-relation Haskell can
/// use to make progress without contradicting yet.
fn non_injective_fact_instances_pairs(
    red: &Reduction,
) -> Result<
    Vec<(
        crate::constraint::constraints::NodeId,
        crate::constraint::constraints::NodeId,
    )>,
    crate::prove::ProveError,
> {
    use crate::constraint::constraints::NodeId;
    let sys = &red.sys;
    let ctxt = red.ctx;
    let mut out: Vec<(NodeId, NodeId)> = Vec::new();
    if ctxt.injective_fact_insts.is_empty() {
        return Ok(out);
    }

    // Resolve node-id → rule via a once-built map instead of a linear
    // `nodes.iter().find` per lookup (see `System::node_rule_map`).
    let node_rule_map = sys.node_rule_map();
    let lookup_node =
        |id: &NodeId| -> Option<&crate::rule::RuleACInst> { node_rule_map.get(id).copied() };
    // HS runs the unifier purely, so a failed backend aborts the pass.
    let non_unifiable_nodes = |i: &NodeId, j: &NodeId| {
        non_unifiable_nodes(&ctxt.maude, &node_rule_map, i, j)
            .map_err(|error| crate::prove::ProveError::maude("injective-fact unification", error))
    };
    // HS walks `S.toList sEdges` and `M.toList sNodes`.
    let edges_sorted = sys.edges_in_set_order();
    let nodes_sorted = sys.nodes_in_map_order();
    // The `alwaysBefore` adjacency is invariant across the edge/node loop
    // (`sys` is read-only), so build it once and query with
    // `always_before_with` instead of rebuilding the relation per pair.
    let ab_adj = sys.build_always_before_adj();
    for e in &edges_sorted {
        let (i, conc_idx) = (e.src.0, e.src.1);
        let k = e.tgt.0;
        let i_rule = match lookup_node(&i) {
            Some(r) => r,
            None => continue,
        };
        let k_fa_prem = match i_rule.conclusions.get(conc_idx.0) {
            Some(f) => f,
            None => continue,
        };
        if !ctxt.is_injective_tag(&k_fa_prem.tag) {
            continue;
        }
        let k_term = match k_fa_prem.terms().first() {
            Some(t) => t,
            None => continue,
        };
        let conflicting = |fa: &crate::fact::LNFact| -> bool {
            fa.tag == k_fa_prem.tag && fa.terms().first() == Some(k_term)
        };
        for (j, j_rule) in &nodes_sorted {
            if j == &i || j == &k {
                continue;
            }
            // Haskell's `guard (k ∈ reachableSet [j] less)` runs
            // *before* the case dispatch — so we require it up-front.
            if !sys.always_before_with(&ab_adj, j, &k) {
                continue;
            }
            let has_conflict = j_rule.premises.iter().any(conflicting)
                || j_rule.conclusions.iter().any(conflicting);
            if !has_conflict {
                continue;
            }
            // checkRuleJK: j<k and nonUnifiable(j, i) — return (j, i)
            if non_unifiable_nodes(j, &i)? {
                out.push((*j, i));
                continue;
            }
            // checkRuleIJ: i<j and nonUnifiable(k, j) — return (k, j)
            // Haskell's IJ branch uses `D.reachableSet [i] less`; we
            // mirror that with `i < j`.
            if sys.always_before_with(&ab_adj, &i, j) && non_unifiable_nodes(&k, j)? {
                out.push((k, *j));
            }
        }
    }
    Ok(out)
}

/// CR-rule *N6*, HS `exploitUniqueMsgOrder` (Simplify.hs): a term that is
/// both a KD conclusion and a KU action is deconstructed before it is
/// constructed. Each `M.fromList` keeps the last node for a repeated term.
///
/// The insertion is unconditional, including the reflexive `i < i` when one
/// node concludes `KD(m)` and acts `KU(m)`; the resulting cycle prunes source
/// cases from rules that misuse the reserved K facts (regression/trace/
/// issue515.spthy).
fn exploit_unique_msg_order(red: &mut Reduction) {
    use crate::constraint::constraints::{LessAtom, Reason};
    use std::collections::BTreeMap;
    let kd_concs: BTreeMap<_, _> = red
        .sys
        .all_kd_concs()
        .into_iter()
        .map(|(i, _, m)| (m.clone(), i))
        .collect();
    let ku_actions: BTreeMap<_, _> = red
        .sys
        .all_ku_actions()
        .into_iter()
        .map(|(i, _, m)| (m.clone(), i))
        .collect();
    let lesses: Vec<LessAtom> = kd_concs
        .iter()
        .filter_map(|(m, i)| {
            ku_actions
                .get(m)
                .map(|j| LessAtom::new(*i, *j, Reason::NormalForm))
        })
        .collect();
    for less in lesses {
        red.insert_less(less);
    }
}

/// CR-rule pass: `evalFormulaAtoms` (Haskell). Walks every guarded
/// formula in `sFormulas`, applies `partial_atom_valuation` to its
/// atoms, and re-inserts the simplified result. Atoms that evaluate
/// to a known truth value collapse to `gtrue`/`gfalse`, dropping
/// out of disjunctions or short-circuiting conjunctions.
pub(crate) fn eval_formula_atoms_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::guarded::{simplify_guarded_with, Guarded};
    // HS iterates `Stored.toList sFormulas`.
    let formulas = crate::constraint::system::formulas_in_set_order(&red.sys.formulas);
    // `applyChangeList`: every change is computed against the pre-pass
    // `valuation`, then applied in order.
    let mut change_list: Vec<(Guarded, Guarded)> = Vec::new();
    {
        let maude = red.ctx.maude.clone();
        let ab_adj = red.sys.build_always_before_adj();
        let node_rule_map = red.sys.node_rule_map();
        let reducible = maude.maude_sig().reducible_fun_syms_fast.clone();
        let subterms =
            crate::tools::subterm_store::StoreValuation::new(&reducible, &red.sys.subterm_store);
        let val = |a: &crate::atom::Atom<tamarin_term::lterm::LNTerm>| {
            partial_atom_valuation_with(&red.sys, &maude, &ab_adj, &node_rule_map, &subterms, a)
        };
        for fm in formulas.into_iter() {
            let simp = simplify_guarded_with(fm, &val)?;
            if &simp == fm {
                continue;
            }
            change_list.push((fm.clone(), simp));
        }
    }
    apply_formula_atom_changes(red, &change_list)
}

/// Continue the frozen evalFormulaAtoms change list in every equality branch.
/// Returning immediately on a split defers the remaining changes until after
/// substSystem, reopening knowledge goals under an intermediate substitution.
fn apply_formula_atom_changes(
    red: &mut Reduction,
    mut changes: &[(crate::guarded::Guarded, crate::guarded::Guarded)],
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::guarded::Guarded;
    while let Some(((fm, simp), rest)) = changes.split_first() {
        // Mark a disjunction's split goal solved before moving the original
        // formula to solved_formulas and inserting its simplified replacement.
        if let Guarded::Disj(items) = &fm {
            let disj_goal = crate::constraint::constraints::Goal::Disj(
                crate::constraint::constraints::Disj::new(items.to_vec()),
            );
            for (g, st) in red.sys.goals_mut().iter_mut() {
                if g == &disj_goal && !st.solved {
                    st.solved = true;
                    break;
                }
            }
        }
        // Remove the original formula and route the simplified one
        // through `insert_formula` — mirrors Haskell's
        // `evalFormulaAtoms` (Simplify.hs):
        //   modM sFormulas       $ S.delete fm
        //   modM sSolvedFormulas $ S.insert fm
        //   insertFormula fm'
        //
        // Critical: route `simp` through `insert_formula` so its atom
        // decomposition runs. A bare `Atom(Last(k))` must go through
        // `insertAtom`'s `last_atom` side effect; bypassing it leads to a
        // vacuous Simplify step downstream where Haskell goes straight to
        // Solve (injectivity_check class).
        red.sys.invalidate_max_var_idx_cache();
        red.sys.formulas_mut().retain(|f| **f != *fm);
        red.sys.insert_solved_formula(fm.clone());
        // `evalFormulaAtoms` (Simplify.hs) inserts every evaluated result.
        // This includes gtrue: `insertFormula` records the empty conjunction
        // as solved, so later passes recognize the completed formula.
        red.changed = ChangeIndicator::Changed;
        match red.insert_formula(simp.clone())? {
            SystemOutcome::Linear => changes = rest,
            SystemOutcome::Contradictory => return Ok(SystemOutcome::Contradictory),
            SystemOutcome::Cases(arms) => {
                return red
                    .continue_in_arms(arms, |branch| apply_formula_atom_changes(branch, rest));
            }
        }
    }
    Ok(SystemOutcome::Linear)
}

/// HS `partialAtomValuation` (Simplify.hs): `Some(b)` when the atom has truth
/// value `b` in every model of the system, `None` when unknown. `ab_adj` is
/// the pass's `rawLessRel`, HS's shared `before`.  HS runs its unifier
/// purely, so a failed backend is an error, never "unknown".
fn partial_atom_valuation_with(
    sys: &crate::constraint::system::System,
    maude: &tamarin_term::maude_proc::MaudeHandle,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
    node_rule: &tamarin_utils::FastMap<
        &crate::constraint::constraints::NodeId,
        &crate::rule::RuleACInst,
    >,
    subterms: &crate::tools::subterm_store::StoreValuation<'_>,
    atom: &crate::atom::Atom<tamarin_term::lterm::LNTerm>,
) -> Result<Option<bool>, crate::prove::ProveError> {
    use crate::atom::ProtoAtom;
    let failed = |error| crate::prove::ProveError::maude("atom valuation unification", error);
    let non_unifiable_nodes =
        |i: &crate::constraint::constraints::NodeId, j: &crate::constraint::constraints::NodeId| {
            non_unifiable_nodes(maude, node_rule, i, j).map_err(failed)
        };
    Ok(match atom {
        ProtoAtom::Less(i, j) => {
            let (Some(ni), Some(nj)) = (eq_node_id(i), eq_node_id(j)) else {
                return Ok(None);
            };
            // HS guard order: `j before i` wins over `i before j` on a cycle.
            if ni == nj {
                return Ok(Some(false));
            }
            if sys.always_before_with(ab_adj, &nj, &ni) {
                return Ok(Some(false));
            }
            if sys.always_before_with(ab_adj, &ni, &nj) {
                return Ok(Some(true));
            }
            if sys.is_last(&ni) && sys.is_in_trace(&nj) {
                return Ok(Some(false));
            }
            if sys.is_last(&nj) && sys.is_in_trace(&ni) && non_unifiable_nodes(&ni, &nj)? {
                return Ok(Some(true));
            }
            None
        }
        ProtoAtom::EqE(x, y) => {
            if x == y {
                return Ok(Some(true));
            }
            // HS asks `unifiableLNTerms` before reading node ids.
            let unifiers = maude
                .unify(&[tamarin_term::rewriting::Equal {
                    lhs: x.clone(),
                    rhs: y.clone(),
                }])
                .map_err(failed)?;
            if unifiers.is_empty() {
                return Ok(Some(false));
            }
            use tamarin_term::lterm::lterm_node_id;
            let (Some(ni), Some(nj)) = (lterm_node_id(x), lterm_node_id(y)) else {
                return Ok(None);
            };
            if sys.always_before_with(ab_adj, &ni, &nj)
                || sys.always_before_with(ab_adj, &nj, &ni)
                || non_unifiable_nodes(&ni, &nj)?
            {
                return Ok(Some(false));
            }
            None
        }
        ProtoAtom::Action(t, lnfa) => {
            let Some(n) = eq_node_id(t) else {
                return Ok(None);
            };
            // `ActionG i fa` membership counts solved goals too.
            for (g, _st) in sys.goals.iter() {
                if let crate::constraint::constraints::Goal::Action(gi, gfa) = g
                    && gi == &n
                    && gfa == lnfa
                {
                    return Ok(Some(true));
                }
            }
            let Some(rule) = node_rule.get(&n).copied() else {
                return Ok(None);
            };
            if rule.actions.iter().any(|a| a == lnfa) {
                return Ok(Some(true));
            }
            // False when no action unifies with `fa`.
            for a in &rule.actions {
                if crate::rule::unifiable_ln_facts(maude, lnfa, a).map_err(failed)? {
                    return Ok(None);
                }
            }
            Some(false)
        }
        ProtoAtom::Last(t) => {
            let Some(n) = eq_node_id(t) else {
                return Ok(None);
            };
            // HS `Last i` (Simplify.hs); `nodesAfter` walks `rawLessRel`,
            // which includes unsolved chains.
            if sys.is_last(&n) {
                return Ok(Some(true));
            }
            if crate::constraint::solver::goals::reachable_set_adj(ab_adj.map(), &n, false)
                .iter()
                .any(|j| sys.is_in_trace(j))
            {
                return Ok(Some(false));
            }
            // Final fallback: if there's a recorded last_atom and it's
            // non-unifiable with n, then n cannot be last.
            if let Some(la) = &sys.last_atom
                && non_unifiable_nodes(&n, la)?
            {
                return Ok(Some(false));
            }
            None
        }
        // HS `Subterm small big -> isTrueFalse reducible (Just sst) (small, big)`
        // (Simplify.hs).
        ProtoAtom::Subterm(small, big) => subterms.is_true_false(small, big),
        _ => None,
    })
}

/// The node id `partial_atom_valuation_with` reads out of a timepoint term
/// (HS `ltermNodeId'`): any variable leaf, coerced to `LSort::Node` where
/// Haskell errors on another sort.
fn eq_node_id(t: &tamarin_term::lterm::LNTerm) -> Option<crate::constraint::constraints::NodeId> {
    let tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) = t else {
        return None;
    };
    Some(tamarin_term::lterm::LVar::new(
        v.name,
        tamarin_term::lterm::LSort::Node,
        v.idx,
    ))
}

/// CR-rule *S_∀*, HS `insertImpliedFormulas` (Simplify.hs) over
/// `impliedFormulas` (System.hs): instantiate each universal formula and
/// lemma at every matching assignment of the system's actions.
fn insert_implied_formulas_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::atom::Atom as AAtom;
    use crate::atom::ProtoAtom;
    use crate::formula::Quantifier;
    use crate::guarded::Guarded;
    use tamarin_term::lterm::{LNTerm, LVar};

    fn has_existential(formula: &Guarded) -> bool {
        match formula {
            Guarded::Atom(_) => false,
            Guarded::GGuarded { qua, body, .. } => *qua == Quantifier::Ex || has_existential(body),
            Guarded::Disj(items) | Guarded::Conj(items) => items.iter().any(has_existential),
        }
    }
    // Temporary duplicate nodes can otherwise repeatedly generate witnesses
    // for the same existential obligation. Match upstream's stable-pass gate.
    let stable = red.changed == ChangeIndicator::Unchanged;

    // `impliedFormulas` (System.hs) opens every universal, including
    // residual formulas with no binders. `openGuarded` (Guarded.hs) freshens
    // bound variables throughout the guards and body before matching.
    // All binders in this pass share one FreshT-style counter seeded beyond
    // the live system and ambient fresh-variable supply.
    let mut fresh = tamarin_utils::fresh::FastFreshState::seeded(
        crate::constraint::solver::reduction::bounds_max(&red.sys).saturating_add(1),
    );
    // `Stored.toList sFormulas ++ Stored.toList sLemmas`.
    use crate::constraint::system::formulas_in_set_order;
    let universals: Vec<(Vec<LVar>, Vec<AAtom<LNTerm>>, Guarded)> =
        formulas_in_set_order(&red.sys.formulas)
            .into_iter()
            .chain(formulas_in_set_order(&red.sys.lemmas))
            .filter(|formula| stable || !has_existential(formula))
            .filter_map(|f| match f {
                Guarded::GGuarded {
                    qua: Quantifier::All,
                    ..
                } => {
                    let (_, xs, new_guards, new_body) = crate::guarded::open_guarded(f, &mut fresh)
                        .expect("the arm matched a universal GGuarded");
                    Some((xs, new_guards, new_body))
                }
                // Upstream #958: non-universal safety assumptions (including
                // false and ground Boolean formulas) still require reduction.
                // An empty matching prefix emits the formula itself through the
                // same dedup/insertion path. Existential reuse lemmas are not
                // assumptions that may be forced into every proof state.
                _ if crate::guarded::is_safety_formula(f) => {
                    Some((Vec::new(), Vec::new(), f.clone()))
                }
                _ => None,
            })
            .collect();
    if universals.is_empty() {
        return Ok(SystemOutcome::Linear);
    }

    // HS `allActions` (System.hs).
    let sys_actions = red.sys.all_actions();

    // Lookup-only index of `sys_actions` by fact tag (HS `matchFact` compares
    // whole tags, so `!Mark` never matches `Mark`), ascending within a tag,
    // so matching visits the same actions in the same order.
    let mut actions_by_tag: tamarin_utils::FastMap<crate::fact::FactTag, Vec<u32>> =
        tamarin_utils::FastMap::default();
    for (ai, (_, fa)) in sys_actions.iter().enumerate() {
        actions_by_tag.entry(fa.tag).or_default().push(ai as u32);
    }

    let maude = red.ctx.maude.clone();
    let mut new_formulas: Vec<Guarded> = Vec::new();
    // Stored formulas are kept in stored normal form, so a normalised
    // candidate is compared structurally, as `Stored.notMember` does.
    debug_assert!(red
        .sys
        .formulas
        .iter()
        .chain(red.sys.solved_formulas.iter())
        .all(|f| crate::guarded::normalise_stored_formula_cow(f).is_none()));
    for (vars, guards, body) in &universals {
        // HS `prepare` / `sortGAtoms` (System.hs, Guarded.hs): actions, then
        // equalities, drive matching in that order; the remaining atoms
        // become preconditions of the instance.
        let action_guards: Vec<&AAtom<LNTerm>> = guards
            .iter()
            .filter(|a| matches!(a, ProtoAtom::Action(_, _)))
            .collect();
        let eq_guards: Vec<&AAtom<LNTerm>> = guards
            .iter()
            .filter(|a| matches!(a, ProtoAtom::EqE(_, _)))
            .collect();
        let mut driving_guards: Vec<&AAtom<LNTerm>> = Vec::new();
        driving_guards.extend(action_guards);
        driving_guards.extend(eq_guards);
        let other_guards: Vec<&AAtom<LNTerm>> = guards
            .iter()
            .filter(|a| !matches!(a, ProtoAtom::Action(_, _) | ProtoAtom::EqE(_, _)))
            .collect();

        // With no driving guards this emits the single empty-substitution
        // instance `gall [] otherAtoms succedent`.
        try_match_all_guards(
            &maude,
            vars,
            &driving_guards,
            &sys_actions,
            &actions_by_tag,
            body,
            &red.sys,
            &other_guards,
            &mut new_formulas,
        )?;
    }
    if new_formulas.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    red.changed = ChangeIndicator::Changed;
    red.insert_formulas(new_formulas)
}

/// Try every assignment of system actions to the universal's action
/// guards. For each consistent assignment that binds all universal
/// vars, instantiate the body and add to `new_formulas`.
pub(crate) fn try_match_all_guards(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    vars: &[tamarin_term::lterm::LVar],
    action_guards: &[&crate::atom::Atom<tamarin_term::lterm::LNTerm>],
    sys_actions: &[(crate::constraint::constraints::NodeId, &crate::fact::LNFact)],
    // Pass-invariant name index over `sys_actions` (see
    // `insert_implied_formulas_pass`): the Action-guard arm iterates only the
    // name-equal group, in original `sys_actions` order.
    actions_by_tag: &tamarin_utils::FastMap<crate::fact::FactTag, Vec<u32>>,
    body: &crate::guarded::Guarded,
    sys: &crate::constraint::system::System,
    other_guards: &[&crate::atom::Atom<tamarin_term::lterm::LNTerm>],
    out: &mut Vec<crate::guarded::Guarded>,
) -> Result<(), crate::prove::ProveError> {
    use crate::atom::ProtoAtom;
    use crate::guarded::subst_guarded;

    // The universal's bound variables, as `(name, idx)`.
    let pattern_vars: std::collections::BTreeSet<(&'static str, u64)> =
        vars.iter().map(|v| (v.name, v.idx)).collect();

    fn rec(
        maude: &tamarin_term::maude_proc::MaudeHandle,
        vars: &[tamarin_term::lterm::LVar],
        pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
        guards: &[&crate::atom::Atom<tamarin_term::lterm::LNTerm>],
        guard_idx: usize,
        sys_actions: &[(crate::constraint::constraints::NodeId, &crate::fact::LNFact)],
        actions_by_tag: &tamarin_utils::FastMap<crate::fact::FactTag, Vec<u32>>,
        acc: &LNSubst,
        body: &crate::guarded::Guarded,
        sys: &crate::constraint::system::System,
        other_guards: &[&crate::atom::Atom<tamarin_term::lterm::LNTerm>],
        out: &mut Vec<crate::guarded::Guarded>,
    ) -> Result<(), crate::prove::ProveError> {
        if guard_idx == guards.len() {
            // Every driving guard matched: the instance is
            // `gall [] otherAtoms succedent` under the substitution. Atom
            // valuation is left to `evalFormulaAtoms`, as in Haskell.
            let surviving_gatoms: Vec<crate::atom::Atom<crate::formula::BLNTerm>> = other_guards
                .iter()
                .map(|g| {
                    crate::guarded::lift_free_atom(&crate::atom::map_atom(g, &mut |t| {
                        tamarin_term::subst::apply_vterm(acc, t.clone())
                    }))
                })
                .collect();
            let body_subst = subst_guarded(body, acc);
            // HS `insertImpliedFormulas` normalises each instance before its
            // membership test against both stores (150f5eba).
            let implied = crate::guarded::normalise_stored_formula_owned(crate::guarded::gall(
                Vec::new(),
                surviving_gatoms,
                body_subst,
            ));
            if !crate::guarded::stores_contains(&sys.formulas, &implied)
                && !crate::guarded::stores_contains(&sys.solved_formulas, &implied)
                && !out.contains(&implied)
            {
                out.push(implied);
            }
            return Ok(());
        }
        match guards[guard_idx] {
            ProtoAtom::Action(g_time, g_fact) => {
                // `applySkAction subst (a, fa)` (System.hs).
                let g_fact_subst = tamarin_term::apply::Apply::apply(g_fact.clone(), acc);
                let g_time_subst = tamarin_term::subst::apply_vterm(acc, g_time.clone());
                let tag_group = actions_by_tag
                    .get(&g_fact_subst.tag)
                    .map(|v| v.as_slice())
                    .unwrap_or(&[]);
                for &ai in tag_group {
                    let (i, fa_sys) = &sys_actions[ai as usize];
                    if g_fact_subst.arity() != fa_sys.arity() {
                        continue;
                    }
                    // Each AC matcher is its own candidate (`candidateSubsts`).
                    let substs_here = match_atom_via_maude(
                        maude,
                        vars,
                        pattern_vars,
                        &g_fact_subst,
                        &g_time_subst,
                        i,
                        fa_sys.terms(),
                    )?;
                    for subst_here in substs_here {
                        let Some(combined) = combine_substs(acc, &subst_here) else {
                            continue;
                        };
                        rec(
                            maude,
                            vars,
                            pattern_vars,
                            guards,
                            guard_idx + 1,
                            sys_actions,
                            actions_by_tag,
                            &combined,
                            body,
                            sys,
                            other_guards,
                            out,
                        )?;
                    }
                }
            }
            ProtoAtom::EqE(s, t) => {
                // `candidateSubsts subst ((GEqE s' t'):as)` (System.hs): the
                // side without unbound pattern variables is the subject.
                let s_subst = tamarin_term::subst::apply_vterm(acc, s.clone());
                let t_subst = tamarin_term::subst::apply_vterm(acc, t.clone());
                let s_has_pat = atom_has_unbound_pattern_var(&s_subst, vars);
                let t_has_pat = atom_has_unbound_pattern_var(&t_subst, vars);
                let (subj_term, pat_term) = match (s_has_pat, t_has_pat) {
                    (false, _) => (s_subst, t_subst),
                    (true, false) => (t_subst, s_subst),
                    // Haskell errors here (`formulaToGuarded` rules it out);
                    // drop the assignment.
                    (true, true) => return Ok(()),
                };
                // `matchTerm term pat` (Guarded.hs).
                for m in match_skolemized(maude, pattern_vars, vec![(subj_term, pat_term)])? {
                    let subst_here = LNSubst::from_list(m);
                    let Some(combined) = combine_substs(acc, &subst_here) else {
                        continue;
                    };
                    rec(
                        maude,
                        vars,
                        pattern_vars,
                        guards,
                        guard_idx + 1,
                        sys_actions,
                        actions_by_tag,
                        &combined,
                        body,
                        sys,
                        other_guards,
                        out,
                    )?;
                }
            }
            _ => (),
        }
        Ok(())
    }

    rec(
        maude,
        vars,
        &pattern_vars,
        action_guards,
        0,
        sys_actions,
        actions_by_tag,
        &LNSubst::empty(),
        body,
        sys,
        other_guards,
        out,
    )?;
    Ok(())
}

/// Combine two substitutions. If they map the same key to different
/// terms, return None. Otherwise return the union.
fn combine_substs(a: &LNSubst, b: &LNSubst) -> Option<LNSubst> {
    let mut out: std::collections::BTreeMap<
        tamarin_term::lterm::LVar,
        tamarin_term::lterm::LNTerm,
    > = a.iter().map(|(v, t)| (*v, t.clone())).collect();
    for (k, v) in b.iter() {
        match out.get(k) {
            Some(existing) if existing != v => return None,
            _ => {
                out.insert(*k, v.clone());
            }
        }
    }
    Some(LNSubst::from_map(out))
}

/// True iff a term mentions any `LVar` whose `(name, idx)` is in `vars` —
/// i.e. there's a pattern variable that hasn't yet been substituted.  Used by
/// the `EqE` guard arm of `try_match_all_guards` to pick which side of the
/// equality is the pattern (the side with unbound pattern vars).
fn atom_has_unbound_pattern_var(
    t: &tamarin_term::lterm::LNTerm,
    vars: &[tamarin_term::lterm::LVar],
) -> bool {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => vars.iter().any(|p| p.name == v.name && p.idx == v.idx),
        Term::Lit(Lit::Con(_)) => false,
        Term::App(_, args) => args.iter().any(|a| atom_has_unbound_pattern_var(a, vars)),
    }
}

/// HS `matchAction` (Guarded.hs) for one guard against one system action:
/// the matchers binding the universal's variables (`pattern_vars`).
fn match_atom_via_maude(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    vars: &[tamarin_term::lterm::LVar],
    pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
    g_fact: &crate::fact::LNFact,
    g_time: &tamarin_term::lterm::LNTerm,
    i: &crate::constraint::constraints::NodeId,
    sys_args: &[tamarin_term::lterm::LNTerm],
) -> Result<Vec<LNSubst>, crate::prove::ProveError> {
    use tamarin_term::term::Term as LTerm;
    use tamarin_term::vterm::Lit as LLit;
    let mut base_subst: std::collections::BTreeMap<
        tamarin_term::lterm::LVar,
        tamarin_term::lterm::LNTerm,
    > = std::collections::BTreeMap::new();

    // The time is matched with the fact: an unbound universal binds to `i`;
    // a time already bound by an earlier guard (a skolem constant in
    // Haskell) must be `i` itself.
    let LTerm::Lit(LLit::Var(g_t)) = g_time else {
        return Ok(Vec::new());
    };
    if vars.iter().any(|v| v.name == g_t.name && v.idx == g_t.idx) {
        base_subst.insert(
            *g_t,
            tamarin_term::vterm::var_term(tamarin_term::lterm::LVar::new(
                i.name,
                tamarin_term::lterm::LSort::Node,
                i.idx,
            )),
        );
    } else if !(g_t.name == i.name && g_t.idx == i.idx) {
        // Bound (ground) time that is not this system node — no match.
        return Ok(Vec::new());
    }

    // HS `matchFact` (Guarded.hs): one problem over all argument pairs.
    let pairs = sys_args
        .iter()
        .cloned()
        .zip(g_fact.terms().iter().cloned())
        .collect();
    Ok(match_skolemized(maude, pattern_vars, pairs)?
        .into_iter()
        .map(|m| {
            let mut subst = base_subst.clone();
            subst.extend(m);
            LNSubst::from_map(subst)
        })
        .collect())
}

/// HS `solveMatchLTerm` on skolemised `(subject, pattern)` pairs
/// (`matchAction` / `matchTerm`, Guarded.hs): only the universal's variables
/// (`pattern_vars`) bind, and only an AC problem goes to Maude. Returns each
/// matcher's bindings of those variables.
fn match_skolemized(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
    pairs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>,
) -> Result<
    Vec<Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>>,
    crate::prove::ProveError,
> {
    use tamarin_term::unification::{solve_match_lterm, MatchOutcome};
    let bindable = |v: &tamarin_term::lterm::LVar| pattern_vars.contains(&(v.name, v.idx));
    let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs.clone());
    match solve_match_lterm(&tamarin_term::lterm::sort_of_name, &bindable, problem) {
        MatchOutcome::Matched(s) => Ok(vec![s.iter().map(|(v, t)| (*v, t.clone())).collect()]),
        MatchOutcome::NoMatcher => Ok(Vec::new()),
        MatchOutcome::NeedsAc => {
            let eqs: Vec<_> = pairs
                .into_iter()
                .map(|(subject, pattern)| tamarin_term::rewriting::Equal {
                    lhs: pattern,
                    rhs: subject,
                })
                .collect();
            // A Maude failure is an error, never an absent match.
            let matches = maude
                .match_eqs_skolemize_both(&eqs, pattern_vars)
                .map_err(|error| crate::prove::ProveError::maude("", error))?;
            Ok(matches
                .into_iter()
                .map(|m| m.into_iter().filter(|(v, _)| bindable(v)).collect())
                .collect())
        }
    }
}

/// HS `merge solver candidates` (Simplify.hs) over `(key, payload, node)`
/// candidates: group by key (ascending, stable), keep each group's first
/// entry, and solve the payload equalities with `solve_payload_eqs` and the
/// node-id equalities in every resulting branch.
fn merge_candidates<K, P, F>(
    red: &mut Reduction,
    candidates: Vec<(K, P, crate::constraint::constraints::NodeId)>,
    solve_payload_eqs: F,
) -> Result<SystemOutcome, crate::prove::ProveError>
where
    K: Ord,
    P: Clone + PartialEq,
    F: Fn(
        &mut Reduction,
        &[tamarin_term::rewriting::Equal<P>],
    ) -> std::result::Result<SystemOutcome, crate::prove::ProveError>,
{
    use crate::constraint::constraints::NodeId;
    if candidates.len() < 2 {
        return Ok(SystemOutcome::Linear);
    }
    let mut by_key: std::collections::BTreeMap<K, Vec<(NodeId, P)>> =
        std::collections::BTreeMap::new();
    for (key, payload, i) in candidates {
        by_key.entry(key).or_default().push((i, payload));
    }
    let mut groups = Vec::new();
    for (_key, group) in by_key {
        if group.len() < 2 {
            continue;
        }
        let mut node_eqs: Vec<tamarin_term::rewriting::Equal<NodeId>> = Vec::new();
        let mut payload_eqs: Vec<tamarin_term::rewriting::Equal<P>> = Vec::new();
        let (keep_id, keep_payload) = &group[0];
        for (i, payload) in group.iter().skip(1) {
            if i != keep_id {
                node_eqs.push(tamarin_term::rewriting::Equal {
                    lhs: *keep_id,
                    rhs: *i,
                });
            }
            if payload != keep_payload {
                payload_eqs.push(tamarin_term::rewriting::Equal {
                    lhs: keep_payload.clone(),
                    rhs: payload.clone(),
                });
            }
        }
        if !node_eqs.is_empty() || !payload_eqs.is_empty() {
            groups.push((payload_eqs, node_eqs));
        }
    }
    if groups.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    merge_candidate_groups(red, &groups, &solve_payload_eqs)
}

type MergeGroup<P> = (
    Vec<tamarin_term::rewriting::Equal<P>>,
    Vec<tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>>,
);

fn merge_candidate_groups<P, F>(
    red: &mut Reduction,
    mut groups: &[MergeGroup<P>],
    solve_payload_eqs: &F,
) -> Result<SystemOutcome, crate::prove::ProveError>
where
    P: Clone,
    F: Fn(
        &mut Reduction,
        &[tamarin_term::rewriting::Equal<P>],
    ) -> std::result::Result<SystemOutcome, crate::prove::ProveError>,
{
    while let Some(((payload_eqs, node_eqs), rest)) = groups.split_first() {
        match merge_candidate_group(red, payload_eqs, node_eqs, solve_payload_eqs)? {
            SystemOutcome::Linear => groups = rest,
            SystemOutcome::Contradictory => return Ok(SystemOutcome::Contradictory),
            SystemOutcome::Cases(arms) => {
                return red.continue_in_arms(arms, |branch| {
                    merge_candidate_groups(branch, rest, solve_payload_eqs)
                });
            }
        }
    }
    Ok(SystemOutcome::Linear)
}

fn merge_candidate_group<P, F>(
    red: &mut Reduction,
    payload_eqs: &[tamarin_term::rewriting::Equal<P>],
    node_eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
    solve_payload_eqs: &F,
) -> Result<SystemOutcome, crate::prove::ProveError>
where
    P: Clone,
    F: Fn(
        &mut Reduction,
        &[tamarin_term::rewriting::Equal<P>],
    ) -> std::result::Result<SystemOutcome, crate::prove::ProveError>,
{
    if payload_eqs.is_empty() {
        return merge_candidate_node_eqs(red, node_eqs);
    }
    let res = solve_payload_eqs(red, payload_eqs);
    Ok(match complete_solve(red, res)? {
        SystemOutcome::Linear => merge_candidate_node_eqs(red, node_eqs)?,
        SystemOutcome::Contradictory => SystemOutcome::Contradictory,
        SystemOutcome::Cases(arms) if node_eqs.is_empty() => SystemOutcome::Cases(arms),
        SystemOutcome::Cases(arms) => {
            red.continue_in_arms(arms, |branch| merge_candidate_node_eqs(branch, node_eqs))?
        }
    })
}

fn merge_candidate_node_eqs(
    red: &mut Reduction,
    node_eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if node_eqs.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    let res = red.solve_node_id_eqs(node_eqs);
    complete_solve(red, res)
}

/// CR-rule *DG4* (HS `enforceNodeUniqueness`, Simplify.hs): identical Fresh
/// rule instances are one node. Only the node ids are equated; the next
/// `substSystem` merges the nodes.
fn enforce_fresh_node_uniqueness_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::rule::{ProtoRuleName, RuleInfo};
    // Group by the rule instance (no `Ord` on `RuleACInst`, so linearly).
    let mut buckets: Vec<(
        crate::rule::RuleACInst,
        Vec<crate::constraint::constraints::NodeId>,
    )> = Vec::new();
    for (id, rule) in red.sys.nodes.iter() {
        let is_fresh = matches!(&rule.info,
            RuleInfo::Proto(p) if p.name == ProtoRuleName::Fresh);
        if !is_fresh {
            continue;
        }
        if let Some(slot) = buckets.iter_mut().find(|(r, _)| r == rule) {
            slot.1.push(*id);
        } else {
            buckets.push((rule.clone(), vec![*id]));
        }
    }
    for (_rule, mut ids) in buckets {
        if ids.len() < 2 {
            continue;
        }
        // `M.toList sNodes` order keeps the lowest node id.
        ids.sort();
        let keep = ids[0];
        let eqs: Vec<_> = ids
            .into_iter()
            .skip(1)
            .map(|i| tamarin_term::rewriting::Equal { lhs: keep, rhs: i })
            .collect();
        let res = red.solve_node_id_eqs(&eqs);
        match complete_solve(red, res)? {
            SystemOutcome::Linear => {}
            outcome => return Ok(outcome),
        }
    }
    Ok(SystemOutcome::Linear)
}

/// CR-rule *N5_u* (HS `enforceNodeUniqueness`, Simplify.hs): the KU actions
/// of a term are one action, merged with `solveFactEqs SplitNow`.
fn enforce_ku_action_uniqueness_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::constraint::constraints::NodeId;
    use crate::fact::LNFact;
    use tamarin_term::lterm::LNTerm;

    // HS `allKUActions`: unsolved goals precede node actions, so a goal's
    // node id is kept within a term group.
    let acts: Vec<(LNTerm, LNFact, NodeId)> = red
        .sys
        .all_ku_actions()
        .into_iter()
        .map(|(i, fa, m)| (m.clone(), fa.clone(), i))
        .collect();
    // Haskell's `enforceFreshAndKuNodeUniqueness` merges the KU actions with
    // `solveFactEqs SplitNow` as the `merge` solver.
    merge_candidates(red, acts, |red, eqs| {
        red.solve_fact_eqs(
            crate::constraint::solver::reduction::SplitStrategy::SplitNow,
            eqs,
        )
    })
}

/// CR-rule *S_@* (`solveUniqueActions`). Mirrors HS's
/// `solveUniqueActions` (Simplify.hs) running inside the
/// `Reduction = StateT System (FreshT (DisjT ...))` monad — when
/// `solveGoal (ActionG i fa)` internally calls `disjunctionOfList`
/// (over source-cases / variants / rule actions / Maude unifiers),
/// the resulting `Disj` fans the entire simplify computation out into
/// multiple branches. The caller continues the simplify loop for each
/// branch independently.
///
/// A fan-out carries complete systems after the remaining captured action
/// goals have been processed in each arm.
fn solve_unique_actions_pass_fan_out(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    let candidates = collect_unique_action_candidates(red);
    execute_captured_actions(red, &candidates)
}

/// Execute one Haskell `mapM trySolve actionAtoms` continuation.
///
/// `remaining` is the pre-pass snapshot of the unique action atoms.  Keep
/// walking that borrowed snapshot after a split: re-collecting from a branch
/// would observe substitutions that Haskell does not apply until the next
/// outer simplify iteration.
fn execute_captured_actions(
    red: &mut Reduction<'_>,
    mut remaining: &[(crate::constraint::constraints::NodeId, crate::fact::LNFact)],
) -> Result<SystemOutcome, crate::prove::ProveError> {
    while let Some(((i, fa), suffix)) = remaining.split_first() {
        // `solveUniqueActions` (Simplify.hs) processes every captured atom,
        // even if an earlier solve substituted its live goal key. The goal
        // solver labels a missing node or unifies an existing node's actions;
        // filtering against the updated goal map would skip required work.
        let outcome = crate::constraint::solver::goals::solve_goal(
            red,
            &crate::constraint::constraints::Goal::Action(*i, fa.clone()),
        )?;
        match outcome {
            GoalCases::Contradictory => return Ok(SystemOutcome::Contradictory),
            GoalCases::LinearNamed(_) => {
                // `red.sys` is already mutated in place by the goal solver.
                remaining = suffix;
            }
            GoalCases::Cases(cases) => {
                // HS-faithful fan-out (Simplify.hs):
                //   solveUniqueActions = do
                //     ...
                //     actionAtoms <- gets unsolvedActionAtoms
                //     mconcat <$> mapM trySolve actionAtoms
                //
                // The list `actionAtoms` is captured ONCE pre-mapM.  When
                // a `trySolve` call's inner `solveGoal (ActionG i fa)`
                // produces a DisjT fan-out (via `disjunctionOfList arms`
                // in `solveFactEqs SplitNow`), every subsequent
                // `trySolve` runs INSIDE the fanned branch using the
                // SAME captured (i, fa) — NOT a re-substituted version.
                //
                // Do NOT return immediately on fan-out and let the caller
                // re-collect candidates per-case from the (substituted)
                // goal set: the substituted term may carry a Union that
                // `is_unique` rejects, dropping a goal HS keeps (captured
                // pre-substitution).  HS produces N×M simplify cases where
                // re-collection would yield N×1.
                //
                // Fix: process the REMAINING captured candidates in
                // EACH fanned arm using the ORIGINAL (i, fa) values
                // (not re-collected from the substituted goal set).
                // Continue over the borrowed suffix in each arm.
                // Deliberately no `subst_system`: Haskell applies it only at
                // the start of the next outer simplify iteration.
                let arms = cases
                    .into_iter()
                    .filter(|branch| !branch.sys.eq_store().is_false())
                    .map(|branch| SystemBranch {
                        sys: branch.sys,
                        counter: branch.counter,
                    })
                    .collect();
                return red
                    .continue_in_arms(arms, |branch| execute_captured_actions(branch, suffix));
            }
        }
    }
    Ok(SystemOutcome::Linear)
}

/// The action atoms `solveUniqueActions` (Simplify.hs) solves: unsolved
/// action goals in `M.toList sGoals` order whose `(tag, arity)` occurs once
/// among the rule actions and that have no top-level multiset-union term.
fn collect_unique_action_candidates(
    red: &Reduction,
) -> Vec<(crate::constraint::constraints::NodeId, crate::fact::LNFact)> {
    use crate::constraint::constraints::Goal;
    use crate::fact::LNFact;

    if !red
        .sys
        .goals
        .iter()
        .any(|(g, st)| matches!(g, Goal::Action(_, _)) && !st.solved)
    {
        return Vec::new();
    }

    let is_unique = |fa: &LNFact| -> bool {
        for t in fa.terms().iter() {
            if has_funion_head(t) {
                return false;
            }
        }
        red.ctx.unique_action_shapes.contains(&(fa.tag, fa.arity()))
    };

    let mut candidates: Vec<(crate::constraint::constraints::NodeId, LNFact)> = red
        .sys
        .goals
        .iter()
        .filter_map(|(g, st)| match g {
            Goal::Action(i, fa) if !st.solved && is_unique(fa) => Some((*i, fa.clone())),
            _ => None,
        })
        .collect();
    candidates.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    candidates
}

/// HS `FUnion _ <- viewTerm2 t`: the term's top-level symbol (only) is the
/// multiset union.
fn has_funion_head(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    matches!(t, Term::App(FunSym::Ac(AcSym::Union), _))
}

/// CR-rule *N5_d* (HS `enforceNodeUniqueness`, Simplify.hs): the KD
/// conclusions of a term come from one node, merged with
/// `solveRuleEqs SplitNow`.
fn enforce_kd_fact_uniqueness_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::constraint::constraints::NodeId;
    use crate::rule::RuleACInst;
    use tamarin_term::lterm::LNTerm;

    let kd_concs: Vec<(LNTerm, RuleACInst, NodeId)> = red
        .sys
        .all_kd_concs()
        .into_iter()
        .map(|(i, ru, m)| (m.clone(), ru.clone(), i))
        .collect();
    merge_candidates(red, kd_concs, |red, eqs| {
        red.solve_rule_eqs(
            crate::constraint::solver::reduction::SplitStrategy::SplitNow,
            eqs,
        )
    })
}

fn plain_route(
    start: crate::constraint::constraints::NodeId,
    single_linear_conc: &std::collections::BTreeSet<crate::constraint::constraints::NodeId>,
    edge_map: &std::collections::BTreeMap<
        crate::constraint::constraints::NodeConc,
        crate::constraint::constraints::NodeId,
    >,
) -> Vec<crate::constraint::constraints::NodeId> {
    let mut route = Vec::new();
    let mut visited = std::collections::BTreeSet::new();
    let mut current = start;
    loop {
        // Valid constraint systems are acyclic, but stopping at a repeated
        // node makes malformed input finite without truncating valid routes.
        if !visited.insert(current) {
            break;
        }
        route.push(current);
        if !single_linear_conc.contains(&current) {
            break;
        }
        let Some(next) = edge_map.get(&(current, crate::rule::ConcIdx(0))) else {
            break;
        };
        current = *next;
    }
    route
}

type FreshSubtermGraph = std::collections::BTreeMap<tamarin_term::lterm::LNTerm, Vec<usize>>;

/// Build HS `freshOrdering`'s shared graph once.  Each right-hand term maps
/// to the positive subterm edges whose left side contains it without crossing
/// a reducible head.  Fresh roots are keys too (HS adds `(fresh, fresh)` fake
/// edges); those self-edges need not be stored because each traversal seeds
/// its root explicitly.
fn fresh_subterm_graph(
    raw_subterms: &[(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)],
    fresh_roots: impl IntoIterator<Item = tamarin_term::lterm::LNTerm>,
    reducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
) -> FreshSubtermGraph {
    let mut keys: std::collections::BTreeSet<_> =
        raw_subterms.iter().map(|(_, big)| big.clone()).collect();
    keys.extend(fresh_roots);
    keys.into_iter()
        .map(|key| {
            let successors = raw_subterms
                .iter()
                .enumerate()
                .filter_map(|(index, (small, _))| {
                    crate::tools::subterm_store::elem_not_below_reducible(reducible, &key, small)
                        .then_some(index)
                })
                .collect();
            (key, successors)
        })
        .collect()
}

/// HS `freshOrdering`'s `floodFill`: all right-hand terms transitively
/// reachable from the fake `(fresh, fresh)` edge through the shared graph.
fn terms_containing_fresh(
    fresh: &tamarin_term::lterm::LNTerm,
    raw_subterms: &[(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)],
    graph: &FreshSubtermGraph,
) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut containing = std::collections::BTreeSet::from([fresh.clone()]);
    let mut visited = std::collections::BTreeSet::new();
    let mut pending: Vec<_> = graph.get(fresh).into_iter().flatten().copied().collect();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) {
            continue;
        }
        let edge = &raw_subterms[index];
        containing.insert(edge.1.clone());
        if let Some(successors) = graph.get(&edge.1) {
            pending.extend(successors.iter().copied());
        }
    }
    containing.into_iter().collect()
}

/// CR-rule *S_fresh-order*, HS `freshOrdering` (Simplify.hs): the node with
/// premise `Fr(~x)` precedes every non-unifiable node whose premises or
/// actions contain `~x` (directly or through positive subterms) outside a
/// reducible symbol, and so does the end of its linear route.
pub(crate) fn enforce_fresh_ordering_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::constraint::constraints::{LessAtom, Reason};
    use crate::fact::FactTag;
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // `getFreshVars`: `(i, ~x)` for every premise `Fr(~x)` of node `i`.
    let mut suppliers: Vec<(crate::constraint::constraints::NodeId, LVar)> = Vec::new();
    for (id, rule) in red.sys.nodes.iter() {
        for prem in &rule.premises {
            if !matches!(prem.tag, FactTag::Fresh) {
                continue;
            }
            if let Some(Term::Lit(Lit::Var(v))) = prem.terms().first()
                && v.sort == tamarin_term::lterm::LSort::Fresh
            {
                suppliers.push((*id, *v));
            }
        }
    }
    if suppliers.is_empty() {
        return Ok(SystemOutcome::Linear);
    }

    // `newLesses`. The node snapshot is an `Arc` handle, so `insert_less`
    // below cannot disturb it.
    let nodes_snapshot = red.sys.nodes.clone();
    let mut node_rules = crate::constraint::system::NodeRuleMap::default();
    for (id, rule) in nodes_snapshot.iter() {
        node_rules.entry(id).or_insert(rule);
    }
    let maude = red.ctx.maude.clone();
    // HS runs the unifier purely, so a dead or cancelled backend aborts the
    // pass rather than reading as "unifiable".
    let non_unifiable = |i: &crate::constraint::constraints::NodeId,
                         j: &crate::constraint::constraints::NodeId| {
        non_unifiable_nodes(&maude, &node_rules, i, j)
            .map_err(|error| crate::prove::ProveError::maude("fresh-ordering unification", error))
    };

    // `getRoute` follows nodes with a single linear conclusion.
    let single_linear_conc: std::collections::BTreeSet<crate::constraint::constraints::NodeId> =
        nodes_snapshot
            .iter()
            .filter(|(_, r)| r.conclusions.len() == 1 && r.conclusions[0].is_linear())
            .map(|(id, _)| *id)
            .collect();
    let edge_map: std::collections::BTreeMap<
        crate::constraint::constraints::NodeConc,
        crate::constraint::constraints::NodeId,
    > = red.sys.edges.iter().map(|e| (e.src, e.tgt.0)).collect();
    let mut new_lesses: Vec<(
        crate::constraint::constraints::NodeId,
        crate::constraint::constraints::NodeId,
    )> = Vec::new();

    // Containment is `elemNotBelowReducible`, through the `floodFill` of the
    // positive subterm graph.
    let reducible = &maude.maude_sig().reducible_fun_syms_fast;
    let raw_subterms: Vec<_> = red
        .sys
        .subterm_store
        .subterms
        .iter()
        .map(|constraint| (constraint.small.clone(), constraint.big.clone()))
        .collect();
    let graph = if raw_subterms.is_empty() {
        FreshSubtermGraph::new()
    } else {
        fresh_subterm_graph(
            &raw_subterms,
            suppliers
                .iter()
                .map(|(_, fresh_var)| Term::Lit(Lit::Var(*fresh_var))),
            reducible,
        )
    };
    let mut containing_by_fresh = std::collections::BTreeMap::new();
    if !raw_subterms.is_empty() {
        for (_, fresh_var) in &suppliers {
            containing_by_fresh.entry(*fresh_var).or_insert_with(|| {
                let fresh_term = Term::Lit(Lit::Var(*fresh_var));
                terms_containing_fresh(&fresh_term, &raw_subterms, &graph)
            });
        }
    }
    // Index direct fresh-variable occurrences for O(1) probes. Only a supplier
    // whose flood-fill reaches additional terms needs the general term checks.
    let node_fresh_vars: Vec<tamarin_utils::FastSet<LVar>> = nodes_snapshot
        .iter()
        .map(|(_, rule)| {
            let mut out = tamarin_utils::FastSet::default();
            for fact in rule.premises.iter().chain(rule.actions.iter()) {
                for term in fact.terms().iter() {
                    crate::tools::subterm_store::collect_fresh_vars_not_below_reducible(
                        reducible, term, &mut out,
                    );
                }
            }
            out
        })
        .collect();
    let node_terms: Vec<Vec<&tamarin_term::lterm::LNTerm>> = if raw_subterms.is_empty() {
        Vec::new()
    } else {
        nodes_snapshot
            .iter()
            .map(|(_, rule)| {
                rule.premises
                    .iter()
                    .chain(rule.actions.iter())
                    .flat_map(|fact| fact.terms().iter())
                    .collect()
            })
            .collect()
    };

    // Lazily built dedup index for the less-atom inserts below.
    let mut less_idx: Option<crate::constraint::system::LessIndex> = None;

    for (sup_id, fresh_var) in &suppliers {
        for (idx, (other_id, _)) in nodes_snapshot.iter().enumerate() {
            if other_id == sup_id {
                continue;
            }
            let direct = node_fresh_vars[idx].contains(fresh_var);
            let transitive = || {
                containing_by_fresh
                    .get(fresh_var)
                    .is_some_and(|containing| {
                        containing.len() > 1
                            && containing.iter().any(|term| {
                                node_terms[idx].iter().any(|outer| {
                                    crate::tools::subterm_store::elem_not_below_reducible(
                                        reducible, term, outer,
                                    )
                                })
                            })
                    })
            };
            if !direct && !transitive() {
                continue;
            }
            if !non_unifiable(sup_id, other_id)? {
                continue;
            }
            if less_idx.is_none() {
                less_idx = Some(red.sys.build_less_index());
            }
            if red.sys.add_less_indexed(
                LessAtom::new(*sup_id, *other_id, Reason::Fresh),
                less_idx.as_mut().unwrap(),
            ) {
                red.changed = ChangeIndicator::Changed;
            }
            new_lesses.push((*sup_id, *other_id));
        }
    }

    // `enhancedLesses`: `last (route i) < j` when the whole route tail is
    // non-unifiable with `j` (csf23-subterms FreshOrderingTest::Order2).
    let supplier_ids: std::collections::BTreeSet<_> = suppliers.iter().map(|(id, _)| *id).collect();
    for (i, j) in &new_lesses {
        if !supplier_ids.contains(i) {
            continue;
        } // i must be a frI
        let rs = plain_route(*i, &single_linear_conc, &edge_map);
        if rs.len() <= 1 {
            continue;
        }
        // `tail rs` — all nodes after the first.
        let tail = &rs[1..];
        // Side condition: `all (nonUnifiableNodes j) (tail rs)`.
        let mut all_non_unifiable = true;
        for t_id in tail {
            if !non_unifiable(j, t_id)? {
                all_non_unifiable = false;
                break;
            }
        }
        if !all_non_unifiable {
            continue;
        }
        let last = match rs.last() {
            Some(l) => *l,
            None => continue,
        };
        if less_idx.is_none() {
            less_idx = Some(red.sys.build_less_index());
        }
        if red.sys.add_less_indexed(
            LessAtom::new(last, *j, Reason::Fresh),
            less_idx.as_mut().unwrap(),
        ) {
            red.changed = ChangeIndicator::Changed;
        }
    }
    Ok(SystemOutcome::Linear)
}

/// CR-rules *DG2_1* and *DG3*, HS `enforceEdgeUniqueness` (Simplify.hs): a
/// premise has one incoming edge, and a linear conclusion one outgoing edge.
fn enforce_edge_uniqueness_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    // HS `proveLinearConc`: the conclusion exists and is a linear fact.
    let linear_concs: std::collections::BTreeSet<crate::constraint::constraints::NodeConc> = {
        let rules = red.sys.node_rule_map();
        red.sys
            .edges
            .iter()
            .map(|e| e.src)
            .filter(|(v, i)| {
                rules
                    .get(v)
                    .and_then(|ru| ru.conclusions.get(i.0))
                    .is_some_and(|fa| fa.is_linear())
            })
            .collect()
    };
    // `mergeNodes eSrc eTgt edges`, then `mergeNodes eTgt eSrc` on the
    // edges from linear conclusions. Each requires equal indices and
    // equates the node ids; `substSystem` merges the nodes later.
    let mut by_tgt: std::collections::BTreeMap<
        crate::constraint::constraints::NodePrem,
        Vec<crate::constraint::constraints::NodeConc>,
    > = std::collections::BTreeMap::new();
    let mut by_src: std::collections::BTreeMap<
        crate::constraint::constraints::NodeConc,
        Vec<crate::constraint::constraints::NodePrem>,
    > = std::collections::BTreeMap::new();
    // HS groups `S.toList sEdges`.
    for e in red.sys.edges_in_set_order() {
        by_tgt.entry(e.tgt).or_default().push(e.src);
        by_src.entry(e.src).or_default().push(e.tgt);
    }
    let mut node_eqs: Vec<tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>> =
        Vec::new();
    let mut conc_idx_clash = false;
    let mut prem_idx_clash = false;
    for (_tgt, srcs) in by_tgt {
        if srcs.len() < 2 {
            continue;
        }
        let keep = &srcs[0];
        for other in srcs.iter().skip(1) {
            if keep.1 != other.1 {
                conc_idx_clash = true;
                continue;
            }
            node_eqs.push(tamarin_term::rewriting::Equal {
                lhs: keep.0,
                rhs: other.0,
            });
        }
    }
    if conc_idx_clash {
        red.mark_contradictory();
        return Ok(SystemOutcome::Contradictory);
    }
    for (src, prems) in by_src {
        if prems.len() < 2 {
            continue;
        }
        if !linear_concs.contains(&src) {
            continue;
        }
        let keep = &prems[0];
        for other in prems.iter().skip(1) {
            if keep.1 != other.1 {
                prem_idx_clash = true;
                continue;
            }
            node_eqs.push(tamarin_term::rewriting::Equal {
                lhs: keep.0,
                rhs: other.0,
            });
        }
    }
    if prem_idx_clash {
        red.mark_contradictory();
        return Ok(SystemOutcome::Contradictory);
    }
    node_eqs.retain(|e| e.lhs != e.rhs);
    if node_eqs.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    let res = red.solve_node_id_eqs(&node_eqs);
    red.changed = ChangeIndicator::Changed;
    complete_solve(red, res)
}

/// Lift a `NodeId` (an `LVar` of sort Node) to an `LNTerm` variable —
/// HS `varTerm (Free i)` for a node-id.
fn node_id_to_lnterm(n: &crate::constraint::constraints::NodeId) -> tamarin_term::lterm::LNTerm {
    tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(*n))
}

/// HS `simpInjectiveFactEqMon` (Simplify.hs): for two nodes using the same
/// injective fact instance, emit the cases (1)-(5) equalities, inequalities
/// and orderings implied by each position's monotonic behaviour. Cases (6)
/// and (6.1) are commented out upstream.
fn simp_injective_fact_eq_mon_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::tools::injective_fact_instances::MonotonicBehaviour;

    if red.ctx.injective_fact_insts.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    // HS `getPairs`: per injective tag (in set order), `behaviourTerms` maps
    // each node, in `M.toList` order, to its `trimmedPairTerms` premises
    // (`mapMaybe`: a premise whose terms do not fit the shape is dropped).
    // A node without such premises pairs with nothing, so it is left out.
    // So is a premise whose leaves are all `Unstable` or `Unspecified`:
    // `simpSingle` yields nothing for those, and both sides of a pair share
    // the tag's behaviours, so none of its pairs can contribute.
    type BehaviourTerms = Vec<(
        tamarin_term::lterm::LNTerm,
        Vec<(MonotonicBehaviour, tamarin_term::lterm::LNTerm)>,
    )>;
    let per_tag: Vec<Vec<(crate::constraint::constraints::NodeId, BehaviourTerms)>> = red
        .ctx
        .injective_fact_insts
        .iter()
        .map(|(tag, behaviours)| {
            red.sys
                .nodes_in_map_order()
                .into_iter()
                .filter_map(|(id, rule)| {
                    let terms: BehaviourTerms = rule
                        .premises
                        .iter()
                        .filter(|prem| prem.tag == *tag)
                        .filter_map(|prem| {
                            crate::tools::injective_fact_instances::trimmed_pair_terms(
                                prem, behaviours,
                            )
                        })
                        .filter(|(_, pairs)| {
                            pairs.iter().any(|(bh, _)| {
                                !matches!(
                                    bh,
                                    MonotonicBehaviour::Unstable | MonotonicBehaviour::Unspecified
                                )
                            })
                        })
                        .collect();
                    (!terms.is_empty()).then_some((*id, terms))
                })
                .collect()
        })
        .collect();
    // Pairs need two distinct nodes of the same tag.
    if per_tag.iter().all(|nodes| nodes.len() < 2) {
        return Ok(SystemOutcome::Linear);
    }

    // HS `inequalities`: the stored `¬(s = t)` formulas, probed in both
    // orientations.
    let inequalities: std::collections::BTreeSet<(
        tamarin_term::lterm::LNTerm,
        tamarin_term::lterm::LNTerm,
    )> = {
        let mut set = std::collections::BTreeSet::new();
        let all_fms = red
            .sys
            .formulas
            .iter()
            .chain(red.sys.solved_formulas.iter());
        for fm in all_fms {
            if let crate::guarded::Guarded::GGuarded {
                qua,
                vars,
                guards,
                body,
            } = fm.as_ref()
            {
                if !matches!(qua, crate::formula::Quantifier::All) {
                    continue;
                }
                if !vars.is_empty() {
                    continue;
                }
                if guards.len() != 1 {
                    continue;
                }
                if **body != crate::guarded::gfalse() {
                    continue;
                }
                if let crate::atom::ProtoAtom::EqE(s_g, t_g) = &guards[0] {
                    set.insert((
                        crate::guarded::bterm_to_lterm(s_g),
                        crate::guarded::bterm_to_lterm(t_g),
                    ));
                }
            }
        }
        set
    };
    // HS `oldFormulas = sFormulas ∪ sSolvedFormulas`, for change detection.
    let formula_set = |red: &Reduction| -> Vec<std::sync::Arc<crate::guarded::Guarded>> {
        let mut v: Vec<std::sync::Arc<crate::guarded::Guarded>> = red
            .sys
            .formulas
            .iter()
            .chain(red.sys.solved_formulas.iter())
            .cloned()
            .collect();
        v.sort();
        v.dedup();
        v
    };
    let old_formulas = formula_set(red);
    // Cases (1), (2) and (4) become formulas, (3) and (5) less atoms.
    let mut new_formulas: Vec<crate::guarded::Guarded> = Vec::new();
    let mut new_lesses: Vec<(
        crate::constraint::constraints::NodeId,
        crate::constraint::constraints::NodeId,
    )> = Vec::new();
    let reducible = red.ctx.maude.maude_sig().reducible_fun_syms_fast.clone();
    // HS `triviallySmaller` / `triviallyNotSmaller`.
    let valuation =
        crate::tools::subterm_store::StoreValuation::new(&reducible, &red.sys.subterm_store);
    let trivially_smaller = |s: &tamarin_term::lterm::LNTerm, t: &tamarin_term::lterm::LNTerm| {
        valuation.is_true_false(s, t) == Some(true)
    };
    let trivially_not_smaller = |s: &tamarin_term::lterm::LNTerm,
                                 t: &tamarin_term::lterm::LNTerm| {
        valuation.is_true_false(s, t) == Some(false)
    };
    // HS `paired`: premises with the same first term on different nodes,
    // `((b, s), (_, t)) <- zip ss tt`.
    let ab_adj = red.sys.build_always_before_adj();
    let paired = per_tag.iter().flat_map(|nodes| {
        nodes.iter().flat_map(move |(i, l1)| {
            nodes
                .iter()
                .filter(move |(j, _)| j != i)
                .flat_map(move |(j, l2)| {
                    l1.iter().flat_map(move |(first_i, ss)| {
                        l2.iter()
                            .filter(move |(first_j, _)| first_j == first_i)
                            .flat_map(move |(_, tt)| {
                                ss.iter()
                                    .zip(tt)
                                    .map(move |((bh, s), (_, t))| (bh, (i, s), (j, t)))
                            })
                    })
                })
        })
    });
    for (bh, (i, s), (j, t)) in paired {
        // `simpSingle` turns decreasing positions into increasing
        // ones with the node ids swapped.
        let (eff_bh, ii, jj) = match bh {
            MonotonicBehaviour::Decreasing => (MonotonicBehaviour::Increasing, j, i),
            MonotonicBehaviour::StrictlyDecreasing => {
                (MonotonicBehaviour::StrictlyIncreasing, j, i)
            }
            other => (*other, i, j),
        };
        match eff_bh {
            // (1)
            MonotonicBehaviour::Constant if s != t => {
                new_formulas.push(crate::guarded::Guarded::Atom(crate::atom::ProtoAtom::EqE(
                    crate::formula::lift_free(s),
                    crate::formula::lift_free(t),
                )));
            }
            // Each case has its own guard, so several can fire
            // together; e.g. (2) and (5) with a stale `s ≠ t` give
            // the cycle counter.spthy::counters_linear_order needs.
            MonotonicBehaviour::StrictlyIncreasing => {
                let ab_ij = red.sys.always_before_with(&ab_adj, ii, jj);
                let ab_ji = red.sys.always_before_with(&ab_adj, jj, ii);
                // (2)
                if s == t && ii != jj {
                    new_formulas.push(crate::guarded::Guarded::Atom(crate::atom::ProtoAtom::EqE(
                        crate::formula::lift_free(&node_id_to_lnterm(ii)),
                        crate::formula::lift_free(&node_id_to_lnterm(jj)),
                    )));
                }
                // (4)
                let comparable = ab_ij || ab_ji;
                let already_ineq = inequalities.contains(&(s.clone(), t.clone()))
                    || inequalities.contains(&(t.clone(), s.clone()));
                if comparable && !already_ineq {
                    let neg = crate::guarded::gall(
                        Vec::new(),
                        vec![crate::atom::ProtoAtom::EqE(
                            crate::formula::lift_free(s),
                            crate::formula::lift_free(t),
                        )],
                        crate::guarded::gfalse(),
                    );
                    new_formulas.push(neg);
                }
                // (3)
                if trivially_smaller(s, t) && !ab_ij {
                    new_lesses.push((*ii, *jj));
                }
                // (5)
                if trivially_not_smaller(s, t)
                    && !ab_ji
                    && (inequalities.contains(&(s.clone(), t.clone()))
                        || inequalities.contains(&(t.clone(), s.clone())))
                {
                    new_lesses.push((*jj, *ii));
                }
            }
            // Only the less atoms (3) and (5) of the strict case.
            MonotonicBehaviour::Increasing => {
                if trivially_smaller(s, t) && !red.sys.always_before_with(&ab_adj, ii, jj) {
                    new_lesses.push((*ii, *jj));
                }
                if trivially_not_smaller(s, t)
                    && !red.sys.always_before_with(&ab_adj, jj, ii)
                    && (inequalities.contains(&(s.clone(), t.clone()))
                        || inequalities.contains(&(t.clone(), s.clone())))
                {
                    new_lesses.push((*jj, *ii));
                }
            }
            _ => {}
        }
    }
    // `mapM_ insertFormula newFormulas`, then `mapM_ insertLess newLesses`.
    let any_new_lesses = !new_lesses.is_empty();
    let insert_lesses = |red: &mut Reduction| {
        for &(sm, lg) in &new_lesses {
            red.insert_less(crate::constraint::constraints::LessAtom::new(
                sm,
                lg,
                crate::constraint::constraints::Reason::InjectiveFacts,
            ));
        }
    };
    match red.insert_formulas(new_formulas)? {
        SystemOutcome::Linear => insert_lesses(red),
        SystemOutcome::Contradictory => return Ok(SystemOutcome::Contradictory),
        SystemOutcome::Cases(arms) => {
            return red.continue_in_arms(arms, |branch| {
                insert_lesses(branch);
                Ok(SystemOutcome::Linear)
            });
        }
    }
    let updated_formulas = formula_set(red);
    if updated_formulas != old_formulas || any_new_lesses {
        red.changed = ChangeIndicator::Changed;
    }
    Ok(SystemOutcome::Linear)
}

/// HS `reduceFormulas` (Simplify.hs): reinsert every reducible formula, and
/// every disjunction without its split goal, in `Stored.toList` order.
fn reduce_formulas_pass(red: &mut Reduction) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::guarded::reducible_formula;
    let to_decompose: Vec<crate::guarded::Guarded> =
        crate::constraint::system::formulas_in_set_order(&red.sys.formulas)
            .into_iter()
            .filter(|f| match f {
                crate::guarded::Guarded::Disj(items) => !red.sys.goals.iter().any(|(goal, _)| {
                    matches!(goal, crate::constraint::constraints::Goal::Disj(disj) if disj.0.as_slice() == items.as_ref())
                }),
                _ => reducible_formula(f),
            })
            .cloned()
            .collect();
    if to_decompose.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    red.sys.invalidate_max_var_idx_cache();
    red.sys.formulas_mut().retain(|f| !to_decompose.contains(f));
    red.changed = ChangeIndicator::Changed;
    red.insert_formulas(to_decompose)
}

/// HS `simpSubterms` (Simplify.hs) running `simpSubtermStore`
/// (SubtermStore.hs): `simpSplitNegSt` on the negative subterms not in
/// `oldNegSubterms`, `simpSplitPosSt` with the arity-one deduction,
/// `negativeSubtermVars`, `hasSubtermCycle` and `simpNatCycles`, followed by
/// the subterm-goal and formula updates.
fn propagate_subterm_obvious(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::tools::subterm_store::{split_subterm, subterm_step, SubtermSplit};
    use tamarin_term::lterm::{sort_of_lnterm, LSort};
    // Snapshot only the semantic constraints. Keeping the store's Arc here
    // would force copy-on-write of its bookkeeping on every simplification pass.
    let pairs = |constraints: &[crate::tools::subterm_store::SubtermConstraint]| {
        let mut pairs: Vec<_> = constraints
            .iter()
            .map(|constraint| {
                let (small, big) = constraint.hs_pair();
                (small.clone(), big.clone())
            })
            .collect();
        pairs.sort_unstable();
        pairs.dedup();
        pairs
    };
    let previous_contradictory = red.sys.subterm_store.contradictory;
    let previous_neg = red.sys.subterm_store.neg_subterms.clone();
    let previous_pos = pairs(&red.sys.subterm_store.subterms);
    let previous_solved = pairs(&red.sys.subterm_store.solved_subterms);
    let mut changed_goals = false;
    let reducible = red.ctx.maude.maude_sig().reducible_fun_syms_fast.clone();

    let mut new_formulas: Vec<crate::guarded::Guarded> = Vec::new();
    // Build an Eq atom from two LNTerms.
    let mk_eq_atom = |s: &tamarin_term::lterm::LNTerm,
                      t: &tamarin_term::lterm::LNTerm|
     -> crate::atom::Atom<crate::formula::BLNTerm> {
        crate::atom::ProtoAtom::EqE(crate::formula::lift_free(s), crate::formula::lift_free(t))
    };
    let emit_neg_eq = |s: tamarin_term::lterm::LNTerm,
                       t: tamarin_term::lterm::LNTerm,
                       new_formulas: &mut Vec<crate::guarded::Guarded>| {
        // ¬(s = t) as `gall [] [s=t] gfalse`.
        let atom = mk_eq_atom(&s, &t);
        let f = crate::guarded::gall(Vec::new(), vec![atom], crate::guarded::gfalse());
        if !new_formulas.contains(&f) {
            new_formulas.push(f);
        }
    };
    // `acFormulas` from simpSplitNegSt (HS SubtermStore.hs):
    //   closeGuarded All [newVar] [EqE smallPlus big] gfalse
    // (∀ newVar. smallPlus = big ⇒ ⊥).
    let emit_ac_neg = |small_plus: &tamarin_term::lterm::LNTerm,
                       big: &tamarin_term::lterm::LNTerm,
                       new_var: &tamarin_term::lterm::LVar,
                       new_formulas: &mut Vec<crate::guarded::Guarded>| {
        let f = crate::guarded::close_guarded(
            crate::formula::Quantifier::All,
            vec![*new_var],
            vec![crate::atom::ProtoAtom::EqE(small_plus.clone(), big.clone())],
            crate::guarded::gfalse(),
        );
        if !new_formulas.contains(&f) {
            new_formulas.push(f);
        }
    };
    // `freshLVar "newVar"` for the `ACNewVarD` splits.
    let mut mk_fresh = {
        let avoid_max = crate::constraint::solver::reduction::bounds_max(&red.sys);
        red.fresh.advance_to(avoid_max.saturating_add(1));
        |sort: tamarin_term::lterm::LSort| -> tamarin_term::lterm::LVar {
            tamarin_term::lterm::LVar::new("newVar", sort, red.fresh.fresh_idents(1))
        }
    };
    let mut contradictory = false;
    // Phase 1: `simpSplitNegSt` on `negSubterms \ oldNegSubterms`.
    {
        type Pair = (tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm);
        let original_negs = red.sys.subterm_store.neg_subterms.clone();
        let changed_negs: Vec<Pair> = original_negs
            .iter()
            .filter(|p| {
                red.sys
                    .subterm_store
                    .old_neg_subterms
                    .binary_search(p)
                    .is_err()
            })
            .cloned()
            .collect();
        let mut splits_all: Vec<SubtermSplit> = Vec::new();
        let mut already_false: Vec<Pair> = Vec::new();
        for (s, t) in &changed_negs {
            let splits = split_subterm(&reducible, true, s, t, &mut mk_fresh);
            if splits.is_empty() {
                already_false.push((s.clone(), t.clone()));
            }
            splits_all.extend(splits);
        }
        if splits_all.iter().any(|x| matches!(x, SubtermSplit::TrueD)) {
            contradictory = true;
        }
        // eqFormulas — ¬(x = y) for each EqualD.
        for x in &splits_all {
            if let SubtermSplit::EqualD(l, r) = x {
                emit_neg_eq(l.clone(), r.clone(), &mut new_formulas);
            }
        }
        // acFormulas — `∀ newVar. smallPlus = big ⇒ ⊥` for each
        // ACNewVarD.
        for x in &splits_all {
            if let SubtermSplit::AcNewVarD(small_plus, big, new_var) = x {
                emit_ac_neg(small_plus, big, new_var, &mut new_formulas);
            }
        }
        // Upstream #958: flip a negative natural order only when its
        // smaller operand is already natural, not an unconstrained message.
        for x in &splits_all {
            if let SubtermSplit::NatSubtermD(ns, nt) = x
                && sort_of_lnterm(ns) == LSort::Nat
            {
                use tamarin_term::function_symbols::{nat_one_sym, AcSym};
                use tamarin_term::term::{f_app_ac, f_app_no_eq};
                let one_term: tamarin_term::lterm::LNTerm = f_app_no_eq(nat_one_sym(), vec![]);
                let s_plus_one = f_app_ac(AcSym::NatPlus, vec![ns.clone(), one_term]);
                let exists = red
                    .sys
                    .subterm_store
                    .subterms
                    .iter()
                    .any(|c| c.small == *nt && c.big == s_plus_one)
                    || red
                        .sys
                        .subterm_store
                        .solved_subterms
                        .iter()
                        .any(|c| c.small == *nt && c.big == s_plus_one);
                if !exists {
                    red.sys.invalidate_max_var_idx_cache();
                    red.sys.subterm_store_mut().subterms.push(
                        crate::tools::subterm_store::SubtermConstraint {
                            small: nt.clone(),
                            big: s_plus_one,
                            propagated: false,
                        },
                    );
                }
            }
        }
        // splitSubterms — SubD + NatD leaves union into negSubterms.
        for x in &splits_all {
            if let SubtermSplit::SubtermD(s, t) | SubtermSplit::NatSubtermD(s, t) = x {
                red.sys.invalidate_max_var_idx_cache();
                red.sys.subterm_store_mut().add_neg(s.clone(), t.clone());
            }
        }
        // negSubterms \ alreadyFalse.
        for p in &already_false {
            if let Ok(pos) = red.sys.subterm_store.neg_subterms.binary_search(p) {
                red.sys.invalidate_max_var_idx_cache();
                red.sys.subterm_store_mut().neg_subterms.remove_at(pos);
            }
        }
        // Not a change by itself (`ignoringOldSst1`).
        red.sys.subterm_store_mut().old_neg_subterms = original_negs;
    }

    // Phase 2: `simpSplitPosSt`, one split step per positive subterm:
    // `[TrueD]` drops it, `[]` is a contradiction (it stays, as a goal),
    // no step leaves it without a goal, and a real split makes a goal.
    let mut kept: Vec<crate::tools::subterm_store::SubtermConstraint> = Vec::new();
    let solved: Vec<crate::tools::subterm_store::SubtermConstraint> =
        std::mem::take(&mut red.sys.subterm_store_mut().solved_subterms);
    let mut subs = std::mem::take(&mut red.sys.subterm_store_mut().subterms);
    // sst0: `posSubterms \ solvedSubterms`.
    subs.retain(|c| !solved.iter().any(|x| x.small == c.small && x.big == c.big));
    // `splittableSubterms`.
    let mut subterm_goals: Vec<crate::constraint::constraints::Goal> = Vec::new();
    for c in subs {
        let split = subterm_step(&reducible, &c.small, &c.big, &mut mk_fresh);
        match split {
            Some(ref entries)
                if entries.len() == 1 && matches!(entries[0], SubtermSplit::TrueD) =>
            {
                // `toRemoveAsTrue` removes the pair from the live store.
                // Only `solveSubtermGoal` populates `solved_subterms`.
            }
            Some(ref entries) if entries.is_empty() => {
                contradictory = true;
                subterm_goals.push(crate::constraint::constraints::Goal::Subterm((
                    c.small.clone(),
                    c.big.clone(),
                )));
                kept.push(c);
            }
            None => kept.push(c),
            Some(splits) => {
                subterm_goals.push(crate::constraint::constraints::Goal::Subterm((
                    c.small.clone(),
                    c.big.clone(),
                )));
                // Arity-one deduction: a split `[SubtermD st, EqualD st]`
                // with `st` a negative subterm gives the equality.
                let ss = &splits;
                if let (Some(SubtermSplit::SubtermD(s1, b1)), Some(SubtermSplit::EqualD(s2, b2))) =
                    (ss.first(), ss.get(1))
                    && ss.len() == 2
                    && s1 == s2
                    && b1 == b2
                {
                    // st = (s1, b1)
                    let st_pair = (s1.clone(), b1.clone());
                    if red
                        .sys
                        .subterm_store
                        .neg_subterms
                        .binary_search(&st_pair)
                        .is_ok()
                    {
                        // emit l = r as positive equality
                        let atom = mk_eq_atom(s1, b1);
                        let f = crate::guarded::Guarded::Atom(atom);
                        if !new_formulas.contains(&f) {
                            new_formulas.push(f);
                        }
                    }
                }
                kept.push(c);
            }
        }
    }
    red.sys.invalidate_max_var_idx_cache();
    red.sys.subterm_store_mut().subterms = kept;
    red.sys.invalidate_max_var_idx_cache();
    red.sys.subterm_store_mut().solved_subterms = solved;

    // Phase 3: `negativeSubtermVars` (S_neg): `s ¬⊏ r, t ⊏ r` gives
    // `s ¬⊏ t, s ≠ t`.
    {
        let negs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)> =
            red.sys.subterm_store.neg_subterms.to_vec();
        let pos: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)> = red
            .sys
            .subterm_store
            .subterms
            .iter()
            .chain(red.sys.subterm_store.solved_subterms.iter())
            .map(|c| (c.small.clone(), c.big.clone()))
            .collect();
        for (ns, nr) in &negs {
            for (ps, pr) in &pos {
                if nr == pr {
                    // emit ¬(ns = ps)
                    emit_neg_eq(ns.clone(), ps.clone(), &mut new_formulas);
                    // negSubterms ∪ {(ns, ps)}.
                    red.sys.invalidate_max_var_idx_cache();
                    red.sys.subterm_store_mut().add_neg(ns.clone(), ps.clone());
                }
            }
        }
    }

    // Phase 3b: `hasSubtermCycle` (S_chain) only sets the flag.
    if !contradictory
        && crate::tools::subterm_store::has_subterm_cycle(&reducible, &red.sys.subterm_store)
    {
        contradictory = true;
    }

    // Phase 4: `simpNatCycles`, unconditionally.
    {
        let pos_pairs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)> = red
            .sys
            .subterm_store
            .subterms
            .iter()
            .map(|c| (c.small.clone(), c.big.clone()))
            .collect();
        match nat_subterm_equalities(&pos_pairs) {
            None => {
                contradictory = true;
            }
            Some(eqs) => {
                for (l, r) in eqs {
                    let atom = mk_eq_atom(&l, &r);
                    let f = crate::guarded::Guarded::Atom(atom);
                    if !new_formulas.contains(&f) {
                        new_formulas.push(f);
                    }
                }
            }
        }
    }

    // `simpSubterms` goal update, only for a non-empty goal list: remove
    // open subterm goals not in it, add the new ones. Divergence: Haskell
    // walks `posSubterms` in set order, Rust in insertion order, which can
    // number several goals added in one pass differently.
    if !subterm_goals.is_empty() {
        use crate::constraint::constraints::Goal;
        let to_remove: Vec<Goal> = red
            .sys
            .goals
            .iter()
            .filter(|(g, st)| !st.solved && matches!(g, Goal::Subterm(_)))
            .filter(|(g, _)| !subterm_goals.contains(g))
            .map(|(g, _)| g.clone())
            .collect();
        let to_add: Vec<Goal> = subterm_goals
            .iter()
            .filter(|g| !red.sys.goals.iter().any(|(eg, _)| eg == *g))
            .cloned()
            .collect();
        if !to_remove.is_empty() || !to_add.is_empty() {
            changed_goals = true;
        }
        for g in &to_remove {
            red.sys.invalidate_max_var_idx_cache();
            red.sys.goals_mut().retain(|(eg, _)| eg != g);
        }
        for g in to_add {
            red.insert_goal(g);
        }
    }

    if contradictory {
        red.sys.subterm_store_mut().contradictory = true;
    }
    // Match simpSubterms: compare the resulting constraints, ignoring the
    // old-negative bookkeeping and Rust's propagation markers. Intermediate
    // removal/reinsertion of an already-false negative is not a change.
    let store = &red.sys.subterm_store;
    let changed_store = store.contradictory != previous_contradictory
        || store.neg_subterms != previous_neg
        || pairs(&store.subterms) != previous_pos
        || pairs(&store.solved_subterms) != previous_solved;
    let changed_formulas = new_formulas.iter().any(|f| {
        !crate::guarded::stores_contains(&red.sys.formulas, f)
            && !crate::guarded::stores_contains(&red.sys.solved_formulas, f)
    });
    if changed_store || changed_goals || changed_formulas {
        red.changed = ChangeIndicator::Changed;
    }
    // `forM_ formulas insertFormula`, in derivation order.
    red.insert_formulas(new_formulas)
}

#[cfg(test)]
#[path = "simplify_tests.rs"]
mod tests;
