// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.Solver.Simplify`.
//!
//! `simplifySystem` runs CR-rules that don't case-split until the
//! system stabilises. For the authoritative per-pass order — including
//! the KD-node (N5↓) pass and the Rust-specific passes
//! (remove_solved_split_goals, propagate_subterm_obvious — the
//! `simpSubterms` analog —, dedupe_formulas, drop_trivially_true,
//! normalise_less_atoms) — see the documented sequence at the
//! `simplify_system` loop below.
//!
//! Each pass is a `Reduction` step that may modify the system. This Rust
//! port implements the full fixpoint loop and every pass. Branch and fresh-
//! counter ownership follows `constraint/solver/BRANCHING.md`.

use crate::constraint::solver::reduction::{
    ChangeIndicator, GoalCases, Reduction, SystemBranch, SystemOutcome,
};
use crate::tools::equation_store::LNSubst;
use crate::tools::subterm_store::nat_subterm_equalities;

type SimplifyPass = fn(&mut Reduction<'_>);
type FalliblePass = fn(&mut Reduction<'_>) -> Result<SystemOutcome, crate::prove::ProveError>;

#[derive(Clone, Copy)]
enum Pass {
    Linear(SimplifyPass),
    Fallible(FalliblePass),
}

impl Pass {
    fn run(self, red: &mut Reduction<'_>) -> Result<SystemOutcome, crate::prove::ProveError> {
        Ok(match self {
            Pass::Linear(pass) => {
                pass(red);
                SystemOutcome::Linear
            }
            Pass::Fallible(pass) => return pass(red),
        })
    }
}

const SIMPLIFY_PASSES: &[Pass] = &[
    Pass::Fallible(enforce_fresh_node_uniqueness_pass),
    Pass::Fallible(enforce_kd_fact_uniqueness_pass),
    Pass::Fallible(enforce_ku_action_uniqueness_pass),
    Pass::Fallible(enforce_edge_uniqueness_pass),
    Pass::Fallible(solve_unique_actions_pass_fan_out),
    Pass::Fallible(reduce_formulas_pass),
    Pass::Fallible(eval_formula_atoms_pass),
    Pass::Linear(enforce_fresh_ordering_pass),
    Pass::Fallible(propagate_subterm_obvious),
    Pass::Fallible(simp_injective_fact_eq_mon_pass),
    Pass::Fallible(merge_last_injective_fact_nodes),
    Pass::Fallible(insert_implied_formulas_pass),
    Pass::Linear(dedupe_formulas_pass),
    Pass::Linear(drop_trivially_true_formulas_pass),
    Pass::Linear(normalise_less_atoms_pass),
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
    let base = red.sys.clone();
    let result = red.solve_node_id_eqs(&equations);
    complete_solve(red, base, result)
}

/// The non-diff tail of HS `simplifySystem` (Simplify.hs), run once after
/// the fixpoint loop: `exploitUniqueMsgOrder`, `removeSolvedSplitGoals`,
/// `addNonInjectiveFactInstances`.
fn simp_post_loop_steps(red: &mut Reduction) {
    exploit_unique_msg_order(red);
    red.remove_solved_split_goals();
    add_non_injective_fact_instances(red);
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
    // `new_inheriting` consults the `REFINE_FLOOR` thread-local so this
    // sub-reduction inherits the source precompute's `avoid th` seed (HS
    // Sources.hs); 0 (general proving path) is a no-op.
    let mut red = Reduction::new_inheriting(ctx, sys, seed);
    simplify_system_fan_out_inner(&mut red)
}

/// Inner driver — mirrors the body of `simplify_system` but propagates
/// fan-out from two sources:
///   1. `solve_unique_actions_pass_fan_out` — when `solveGoal (ActionG)`
///      returns `GoalCases::Cases`.
///   2. `SystemOutcome::Cases` from any branching simplify pass.
///
/// Each branch continues with its own system and inherited FreshT counter,
/// including allocations that are no longer visible in the system.
fn simplify_system_fan_out_inner(
    red: &mut Reduction,
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    simplify_system_fan_out_inner_with_passes(red, SIMPLIFY_PASSES)
}

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
    simp_post_loop_steps(red);
    Ok(vec![SystemBranch {
        sys: std::mem::replace(&mut red.sys, crate::constraint::system::System::empty()),
        counter: red.maude.fresh_counter_peek(),
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
        let outcome = pass.run(red)?;
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
    let mut out = Vec::new();
    for arm in arms {
        let mut branch_out = continue_simplify_branch(arm, ctx, passes, next_pass, changed)?;
        out.append(&mut branch_out);
    }
    Ok(out)
}

fn continue_simplify_branch(
    arm: SystemBranch,
    ctx: &crate::constraint::solver::context::ProofContext,
    passes: &[Pass],
    next_pass: usize,
    changed: ChangeIndicator,
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    if arm.sys.eq_store().is_false() {
        return Ok(Vec::new());
    }
    let mut branch = Reduction::new_inheriting(ctx, arm.sys, arm.counter);
    branch.changed = changed;
    match continue_simplify_iteration(&mut branch, passes, next_pass)? {
        Some(branches) => Ok(branches),
        None if branch.changed == ChangeIndicator::Changed => {
            simplify_system_fan_out_inner_with_passes(&mut branch, passes)
        }
        None => {
            simp_post_loop_steps(&mut branch);
            Ok(vec![SystemBranch {
                sys: branch.sys,
                counter: branch.maude.fresh_counter_peek(),
            }])
        }
    }
}

/// Attach a low-level equality result to its common pre-solve system.
fn complete_solve(
    red: &mut Reduction,
    base: crate::constraint::system::System,
    res: std::result::Result<
        crate::constraint::solver::reduction::SolveOutcome,
        crate::prove::ProveError,
    >,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    Ok(match res {
        Err(error) => return Err(error),
        Ok(crate::constraint::solver::reduction::SolveOutcome::Contradictory) => {
            red.mark_contradictory();
            SystemOutcome::Contradictory
        }
        Ok(crate::constraint::solver::reduction::SolveOutcome::Linear) => SystemOutcome::Linear,
        Ok(crate::constraint::solver::reduction::SolveOutcome::Cases(arms)) => {
            let cases = arms
                .into_iter()
                .map(|arm| {
                    let mut sys = base.clone();
                    sys.invalidate_max_var_idx_cache();
                    sys.set_eq_store(std::sync::Arc::new(arm.eq_store));
                    SystemBranch {
                        sys,
                        counter: arm.counter,
                    }
                })
                .collect();
            red.finish_system_cases(cases)
        }
    })
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
fn add_non_injective_fact_instances(red: &mut Reduction) {
    use crate::constraint::constraints::{LessAtom, Reason};
    let pairs = non_injective_fact_instances_pairs(red);
    for (a, b) in pairs {
        red.insert_less(LessAtom::new(a, b, Reason::InjectiveFacts));
    }
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
) -> Vec<(
    crate::constraint::constraints::NodeId,
    crate::constraint::constraints::NodeId,
)> {
    use crate::constraint::constraints::NodeId;
    let sys = &red.sys;
    let ctxt = red.ctx;
    let mut out: Vec<(NodeId, NodeId)> = Vec::new();
    if ctxt.injective_fact_insts.is_empty() {
        return out;
    }

    // Resolve node-id → rule via a once-built map instead of a linear
    // `nodes.iter().find` per lookup (see `System::node_rule_map`).
    let node_rule_map = sys.node_rule_map();
    let lookup_node =
        |id: &NodeId| -> Option<&crate::rule::RuleACInst> { node_rule_map.get(id).copied() };
    let non_unifiable_nodes = |i: &NodeId, j: &NodeId| {
        non_unifiable_nodes(&ctxt.maude, &node_rule_map, i, j).unwrap_or(false)
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
        if !ctxt.injective_fact_insts.contains_key(&k_fa_prem.tag) {
            continue;
        }
        let k_term = match k_fa_prem.terms.first() {
            Some(t) => t,
            None => continue,
        };
        let conflicting = |fa: &crate::fact::LNFact| -> bool {
            fa.tag == k_fa_prem.tag && fa.terms.first() == Some(k_term)
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
            if non_unifiable_nodes(j, &i) {
                out.push((*j, i));
                continue;
            }
            // checkRuleIJ: i<j and nonUnifiable(k, j) — return (k, j)
            // Haskell's IJ branch uses `D.reachableSet [i] less`; we
            // mirror that with `i < j`.
            if sys.always_before_with(&ab_adj, &i, j) && non_unifiable_nodes(&k, j) {
                out.push((k, *j));
            }
        }
    }
    out
}

/// CR-rule *N6* — `exploitUniqueMsgOrder` (`Simplify.hs`).
///
/// Every term `m` that appears as both a KD-conclusion (at node
/// `i_kd`) and a KU-action (at node `i_ku`) must satisfy
/// `i_kd < i_ku` — the adversary deconstructs `m` from a message
/// before it can use `m` as part of a constructed message.  This
/// is normal-form invariant N6 from the constraint-system paper.
///
/// Adds `LessAtom(i_kd, i_ku, NormalForm)` for every such pair
/// (skipping cases where `i_kd == i_ku`, which would just be a
/// redundant reflexive ordering).
fn exploit_unique_msg_order(red: &mut Reduction) {
    use crate::constraint::constraints::{LessAtom, NodeId, Reason};
    use crate::fact::FactTag;
    use std::collections::BTreeMap;
    use tamarin_term::lterm::LNTerm;

    // Collect KD-conclusion (term, node) pairs.
    let mut kd_conc: BTreeMap<LNTerm, NodeId> = BTreeMap::new();
    for (id, rule) in red.sys.nodes.iter() {
        for fa in &rule.conclusions {
            if matches!(fa.tag, FactTag::Kd)
                && let Some(m) = fa.terms.first()
            {
                // First occurrence wins; N5↓ has already merged
                // duplicates by this point.
                kd_conc.entry(m.clone()).or_insert_with(|| *id);
            }
        }
    }
    if kd_conc.is_empty() {
        return;
    }
    // Collect KU-action (term, node) pairs.  Haskell `allActions`
    // (System.hs) combines `unsolvedActionAtoms` with `rule.acts`
    // — so we MUST include open Action goals here, not just rule
    // actions.  Without this, KU goals added by existential atom
    // decomposition (e.g. `∃ #j. KU(t) @ j`) don't participate in
    // N6's NormalForm ordering, leaving a Cyclic detection gap.
    let mut ku_act: BTreeMap<LNTerm, NodeId> = BTreeMap::new();
    for (id, rule) in red.sys.nodes.iter() {
        for fa in &rule.actions {
            if matches!(fa.tag, FactTag::Ku)
                && let Some(m) = fa.terms.first()
            {
                ku_act.entry(m.clone()).or_insert_with(|| *id);
            }
        }
    }
    for (goal, st) in red.sys.goals.iter() {
        if st.solved {
            continue;
        }
        if let crate::constraint::constraints::Goal::Action(i, fa) = goal
            && matches!(fa.tag, FactTag::Ku)
            && let Some(m) = fa.terms.first()
        {
            ku_act.entry(m.clone()).or_insert_with(|| *i);
        }
    }
    if ku_act.is_empty() {
        return;
    }
    // Intersection: for every term in both maps, add the ordering.  HS
    // inserts UNCONDITIONALLY (`F.mapM_ insertLess … M.intersectionWith`,
    // Simplify.hs) — including the REFLEXIVE `LessAtom i i` when one
    // node both concludes KD(m) and carries a KU(m) action.  That self-edge
    // makes `rawLessRel` cyclic, so the contradiction check kills the
    // system: exactly how HS prunes source cases built from (wf-invalid)
    // protocol rules that use the reserved KU/KD facts (regression/trace/
    // issue515.spthy).  An `i_kd != i_ku` guard here would keep a spurious
    // source case for every such KU pattern whose premises are solvable.
    for (m, i_kd) in &kd_conc {
        if let Some(i_ku) = ku_act.get(m) {
            red.insert_less(LessAtom::new(*i_kd, *i_ku, Reason::NormalForm));
        }
    }
}

/// CR-rule pass: `evalFormulaAtoms` (Haskell). Walks every guarded
/// formula in `sFormulas`, applies `partial_atom_valuation` to its
/// atoms, and re-inserts the simplified result. Atoms that evaluate
/// to a known truth value collapse to `gtrue`/`gfalse`, dropping
/// out of disjunctions or short-circuiting conjunctions.
fn eval_formula_atoms_pass(red: &mut Reduction) -> Result<SystemOutcome, crate::prove::ProveError> {
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
            let simp = simplify_guarded_with(fm, &val);
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
                let mut completed = Vec::new();
                for arm in arms {
                    let mut branch = Reduction::new_inheriting(red.ctx, arm.sys, arm.counter);
                    match apply_formula_atom_changes(&mut branch, rest)? {
                        SystemOutcome::Linear => completed.push(SystemBranch {
                            sys: branch.sys,
                            counter: branch.maude.fresh_counter_peek(),
                        }),
                        SystemOutcome::Cases(arms) => completed.extend(arms),
                        SystemOutcome::Contradictory => {}
                    }
                }
                return Ok(red.finish_system_cases(completed));
            }
        }
    }
    Ok(SystemOutcome::Linear)
}

/// HS `partialAtomValuation` (Simplify.hs): `Some(b)` when the atom has truth
/// value `b` in every model of the system, `None` when unknown. `ab_adj` is
/// the pass's `rawLessRel`, HS's shared `before`.
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
) -> Option<bool> {
    use crate::atom::ProtoAtom;
    // Maude errors count as unifiable.
    let non_unifiable_nodes =
        |i: &crate::constraint::constraints::NodeId, j: &crate::constraint::constraints::NodeId| {
            non_unifiable_nodes(maude, node_rule, i, j).unwrap_or(false)
        };
    match atom {
        ProtoAtom::Less(i, j) => {
            let ni = eq_node_id(i)?;
            let nj = eq_node_id(j)?;
            // HS guard order: `j before i` wins over `i before j` on a cycle.
            if ni == nj {
                return Some(false);
            }
            if sys.always_before_with(ab_adj, &nj, &ni) {
                return Some(false);
            }
            if sys.always_before_with(ab_adj, &ni, &nj) {
                return Some(true);
            }
            if sys.is_last(&ni) && sys.is_in_trace(&nj) {
                return Some(false);
            }
            if sys.is_last(&nj) && sys.is_in_trace(&ni) && non_unifiable_nodes(&ni, &nj) {
                return Some(true);
            }
            None
        }
        ProtoAtom::EqE(x, y) => {
            if x == y {
                return Some(true);
            }
            // Node-id case: compare via the order relation and
            // rule-instance unifiability.
            if let (Some(ni), Some(nj)) = (eq_node_id(x), eq_node_id(y)) {
                if sys.always_before_with(ab_adj, &ni, &nj)
                    || sys.always_before_with(ab_adj, &nj, &ni)
                {
                    return Some(false);
                }
                if non_unifiable_nodes(&ni, &nj) {
                    return Some(false);
                }
                return None;
            }
            // Term-level case: ask Maude whether the two terms are
            // unifiable.  Mirrors Haskell's `EqE` arm in
            // `partialAtomValuation` (Simplify.hs) via
            // `unifiableLNTerms`.  If non-unifiable, the equality
            // is False in every model.  If unifiable, we leave it
            // unknown — the equality may or may not hold once the
            // proof state is refined.
            match maude.unify(&[tamarin_term::rewriting::Equal {
                lhs: x.clone(),
                rhs: y.clone(),
            }]) {
                Ok(uns) if uns.is_empty() => Some(false),
                _ => None,
            }
        }
        ProtoAtom::Action(t, lnfa) => {
            let n = eq_node_id(t)?;
            // `ActionG i fa` membership counts solved goals too.
            for (g, _st) in sys.goals.iter() {
                if let crate::constraint::constraints::Goal::Action(gi, gfa) = g
                    && gi == &n
                    && gfa == lnfa
                {
                    return Some(true);
                }
            }
            let rule = node_rule.get(&n).copied()?;
            if rule.actions.iter().any(|a| a == lnfa) {
                return Some(true);
            }
            // False when no action unifies with `fa`; a Maude error counts
            // as unifiable.
            let mut all_non_unif = true;
            for a in &rule.actions {
                match crate::rule::unifiable_ln_facts(maude, lnfa, a) {
                    Ok(true) => {
                        all_non_unif = false;
                        break;
                    }
                    Ok(false) => {}
                    Err(_) => {
                        all_non_unif = false;
                        break;
                    }
                }
            }
            if all_non_unif {
                return Some(false);
            }
            None
        }
        ProtoAtom::Last(t) => {
            let n = eq_node_id(t)?;
            // Haskell-faithful (Simplify.hs):
            //   Last i
            //     | isLast sys i                       -> Just True
            //     | any (isInTrace sys) (nodesAfter i) -> Just False
            //     | otherwise -> case sLastAtom of
            //         Just j | nonUnifiableNodes i j   -> Just False
            //         _                                -> Nothing
            //
            // `nodesAfter i = filter (i /=) $ reachableSet [i] lessRel`
            // where `lessRel = sLessAtoms ++ rawEdgeRel`.
            // `isInTrace` is the 3-clause check (sNodes / isLast /
            // unsolvedActionAtoms).  Do NOT add
            // extra "successor exists → Some(false)" checks: HS returns
            // `Nothing` when a successor is a free variable not in trace.
            if sys.is_last(&n) {
                return Some(true);
            }
            // Build lessRel = less_atoms ∪ edges-as-less.
            let less_rel: Vec<(
                crate::constraint::constraints::NodeId,
                crate::constraint::constraints::NodeId,
            )> = sys
                .less_atoms
                .iter()
                .map(|l| (l.smaller, l.larger))
                .chain(sys.edges.iter().map(|e| (e.src.0, e.tgt.0)))
                .collect();
            // nodesAfter n = transitive closure from n via less_rel.
            let mut frontier: Vec<crate::constraint::constraints::NodeId> = vec![n];
            let mut seen: std::collections::BTreeSet<_> = [n].into_iter().collect();
            while let Some(cur) = frontier.pop() {
                for (a, b) in &less_rel {
                    if a == &cur && !seen.contains(b) {
                        seen.insert(*b);
                        frontier.push(*b);
                    }
                }
            }
            // Check `any (isInTrace) (nodesAfter n)` (excluding n itself).
            for j in seen.iter() {
                if j != &n && sys.is_in_trace(j) {
                    return Some(false);
                }
            }
            // Final fallback: if there's a recorded last_atom and it's
            // non-unifiable with n, then n cannot be last.
            if let Some(la) = &sys.last_atom
                && non_unifiable_nodes(&n, la)
            {
                return Some(false);
            }
            None
        }
        // HS `Subterm small big -> isTrueFalse reducible (Just sst) (small, big)`
        // (Simplify.hs).
        ProtoAtom::Subterm(small, big) => subterms.is_true_false(small, big),
        _ => None,
    }
}

/// The node id `partial_atom_valuation_with` reads out of a timepoint term:
/// any variable leaf, coerced to `LSort::Node`.
///
/// DIVERGENCE from HS `partialAtomValuation` (Simplify.hs).  The `EqE`
/// arm there asks `unifiableLNTerms` FIRST and only then reads `ltermNodeId`,
/// which answers `Just` at `LSortNode` alone (LTerm.hs), so
/// `$A = ~b` is `Just False` for HS.  Here the arm consults this coercing
/// lookup before Maude and answers `None` for that atom.  The port's `Less`,
/// `Action` and `Last` arms read the same lookup where HS's `ltermNodeId'`
/// errors on any other sort.
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
    use crate::constraint::constraints::Goal;
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
    let mut fresh =
        tamarin_utils::fresh::FastFreshState::seeded(red.fresh_var_baseline().saturating_add(1));
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

    // HS `allActions` (System.hs): unsolved action goals in goal order, then
    // node actions in node-id order.
    let mut unsolved_actions: Vec<(crate::constraint::constraints::NodeId, crate::fact::LNFact)> =
        red.sys
            .goals
            .iter()
            .filter(|(_, st)| !st.solved)
            .filter_map(|(g, _)| match g {
                Goal::Action(i, fa) => Some((*i, fa.clone())),
                _ => None,
            })
            .collect();
    unsolved_actions.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    let mut sys_actions = unsolved_actions;
    for (id, rule) in red.sys.nodes_in_map_order() {
        sys_actions.extend(rule.actions.iter().map(|a| (*id, a.clone())));
    }

    // Lookup-only index of `sys_actions` by fact name, ascending within a
    // name, so matching visits the same actions in the same order.
    let mut actions_by_name: tamarin_utils::FastMap<String, Vec<u32>> =
        tamarin_utils::FastMap::default();
    for (ai, (_, fa)) in sys_actions.iter().enumerate() {
        actions_by_name
            .entry(crate::fact::fact_tag_name(&fa.tag))
            .or_default()
            .push(ai as u32);
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
            &actions_by_name,
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
    red.insert_formulas(&new_formulas)
}

/// Try every assignment of system actions to the universal's action
/// guards. For each consistent assignment that binds all universal
/// vars, instantiate the body and add to `new_formulas`.
fn try_match_all_guards(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    vars: &[tamarin_term::lterm::LVar],
    action_guards: &[&crate::atom::Atom<tamarin_term::lterm::LNTerm>],
    sys_actions: &[(crate::constraint::constraints::NodeId, crate::fact::LNFact)],
    // Pass-invariant name index over `sys_actions` (see
    // `insert_implied_formulas_pass`): the Action-guard arm iterates only the
    // name-equal group, in original `sys_actions` order.
    actions_by_name: &tamarin_utils::FastMap<String, Vec<u32>>,
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
        sys_actions: &[(crate::constraint::constraints::NodeId, crate::fact::LNFact)],
        actions_by_name: &tamarin_utils::FastMap<String, Vec<u32>>,
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
                let name_group = actions_by_name
                    .get(&crate::fact::fact_tag_name(&g_fact_subst.tag))
                    .map(|v| v.as_slice())
                    .unwrap_or(&[]);
                for &ai in name_group {
                    let (i, fa_sys) = &sys_actions[ai as usize];
                    if g_fact_subst.terms.len() != fa_sys.terms.len() {
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
                        &fa_sys.terms,
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
                            actions_by_name,
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
                let (pat_term, subj_term) = match (s_has_pat, t_has_pat) {
                    // Both sides ground after skolemisation: match iff equal.
                    (false, false) => {
                        if s_subst == t_subst {
                            rec(
                                maude,
                                vars,
                                pattern_vars,
                                guards,
                                guard_idx + 1,
                                sys_actions,
                                actions_by_name,
                                acc,
                                body,
                                sys,
                                other_guards,
                                out,
                            )?;
                        }
                        return Ok(());
                    }
                    // s has pattern vars → s is the pattern.
                    (true, false) => (s_subst, t_subst),
                    // t has pattern vars → t is the pattern.
                    (false, true) => (t_subst, s_subst),
                    // Both have pattern vars — Haskell errors on
                    // this case.  We bail out: drop this assignment
                    // rather than trying to match unbound-vs-unbound,
                    // which can't soundly produce a unique sigma.
                    (true, true) => return Ok(()),
                };
                // Run the structural match, with the recursion-invariant
                // `pattern_vars` set hoisted to `try_match_all_guards` (it
                // depends only on `vars`).
                let (pat_lnt, subj_lnt) = (pat_term, subj_term);
                let mut struct_subst = std::collections::BTreeMap::new();
                let struct_outcome =
                    structural_match(&pat_lnt, &subj_lnt, pattern_vars, &mut struct_subst);
                // Use native matching unless the terms require AC matching.
                // Skolemize free system variables on both sides with the same
                // map; only universal-bound variables may receive bindings.
                // Each AC matcher produces a separate continuation.
                let candidates: Vec<
                    std::collections::BTreeMap<
                        tamarin_term::lterm::LVar,
                        tamarin_term::lterm::LNTerm,
                    >,
                > = match struct_outcome {
                    StructMatch::Matched => vec![struct_subst],
                    StructMatch::NoMatcher => return Ok(()),
                    StructMatch::NeedsAc => {
                        let eqs = vec![tamarin_term::rewriting::Equal {
                            lhs: pat_lnt,
                            rhs: subj_lnt,
                        }];
                        match maude.match_eqs_skolemize_both(&eqs, pattern_vars) {
                            Ok(matches) => matches
                                .into_iter()
                                .map(|m| m.into_iter().collect())
                                .collect(),
                            Err(error) => {
                                return Err(crate::prove::ProveError::Maude(error.to_string()))
                            }
                        }
                    }
                };
                if candidates.is_empty() {
                    return Ok(());
                }
                for struct_subst in candidates {
                    // Keep the LVar → LNTerm bindings of the universal's own
                    // variables.
                    let mut subst_here: std::collections::BTreeMap<
                        tamarin_term::lterm::LVar,
                        tamarin_term::lterm::LNTerm,
                    > = std::collections::BTreeMap::new();
                    for (lv, lt) in struct_subst {
                        if !vars.iter().any(|v| v.name == lv.name && v.idx == lv.idx) {
                            continue;
                        }
                        subst_here.insert(lv, lt);
                    }
                    let subst_here = LNSubst::from_map(subst_here);
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
                        actions_by_name,
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
        actions_by_name,
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

/// Outcome of `structural_match`, mirroring HS `matchRaw`'s three
/// possible results (`Term/Unification.hs`):
///
/// * `Matched`   — `Right ()`: the native matcher succeeded; the
///   accumulated `subst` is the (unique) matcher.  HS returns
///   `[substFromMap mappings]`, NO Maude call.
/// * `NoMatcher` — `Left NoMatcher`: a structural clash (constant vs
///   constant, head/arity mismatch, sort mismatch, a non-pattern var
///   facing a non-identical subject, OR a pattern var already bound to
///   a different subject).  HS returns `[]` natively, NO Maude call.
/// * `NeedsAc`   — `Left ACProblem`: an AC-/C-headed pair appeared on
///   BOTH sides during the recursion (`(FApp (AC _) _, FApp (AC _) _)`
///   / `(FApp (C _) _, FApp (C _) _)`, `Unification.hs`).  Only
///   here does HS call `matchViaMaude` on the *whole* problem.
///
/// CRITICAL HS-faithfulness point: an AC-/C-headed subterm under a
/// PATTERN VARIABLE never triggers `NeedsAc` — HS checks the pattern-var
/// arm `(_, Lit (Var vp))` FIRST (`Unification.hs`) and binds the
/// var to the whole subject without inspecting its AC shape.  Likewise a
/// function-app PATTERN facing a plain-variable SUBJECT is a `NoMatcher`
/// (HS falls to the `_ -> throwError NoMatcher` arm), NOT an AC problem —
/// because the AC arm requires BOTH sides AC-headed.  A coarse "any AC
/// symbol appears anywhere" proxy over-triggers Maude on
/// structurally-failing matches that merely mention an AC operator
/// (LAK06: 28,879 Maude matches where HS issues 0; Scott: 10,748 vs 598)
/// — which is why only `NeedsAc` (both sides AC-/C-headed) reaches Maude
/// while `NoMatcher` fails natively.
#[derive(Debug, PartialEq, Eq)]
enum StructMatch {
    Matched,
    NoMatcher,
    NeedsAc,
}

/// Structural pattern matcher for `LNTerm`s.  Faithful port of the
/// pure portion of Haskell's `Term.Unification.matchRaw`
/// (`lib/term/src/Term/Unification.hs`), returning the 3-way
/// `StructMatch` outcome so the caller can mirror `solveMatchLTerm`'s
/// `case runState (runExceptT match)` dispatch (`Unification.hs`)
/// exactly — only `NeedsAc` warrants a Maude AC fallback.
///
///   - If `pat` is an LVar whose (name, idx) is in `pattern_vars`
///     (a bindable universal var = HS's post-`openGuarded` `Var`),
///     bind it to `subj` (or check consistency with an existing
///     binding) — but only if the subject's sort is a subsort of
///     the pattern var's sort.  (HS `sortGeqLTerm`, `Unification.hs`.)
///   - If `pat` is a non-pattern LVar (= HS `Con (SkConst _)` after
///     `skolemizeGuarded`), it matches only the *same* literal LVar.
///   - Constant vs constant: match iff equal.
///   - `NoEq`/`List` app vs same: equal head + arity ⇒ recurse pairwise
///     (left-to-right, first failure wins, like HS `sequence_ . zipWith`).
///   - `AC`-vs-`AC` or `C`-vs-`C`: `NeedsAc` (HS `throwError ACProblem`).
///   - Otherwise (head/arity/shape mismatch): `NoMatcher`.
///
/// Left-to-right short-circuit on the FIRST failure matches HS `forM_` /
/// `sequence_` ordering, so the first failing pair's classification
/// (NoMatcher vs ACProblem) is the one that propagates.
fn structural_match(
    pat: &tamarin_term::lterm::LNTerm,
    subj: &tamarin_term::lterm::LNTerm,
    pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
    subst: &mut std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm>,
) -> StructMatch {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    fn sort_compatible(pat_sort: LSort, subj_sort: LSort) -> bool {
        // Subject's sort must be the pattern sort or a subsort.
        // Subsort lattice: Pub < Msg, Fresh < Msg, Nat < Msg,
        // Node has its own line, Msg < TOP.
        if pat_sort == subj_sort {
            return true;
        }
        matches!(
            (pat_sort, subj_sort),
            (LSort::Msg, LSort::Pub | LSort::Fresh | LSort::Nat)
        )
    }
    // Pairwise left-to-right recursion shared by the `NoEq` and `List`
    // arms (HS `sequence_ . zipWith match`): equal arity required, first
    // non-`Matched` outcome wins.
    fn match_args(
        p_args: &[tamarin_term::lterm::LNTerm],
        s_args: &[tamarin_term::lterm::LNTerm],
        pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
        subst: &mut std::collections::BTreeMap<
            tamarin_term::lterm::LVar,
            tamarin_term::lterm::LNTerm,
        >,
    ) -> StructMatch {
        if p_args.len() != s_args.len() {
            return StructMatch::NoMatcher;
        }
        for (pa, sa) in p_args.iter().zip(s_args.iter()) {
            match structural_match(pa, sa, pattern_vars, subst) {
                StructMatch::Matched => {}
                other => return other,
            }
        }
        StructMatch::Matched
    }
    match (pat, subj) {
        // Pattern-bound var: bindable Maude var.  Mirrors HS
        // `(_, Lit (Var vp))` (`Unification.hs`) — checked
        // FIRST, so an AC-headed subject under a pattern var is bound
        // natively (never `NeedsAc`).  After `skolemizeGuarded`
        // (System.hs + Guarded.hs) the universal's bound
        // vars remain `Var`; free system vars become `SkConst`.
        (Term::Lit(Lit::Var(pv)), _) if pattern_vars.contains(&(pv.name, pv.idx)) => {
            let subj_sort = tamarin_term::lterm::sort_of_lnterm(subj);
            if !sort_compatible(pv.sort, subj_sort) {
                return StructMatch::NoMatcher;
            }
            if let Some(existing) = subst.get(pv) {
                // HS `Just tp | t == tp -> () | otherwise -> NoMatcher`
                // (Unification.hs).
                return if existing == subj {
                    StructMatch::Matched
                } else {
                    StructMatch::NoMatcher
                };
            }
            if matches!(subj, Term::Lit(Lit::Var(sv)) if sv == pv) {
                return StructMatch::Matched;
            }
            subst.insert(*pv, subj.clone());
            StructMatch::Matched
        }
        // Non-pattern LVar = SkConst-equivalent: matches only the same
        // literal LVar on the subject side.  HS `skolemizeAtom` turns
        // free LVars into `Con (SkConst v)`, so on the pattern side this
        // is a constant — it falls into HS's `(Lit (Con _), Lit (Con _))`
        // arm (Unification.hs) which matches iff equal.
        (Term::Lit(Lit::Var(pv)), Term::Lit(Lit::Var(sv))) => {
            if pv == sv {
                StructMatch::Matched
            } else {
                StructMatch::NoMatcher
            }
        }
        (Term::Lit(Lit::Con(pn)), Term::Lit(Lit::Con(sn))) => {
            if pn == sn {
                StructMatch::Matched
            } else {
                StructMatch::NoMatcher
            }
        }
        // HS `(FApp (NoEq tfsym) targs, FApp (NoEq pfsym) pargs)`
        // (Unification.hs) and the `List` arm:
        // equal head + arity ⇒ recurse pairwise.  Note: `subj` is HS's
        // `t` (term/subject), `pat` is HS's `p` (pattern); the head/arity
        // guard is symmetric so the order here doesn't matter.
        (Term::App(FunSym::NoEq(pf), p_args), Term::App(FunSym::NoEq(sf), s_args)) => {
            if pf != sf {
                return StructMatch::NoMatcher;
            }
            match_args(p_args, s_args, pattern_vars, subst)
        }
        (Term::App(FunSym::List, p_args), Term::App(FunSym::List, s_args)) => {
            match_args(p_args, s_args, pattern_vars, subst)
        }
        // HS `(FApp (AC _) _, FApp (AC _) _) -> throwError ACProblem`
        // and `(FApp (C _) _, FApp (C _) _) -> throwError ACProblem`
        // (Unification.hs): ONLY when BOTH sides are AC-/C-headed.
        (Term::App(FunSym::Ac(_), _), Term::App(FunSym::Ac(_), _))
        | (Term::App(FunSym::C(_), _), Term::App(FunSym::C(_), _)) => StructMatch::NeedsAc,
        // HS `_ -> throwError NoMatcher` (Unification.hs): every
        // other constructor pairing (incl. AC-vs-NoEq, app-vs-literal,
        // mismatched AC vs C heads).
        _ => StructMatch::NoMatcher,
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

    let mut eqs = Vec::new();
    for (g_arg, sys_term) in g_fact.terms.iter().zip(sys_args.iter()) {
        eqs.push(tamarin_term::rewriting::Equal {
            lhs: g_arg.clone(),
            rhs: sys_term.clone(),
        });
    }
    if eqs.is_empty() {
        return Ok(vec![LNSubst::from_map(base_subst)]);
    }

    // HS `matchTerms` (Unification.hs): one shared mapping across all pairs,
    // stopping at the first failure; only an `ACProblem` goes to Maude.
    let mut struct_subst: std::collections::BTreeMap<
        tamarin_term::lterm::LVar,
        tamarin_term::lterm::LNTerm,
    > = std::collections::BTreeMap::new();
    let mut outcome = StructMatch::Matched;
    for eq in &eqs {
        match structural_match(&eq.lhs, &eq.rhs, pattern_vars, &mut struct_subst) {
            StructMatch::Matched => {}
            other => {
                outcome = other;
                break;
            }
        }
    }
    let ms: Vec<Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>> = match outcome {
        StructMatch::Matched => vec![struct_subst.into_iter().collect()],
        StructMatch::NoMatcher => return Ok(Vec::new()),
        StructMatch::NeedsAc => {
            // A Maude failure is an error, never an absent match.
            let matches = maude
                .match_eqs_skolemize_both(&eqs, pattern_vars)
                .map_err(|error| crate::prove::ProveError::Maude(error.to_string()))?;
            if matches.is_empty() {
                return Ok(Vec::new());
            }
            matches
        }
    };

    // Keep only the universal's bindings; system variables are skolemised.
    let mut out: Vec<LNSubst> = Vec::with_capacity(ms.len());
    for m in ms {
        let mut subst = base_subst.clone();
        for (lv, lt) in m {
            if !pattern_vars.contains(&(lv.name, lv.idx)) {
                continue;
            }
            subst.insert(lv, lt);
        }
        out.push(LNSubst::from_map(subst));
    }
    Ok(out)
}

/// Apply the eq-store substitution to existing `less_atoms` so any
/// mid-loop node merges propagate to atoms that were inserted earlier.
fn normalise_less_atoms_pass(red: &mut Reduction) {
    let mut changed = if red.sys.normalise_less_atoms() {
        ChangeIndicator::Changed
    } else {
        ChangeIndicator::Unchanged
    };
    // HS-faithful dedup post-normalise: HS's `sLessAtoms` is a `Set`;
    // post-subst image collapsing two distinct atoms is auto-deduped.
    // See `subst_system_once` (reduction.rs) for full rationale.
    let pre_len = red.sys.less_atoms.len();
    let mut new_less: Vec<crate::constraint::constraints::LessAtom> = Vec::with_capacity(pre_len);
    // First-occurrence-wins dedup: `LessAtom`'s manual `Eq` (constraints.rs)
    // ignores the reason, so the identity key is the `(smaller,larger)`
    // pair.  A `FastSet` membership probe: the atom is pushed iff its pair
    // is unseen — the same relation a linear `any(|x| x == &la)` scan tests
    // — turning the O(n²) dedup into O(n).  The set
    // never escapes (only membership is read), so its hash order is
    // irrelevant; only `new_less`'s Vec order is output-bearing.
    let mut seen: tamarin_utils::FastSet<(tamarin_term::lterm::LVar, tamarin_term::lterm::LVar)> =
        tamarin_utils::FastSet::default();
    for la in std::mem::take(&mut red.sys.content_mut_untracked().less_atoms) {
        if seen.insert((la.smaller, la.larger)) {
            new_less.push(la);
        }
    }
    if new_less.len() != pre_len {
        changed = ChangeIndicator::Changed;
        red.sys.invalidate_max_var_idx_cache();
    }
    red.sys.content_mut_untracked().less_atoms = new_less;
    if changed == ChangeIndicator::Changed {
        red.changed = ChangeIndicator::Changed;
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
    ) -> std::result::Result<
        crate::constraint::solver::reduction::SolveOutcome,
        crate::prove::ProveError,
    >,
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
        node_eqs.retain(|e| e.lhs != e.rhs);
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
    ) -> std::result::Result<
        crate::constraint::solver::reduction::SolveOutcome,
        crate::prove::ProveError,
    >,
{
    while let Some(((payload_eqs, node_eqs), rest)) = groups.split_first() {
        match merge_candidate_group(red, payload_eqs, node_eqs, solve_payload_eqs)? {
            SystemOutcome::Linear => groups = rest,
            SystemOutcome::Contradictory => return Ok(SystemOutcome::Contradictory),
            SystemOutcome::Cases(arms) => {
                return continue_merge_groups(red, arms, rest, solve_payload_eqs);
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
    ) -> std::result::Result<
        crate::constraint::solver::reduction::SolveOutcome,
        crate::prove::ProveError,
    >,
{
    if payload_eqs.is_empty() {
        return merge_candidate_node_eqs(red, node_eqs);
    }
    let base = red.sys.clone();
    let res = solve_payload_eqs(red, payload_eqs);
    Ok(match complete_solve(red, base, res)? {
        SystemOutcome::Linear => merge_candidate_node_eqs(red, node_eqs)?,
        SystemOutcome::Contradictory => SystemOutcome::Contradictory,
        SystemOutcome::Cases(arms) if node_eqs.is_empty() => SystemOutcome::Cases(arms),
        SystemOutcome::Cases(arms) => continue_merge_nodes(red, arms, node_eqs)?,
    })
}

fn merge_candidate_node_eqs(
    red: &mut Reduction,
    node_eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if node_eqs.is_empty() {
        return Ok(SystemOutcome::Linear);
    }
    let base = red.sys.clone();
    let res = red.solve_node_id_eqs(node_eqs);
    complete_solve(red, base, res)
}

fn continue_merge_nodes(
    red: &mut Reduction,
    arms: Vec<SystemBranch>,
    node_eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
) -> Result<SystemOutcome, crate::prove::ProveError> {
    let mut completed = Vec::new();
    for arm in arms {
        let mut branch = Reduction::new_inheriting(red.ctx, arm.sys, arm.counter);
        match merge_candidate_node_eqs(&mut branch, node_eqs)? {
            SystemOutcome::Linear => completed.push(SystemBranch {
                sys: branch.sys,
                counter: branch.maude.fresh_counter_peek(),
            }),
            SystemOutcome::Cases(arms) => completed.extend(arms),
            SystemOutcome::Contradictory => {}
        }
    }
    Ok(red.finish_system_cases(completed))
}

fn continue_merge_groups<P, F>(
    red: &mut Reduction,
    arms: Vec<SystemBranch>,
    groups: &[MergeGroup<P>],
    solve_payload_eqs: &F,
) -> Result<SystemOutcome, crate::prove::ProveError>
where
    P: Clone,
    F: Fn(
        &mut Reduction,
        &[tamarin_term::rewriting::Equal<P>],
    ) -> std::result::Result<
        crate::constraint::solver::reduction::SolveOutcome,
        crate::prove::ProveError,
    >,
{
    let mut completed = Vec::new();
    for arm in arms {
        let mut branch = Reduction::new_inheriting(red.ctx, arm.sys, arm.counter);
        match merge_candidate_groups(&mut branch, groups, solve_payload_eqs)? {
            SystemOutcome::Linear => completed.push(SystemBranch {
                sys: branch.sys,
                counter: branch.maude.fresh_counter_peek(),
            }),
            SystemOutcome::Cases(arms) => completed.extend(arms),
            SystemOutcome::Contradictory => {}
        }
    }
    Ok(red.finish_system_cases(completed))
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
        let base = red.sys.clone();
        let res = red.solve_node_id_eqs(&eqs);
        match complete_solve(red, base, res)? {
            SystemOutcome::Linear => {}
            outcome => return Ok(outcome),
        }
    }
    Ok(SystemOutcome::Linear)
}

/// CR-rule *N5_u*: KU-action uniqueness. For every term `m` that
/// appears as the argument of two distinct `KU(m)` actions, the
/// producing nodes must be the same. Mirrors the KU (N5_u) component of
/// Haskell's `enforceNodeUniqueness` (Simplify.hs; the
/// diff-mode analog is `enforceFreshAndKuNodeUniqueness`,
/// Simplify.hs) — we
/// collect `(node_id, fact, term)` triples for KU actions, group by
/// term, and within each group merge the trailing entries' facts and
/// node ids onto the first.
///
/// Only emits non-trivial equalities (`solve_node_id_eqs` and
/// `solve_fact_eqs` filter `lhs == rhs` themselves, but we mirror the
/// pattern from `enforce_edge_uniqueness_pass` to avoid spurious
/// `Changed` flags that would re-fire the simplify loop forever).
fn enforce_ku_action_uniqueness_pass(
    red: &mut Reduction,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    use crate::constraint::constraints::NodeId;
    use crate::fact::{FactTag, LNFact};
    use tamarin_term::lterm::LNTerm;

    // Collect (node, fact, term) for every KU action — both the
    // rule-instance actions and the UNSOLVED open goals.  Mirrors
    // Haskell's `allKUActions`: `unsolvedActionAtoms sys ++ <rule actions>`.
    // Do NOT include SOLVED goals here: an auto-solved KU(t) goal still
    // points to a fresh-allocated vk node, so merging it emits
    // `node_eqs` that induce self-loops in less_atoms.  Haskell's filter
    // avoids this.
    // Apply eq_store subst to the action term before grouping (mirrors
    // HS's `allKUActions` which extracts m from the node's action fact
    // AFTER substSystem propagated bindings).  Without this, RS's stored
    // action terms may have bare vars (x.19 from requiresKU on
    // pair-components) that haven't been rewritten by substSystem when
    // the substitution is in eq_store but not yet applied.
    let subst = &red.sys.eq_store().subst;
    let apply_subst = |t: &LNTerm| -> LNTerm { tamarin_term::subst::apply_vterm(subst, t.clone()) };
    // HS-faithful order: `allActions = unsolvedActionAtoms sys <|>
    // <rule actions>` (System.hs).  Goals come FIRST so
    // that `groupSortOn fst` keeps a goal's NodeId as `iKeep` and
    // emits `solveTermEqs [iKeep = rule_node_id]` — meaning the
    // rule node is renamed onto the goal's id, NOT vice versa.
    // Nodes-first would instead collapse the goal id onto a fresh
    // `vk.X` that dedup-merges with a grafted solved goal.  See
    // Simplify.hs (`kuActions se = (\(i,fa,m) -> (m,(fa,i)))
    // <$> allKUActions se`).
    let mut acts: Vec<(LNTerm, LNFact, NodeId)> = Vec::new();
    for (i, fa) in red.sys.unsolved_action_atoms() {
        if matches!(fa.tag, FactTag::Ku)
            && let Some(m) = fa.terms.first()
        {
            acts.push((apply_subst(m), fa.clone(), i));
        }
    }
    // HS-faithful order: HS `allKUActions` draws rule actions from
    // `M.toList (get sNodes se)` (node-id-sorted), and `merge`'s
    // `groupSortOn fst` is stable (Simplify.hs), so within
    // a term-group the kept action (`iKeep`) is the one from the LOWEST
    // node-id.  RS iterated `sys.nodes` in Vec (production) order, so a
    // term-group with no goal kept whichever same-term node was created
    // first, not the lowest id.  Sort the rule-action nodes by node-id so
    // `group[0]` is the lowest, matching HS.  (Unsolved KU-action goals are
    // still pushed FIRST — `allKUActions` lists `unsolvedActionAtoms`
    // before rule actions — so a goal still wins `iKeep` over a rule node.)
    let mut sorted_nodes: Vec<_> = red.sys.nodes.iter().collect();
    sorted_nodes.sort_by_key(|a| a.0);
    for (id, rule) in sorted_nodes {
        for fa in &rule.actions {
            if matches!(fa.tag, FactTag::Ku)
                && let Some(m) = fa.terms.first()
            {
                acts.push((apply_subst(m), fa.clone(), *id));
            }
        }
    }
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
        let outcome = red.solve_action_goal(i, fa)?;
        match outcome {
            GoalCases::Contradictory => return Ok(SystemOutcome::Contradictory),
            GoalCases::LinearNamed(_) => {
                // `red.sys` is already mutated in place by `solve_action_goal`.
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
                let mut completed = Vec::new();
                for branch in cases {
                    if branch.sys.eq_store().is_false() {
                        continue;
                    }

                    // Keep each branch's FreshT continuation paired with its
                    // system. Deliberately do not call `subst_system`:
                    // Haskell applies it only at the start of the next outer
                    // simplify iteration.
                    let mut branch_red =
                        Reduction::new_inheriting(red.ctx, branch.sys, branch.counter);
                    let outcome = execute_captured_actions(&mut branch_red, suffix)?;
                    match outcome {
                        SystemOutcome::Linear => completed.push(SystemBranch {
                            sys: branch_red.sys,
                            counter: branch_red.maude.fresh_counter_peek(),
                        }),
                        SystemOutcome::Cases(arms) => completed.extend(arms),
                        SystemOutcome::Contradictory => {}
                    }
                }
                return Ok(red.finish_system_cases(completed));
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
        for t in fa.terms.iter() {
            if has_funion_head(t) {
                return false;
            }
        }
        red.ctx
            .unique_action_shapes
            .contains(&(fa.tag, fa.terms.len()))
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
    use crate::fact::FactTag;
    use crate::rule::RuleACInst;
    use tamarin_term::lterm::LNTerm;

    // Haskell-faithful (`Simplify.hs`): `enforceNodeUniqueness`
    // kdConcs branch uses `(merge (solveRuleEqs SplitNow) kdConcs)`.
    // The merger emits BOTH `solveRuleEqs` (full rule-instance
    // equality) AND `solveNodeIdEqs` — both are required so the merged
    // KD-conc rules are unified at the rule level.
    //
    // Collect (node, rule, term) for every KD-conc.
    let mut kd_concs: Vec<(LNTerm, RuleACInst, NodeId)> = Vec::new();
    for (id, rule) in red.sys.nodes.iter() {
        for fa in &rule.conclusions {
            if matches!(fa.tag, FactTag::Kd)
                && let Some(m) = fa.terms.first()
            {
                kd_concs.push((m.clone(), rule.clone(), *id));
            }
        }
    }
    // Haskell uses `solveRuleEqs SplitNow` for the kdConcs merger
    // (Simplify.hs `merge (solveRuleEqs SplitNow) kdConcs`).  Multi-arm AC
    // unifications fork the DisjT continuation in HS (Reduction.hs);
    // `merge_candidates` mirrors that via install + pending branches.
    // Joux_EphkRev: dropping a `Cases` result here leaves the `mem::take`'d
    // default eq-store (conj=[], next_split=0) installed — the next
    // substSystem then parks its setNodes rule-eq disjunctions at
    // SplitId(0)/(1)/(2) as spurious splitEqs goals HS never has.
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
fn enforce_fresh_ordering_pass(red: &mut Reduction) {
    use crate::constraint::constraints::{LessAtom, Reason};
    use crate::fact::FactTag;
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Fast path: an empty eq-store subst makes `apply_vterm` the identity,
    // so the per-premise normalisation below is a no-op and the suppliers
    // are collected from the raw terms.
    //
    // Step 1: collect (consumer_node_id, fresh_var) for every node
    // whose premise is `Fr(~x)`. Matches Haskell's `getFreshVars`.
    //
    // The subst is read-only here and `suppliers` is fully collected before
    // any `less_atoms` mutation below, so a scoped shared borrow of the
    // eq-store subst suffices — `eq_store` and `nodes` are disjoint `System`
    // fields, so this reads both at once with no per-pass BTreeMap+Term deep
    // clone of the subst.
    let mut suppliers: Vec<(crate::constraint::constraints::NodeId, LVar)> = Vec::new();
    {
        let subst = &red.sys.eq_store().subst;
        let subst_empty = subst.is_empty();
        for (id, rule) in red.sys.nodes.iter() {
            for prem in &rule.premises {
                if !matches!(prem.tag, FactTag::Fresh) {
                    continue;
                }
                let t = match prem.terms.first() {
                    Some(t) => t,
                    None => continue,
                };
                let t_norm = if subst_empty {
                    t.clone()
                } else {
                    tamarin_term::subst::apply_vterm(subst, t.clone())
                };
                if let Term::Lit(Lit::Var(v)) = t_norm
                    && v.sort == tamarin_term::lterm::LSort::Fresh
                {
                    suppliers.push((*id, v));
                }
            }
        }
    }
    if suppliers.is_empty() {
        return;
    }

    // `newLesses`. The node snapshot is an `Arc` handle, so `insert_less`
    // below cannot disturb it.
    let nodes_snapshot = red.sys.nodes.clone();
    let mut node_rules = crate::constraint::system::NodeRuleMap::default();
    for (id, rule) in nodes_snapshot.iter() {
        node_rules.entry(id).or_insert(rule);
    }
    let maude = red.ctx.maude.clone();
    let non_unifiable = |i: &crate::constraint::constraints::NodeId,
                         j: &crate::constraint::constraints::NodeId| {
        non_unifiable_nodes(&maude, &node_rules, i, j).unwrap_or(false)
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
                for term in fact.terms.iter() {
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
                    .flat_map(|fact| fact.terms.iter())
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
            if !non_unifiable(sup_id, other_id) {
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
        if !tail.iter().all(|t_id| non_unifiable(j, t_id)) {
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
    let base = red.sys.clone();
    let res = red.solve_node_id_eqs(&node_eqs);
    red.changed = ChangeIndicator::Changed;
    complete_solve(red, base, res)
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
    // HS `behaviourTerms` via `trimmedPairTerms`, in `M.toList` node order,
    // keeping the tag so only same-tag premises are paired.
    let mut by_inj: Vec<(
        crate::constraint::constraints::NodeId,
        crate::fact::FactTag,
        tamarin_term::lterm::LNTerm,
        Vec<(MonotonicBehaviour, tamarin_term::lterm::LNTerm)>,
    )> = Vec::new();
    for (id, rule) in red.sys.nodes_in_map_order() {
        for prem in &rule.premises {
            if let Some(behaviours) = red.ctx.injective_fact_insts.get(&prem.tag)
                && let Some((first, pairs)) =
                    crate::tools::injective_fact_instances::trimmed_pair_terms(prem, behaviours)
            {
                by_inj.push((*id, prem.tag, first, pairs));
            }
        }
    }
    if by_inj.len() < 2 {
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
    // HS `paired`: ordered pairs of same-tag premises with the same first
    // term on different nodes.
    let ab_adj = red.sys.build_always_before_adj();
    for a in 0..by_inj.len() {
        for b in 0..by_inj.len() {
            if a == b {
                continue;
            }
            let (i, tag_i, first_i, pairs_i) = &by_inj[a];
            let (j, tag_j, first_j, pairs_j) = &by_inj[b];
            if i == j || tag_i != tag_j || first_i != first_j {
                continue;
            }
            // `((b, s), (_, t)) <- zip ss tt`
            for (k, (bh, s)) in pairs_i.iter().enumerate() {
                let t = match pairs_j.get(k) {
                    Some((_, t)) => t,
                    None => continue,
                };
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
                        new_formulas.push(crate::guarded::Guarded::Atom(
                            crate::atom::ProtoAtom::EqE(
                                crate::formula::lift_free(s),
                                crate::formula::lift_free(t),
                            ),
                        ));
                    }
                    // Each case has its own guard, so several can fire
                    // together; e.g. (2) and (5) with a stale `s ≠ t` give
                    // the cycle counter.spthy::counters_linear_order needs.
                    MonotonicBehaviour::StrictlyIncreasing => {
                        let ab_ij = red.sys.always_before_with(&ab_adj, ii, jj);
                        let ab_ji = red.sys.always_before_with(&ab_adj, jj, ii);
                        // (2)
                        if s == t && ii != jj {
                            new_formulas.push(crate::guarded::Guarded::Atom(
                                crate::atom::ProtoAtom::EqE(
                                    crate::formula::lift_free(&node_id_to_lnterm(ii)),
                                    crate::formula::lift_free(&node_id_to_lnterm(jj)),
                                ),
                            ));
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
    match red.insert_formulas(&new_formulas)? {
        SystemOutcome::Linear => insert_lesses(red),
        SystemOutcome::Contradictory => return Ok(SystemOutcome::Contradictory),
        SystemOutcome::Cases(arms) => {
            return Ok(SystemOutcome::Cases(
                arms.into_iter()
                    .map(|arm| {
                        let mut branch = Reduction::new_inheriting(red.ctx, arm.sys, arm.counter);
                        insert_lesses(&mut branch);
                        SystemBranch {
                            sys: branch.sys,
                            counter: branch.maude.fresh_counter_peek(),
                        }
                    })
                    .collect(),
            ));
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
    red.insert_formulas(&to_decompose)
}

/// Drop `gtrue` (`Conj []`) entries from the formula list — those are
/// vacuously satisfied. Mirrors a tiny piece of `reduceFormulas`.
///
/// IMPORTANT: gtrue must also be recorded in `solved_formulas`, because
/// `is_initial_system` discriminates a fresh system from one that has
/// closed a trivial formula via the (non-emptiness of) `solved_formulas`.
/// Without this marker, a system whose only formula was `gtrue` becomes
/// indistinguishable from the initial system after this pass — so
/// `is_finished` keeps returning `None` (initial) and the search reaches
/// "no method" Sorry, even though the proof is trivially Solved.
/// This matches Haskell's `insertFormula` which calls `markAsSolved`
/// on every formula it inserts, including `gtrue`.
fn drop_trivially_true_formulas_pass(red: &mut Reduction) {
    let before = red.sys.formulas.len();
    let gt = crate::guarded::gtrue();
    let had_gtrue = crate::guarded::stores_contains(&red.sys.formulas, &gt);
    red.sys.invalidate_max_var_idx_cache();
    red.sys.formulas_mut().retain(|f| **f != gt);
    if had_gtrue && !crate::guarded::stores_contains(&red.sys.solved_formulas, &gt) {
        red.sys.insert_solved_formula(gt);
    }
    if red.sys.formulas.len() != before {
        red.changed = ChangeIndicator::Changed;
    }
}

/// Deduplicate the formula list, keeping the first `Arc` of each group of
/// equal formulas. Haskell uses `Set` storage so this is implicit; we use
/// `Vec` so a manual pass is needed.
fn dedupe_formulas_pass(red: &mut Reduction) {
    use crate::constraint::solver::reduction::first_occurrences;
    // Read via `iter()` (Deref, no mut borrow) so the common no-op path (no
    // duplicates) takes ZERO mutable borrow and ZERO stamp bump — this pass
    // runs every simplify fixpoint iteration, including the final no-op one
    // that follows the `subst_system` marker-set, and an unconditional bump
    // here would staleify that marker and collapse the skip (design Finding 2).
    let first = first_occurrences(&red.sys.formulas[..]);
    if first.contains(&false) {
        // A real drop: `formulas_mut()` bumps `content_stamp` on handout.
        let mut keep = first.iter();
        red.sys
            .formulas_mut()
            .retain(|_| *keep.next().unwrap_or(&false));
        red.changed = ChangeIndicator::Changed;
    }
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
        let avoid_max = red.fresh_var_baseline();
        red.maude.ensure_above(avoid_max);
        let maude = red.maude.clone();
        move |sort: tamarin_term::lterm::LSort| -> tamarin_term::lterm::LVar {
            tamarin_term::lterm::LVar::new("newVar", sort, maude.fresh_idx())
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
    red.insert_formulas(&new_formulas)
}

#[cfg(test)]
#[path = "simplify_tests.rs"]
mod tests;
