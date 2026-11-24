// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Stored-proof replay: HS `checkAndExtendProver` and `replaceSorryProver`
//! (Theory/Proof.hs).
//!
//! `--prove` re-executes a lemma's saved proof, keeping the user's case
//! structure, and auto-proves its annotated `sorry` leaves. The saved tree is
//! checked first, including every stored terminal claim; annotated sorries are
//! then replaced lazily and solutions extracted from the combined tree, so an
//! infinite unfinished sibling cannot hide a later saved trace (upstream #955).
//! Search frontiers use whole-tree depth; bounds and heuristic depth stay local
//! to each replacement. `CutAfterSorry` instead extends each sorry where it is
//! checked. Stored-only branches keep no system and are never auto-proved.

use std::collections::BTreeMap;

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::proof_method::{
    exec_proof_method, finished_step_is_valid, ProofMethod, Result as MethodResult,
};
use crate::constraint::solver::search::{
    node_status_of, rollup_statuses, run_proof_search_at_depth, NodeStatus, ProofNode,
};
use crate::constraint::system::System;
use crate::prove::ProveError;
use crate::theory::ProofTree;

/// Check a lemma's saved skeleton, extend its unfinished leaves, and apply
/// whole-proof solution extraction (HS `proveLemma`, TheoryLoader.hs).
/// `proof_bound` (`--bound=N`) applies per replacement, as HS applies
/// `boundProofDepth` inside `runAutoProver`; each replacement also gets its
/// own time budget.
pub fn replace_sorry_prove(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ProofTree,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    if ctx.cut == crate::constraint::solver::context::CutStrategy::AfterSorry {
        replay_node(ctx, initial, skeleton, proof_bound, true)
    } else {
        let checked = replay_node(ctx, initial, skeleton, proof_bound, false)?;
        crate::constraint::solver::search::extend_saved_proof(ctx, checked, proof_bound)
    }
}

/// Replay a stored skeleton without auto-proving its sorry leaves: HS's
/// close-time `checkAndExtendProver (sorryProver Nothing)` (CloseRule.hs).
/// Steps that `checkProof` cannot replay keep their stored subtree
/// unannotated (`/* unannotated */`). Used for lemmas `--prove` does not
/// select, whose replayed proof HS keeps (`proveLemma`'s `otherwise = lem`).
pub fn check_and_extend(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ProofTree,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    replay_node(ctx, initial, skeleton, proof_bound, false)
}

/// An annotated `Sorry` leaf: HS `checkProof` annotates the node itself, so
/// it renders as plain `by sorry`.
fn annotated_sorry(reason: Option<String>, sys: System) -> ProofNode {
    ProofNode {
        method: ProofMethod::Sorry(reason),
        sys,
        children: BTreeMap::new(),
        status: NodeStatus::Sorry,
        annotated: true,
    }
}

/// HS `sorryNode reason cs`: keep the `Sorry` node annotated while mapping
/// every stored child through `noSystemPrf`.
fn annotated_sorry_with_children(
    reason: Option<String>,
    sys: System,
    children: &[(String, ProofTree)],
) -> ProofNode {
    ProofNode {
        method: ProofMethod::Sorry(reason),
        children: children
            .iter()
            .map(|(name, child)| (name.clone(), parsed_to_unannotated(child, sys.clone())))
            .collect(),
        sys,
        status: NodeStatus::Sorry,
        annotated: true,
    }
}

/// HS `checkProof` on a step it cannot replay:
/// `sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)`
/// over the stored subtree mapped through `noSystemPrf`.
fn invalid_step_node(node: &ProofTree, sys: System) -> ProofNode {
    let child = parsed_to_unannotated(node, sys.clone());
    let mut children = BTreeMap::new();
    children.insert("".to_string(), child);
    ProofNode {
        method: ProofMethod::Sorry(Some("invalid proof step encountered".into())),
        sys,
        children,
        status: NodeStatus::Sorry,
        annotated: true,
    }
}

/// HS `noSystemPrf` (Theory/Proof.hs): the stored subtree with no system
/// annotation anywhere, keeping each stored method. `sys` is only a
/// placeholder required by `ProofNode`.
fn parsed_to_unannotated(node: &ProofTree, sys: System) -> ProofNode {
    let method = node.method.clone();
    let status = match &method {
        ProofMethod::Finished(r) => node_status_of(r),
        ProofMethod::Sorry(_) if node.cases.is_empty() => NodeStatus::Sorry,
        _ => NodeStatus::Open,
    };
    let children: BTreeMap<String, ProofNode> = node
        .cases
        .iter()
        .map(|(name, sub)| (name.clone(), parsed_to_unannotated(sub, sys.clone())))
        .collect();
    ProofNode {
        method,
        sys,
        children,
        status,
        annotated: false,
    }
}

/// The annotated `sorry` HS keeps for a lemma with no stored proof
/// (`unproven`, ProofSkeleton.hs).
pub fn annotated_sorry_root(sys: System) -> ProofNode {
    annotated_sorry(None, sys)
}

/// Replay a terminal leaf (`by contradiction`, `SOLVED`, `UNFINISHABLE`).
/// A stored result whose kind the system still reaches is kept verbatim, so
/// a stored `by contradiction` matches any runtime reason and prints without
/// one. Otherwise the step is invalid: unannotated without the auto-prover,
/// else re-proved, as `replaceSorryProver` re-proves `checkProof`'s sorry.
fn finished_leaf(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    stored: &MethodResult,
    auto_prove: bool,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    match finished_step_is_valid(ctx, &sys, stored)? {
        true => Ok(ProofNode {
            method: ProofMethod::Finished(stored.clone()),
            sys,
            children: BTreeMap::new(),
            status: node_status_of(stored),
            annotated: true,
        }),
        _ if !auto_prove => Ok(invalid_step_node(node, sys)),
        _ => run_proof_search_at_depth(ctx, sys, proof_bound, 0),
    }
}

/// Replay one node of the skeleton against `sys`. Without `auto_prove`,
/// steps the auto-prover would extend stay sorries (HS check-and-extend).
fn replay_node(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    proof_bound: usize,
    auto_prove: bool,
) -> Result<ProofNode, ProveError> {
    tamarin_utils::cancellation::check()?;
    let result = replay_node_inner(ctx, sys, node, proof_bound, auto_prove);
    // Terminal classification includes boolean Maude queries. A
    // cancellation error there must never become a changed proof verdict.
    tamarin_utils::cancellation::check()?;
    result
}

fn replay_node_inner(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    proof_bound: usize,
    auto_prove: bool,
) -> Result<ProofNode, ProveError> {
    // HS `replace prf@(LNode (ProofStep (Sorry _) (Just se)) _)`: auto-prove a
    // sorry, or keep it with its stored children (`sorryNode reason cs`).
    if let ProofMethod::Sorry(reason) = &node.method {
        if !auto_prove {
            return Ok(annotated_sorry_with_children(
                reason.clone(),
                sys,
                &node.cases,
            ));
        }
        return run_proof_search_at_depth(ctx, sys, proof_bound, 0);
    }

    crate::constraint::solver::trace::trace_state(&sys);

    if let ProofMethod::Finished(stored) = &node.method
        && node.cases.is_empty()
    {
        return finished_leaf(ctx, sys, node, stored, auto_prove, proof_bound);
    }

    // Re-execute the stored method (`checkAndExecProofMethod`), then merge
    // its cases with the stored children (`mergeMapsWith`, Theory/Proof.hs).
    let (method, cases) = match exec_method_for(&node.method, &sys, ctx)? {
        Some(p) => p,
        None => {
            if !auto_prove {
                return Ok(invalid_step_node(node, sys));
            }
            return run_proof_search_at_depth(ctx, sys, proof_bound, 0);
        }
    };

    // Both maps empty: a contradictory closure. When only the runtime map is
    // empty, every stored child is kept unannotated below.
    if cases.is_empty() && node.cases.is_empty() {
        return Ok(ProofNode {
            method,
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Contradictory,
            annotated: true,
        });
    }

    let produced: BTreeMap<String, System> = cases.into_iter().collect();

    let mut children: BTreeMap<String, ProofNode> = BTreeMap::new();
    // A stored-only child counts as incomplete whatever its stored method.
    let mut statuses = Vec::new();

    for (skel_name, sub_tree) in &node.cases {
        // An unnamed stored child (from Simplify or a one-case solve) adopts
        // the single runtime case; a named one matches by name.
        let runtime_name = if skel_name.is_empty() {
            if produced.len() == 1 {
                Some(produced.keys().next().unwrap().clone())
            } else {
                None
            }
        } else if produced.contains_key(skel_name) {
            Some(skel_name.clone())
        } else {
            None
        };
        let Some(runtime_name) = runtime_name else {
            // A stored-only case (`noSystemPrf` in `mergeMapsWith`) is kept
            // verbatim and unannotated, with or without the auto-prover.
            let placeholder = parsed_to_unannotated(sub_tree, sys.clone());
            children.insert(skel_name.clone(), placeholder);
            statuses.push(NodeStatus::Sorry);
            continue;
        };
        let child_sys = produced.get(&runtime_name).cloned().unwrap();
        let _path = crate::constraint::solver::trace::CasePathGuard::push(&runtime_name);
        let child_node = replay_node(ctx, child_sys, sub_tree, proof_bound, auto_prove)?;
        statuses.push(child_node.status);
        children.insert(runtime_name, child_node);
    }

    // A runtime-only case goes through `unhandledCase = mapProofInfo
    // (Nothing,) . prover d`: an annotated sorry, which `--prove` extends.
    for (rt_name, rt_sys) in produced.into_iter() {
        // Includes a runtime case an unnamed stored child adopted.
        if children.contains_key(&rt_name) {
            continue;
        }
        let _path = crate::constraint::solver::trace::CasePathGuard::push(&rt_name);
        let auto = if auto_prove {
            run_proof_search_at_depth(ctx, rt_sys, proof_bound, 0)?
        } else {
            annotated_sorry(None, rt_sys)
        };
        statuses.push(auto.status);
        children.insert(rt_name, auto);
    }

    Ok(ProofNode {
        method,
        sys,
        children,
        status: rollup_statuses(statuses),
        annotated: true,
    })
}

/// HS `checkAndExecProofMethod` (Theory/Proof.hs): [`resolve_method`]
/// validates the stored step, then it runs against `sys`.
fn exec_method_for(
    stored: &ProofMethod,
    sys: &System,
    ctx: &ProofContext,
) -> Result<Option<(ProofMethod, Vec<(String, System)>)>, ProveError> {
    let Some(method) = resolve_method(stored, sys) else {
        return Ok(None);
    };
    Ok(exec_proof_method(ctx, &method, sys)?.map(|cases| (method, cases)))
}

/// Bind a stored method to `sys`: a `SolveGoal` takes the equal live goal.
/// Terminal methods are leaves in [`replay_node`]; one with stored cases is
/// malformed, and `Invalidated` never executes.
fn resolve_method(stored: &ProofMethod, sys: &System) -> Option<ProofMethod> {
    match stored {
        ProofMethod::Sorry(reason) => Some(ProofMethod::Sorry(reason.clone())),
        ProofMethod::Simplify => Some(ProofMethod::Simplify),
        ProofMethod::Induction => Some(ProofMethod::Induction),
        ProofMethod::SolveGoal(g) => Some(ProofMethod::SolveGoal(match_goal(g, sys)?)),
        ProofMethod::Finished(_) | ProofMethod::Invalidated => None,
    }
}

/// The goal of `sys` equal to the stored one (HS `goal \`M.member\` sGoals`,
/// ProofMethod.hs). Fact equality ignores annotations, so the live goal is
/// returned for execution.
fn match_goal(stored: &Goal, sys: &System) -> Option<Goal> {
    sys.goals
        .iter()
        .map(|(goal, _)| goal)
        .find(|live| *live == stored)
        .cloned()
}

#[cfg(test)]
#[path = "replay_tests.rs"]
mod tests;
