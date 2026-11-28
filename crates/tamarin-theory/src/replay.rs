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
    exec_proof_method, finished_step_is_valid, ProofMethod,
};
use crate::constraint::solver::search::{
    node_status_of, rollup_statuses, run_proof_search_at_depth, NodeStatus, ProofAnnotation,
    ProofNode,
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

/// HS `sorryNode reason cs` (Theory/Proof.hs): an annotated `Sorry` node,
/// with every stored child mapped through `noSystemPrf`.  Without children it
/// renders as plain `by sorry`.
pub(crate) fn sorry_node<'a>(
    reason: Option<String>,
    sys: System,
    children: impl IntoIterator<Item = (String, &'a ProofTree)>,
) -> ProofNode {
    ProofNode {
        method: ProofMethod::Sorry(reason),
        children: children
            .into_iter()
            .map(|(name, child)| (name, parsed_to_unannotated(child)))
            .collect(),
        annotation: ProofAnnotation::checked(sys),
        status: NodeStatus::Sorry,
    }
}

/// HS `checkProof` on a step it cannot replay:
/// `sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)`.
fn invalid_step_node(node: &ProofTree, sys: System) -> ProofNode {
    sorry_node(
        Some("invalid proof step encountered".into()),
        sys,
        [(String::new(), node)],
    )
}

/// HS `noSystemPrf` (Theory/Proof.hs): the stored subtree with no system
/// annotation anywhere, keeping each stored method.
fn parsed_to_unannotated(node: &ProofTree) -> ProofNode {
    let method = node.method.clone();
    let status = match &method {
        ProofMethod::Finished(r) => node_status_of(r),
        ProofMethod::Sorry(_) if node.cases.is_empty() => NodeStatus::Sorry,
        _ => NodeStatus::Open,
    };
    let children: BTreeMap<String, ProofNode> = node
        .cases
        .iter()
        .map(|(name, sub)| (name.clone(), parsed_to_unannotated(sub)))
        .collect();
    ProofNode {
        method,
        annotation: ProofAnnotation::Unchecked,
        children,
        status,
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
            return Ok(sorry_node(
                reason.clone(),
                sys,
                node.cases.iter().map(|(name, child)| (name.clone(), child)),
            ));
        }
        return run_proof_search_at_depth(ctx, sys, proof_bound, 0);
    }

    crate::constraint::solver::trace::trace_state(&sys);

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

    let mut produced: BTreeMap<String, System> = cases.into_iter().collect();
    let mut children = BTreeMap::new();
    for (name, stored) in &node.cases {
        let child = match produced.remove(name) {
            Some(child_sys) => {
                let _path = crate::constraint::solver::trace::CasePathGuard::push(name);
                replay_node(ctx, child_sys, stored, proof_bound, auto_prove)?
            }
            None => parsed_to_unannotated(stored),
        };
        children.insert(name.clone(), child);
    }

    // A runtime-only case starts as an annotated sorry, which `--prove` extends.
    for (rt_name, rt_sys) in produced {
        let _path = crate::constraint::solver::trace::CasePathGuard::push(&rt_name);
        let auto = if auto_prove {
            run_proof_search_at_depth(ctx, rt_sys, proof_bound, 0)?
        } else {
            sorry_node(None, rt_sys, [])
        };
        children.insert(rt_name, auto);
    }

    let status = match &method {
        ProofMethod::Finished(result) => node_status_of(result),
        _ if children.is_empty() => NodeStatus::Contradictory,
        _ => rollup_statuses(children.values().map(|child| {
            if child.annotation.is_checked() {
                child.status
            } else {
                NodeStatus::Sorry
            }
        })),
    };
    Ok(ProofNode {
        method,
        annotation: ProofAnnotation::checked(sys),
        children,
        status,
    })
}

/// Validate and execute a stored method (HS `checkAndExecProofMethod`).
fn exec_method_for(
    stored: &ProofMethod,
    sys: &System,
    ctx: &ProofContext,
) -> Result<Option<(ProofMethod, Vec<(String, System)>)>, ProveError> {
    let method = match stored {
        ProofMethod::Finished(result) => {
            return Ok(
                finished_step_is_valid(ctx, sys, result)?.then(|| (stored.clone(), Vec::new()))
            );
        }
        ProofMethod::SolveGoal(goal) => {
            let Some(live) = match_goal(goal, sys) else {
                return Ok(None);
            };
            ProofMethod::SolveGoal(live)
        }
        _ => stored.clone(),
    };
    Ok(exec_proof_method(ctx, &method, sys)?.map(|cases| (method, cases)))
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
