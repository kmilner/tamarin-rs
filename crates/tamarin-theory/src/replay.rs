// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Skeleton-replay prover — port of HS `replaceSorryProver`
//! (lib/theory/src/Theory/Proof.hs).
//!
//! HS's `--prove` flag wires `replaceSorryProver $ runAutoProver`
//! (TheoryLoader.hs:705-707, see line 706) so the auto-prover runs **only at `by sorry`
//! leaves of the user-written skeleton**, not from scratch.  This
//! preserves the case-decomposition structure the user wrote in the
//! `.spthy` file even when the auto-prover would have picked a
//! different (still-sound) decomposition.
//!
//! ## HS reference (Theory/Proof.hs)
//!
//! ```haskell
//! -- | Replace all annotated sorry steps using the given prover.
//! replaceSorryProver :: Prover -> Prover
//! replaceSorryProver prover0 = Prover prover
//!   where
//!     prover ctxt d _ = return . replace
//!       where
//!         replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
//!             fromMaybe prf $ runProver prover0 ctxt d se prf
//!         replace (LNode ps cases) =
//!             LNode ps $ M.map replace cases
//! ```
//!
//! HS recurses through the static skeleton tree; at each Sorry leaf
//! that carries a `Just se` annotation (System state), the auto-prover
//! `prover0` is invoked.  `replaceSorryProver` itself does NOT re-exec
//! non-sorry nodes — `replace (LNode ps cases) = LNode ps $ M.map
//! replace cases` keeps each node's stored `ProofStep` and only
//! recurses into the already-built case-map.  The `ProofMethod`s were
//! executed earlier, when the annotated tree was first constructed
//! (`oneStepProver` / `checkProof`'s `execProofMethod ctxt method se`).
//!
//! ## Replay strategy in this port
//!
//! The full HS `--prove` flow runs in two passes that this one-pass
//! walker folds together:
//!   1. close-time `checkAndExtendProver (sorryProver Nothing)`
//!      (`proveTheory (const True) checkProofM`, CloseRule.hs:57-71) over
//!      ALL lemmas — it re-execs each stored step, keeping the verbatim
//!      structure and turning any step that no longer applies into an
//!      annotated `sorry /* invalid proof step encountered */`;
//!   2. prove-time `replaceSorryProver $ runAutoProver` (TheoryLoader.hs:705-707, see line 706)
//!      over the lemmas the `--prove` selector targets — it re-runs the
//!      auto-prover at every annotated `sorry` leaf.
//!
//! We do both in one pass: at every non-Sorry node we exec the proof
//! method, get the case list, and recurse into each; at Sorry leaves and
//! at unmatched-case children we fall through to [`run_proof_search`]
//! (target lemmas) or emit an annotated/unannotated `sorry` (non-target
//! lemmas, via `auto_prove == false`).
//!
//! This matches HS's end result for any skeleton whose
//! `exec_proof_method`-produced case names match the skeleton's
//! child names — which is the normal case, since HS produced those
//! names in the first place.  When names diverge (e.g. a case the
//! user's skeleton has but our prover's `exec_proof_method` doesn't
//! produce, or vice versa), we mirror `checkProof`'s `mergeMapsWith`
//! handling: stored-only cases are kept verbatim and runtime-only cases
//! are auto-proved (target) or annotated-sorry'd (non-target).

use std::collections::BTreeMap;

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::goals::RankingError;
use crate::constraint::solver::proof_method::{
    check_and_exec_proof_method, is_finished, ProofMethod, Result as MethodResult,
};
use crate::constraint::solver::search::{
    node_status_of, run_proof_search_at_depth, NodeStatus, ProofNode,
};
use crate::constraint::system::System;
use crate::theory::ProofTree;

/// Drive a single lemma's skeleton.  Equivalent of HS
/// `runProver (replaceSorryProver (runAutoProver autoProver)) ctxt 0
///  initial sysOnTree` (Proof.hs).
///
/// `proof_bound` (`--bound=N`; `usize::MAX` = unbounded) is plumbed
/// through to `run_proof_search` for the fall-through auto-prover
/// invocations.  HS applies `boundProofDepth` inside `runAutoProver`
/// (Theory/Proof.hs:730-750#runAutoProver), i.e. per sorry-replacement — so each
/// fall-through search here counts depth from its own subtree root,
/// exactly as HS does.
pub fn replace_sorry_prove(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ProofTree,
    proof_bound: usize,
) -> Result<ProofNode, RankingError> {
    replay_node(ctx, initial, skeleton, proof_bound, true)
}

/// Replay a stored skeleton WITHOUT auto-proving its open/sorry leaves —
/// the equivalent of HS's close-time `checkAndExtendProver (sorryProver
/// Nothing)` (CloseRule.hs:57-71, see line 71, Proof.hs).  Each step's method and
/// children are taken verbatim from the skeleton; every fall-through that
/// `checkProof` would turn into a `Sorry` with a `Nothing` system
/// (Proof.hs) becomes an *unannotated* `ProofNode`
/// (`annotated == false`), so the lemma renders byte-identically to HS's
/// reprint of a non-target lemma (incl. `/* unannotated */` markers) and
/// its summary status reflects the stored proof — NOT a fresh search.
///
/// Used for lemmas the `--prove` selector does NOT target (HS keeps their
/// close-time-replayed proof untouched — `proveLemma`'s `| otherwise = lem`,
/// CloseRule.hs:157-159).
pub fn check_and_extend(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ProofTree,
    proof_bound: usize,
) -> Result<ProofNode, RankingError> {
    replay_node(ctx, initial, skeleton, proof_bound, false)
}

/// Build an annotated `Sorry` leaf seeded with `sys`.  HS `checkProof`
/// keeps the *node itself* annotated (`node ... = ProofStep m (Just
/// info, Just sys)`, Proof.hs) — only its forced children are
/// `Nothing`.  A stored `by sorry` leaf therefore renders as plain
/// `by sorry` (no `/* unannotated */`).
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

/// Build the HS check-and-extend "invalid proof step" node.  When
/// `checkProof` finds an invalid step it emits
/// `sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)`
/// where `prf` is the original subtree passed through `noSystemPrf`
/// (→ unannotated).  Mirrors that: a `Sorry` whose single `""` child is
/// `parsed_to_unannotated(node, sys)`.
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

/// HS `noSystemPrf` (Proof.hs): `mapProofInfo (\i -> (Just i, Nothing))`.
///
/// When `checkProof` finds an invalid proof step it creates
/// `sorryNode reason (M.singleton "" prf)` where `prf` is the original
/// proof subtree.  `M.map noSystemPrf` is applied to `prf` — it maps
/// info to `(Just i, Nothing)` **recursively** so every node in the
/// subtree has a `Nothing` system annotation (→ `/* unannotated */`).
///
/// We mirror this by converting the [`ProofTree`] to `ProofNode` with
/// `annotated: false` throughout, keeping each node's stored `ProofMethod`
/// — HS re-renders it with `prettyProofMethod` (ProofMethod.hs:1173-1187).
/// The `sys` placeholder is the parent's sys (unused in display but
/// required by `ProofNode`).
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

/// Public root-level **annotated** `sorry` leaf (HS keeps the parsed
/// `unproven ()` proof when a lemma has no stored skeleton —
/// ProofSkeleton.hs:59-61, see line 61; checkProof annotates the node with the start
/// system, so it renders as plain `by sorry` with no `/* unannotated */`
/// — see `annotated_sorry`).
pub fn annotated_sorry_root(sys: System) -> ProofNode {
    annotated_sorry(None, sys)
}

/// Replay a terminal leaf (`by contradiction`, `SOLVED`, `UNFINISHABLE`).
/// When runtime `is_finished` reaches a result of the same kind as the
/// skeleton's `stored` one, that stored result is emitted verbatim;
/// otherwise the step falls through — `invalid_step_node` when replaying
/// without the auto-prover, else `run_proof_search` (HS `checkProof` marks
/// the stale step an annotated sorry which `replaceSorryProver` then
/// reproves).
///
/// The two results are compared by kind, not by value: the skeleton's `by
/// contradiction` is `Contradictory(None)`
/// (Theory/Text/Parser/Proof.hs:81) and matches a runtime
/// `Contradictory(Just reason)`, and emitting the stored value keeps the
/// reprinted method free of a reason.
fn finished_leaf(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    stored: &MethodResult,
    auto_prove: bool,
    proof_bound: usize,
) -> Result<ProofNode, RankingError> {
    let same_kind = |r: &MethodResult| std::mem::discriminant(r) == std::mem::discriminant(stored);
    match is_finished(ctx, &sys) {
        Some(ref r) if same_kind(r) => Ok(ProofNode {
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

/// Replay one node of the skeleton against `sys`.  When `auto_prove` is
/// false, fall-throughs that would otherwise invoke the auto-prover emit
/// unannotated `Sorry` leaves instead (HS check-and-extend semantics).
fn replay_node(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    proof_bound: usize,
    auto_prove: bool,
) -> Result<ProofNode, RankingError> {
    // ---- Sorry cases first (HS `replace prf@(... Sorry ...)`). ----
    // Any `Sorry` node → invoke the auto-prover on `sys`. HS:
    //   replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
    //       fromMaybe prf $ runProver prover0 ctxt d se prf
    if let ProofMethod::Sorry(reason) = &node.method {
        // HS check-and-extend keeps the stored `Sorry` node annotated and
        // preserves any children without system annotations (`sorryNode
        // reason cs`).
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

    // A terminal leaf: `by contradiction`, `SOLVED`
    // (Theory/Text/Parser/Proof.hs:102-103) or `UNFINISHABLE`.  The stored
    // result is re-checked against `sys` and kept when it still holds; on
    // disagreement the step falls through, which is HS-faithful rather than a
    // divergence.  At close time `checkProof` re-execs the stored `Finished`
    // step (`checkAndExecProofMethod`, Theory/Proof.hs:447-467, see line 456);
    // when the method does not apply it returns `Nothing`, so checkProof
    // emits `sorryNode (Just "invalid proof step encountered")
    // (M.singleton "" prf)` (Theory/Proof.hs:459-460) over the `noSystemPrf`'d
    // subtree, and for a `--prove`-selected lemma `replaceSorryProver` then
    // re-runs the auto-prover on that annotated sorry (CloseRule.hs:57-71, see
    // line 71 → TheoryLoader.hs:705-707, see line 706).  A skeleton's `SOLVED`
    // is HS's claim; RS verifies it with its own solver.
    if let ProofMethod::Finished(stored) = &node.method
        && node.cases.is_empty()
    {
        return finished_leaf(ctx, sys, node, stored, auto_prove, proof_bound);
    }

    // ---- Non-leaf nodes: pick a method, exec it, recurse. ----
    // HS `oneStepProver`:
    //   cases <- execProofMethod ctxt method se
    //   return $ LNode (ProofStep method (Just se))
    //                  (M.map (unprovenLookAhead ctxt) cases)
    // then `replaceSorryProver` recurses on the children — but in
    // HS's setup the skeleton's children take precedence (they're
    // already there from the parse), and `unprovenLookAhead` produces
    // a Sorry that gets replaced by the auto-prover.
    let (method, cases) = match exec_method_for(&node.method, &sys, ctx) {
        Some(p) => p,
        None => {
            // Couldn't resolve OR the method didn't apply.  HS
            // check-and-extend marks the step `Nothing` (Proof.hs):
            //   sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)
            // where `prf` is the current node (method + children) passed
            // through `noSystemPrf` → `annotated = false`.  RS mirrors
            // this by creating a sorry with one child "" → the original
            // stored subtree converted to unannotated ProofNodes.
            if !auto_prove {
                return Ok(invalid_step_node(node, sys));
            }
            return run_proof_search_at_depth(ctx, sys, proof_bound, 0);
        }
    };

    // Match the skeleton's child case-names against the cases
    // exec_proof_method produced.  If BOTH the runtime case-map and the
    // skeleton's child-map are empty (a genuine stored `by solve(...)`
    // leaf whose re-execution also closes), this is a leaf-equivalent.
    // If the runtime map is empty but the skeleton HAS children, do NOT
    // short-circuit: HS `checkProof`'s `mergeMapsWith` runs with an
    // empty LEFT map and every stored child lands in the rightOnly
    // branch (`noSystemPrf`) — the whole stored subtree is kept
    // VERBATIM and renders `/* unannotated */`.  Short-circuiting here
    // dropped a 263-line stored subtree on
    // csf18-alethea/alethea_votingphase_malS_Proof_functional.spthy
    // (HS plain-load: 93 steps; RS: 22) — the merge loop below handles
    // the empty `produced` map correctly (every skeleton child becomes
    // a stored-only placeholder).
    if cases.is_empty() && node.cases.is_empty() {
        // Empty case-map after exec means contradictory closure —
        // mirror search.rs's contradictory-closure handling.
        return Ok(ProofNode {
            method,
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Contradictory,
            annotated: true,
        });
    }

    // Build a map from case name → System for fast lookup.
    let produced: BTreeMap<String, System> = cases.into_iter().collect();

    let mut children: BTreeMap<String, ProofNode> = BTreeMap::new();
    let mut any_solved = false;
    let mut any_contra = false;
    let mut any_unfin = false;
    let mut any_sorry = false;

    // Walk the skeleton's child cases in source order.
    for (skel_name, sub_tree) in &node.cases {
        // Find the matching runtime case.  Two common shapes:
        //   - Skel case is "" (no name; from Simplify or single-case
        //     SolveGoal) → matches the single produced case.
        //   - Skel case has a name → matches by exact name.
        let runtime_name = if skel_name.is_empty() {
            // Skeleton has an unnamed single-child block (Simplify
            // produces a "" case).
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
            // No matching runtime case — the stored skeleton drifted
            // from the current decomposition (a case present in the
            // skeleton but NOT produced by re-executing the method).
            // HS `checkAndExtendProver` (Proof.hs) handles this the
            // SAME WAY regardless of whether sorry-leaves get extended:
            // `mergeMapsWith` maps the stored-only case through
            // `noSystemPrf` (= `mapProofInfo (\i -> (Just i, Nothing))`)
            // over the WHOLE subtree; after `mapProofInfo snd` the info
            // is `Nothing` everywhere, so the entire subtree is kept
            // VERBATIM and renders unannotated (`/* unannotated */`).
            // The auto-prover never runs on it (no system attached), so
            // this is independent of `auto_prove` — both the target
            // lemma (extend sorries) and check-only replay keep drifted
            // cases verbatim.  (KCL07 is a stale-stored-proof theory
            // that exercises this drifted-case path.)
            let placeholder = parsed_to_unannotated(sub_tree, sys.clone());
            children.insert(skel_name.clone(), placeholder);
            any_sorry = true;
            continue;
        };
        let child_sys = produced.get(&runtime_name).cloned().unwrap();
        // Track the actual case name used in the replayed tree, including an
        // unnamed stored child which adopted a named singleton runtime case.
        let _path = crate::constraint::solver::trace::CasePathGuard::push(&runtime_name);
        let child_node = replay_node(ctx, child_sys, sub_tree, proof_bound, auto_prove)?;
        match child_node.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => any_unfin = true,
            NodeStatus::Sorry => any_sorry = true,
            NodeStatus::Open => {}
        }
        children.insert(runtime_name, child_node);
    }

    // For runtime cases NOT covered by the skeleton (e.g. skeleton was
    // stale and a new case appeared), invoke the auto-prover on each.
    // This is HS-faithful: `checkProof`'s `mergeMapsWith` treats the
    // runtime-produced cases as the LEFT map and the stored skeleton's
    // children as the RIGHT map (Theory/Proof.hs:447-467, see line 463
    // `mergeMapsWith
    // unhandledCase noSystemPrf (go (d+1)) cases cs`), so a runtime-only
    // case (present left, absent right) goes through `unhandledCase =
    // mapProofInfo (Nothing,) . prover d` (Theory/Proof.hs:447-467, see line
    // 462) → an annotated
    // `sorry Nothing (Just se)`.  For a `--prove`-selected lemma
    // `replaceSorryProver` then auto-proves that annotated sorry
    // (CloseRule.hs:57-71, see line 71 → TheoryLoader.hs:705-707, see line 706), matching the
    // `run_proof_search` branch below.
    for (rt_name, rt_sys) in produced.into_iter() {
        // A case the skeleton already consumed — including one an unnamed
        // `""` skeleton block claimed, since the loop above re-keys such a
        // child under the RUNTIME name.
        if children.contains_key(&rt_name) {
            continue;
        }
        let _path = crate::constraint::solver::trace::CasePathGuard::push(&rt_name);
        let auto = if auto_prove {
            run_proof_search_at_depth(ctx, rt_sys, proof_bound, 0)?
        } else {
            // HS check-and-extend, `mergeMapsWith` leftOnly branch
            // (Proof.hs): a case PRODUCED by re-executing the method
            // but absent from the stored skeleton is handled by
            // `unhandledCase = mapProofInfo (Nothing,) . prover d`
            // (Proof.hs).  `prover` there is
            // `sorryProver Nothing` (Proof.hs, runProver), which
            // yields `sorry Nothing (Just se)` — info `(Nothing, Just se)`.
            // After `mapProofInfo snd` (Proof.hs) the info is
            // `Just se`, so the leaf is ANNOTATED → plain `by sorry`
            // (NO `/* unannotated */`).  This differs from the rightOnly
            // branch above, which is `Nothing`.
            annotated_sorry(None, rt_sys)
        };
        match auto.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => any_unfin = true,
            NodeStatus::Sorry => any_sorry = true,
            NodeStatus::Open => {}
        }
        children.insert(rt_name, auto);
    }

    let status = if any_solved {
        NodeStatus::Solved
    } else if any_sorry {
        NodeStatus::Sorry
    } else if any_unfin {
        NodeStatus::Unfinishable
    } else if any_contra {
        NodeStatus::Contradictory
    } else {
        NodeStatus::Sorry
    };

    Ok(ProofNode {
        method,
        sys,
        children,
        status,
        annotated: true,
    })
}

/// Re-execute one stored proof step against `sys` and produce the
/// (method, cases) pair it yields.
///
/// HS `checkAndExecProofMethod` (Theory/Proof.hs:447-467, see line 456) runs
/// the stored `ProofMethod` itself; [`resolve_method`] is the `SolveGoal`
/// half of that, binding the stored goal to the equal one among `sys`'s
/// goals before `check_and_exec_proof_method` validates and runs it.
fn exec_method_for(
    stored: &ProofMethod,
    sys: &System,
    ctx: &ProofContext,
) -> Option<(ProofMethod, Vec<(String, System)>)> {
    let method = resolve_method(stored, sys)?;
    check_and_exec_proof_method(ctx, &method, sys).map(|cases| (method, cases))
}

/// Resolve one stored [`ProofMethod`] against `sys`.
///
/// A `SolveGoal` binds the LIVE goal [`match_goal`] finds equal to the
/// stored one, so the executed method carries the value `sys.goals` holds;
/// the terminal methods are handled as leaves in [`replay_node`] and resolve
/// to nothing here.
fn resolve_method(stored: &ProofMethod, sys: &System) -> Option<ProofMethod> {
    match stored {
        ProofMethod::Sorry(reason) => Some(ProofMethod::Sorry(reason.clone())),
        ProofMethod::Simplify => Some(ProofMethod::Simplify),
        ProofMethod::Induction => Some(ProofMethod::Induction),
        ProofMethod::SolveGoal(g) => Some(ProofMethod::SolveGoal(match_goal(g, sys)?)),
        // `Finished` is `by contradiction` / `SOLVED` / `UNFINISHABLE`, each
        // handled as a leaf above; reaching here means the skeleton follows
        // one with `case` blocks, which is malformed.  `Invalidated` executes
        // nowhere (proof_method.rs `exec_proof_method`).
        ProofMethod::Finished(_) | ProofMethod::Invalidated => None,
    }
}

/// Find the goal of `sys` that the stored `solve( ... )` step names.
///
/// HS looks the parsed `Goal` up with
/// `guard (goal \`M.member\` L.get sGoals sys)` (ProofMethod.hs:253-258), i.e.
/// by structural equality.  The LIVE goal is returned, so the executed
/// method carries the value `sys.goals` holds (`Fact` equality ignores the
/// annotations, so the two can differ there).
///
/// `None` means the stored step names a goal this system does not have, and
/// the caller emits `sorry /* invalid proof step encountered */` over the
/// verbatim stored subtree — HS `checkProof`'s `Nothing` branch
/// (Theory/Proof.hs:456-467).
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
