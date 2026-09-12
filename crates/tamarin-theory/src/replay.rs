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
use crate::constraint::solver::proof_method::{
    check_and_exec_proof_method, is_finished, ProofMethod, Result as MethodResult,
};
use crate::constraint::solver::search::{
    node_status_of, run_proof_search_at_depth, NodeStatus, ProofNode,
};
use crate::constraint::system::System;
use crate::prove::ProveError;
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
) -> Result<ProofNode, ProveError> {
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
) -> Result<ProofNode, ProveError> {
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
    fn shallow(node: &ProofTree, sys: System) -> ProofNode {
        let status = match &node.method {
            ProofMethod::Finished(r) => node_status_of(r),
            ProofMethod::Sorry(_) if node.cases.is_empty() => NodeStatus::Sorry,
            _ => NodeStatus::Open,
        };
        ProofNode {
            method: node.method.clone(),
            sys,
            children: BTreeMap::new(),
            status,
            annotated: false,
        }
    }
    let mut result = shallow(node, sys);
    let mut pending = Vec::new();
    let mut next = Some((node, &mut result));
    while let Some((source, target)) = next.take().or_else(|| pending.pop()) {
        // Build in source order, retaining BTreeMap's last-entry-wins behavior
        // for duplicate stored names. Populate only the surviving occurrence.
        let sources: BTreeMap<_, _> = source
            .cases
            .iter()
            .map(|(name, child)| (name, child))
            .collect();
        target.children = sources
            .iter()
            .map(|(name, child)| ((*name).clone(), shallow(child, target.sys.clone())))
            .collect();
        for (source, target) in sources.values().zip(target.children.values_mut()).rev() {
            if let Some(previous) = next.replace((*source, target)) {
                pending.push(previous);
            }
        }
    }
    result
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
) -> Result<ProofNode, ProveError> {
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

/// Aggregate every executed visit, including children later overwritten by a
/// duplicate stored name. Rolling up only the surviving map is not equivalent.
fn insert_replayed_child(result: &mut ProofNode, name: String, child: ProofNode) {
    let rank = |status| match status {
        NodeStatus::Open => 0,
        NodeStatus::Contradictory => 1,
        NodeStatus::Unfinishable => 2,
        NodeStatus::Sorry => 3,
        NodeStatus::Solved => 4,
    };
    if rank(child.status) > rank(result.status) {
        result.status = child.status;
    }
    result.children.insert(name, child);
}

fn replay_node(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    proof_bound: usize,
    auto_prove: bool,
) -> Result<ProofNode, ProveError> {
    use crate::constraint::solver::trace::CasePathGuard;
    // Stored-proof depth is independent of term depth. Lexical guards unwind
    // trace scopes; returned proof nodes retain iterative destruction.
    tamarin_utils::stack::ensure_sufficient_stack(|| {
        let (mut result, produced) = replay_step(ctx, sys, node, proof_bound, auto_prove)?;
        let Some(produced) = produced else {
            return Ok(result);
        };
        // Preserve source order and retain the produced map: duplicate stored
        // names can replay the same runtime case more than once.
        for (stored_name, subtree) in &node.cases {
            let runtime_name = if stored_name.is_empty() {
                (produced.len() == 1).then(|| produced.keys().next().unwrap().clone())
            } else {
                produced
                    .contains_key(stored_name)
                    .then(|| stored_name.clone())
            };
            let Some(name) = runtime_name else {
                // Stored-only cases contribute Sorry regardless of the retained
                // subtree's status, unless an earlier visit already solved.
                let child = parsed_to_unannotated(subtree, result.sys.clone());
                if result.status != NodeStatus::Solved {
                    result.status = NodeStatus::Sorry;
                }
                result.children.insert(stored_name.clone(), child);
                continue;
            };
            let child_sys = produced.get(&name).unwrap().clone();
            let child = {
                let _path = CasePathGuard::push(&name);
                replay_node(ctx, child_sys, subtree, proof_bound, auto_prove)?
            };
            insert_replayed_child(&mut result, name, child);
        }
        // Runtime-only cases follow in map order: annotated sorries in check
        // mode, or auto-proved children (HS mergeMapsWith leftOnly).
        for (name, child_sys) in produced {
            if result.children.contains_key(&name) {
                continue;
            }
            let _path = CasePathGuard::push(&name);
            let child = if auto_prove {
                run_proof_search_at_depth(ctx, child_sys, proof_bound, 0)?
            } else {
                annotated_sorry(None, child_sys)
            };
            insert_replayed_child(&mut result, name, child);
        }
        if result.status == NodeStatus::Open {
            result.status = NodeStatus::Sorry;
        }
        Ok(result)
    })
}

/// Execute one stored step, returning a completed proof or runtime cases
/// awaiting child replay. Check-only fallbacks preserve HS annotations.
fn replay_step(
    ctx: &ProofContext,
    sys: System,
    node: &ProofTree,
    proof_bound: usize,
    auto_prove: bool,
) -> Result<(ProofNode, Option<BTreeMap<String, System>>), ProveError> {
    // ---- Sorry cases first (HS `replace prf@(... Sorry ...)`). ----
    // Any `Sorry` node → invoke the auto-prover on `sys`. HS:
    //   replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
    //       fromMaybe prf $ runProver prover0 ctxt d se prf
    if let ProofMethod::Sorry(reason) = &node.method {
        // HS check-and-extend keeps the stored `Sorry` node annotated and
        // preserves any children without system annotations (`sorryNode
        // reason cs`).
        if !auto_prove {
            return Ok((
                annotated_sorry_with_children(reason.clone(), sys, &node.cases),
                None,
            ));
        }
        return run_proof_search_at_depth(ctx, sys, proof_bound, 0).map(|node| (node, None));
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
        return finished_leaf(ctx, sys, node, stored, auto_prove, proof_bound)
            .map(|node| (node, None));
    }

    // ---- Non-leaf nodes: pick and execute a method. ----
    // HS `oneStepProver`:
    //   cases <- execProofMethod ctxt method se
    //   return $ LNode (ProofStep method (Just se))
    //                  (M.map (unprovenLookAhead ctxt) cases)
    // then `replaceSorryProver` recurses on the children — but in
    // HS's setup the skeleton's children take precedence (they're
    // already there from the parse), and `unprovenLookAhead` produces
    // a Sorry that gets replaced by the auto-prover.
    let (method, cases) = match exec_method_for(&node.method, &sys, ctx)? {
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
                return Ok((invalid_step_node(node, sys), None));
            }
            return run_proof_search_at_depth(ctx, sys, proof_bound, 0).map(|node| (node, None));
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
        return Ok((
            ProofNode {
                method,
                sys,
                children: BTreeMap::new(),
                status: NodeStatus::Contradictory,
                annotated: true,
            },
            None,
        ));
    }

    Ok((
        ProofNode {
            method,
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Open,
            annotated: true,
        },
        Some(cases.into_iter().collect()),
    ))
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
) -> Result<Option<(ProofMethod, Vec<(String, System)>)>, ProveError> {
    let Some(method) = resolve_method(stored, sys) else {
        return Ok(None);
    };
    Ok(check_and_exec_proof_method(ctx, &method, sys)?.map(|cases| (method, cases)))
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
