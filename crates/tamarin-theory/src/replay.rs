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

use tamarin_parser::ast::{DisjAlt, GoalSpec, ParsedMethod, ParsedProofTree};

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::proof_method::{
    exec_proof_method, is_finished, ProofMethod, Result as MethodResult,
};
use crate::constraint::solver::search::{run_proof_search, NodeStatus, ProofNode};
use crate::constraint::system::System;
use crate::fact::fact_tag_name;

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
    skeleton: &ParsedProofTree,
    proof_bound: usize,
) -> ProofNode {
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
    skeleton: &ParsedProofTree,
    proof_bound: usize,
) -> ProofNode {
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

/// Build the HS check-and-extend "invalid proof step" node.  When
/// `checkProof` finds an invalid step it emits
/// `sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)`
/// where `prf` is the original subtree passed through `noSystemPrf`
/// (→ unannotated).  Mirrors that: a `Sorry` whose single `""` child is
/// `parsed_to_unannotated(node, sys)`.
fn invalid_step_node(
    node: &ParsedProofTree,
    sys: System,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> ProofNode {
    let child = parsed_to_unannotated(node, sys.clone(), msig);
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
/// We mirror this by converting the `ParsedProofTree` to `ProofNode`
/// with `annotated: false` throughout.  The `sys` placeholder is the
/// parent's sys (unused in display but required by `ProofNode`).
///
/// Converts:
/// - `Simplify`    → `ProofMethod::Simplify`
/// - `Induction`   → `ProofMethod::Induction`
/// - `Sorry`       → `ProofMethod::Sorry(None)`
/// - `Contradiction` → `ProofMethod::Finished(Contradictory(None))`
/// - `SolveGoal(spec, raw)` → `ProofMethod::SolveGoal(goal)`, or
///   `ProofMethod::RawSolve(raw)` when `spec` carries no convertible goal
/// - `SolvedLeaf`  → `ProofMethod::Finished(Solved)`
/// - `Unfinishable` → `ProofMethod::Finished(Unfinishable)`
/// - `Invalidated` → `ProofMethod::Invalidated`
/// - `Other(s)`    → `ProofMethod::Sorry(Some(s))`
fn parsed_to_unannotated(
    node: &ParsedProofTree,
    sys: System,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> ProofNode {
    let method = parsed_method_to_display(&node.method, msig);
    let status = match &method {
        ProofMethod::Finished(MethodResult::Contradictory(_)) => NodeStatus::Contradictory,
        ProofMethod::Finished(MethodResult::Solved) => NodeStatus::Solved,
        ProofMethod::Finished(MethodResult::Unfinishable) => NodeStatus::Unfinishable,
        ProofMethod::Sorry(_) if node.cases.is_empty() => NodeStatus::Sorry,
        _ => NodeStatus::Open,
    };
    let children: BTreeMap<String, ProofNode> = node
        .cases
        .iter()
        .map(|(name, sub)| (name.clone(), parsed_to_unannotated(sub, sys.clone(), msig)))
        .collect();
    ProofNode {
        method,
        sys,
        children,
        status,
        annotated: false,
    }
}

/// Convert a `ParsedMethod` to the best display-only `ProofMethod`.
/// Used exclusively by `parsed_to_unannotated` — not for exec.
///
/// A goal the elaborator converts becomes a `SolveGoal`, which
/// `prettyProofMethod` (ProofMethod.hs:1174-1187) re-renders through
/// `prettyGoal` exactly as HS's `noSystemPrf` does; the disjunction and
/// unrecognised forms keep their stored text.
fn parsed_method_to_display(
    pm: &ParsedMethod,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> ProofMethod {
    match pm {
        ParsedMethod::Simplify => ProofMethod::Simplify,
        ParsedMethod::Induction => ProofMethod::Induction,
        ParsedMethod::Sorry => ProofMethod::Sorry(None),
        ParsedMethod::Contradiction => ProofMethod::Finished(MethodResult::Contradictory(None)),
        ParsedMethod::SolveGoal(spec, raw) => {
            match crate::elaborate::goal_from_parsed(spec, msig) {
                Ok(g) => ProofMethod::SolveGoal(g),
                Err(_) => ProofMethod::RawSolve(raw.clone()),
            }
        }
        ParsedMethod::SolvedLeaf => ProofMethod::Finished(MethodResult::Solved),
        ParsedMethod::Unfinishable => ProofMethod::Finished(MethodResult::Unfinishable),
        ParsedMethod::Invalidated => ProofMethod::Invalidated,
        ParsedMethod::Other(s) => ProofMethod::Sorry(Some(s.clone())),
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

/// Shared body of the finished-leaf replay arms (`by contradiction`,
/// `SOLVED`, `UNFINISHABLE`).  Each arm has the same shape: if runtime
/// `is_finished` agrees with the skeleton's claimed terminal method
/// (`matches_expected`), emit a `Finished(method)` node carrying `status`;
/// otherwise fall through — `invalid_step_node` when replaying without the
/// auto-prover, else `run_proof_search` (HS `checkProof` marks the stale
/// step an annotated sorry which `replaceSorryProver` then reproves).
///
/// `method` is emitted verbatim and may differ from what `matches_expected`
/// accepts: `by contradiction` matches any `Contradictory(_)` but emits
/// `Contradictory(None)` so the reprinted method carries no reason.
fn finished_leaf(
    ctx: &ProofContext,
    sys: System,
    node: &ParsedProofTree,
    matches_expected: impl Fn(&MethodResult) -> bool,
    method: MethodResult,
    status: NodeStatus,
    auto_prove: bool,
    proof_bound: usize,
) -> ProofNode {
    match is_finished(ctx, &sys) {
        Some(ref r) if matches_expected(r) => ProofNode {
            method: ProofMethod::Finished(method),
            sys,
            children: BTreeMap::new(),
            status,
            annotated: true,
        },
        _ => {
            if !auto_prove {
                invalid_step_node(node, sys, &ctx.maude.maude_sig())
            } else {
                run_proof_search(ctx, sys, proof_bound)
            }
        }
    }
}

/// Replay one node of the skeleton against `sys`.  When `auto_prove` is
/// false, fall-throughs that would otherwise invoke the auto-prover emit
/// unannotated `Sorry` leaves instead (HS check-and-extend semantics).
fn replay_node(
    ctx: &ProofContext,
    sys: System,
    node: &ParsedProofTree,
    proof_bound: usize,
    auto_prove: bool,
) -> ProofNode {
    // ---- Leaf cases first (HS `replace prf@(... Sorry ...)`). ----
    // `by sorry` leaf → invoke the auto-prover on `sys`.  HS:
    //   replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
    //       fromMaybe prf $ runProver prover0 ctxt d se prf
    if matches!(node.method, ParsedMethod::Sorry) && node.cases.is_empty() {
        // HS check-and-extend keeps a stored `Sorry` leaf annotated
        // (Proof.hs: `sorryNode reason cs` → node carries
        // `Just sys`), so it renders as plain `by sorry`.
        if !auto_prove {
            return annotated_sorry(None, sys);
        }
        return run_proof_search(ctx, sys, proof_bound);
    }

    // `by contradiction` leaf → emit a Finished(Contradictory) node if
    // a contradiction can actually be derived; else fall through to the
    // auto-prover.  This is HS-faithful, not a divergence: at close time
    // `checkProof` re-execs the stored `Finished (Contradictory Nothing)`
    // step (`checkAndExecProofMethod`, Theory/Proof.hs:447-467, see line 456);
    // if the system is no
    // longer contradictory the method returns `Nothing`, so checkProof
    // emits `sorryNode (Just "invalid proof step encountered") ...`
    // (Theory/Proof.hs:459-460) carrying `Just sys`.  For a `--prove`-selected
    // lemma `replaceSorryProver` then re-runs the auto-prover on that
    // annotated sorry (CloseRule.hs:57-71, see line 71 → TheoryLoader.hs:705-707, see line 706), exactly the
    // `run_proof_search` fall-through below.
    if matches!(node.method, ParsedMethod::Contradiction) && node.cases.is_empty() {
        // HS replay (checkProof, Theory/Proof.hs) preserves the skeleton's
        // STORED method verbatim — the parser builds `Finished (Contradictory
        // Nothing)` for `by contradiction`
        // (Theory/Text/Parser/Proof.hs:81), so the reprinted
        // method carries no reason (`prettyProofMethod` → plain `by
        // contradiction`).  Emit `Contradictory(None)`, NOT a freshly-
        // recomputed reason (which would print a spurious `/* from
        // formulas */`).  On disagreement HS `checkProof` (Theory/Proof.hs)
        // emits
        //   `sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)`
        // where `prf` is the current leaf, `noSystemPrf`'d → unannotated.
        return finished_leaf(
            ctx,
            sys,
            node,
            |r| matches!(r, MethodResult::Contradictory(_)),
            MethodResult::Contradictory(None),
            NodeStatus::Contradictory,
            auto_prove,
            proof_bound,
        );
    }

    // `SOLVED` leaf (HS Theory/Text/Parser/Proof.hs:102-103).  If runtime
    // is_finished
    // agrees, emit Finished(Solved); else fall through to the auto-prover
    // (whose run_proof_search may simplify/contract further until it
    // reaches Solved naturally).  The fall-through is exactly HS's
    // pipeline: close-time `checkProof` marks the stale `Finished Solved`
    // an annotated `sorry /* invalid proof step encountered */`
    // (Theory/Proof.hs:459-460), and for a `--prove`-selected lemma
    // `replaceSorryProver` then reproves it (CloseRule.hs:57-71, see line 71 →
    // TheoryLoader.hs:705-707, see line 706).  Skeleton's SOLVED is HS's claim; RS verifies
    // via its own solver.
    if matches!(node.method, ParsedMethod::SolvedLeaf) && node.cases.is_empty() {
        return finished_leaf(
            ctx,
            sys,
            node,
            |r| matches!(r, MethodResult::Solved),
            MethodResult::Solved,
            NodeStatus::Solved,
            auto_prove,
            proof_bound,
        );
    }

    // `UNFINISHABLE` leaf — emit Finished(Unfinishable) if runtime
    // agrees, else fall back to auto-prover.
    if matches!(node.method, ParsedMethod::Unfinishable) && node.cases.is_empty() {
        return finished_leaf(
            ctx,
            sys,
            node,
            |r| matches!(r, MethodResult::Unfinishable),
            MethodResult::Unfinishable,
            NodeStatus::Unfinishable,
            auto_prove,
            proof_bound,
        );
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
    let (method, cases) = match exec_method_for(&node.method, &sys, ctx, &node.cases) {
        Some(p) => p,
        None => {
            // Couldn't resolve OR the method didn't apply.  HS
            // check-and-extend marks the step `Nothing` (Proof.hs):
            //   sorryNode (Just "invalid proof step encountered") (M.singleton "" prf)
            // where `prf` is the current node (method + children) passed
            // through `noSystemPrf` → `annotated = false`.  RS mirrors
            // this by creating a sorry with one child "" → the original
            // ParsedProofTree converted to unannotated ProofNodes.
            if !auto_prove {
                return invalid_step_node(node, sys, &ctx.maude.maude_sig());
            }
            return run_proof_search(ctx, sys, proof_bound);
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
        return ProofNode {
            method,
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Contradictory,
            annotated: true,
        };
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
        // Push for case_path tracking — mirrors search.rs's push at
        // expand_inner's case loop.  Without this, contradictions fired
        // during skeleton-replay show path=/ regardless of how deep we
        // are.  Diagnostic-only; doesn't affect proof.
        let push_path = !skel_name.is_empty();
        if push_path {
            crate::constraint::solver::trace::case_path_push(skel_name);
        }
        // `case_path_pop()` is called manually on every exit path of
        // this loop body (the early-continue at the no-match branch and
        // the normal tail below) to balance the push above.
        // Find the matching runtime case.  Two common shapes:
        //   - Skel case is "" (no name; from Simplify or single-case
        //     SolveGoal) → matches the single produced case.
        //   - Skel case has a name → matches by exact name.
        let runtime_name_opt: Option<String> = if skel_name.is_empty() {
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
        let child_sys = match &runtime_name_opt {
            Some(n) => produced.get(n).cloned().unwrap(),
            None => {
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
                let placeholder =
                    parsed_to_unannotated(sub_tree, sys.clone(), &ctx.maude.maude_sig());
                children.insert(skel_name.clone(), placeholder);
                any_sorry = true;
                if push_path {
                    crate::constraint::solver::trace::case_path_pop();
                }
                continue;
            }
        };
        let child_node = replay_node(ctx, child_sys, sub_tree, proof_bound, auto_prove);
        match child_node.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => any_unfin = true,
            NodeStatus::Sorry => any_sorry = true,
            NodeStatus::Open => {}
        }
        // Use the actual runtime name (matches what HS' produced map
        // shows when rendering).
        let key = runtime_name_opt.unwrap_or_else(|| skel_name.clone());
        children.insert(key, child_node);
        if push_path {
            crate::constraint::solver::trace::case_path_pop();
        }
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
        let push_path = !rt_name.is_empty();
        if push_path {
            crate::constraint::solver::trace::case_path_push(&rt_name);
        }
        let auto = if auto_prove {
            run_proof_search(ctx, rt_sys, proof_bound)
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
        if push_path {
            crate::constraint::solver::trace::case_path_pop();
        }
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

    ProofNode {
        method,
        sys,
        children,
        status,
        annotated: true,
    }
}

/// Resolve a parsed method against `sys` and produce a (method, cases)
/// pair if possible.  For `SolveGoal(GoalSpec::Raw(_))` (a `solve(...)`
/// whose goal text neither the goal grammar nor the disjunction splitter
/// recognises), we iterate over the candidate ProofMethods in
/// heuristic-ranked order (same list `expand` in search.rs uses) and pick
/// the first one whose resulting case-set is compatible with the skeleton's
/// child case names.  This is the closest we can come to HS's behavior
/// without a Goal value: HS parses the goal directly, but if our
/// auto-prover would have picked the same goal in that state, the
/// case-decomposition matches.
fn exec_method_for(
    parsed: &ParsedMethod,
    sys: &System,
    ctx: &ProofContext,
    skel_children: &[(String, ParsedProofTree)],
) -> Option<(ProofMethod, Vec<(String, System)>)> {
    let dbg = tamarin_utils::env_gate!("TAM_DBG_REPLAY");
    // Fast path: parsed method resolves directly.
    if let Some(method) = resolve_method(parsed, sys, &ctx.maude.maude_sig()) {
        if let Some(cases) = exec_proof_method(ctx, &method, sys) {
            if dbg {
                let names: Vec<&str> = cases.iter().map(|(n, _)| n.as_str()).collect();
                eprintln!(
                    "[replay] direct {:?} → {} cases: {:?}",
                    method_kind(&method),
                    cases.len(),
                    names
                );
            }
            return Some((method, sort_cases(cases)));
        }
        if dbg {
            eprintln!(
                "[replay] direct {:?} → exec returned None",
                method_kind(&method)
            );
        }
        return None;
    }
    // Slow path: SolveGoal(GoalSpec::Raw(_)) — iterate candidates and
    // pick the first SolveGoal whose case-set has at least one name in
    // common with the skeleton's child names.  This is HS-faithful in
    // spirit: HS parses the goal inside `solve(...)` directly to a Goal
    // value via `goal` (Theory/Text/Parser/Proof.hs:38-72) and would always
    // find it in `sys.goals`; a `Raw` goal text has no such value, so we
    // approximate by trusting the heuristic ranking — for the patterns we
    // hit in the target lemmas, the top-ranked goal IS the one HS parsed.
    if !matches!(parsed, ParsedMethod::SolveGoal(GoalSpec::Raw(_), _)) {
        return None;
    }
    let skel_names: Vec<&str> = skel_children.iter().map(|(s, _)| s.as_str()).collect();
    if dbg {
        let raw = match parsed {
            ParsedMethod::SolveGoal(GoalSpec::Raw(r), _) => r.chars().take(120).collect::<String>(),
            _ => String::new(),
        };
        eprintln!(
            "[replay] raw-solve skel_names={:?} (raw text: {:?})",
            skel_names, raw
        );
    }
    // depth=0 for replay: replayed steps don't need round-robin since the
    // skeleton already specifies the goal.
    let candidates = crate::constraint::solver::search::candidate_methods(sys, ctx, 0);
    let mut tried = 0usize;
    // Cap candidate iteration to avoid pathological case-enumeration
    // explosion (each `exec_proof_method` for a SolveGoal can be
    // expensive — Maude calls, system clones, simplify loops).  32
    // candidates is generous; HS's first-match-wins ranking typically
    // hits at the top.
    const MAX_CANDIDATES: usize = 32;
    for m in candidates {
        if !matches!(m, ProofMethod::SolveGoal(_)) {
            continue;
        }
        tried += 1;
        if tried > MAX_CANDIDATES {
            break;
        }
        if let Some(cases) = exec_proof_method(ctx, &m, sys) {
            if dbg && tried <= 8 {
                let names: Vec<&str> = cases.iter().map(|(n, _)| n.as_str()).collect();
                eprintln!(
                    "[replay]   candidate#{} {:?} → {} cases {:?}",
                    tried,
                    method_kind(&m),
                    cases.len(),
                    names
                );
            }
            if cases_compatible(&cases, &skel_names) {
                if dbg {
                    eprintln!("[replay]   MATCH at candidate#{}", tried);
                }
                return Some((m, sort_cases(cases)));
            }
        }
    }
    if dbg {
        eprintln!("[replay] raw-solve: no candidate matched");
    }
    None
}

fn method_kind(m: &ProofMethod) -> String {
    match m {
        ProofMethod::Simplify => "Simplify".into(),
        ProofMethod::Induction => "Induction".into(),
        ProofMethod::Sorry(_) => "Sorry".into(),
        ProofMethod::Finished(_) => "Finished".into(),
        ProofMethod::Invalidated => "Invalidated".into(),
        ProofMethod::SolveGoal(g) => format!("SolveGoal({})", goal_kind(g)),
        ProofMethod::RawSolve(_) => "RawSolve".into(),
    }
}

fn goal_kind(g: &Goal) -> String {
    match g {
        Goal::Action(_, f) => format!("Action({})", fact_tag_name(&f.tag)),
        Goal::Premise(np, f) => format!("Premise(prem={},{})", (np.1).0, fact_tag_name(&f.tag)),
        Goal::Chain(_, _) => "Chain".into(),
        Goal::Split(_) => "Split".into(),
        Goal::Disj(_) => "Disj".into(),
        Goal::Subterm(_) => "Subterm".into(),
    }
}

/// Match the produced case-name set against the skeleton's child case
/// names.
///
/// HS's `checkProof` (Proof.hs) uses `mergeMapsWith
/// unhandledCase noSystemPrf (go (d+1))` — it tolerates BOTH (a) cases
/// the skeleton has but runtime doesn't produce (preserved as
/// `noSystemPrf` — Sorry-style placeholders), and (b) cases the
/// runtime produces but the skeleton doesn't have (handled by
/// `unhandledCase = prover d` — auto-prover).
///
/// But that only applies AFTER the right candidate goal is picked.
/// When choosing among ranked goal candidates for a `GoalSpec::Raw`
/// goal whose formula we couldn't structurally parse, we need a
/// STRICT match (every skel name in produced) to ensure we pick the
/// correct goal — not just a same-name-prefix candidate.  Otherwise
/// we'd accept an unrelated goal that happens to share a case name
/// (e.g. `case_1`), leading to deeper-tree drift.
fn cases_compatible(produced: &[(String, System)], skel: &[&str]) -> bool {
    if skel.is_empty() {
        return false;
    }
    if skel.len() == 1 && skel[0].is_empty() {
        return produced.len() == 1;
    }
    let prod_names: std::collections::BTreeSet<&str> =
        produced.iter().map(|(n, _)| n.as_str()).collect();
    skel.iter().all(|s| prod_names.contains(s))
}

fn sort_cases(mut cases: Vec<(String, System)>) -> Vec<(String, System)> {
    // Mirror search.rs's alphabetical case sort: cases are visited in
    // alphabetical order so name-based skeleton matching is deterministic.
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    cases
}

/// Resolve a parsed method to a runtime [`ProofMethod`] against `sys`.
///
/// For `SolveGoal`, this involves matching the parsed [`GoalSpec`]
/// against an actual [`Goal`] in `sys.goals`.  See `match_goal`.
fn resolve_method(
    parsed: &ParsedMethod,
    sys: &System,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> Option<ProofMethod> {
    match parsed {
        ParsedMethod::Sorry => Some(ProofMethod::Sorry(None)),
        ParsedMethod::Simplify => Some(ProofMethod::Simplify),
        ParsedMethod::Induction => Some(ProofMethod::Induction),
        ParsedMethod::Contradiction => {
            // Handled inline as a leaf above.  If we reach here it's
            // because the skeleton has a `by contradiction` step
            // followed by `case` blocks — malformed.  Fall back.
            None
        }
        ParsedMethod::SolveGoal(spec, _raw) => {
            let g = match_goal(spec, sys, msig)?;
            Some(ProofMethod::SolveGoal(g))
        }
        ParsedMethod::SolvedLeaf
        | ParsedMethod::Unfinishable
        | ParsedMethod::Invalidated
        | ParsedMethod::Other(_) => None,
    }
}

/// The OPEN goals of `sys`, in `sGoals` creation order — the search space
/// every [`match_goal`] arm ranges over, mirroring HS's `M.member`/`M.toList`
/// over `sGoals`.
fn open_goals(sys: &System) -> impl Iterator<Item = &Goal> {
    sys.goals
        .iter()
        .filter(|(_, st)| !st.solved)
        .map(|(g, _)| g)
}

/// Find a [`Goal`] in `sys.goals` that matches the parsed [`GoalSpec`].
///
/// HS parses the `solve( ... )` text straight into a `Goal` value
/// (`goal`, Theory/Text/Parser/Proof.hs:38-72) and looks it up with
/// `guard (goal `M.member` L.get sGoals sys)` (ProofMethod.hs:253-258), i.e.
/// by structural equality.  The five forms `elaborate::goal_from_parsed`
/// converts are matched that way here.  A disjunction reaches this function
/// as the shape-and-text signature the goal text yields, so its arm below
/// stands in for that equality.
///
/// [`open_goals`] skips goals already marked solved, which is the one place
/// this lookup ranges over less than HS's `sGoals`.
///
/// `None` means the stored step names a goal this system does not have.  For
/// every kind handled here `exec_method_for` then gives up (its raw-solve
/// fallback is reserved for [`GoalSpec::Raw`]), and the caller emits
/// `sorry /* invalid proof step encountered */` over the verbatim stored
/// subtree — HS `checkProof`'s `Nothing` branch (Theory/Proof.hs:456-467).
fn match_goal(
    spec: &GoalSpec,
    sys: &System,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> Option<Goal> {
    match spec {
        GoalSpec::Action(..)
        | GoalSpec::Chain(..)
        | GoalSpec::Premise(..)
        | GoalSpec::Split(_)
        | GoalSpec::Subterm(..) => {
            let stored = crate::elaborate::goal_from_parsed(spec, msig).ok()?;
            open_goals(sys).find(|g| **g == stored).cloned()
        }
        GoalSpec::Disj { alts, alt_texts } => {
            // HS-faithful: HS parses the `solve(...)` text into a
            // `DisjG (Disj [GuardedFormula])` value via
            // `disjSplitGoal` (Theory/Text/Parser/Proof.hs:38-72, see line 61),
            // then
            // dispatches `SolveGoal goal` against `sys.goals` (HS
            // ProofMethod.hs:258: `guard (goal \`M.member\` sGoals)`).
            //
            // Our skeleton parser only captures each alt's structural
            // SIGNATURE (top-level shape — see `DisjAlt`), so the first
            // filter keeps every open `Goal::Disj(d)` whose `d.0` list has
            // the same length AND the same per-alt signature as the
            // skeleton's `alts`.  See HS Theory/Text/Parser/Proof.hs:61.
            //
            // That signature is not always unique: the
            // insertImpliedFormulas pass at a single IH can produce
            // multiple alpha-distinct disjunctions (one per matching
            // action-tuple), all with the same 5-NonQuant shape.  HS
            // distinguishes them via the parsed Guarded's concrete
            // LVar identities; RS uses the textual alt_texts captured
            // by the skeleton parser as a tie-breaker.  See
            // Yubikey::slightly_weaker_invariant at
            // /non_empty_trace/case_1: both binding-(t1,t2) and
            // binding-(t2,t1) IH-body disjs have shape NonQuant×5,
            // but their alt[0] texts differ (`last(#t2)` vs
            // `last(#t1)`).  Without alt-text disambiguation, RS
            // picks the wrong disj — RS's insertion order is reversed
            // vs HS, so matches[0] picks binding (t2,t1) where HS
            // picks (t1,t2), which propagates `last_atom = #t1`
            // instead of `last_atom = #t2`, triggering a false-positive
            // Cyclic contradiction downstream.
            let shape_matches: Vec<&Goal> = open_goals(sys)
                .filter(|g| matches!(g, Goal::Disj(d) if disj_alts_match(alts, &d.0)))
                .collect();
            if shape_matches.is_empty() {
                return None;
            }
            // Render each candidate disj's alts via `pretty_disj_alt` (a
            // strict analogue of HS's `prettyGuarded`) and compare against
            // skel `alt_texts`, both under the same normalization the parser
            // applied (whitespace + `#` stripped).  Score each candidate by
            // HOW MANY alts render exactly as stored and keep the best
            // (ties → source order).
            //
            // Scoring rather than all-or-nothing because the stored text
            // need not be in the runtime's normal form: HS re-parses each
            // alt into a `Guarded` (Theory/Text/Parser/Proof.hs:38-72, see
            // line 61) and the
            // parse normalizes — `gconj`'s `nub` collapses a repeated
            // conjunct (Guarded.hs:415-423), so a stored
            // `… ⇒ (∀ #l. C @ #l ⇒ ⊥) ∧ (∀ #l. C @ #l ⇒ ⊥)` matches a
            // runtime alt printing the conjunct once (ake/dh/UM_three_pass,
            // `case_2/…/R_Activate_case_1`).  An all-or-nothing test rejects
            // that candidate and falls through to source order, binding a
            // DIFFERENT open disj and diverging.
            let dbg = tamarin_utils::env_gate!("TAM_RS_DBG_MATCH_GOAL_DISJ");
            if dbg {
                let path = crate::constraint::solver::trace::case_path_string();
                eprintln!(
                    "[MATCH_GOAL_DISJ] path={} shape_matches={} skel.alt_texts={:?}",
                    path,
                    shape_matches.len(),
                    alt_texts
                );
            }
            if !alt_texts.iter().all(|s| s.is_empty()) {
                let mut best: Option<(usize, &Goal)> = None;
                for g in shape_matches.iter().copied() {
                    let Goal::Disj(d) = g else { continue };
                    let runtime_texts: Vec<String> =
                        d.0.iter()
                            .map(|a| normalize_disj_alt_text_for_match(&pretty_disj_alt(a)))
                            .collect();
                    // `disj_alts_match` already equated the lengths.
                    let score = runtime_texts
                        .iter()
                        .zip(alt_texts.iter())
                        .filter(|(r, w)| r == w)
                        .count();
                    if dbg {
                        eprintln!(
                            "[MATCH_GOAL_DISJ]   runtime_alts={:?} score={}/{}",
                            runtime_texts,
                            score,
                            alt_texts.len()
                        );
                    }
                    if !matches!(best, Some((b, _)) if score <= b) {
                        best = Some((score, g));
                    }
                }
                if let Some((score, g)) = best {
                    if score > 0 {
                        return Some(g.clone());
                    }
                }
            }
            // No alt rendered as stored (or no text info) — fall back to
            // source order (creation order in `sGoals`).
            Some(shape_matches[0].clone())
        }
        GoalSpec::Raw(_) => None,
    }
}

/// Compare the skeleton's per-alt signature against an open
/// `Goal::Disj`'s alts (`Vec<Guarded>`).  Returns true iff the lists
/// have the same length and each per-alt shape matches.
///
/// HS reference: each `Guarded` in the open Disj is what HS would
/// have produced from the same skeleton text via `guardedFormula`
/// (Theory/Text/Parser/Formula.hs).  HS matches by structural EQ of
/// the whole `Guarded` value; we relax to the shape signature so we
/// don't have to rebuild LVar identities from skeleton text (whose
/// var indices are different from the runtime System's).
fn disj_alts_match(skel: &[DisjAlt], runtime: &[crate::guarded::Guarded]) -> bool {
    if skel.len() != runtime.len() {
        return false;
    }
    skel.iter()
        .zip(runtime.iter())
        .all(|(s, r)| disj_alt_shape_matches(s, r))
}

/// Render a single Guarded alt to its HS-faithful `prettyGuarded`
/// representation.  Used by `match_goal`'s GoalSpec::Disj branch to
/// disambiguate among multiple shape-matching disjs via alt-text
/// equality.  See HS `prettyGuarded` (Guarded.hs:824-866).
fn pretty_disj_alt(g: &crate::guarded::Guarded) -> String {
    crate::pretty_formula::pretty_guarded(g)
}

/// Normalize a rendered alt text to the same canonical form as the
/// skeleton parser's `normalize_disj_alt_text` (proof_tree.rs): strip
/// all whitespace and `#` characters.  This bridges the HS-render's
/// `last(#t2)` style and the parser's pre-stripped form.
fn normalize_disj_alt_text_for_match(s: &str) -> String {
    s.chars()
        .filter(|c| !c.is_whitespace() && *c != '#')
        .collect()
}

fn disj_alt_shape_matches(skel: &DisjAlt, g: &crate::guarded::Guarded) -> bool {
    use crate::guarded::{Guarded, Quant};
    match (skel, g) {
        (
            DisjAlt::All { n_vars },
            Guarded::GGuarded {
                qua: Quant::All,
                vars,
                ..
            },
        ) => *n_vars == vars.len(),
        (
            DisjAlt::Ex { n_vars },
            Guarded::GGuarded {
                qua: Quant::Ex,
                vars,
                ..
            },
        ) => *n_vars == vars.len(),
        // `NonQuant` matches anything that isn't a top-level
        // `GGuarded` — atoms, conjunctions, disjunctions, and the
        // `∀[].A ⇒ ⊥` negation idiom (which HS pretty-prints as `¬A`
        // but stores as a quantified Guarded).  For the negation
        // idiom: the skeleton's text starts with `¬` (not `∀`), so
        // the parser classified it `NonQuant`; we accept it matching
        // a `GGuarded { qua: All, vars: [] }` here.  See
        // Guarded.hs:858-859 for the negation rendering.
        (
            DisjAlt::NonQuant,
            Guarded::GGuarded {
                qua: Quant::All,
                vars,
                body,
                ..
            },
        ) if vars.is_empty() => {
            matches!(&**body, Guarded::Disj(v) if v.is_empty())
        }
        (DisjAlt::NonQuant, Guarded::Atom(_))
        | (DisjAlt::NonQuant, Guarded::Conj(_))
        | (DisjAlt::NonQuant, Guarded::Disj(_)) => true,
        _ => false,
    }
}

#[cfg(test)]
#[path = "replay_tests.rs"]
mod tests;
