// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Skeleton-replay prover — port of HS `replaceSorryProver`
//! (lib/theory/src/Theory/Proof.hs).
//!
//! HS's `--prove` flag wires `replaceSorryProver $ runAutoProver`
//! (TheoryLoader.hs:569-615, see line 606) so the auto-prover runs **only at `by sorry`
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
//!      (`proveTheory (const True) checkProof`, Prover.hs:174-185) over
//!      ALL lemmas — it re-execs each stored step, keeping the verbatim
//!      structure and turning any step that no longer applies into an
//!      annotated `sorry /* invalid proof step encountered */`;
//!   2. prove-time `replaceSorryProver $ runAutoProver` (TheoryLoader.hs:569-615, see line 606)
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
use crate::fact::{fact_tag_name, FactTag, Multiplicity};

/// Drive a single lemma's skeleton.  Equivalent of HS
/// `runProver (replaceSorryProver (runAutoProver autoProver)) ctxt 0
///  initial sysOnTree` (Proof.hs).
///
/// `max_steps` is plumbed through to `run_proof_search` for the
/// fall-through auto-prover invocations.
pub fn replace_sorry_prove(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ParsedProofTree,
    max_steps: usize,
) -> ProofNode {
    replay_node(ctx, initial, skeleton, max_steps, true)
}

/// Replay a stored skeleton WITHOUT auto-proving its open/sorry leaves —
/// the equivalent of HS's close-time `checkAndExtendProver (sorryProver
/// Nothing)` (Prover.hs:170-251, see line 185, Proof.hs).  Each step's method and
/// children are taken verbatim from the skeleton; every fall-through that
/// `checkProof` would turn into a `Sorry` with a `Nothing` system
/// (Proof.hs) becomes an *unannotated* `ProofNode`
/// (`annotated == false`), so the lemma renders byte-identically to HS's
/// reprint of a non-target lemma (incl. `/* unannotated */` markers) and
/// its summary status reflects the stored proof — NOT a fresh search.
///
/// Used for lemmas the `--prove` selector does NOT target (HS keeps their
/// close-time-replayed proof untouched, Prover.hs:273-275).
pub fn check_and_extend(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ParsedProofTree,
    max_steps: usize,
) -> ProofNode {
    replay_node(ctx, initial, skeleton, max_steps, false)
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
fn invalid_step_node(node: &ParsedProofTree, sys: System) -> ProofNode {
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
/// We mirror this by converting the `ParsedProofTree` to `ProofNode`
/// with `annotated: false` throughout.  The `sys` placeholder is the
/// parent's sys (unused in display but required by `ProofNode`).
///
/// Converts:
/// - `Simplify`    → `ProofMethod::Simplify`
/// - `Induction`   → `ProofMethod::Induction`
/// - `Sorry`       → `ProofMethod::Sorry(None)`
/// - `Contradiction` → `ProofMethod::Finished(Contradictory(None))`
/// - `SolveGoal(_, raw)` → `ProofMethod::RawSolve(raw)` (display-only)
/// - `SolvedLeaf`  → `ProofMethod::Finished(Solved)`
/// - `Unfinishable` → `ProofMethod::Finished(Unfinishable)`
/// - `Invalidated` → `ProofMethod::Invalidated`
/// - `Other(s)`    → `ProofMethod::Sorry(Some(s))`
fn parsed_to_unannotated(node: &ParsedProofTree, sys: System) -> ProofNode {
    let method = parsed_method_to_display(&node.method);
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

/// Convert a `ParsedMethod` to the best display-only `ProofMethod`.
/// Used exclusively by `parsed_to_unannotated` — not for exec.
fn parsed_method_to_display(pm: &ParsedMethod) -> ProofMethod {
    match pm {
        ParsedMethod::Simplify => ProofMethod::Simplify,
        ParsedMethod::Induction => ProofMethod::Induction,
        ParsedMethod::Sorry => ProofMethod::Sorry(None),
        ParsedMethod::Contradiction => ProofMethod::Finished(MethodResult::Contradictory(None)),
        ParsedMethod::SolveGoal(_, raw) => ProofMethod::RawSolve(raw.clone()),
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
    max_steps: usize,
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
                invalid_step_node(node, sys)
            } else {
                run_proof_search(ctx, sys, max_steps)
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
    max_steps: usize,
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
        return run_proof_search(ctx, sys, max_steps);
    }

    // `by contradiction` leaf → emit a Finished(Contradictory) node if
    // a contradiction can actually be derived; else fall through to the
    // auto-prover.  This is HS-faithful, not a divergence: at close time
    // `checkProof` re-execs the stored `Finished (Contradictory Nothing)`
    // step (`checkAndExecProofMethod`, Proof.hs:447-467, see line 456); if the system is no
    // longer contradictory the method returns `Nothing`, so checkProof
    // emits `sorryNode (Just "invalid proof step encountered") ...`
    // (Proof.hs:459-461) carrying `Just sys`.  For a `--prove`-selected
    // lemma `replaceSorryProver` then re-runs the auto-prover on that
    // annotated sorry (Prover.hs:170-251, see line 185 → TheoryLoader.hs:569-615, see line 606), exactly the
    // `run_proof_search` fall-through below.
    if matches!(node.method, ParsedMethod::Contradiction) && node.cases.is_empty() {
        // HS replay (checkProof, Proof.hs) preserves the skeleton's STORED
        // method verbatim — the parser builds `Finished (Contradictory
        // Nothing)` for `by contradiction` (Proof.hs:81), so the reprinted
        // method carries no reason (`prettyProofMethod` → plain `by
        // contradiction`).  Emit `Contradictory(None)`, NOT a freshly-
        // recomputed reason (which would print a spurious `/* from
        // formulas */`).  On disagreement HS `checkProof` (Proof.hs) emits
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
            max_steps,
        );
    }

    // `SOLVED` leaf (HS Proof.hs:102-103).  If runtime is_finished
    // agrees, emit Finished(Solved); else fall through to the auto-prover
    // (whose run_proof_search may simplify/contract further until it
    // reaches Solved naturally).  The fall-through is exactly HS's
    // pipeline: close-time `checkProof` marks the stale `Finished Solved`
    // an annotated `sorry /* invalid proof step encountered */`
    // (Proof.hs:459-461), and for a `--prove`-selected lemma
    // `replaceSorryProver` then reproves it (Prover.hs:170-251, see line 185 →
    // TheoryLoader.hs:569-615, see line 606).  Skeleton's SOLVED is HS's claim; RS verifies
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
            max_steps,
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
            max_steps,
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
                return invalid_step_node(node, sys);
            }
            return run_proof_search(ctx, sys, max_steps);
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
                let placeholder = parsed_to_unannotated(sub_tree, sys.clone());
                children.insert(skel_name.clone(), placeholder);
                any_sorry = true;
                if push_path {
                    crate::constraint::solver::trace::case_path_pop();
                }
                continue;
            }
        };
        let child_node = replay_node(ctx, child_sys, sub_tree, max_steps, auto_prove);
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
    // children as the RIGHT map (Proof.hs:447-467, see line 463 `mergeMapsWith
    // unhandledCase noSystemPrf (go (d+1)) cases cs`), so a runtime-only
    // case (present left, absent right) goes through `unhandledCase =
    // mapProofInfo (Nothing,) . prover d` (Proof.hs:447-467, see line 462) → an annotated
    // `sorry Nothing (Just se)`.  For a `--prove`-selected lemma
    // `replaceSorryProver` then auto-proves that annotated sorry
    // (Prover.hs:170-251, see line 185 → TheoryLoader.hs:569-615, see line 606), matching the
    // `run_proof_search` branch below.
    for (rt_name, rt_sys) in produced.into_iter() {
        if children.contains_key(&rt_name) {
            continue;
        }
        // Also skip if the skeleton consumed this case via "".
        if node.cases.iter().any(|(s, _)| s.is_empty())
            && children.len() == 1
            && children.keys().next().map(|s| s.as_str()) == Some(rt_name.as_str())
        {
            continue;
        }
        let push_path = !rt_name.is_empty();
        if push_path {
            crate::constraint::solver::trace::case_path_push(&rt_name);
        }
        let auto = if auto_prove {
            run_proof_search(ctx, rt_sys, max_steps)
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
/// in the skeleton whose inner formula we couldn't structurally parse,
/// e.g. a disjunction `(a) ∥ (b)` or a subterm `a ⊏ b`), we iterate
/// over the candidate ProofMethods in heuristic-ranked order (same
/// list `expand` in search.rs uses) and pick the first one whose
/// resulting case-set is compatible with the skeleton's child case
/// names.  This is the closest we can come to HS's behavior without a
/// full formula→Goal parser: HS parses the formula directly into a
/// Goal, but if our auto-prover would have picked the same goal in
/// that state, the case-decomposition matches.
fn exec_method_for(
    parsed: &ParsedMethod,
    sys: &System,
    ctx: &ProofContext,
    skel_children: &[(String, ParsedProofTree)],
) -> Option<(ProofMethod, Vec<(String, System)>)> {
    let dbg = tamarin_utils::env_gate!("TAM_DBG_REPLAY");
    // Fast path: parsed method resolves directly.
    if let Some(method) = resolve_method(parsed, sys) {
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
    // spirit: HS parses the formula inside `solve(...)` directly to a
    // Goal value via `goal` (Theory/Text/Parser/Proof.hs:39-72) and
    // would always find the goal in `sys.goals`; we can't do that for
    // disjunction / subterm / split goals yet (see GoalSpec::Raw
    // doc-comment), so we approximate by trusting the heuristic
    // ranking — for the patterns we hit in the target lemmas, the
    // top-ranked goal IS the one HS parsed.
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
fn resolve_method(parsed: &ParsedMethod, sys: &System) -> Option<ProofMethod> {
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
            let g = match_goal(spec, sys)?;
            Some(ProofMethod::SolveGoal(g))
        }
        ParsedMethod::SolvedLeaf
        | ParsedMethod::Unfinishable
        | ParsedMethod::Invalidated
        | ParsedMethod::Other(_) => None,
    }
}

/// Exact-match a stored-proof fact's argument terms against a runtime
/// [`LNFact`]'s terms — HS's `M.member` semantics (ProofMethod.hs:253-274, see line 258
/// `guard (goal `M.member` L.get sGoals sys)`).
///
/// HS parses the stored `solve(...)` goal into a full `Goal` carrying
/// concrete LVar identities (`fact llit`, Theory/Text/Parser/Proof.hs:38-72)
/// and looks it up by **structural equality** against `sys.goals`; when the
/// goal is absent from the (drifted) current system `checkProof` returns
/// `Nothing` and marks the step `sorry /* invalid proof step encountered */`,
/// keeping the stored subtree verbatim (Proof.hs:455-468).
///
/// Our skeleton parser keeps each fact argument only as raw surface text
/// (`build_fact` stuffs it into a `Term::Var` name).  We recover the
/// canonical runtime term by re-parsing that text (`parse_term_str`) and
/// converting it through the SAME smart constructors the runtime uses
/// ([`parse_arg_to_lnterm`] → `term_to_lnterm` in elaborate.rs: sorts via
/// sigil, AC flattened+sorted via `f_app_ac`, pairs right-nested,
/// unary-builtins folded, `em` as a C-symbol).  Two terms in that canonical
/// form are equal iff HS's `M.member` would treat the goals as equal, so a
/// plain `==` is the faithful test.
///
/// Exact `==` mirrors HS: a valid replay step's goal is byte-for-byte the
/// runtime goal (RS reproduces HS's reset indices), so any divergence is
/// correctly rejected.  A looser sort-aware alpha-equivalence test would
/// be wrong here — it accepts goals HS rejects, letting a
/// structurally-distinct same-shape goal bind and re-derive a divergent
/// subtree.
fn fact_terms_match_exact(
    parsed_args: &[tamarin_parser::ast::Term],
    runtime_terms: &[tamarin_term::lterm::LNTerm],
) -> bool {
    if parsed_args.len() != runtime_terms.len() {
        return false;
    }
    // The theory's `[AC]` symbol names, read once for the whole fact: the
    // re-parse needs them to read a user AC symbol's infix spelling.
    let ac_names = crate::elaborate::current_user_ac_names();
    parsed_args.iter().zip(runtime_terms.iter()).all(|(p, r)| {
        match parse_arg_to_lnterm(p, &ac_names) {
            // Canonical re-parse equals the runtime term exactly (M.member).
            Some(t) => &t == r,
            // Unparseable / unconvertible arg: we cannot establish exact
            // equality.  HS always has a concrete parsed term here, so
            // failing closed (no match) mirrors an `M.member` miss.
            None => false,
        }
    })
}

/// Re-parse a skeleton fact-argument's raw text into a canonical runtime
/// [`LNTerm`] (the same representation runtime goals use), for exact `==`
/// comparison.  `parsed_term_of_arg` recovers the surface AST from the
/// `Term::Var` name shim; `term_to_lnterm` (elaborate.rs) is HS's
/// `fact llit` term construction (it reads the live elaboration context for
/// user function symbols, which is in scope during proof-search replay).
fn parse_arg_to_lnterm(
    arg: &tamarin_parser::ast::Term,
    ac_names: &[String],
) -> Option<tamarin_term::lterm::LNTerm> {
    let ast = parsed_term_of_arg(arg, ac_names)?;
    crate::elaborate::term_to_lnterm(&ast)
}

/// Recover a structured AST term from a skeleton fact argument.  The
/// skeleton parser stores each arg as a `Term::Var` whose `name` holds
/// the raw surface text (see `build_fact`); re-parse that text.  If the
/// arg is already structured (future-proofing), return it directly.
///
/// `ac_names` are the theory's user-declared `[AC]` symbols, which the
/// re-parse needs to read their infix spelling (`(z add h(y))` for
/// `functions: add/2 [AC]`) — HS's `acterm` takes the same set from the
/// parser state's signature (Theory/Text/Parser/Term.hs:165-174).
fn parsed_term_of_arg(
    arg: &tamarin_parser::ast::Term,
    ac_names: &[String],
) -> Option<tamarin_parser::ast::Term> {
    use tamarin_parser::ast::Term as PTerm;
    match arg {
        PTerm::Var(v) => tamarin_parser::parser::parse_term_str(&v.name, ac_names).ok(),
        other => Some(other.clone()),
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
/// HS looks the goal up by structural equality on the parsed `Goal` value
/// itself (`Theory.Text.Parser.Proof.goal`, Proof.hs:39-72), whose LVar
/// identities come from the parser's name table.  RS's skeleton parser keeps
/// only surface text, so each arm rebuilds as much of that equality as its
/// goal kind allows: the fact-bearing kinds re-parse the stored terms and
/// compare them exactly ([`fact_terms_match_exact`]), the rest compare
/// canonicalised rendered text or a stable id.
///
/// `None` means the stored step names a goal this system does not have.  For
/// every kind handled here `exec_method_for` then gives up (its raw-solve
/// fallback is reserved for [`GoalSpec::Raw`]), and the caller emits
/// `sorry /* invalid proof step encountered */` over the verbatim stored
/// subtree — HS `checkProof`'s `Nothing` branch (Proof.hs:455-468).
fn match_goal(spec: &GoalSpec, sys: &System) -> Option<Goal> {
    match spec {
        GoalSpec::Action {
            fact,
            time_var,
            time_idx,
            ..
        } => {
            // HS's parsed `ActionG i fa` matches by structural equality
            // against a key of `sGoals` (ProofMethod.hs:253-274, see line
            // 258, `goal `M.member` sGoals`), so the conjuncts below are one
            // `M.member` test split into the three things RS can check:
            //
            // * (name, arity, persistent) — the fact SHAPE.  Skip KU goals
            //   (auto-handled) unless the spec itself names `KU`: the
            //   skeleton usually names protocol facts, but it may explicitly
            //   solve a `!KU( t ) @ #i` (noise secrecy proofs do), and a
            //   non-KU spec must not spuriously bind a KU goal of matching
            //   arity.
            // * `fact_terms_match_exact` — the TERMS.  Shape alone is not
            //   enough: a stale stored `!KU( ~r1 )` must not bind a present
            //   `!KU( h(...) )`, which would re-derive the wrong goal and
            //   cascade into a divergent subtree.
            // * the FULL timepoint LVar, name AND idx.  A stored step whose
            //   idx has drifted from the re-executed system's (stored
            //   `!KU(~e0)@#vk.17` vs a re-minted `#vk.18` after upstream
            //   case-numbering changed) is a `M.member` miss in HS.  Root
            //   name alone is too lenient — it re-binds the drifted goal and
            //   replays it as a live step.
            //
            // `sGoals` is keyed by `Goal`, so at most one open goal can
            // satisfy all three.
            let want_ku = fact.name == "KU";
            open_goals(sys)
                .find(|g| match g {
                    Goal::Action(i, fa) => {
                        name_matches(&fa.tag, &fact.name)
                            && fa.terms.len() == fact.args.len()
                            && tag_persistent(&fa.tag) == fact.persistent
                            && (want_ku || !matches!(fa.tag, FactTag::Ku))
                            && fact_terms_match_exact(&fact.args, &fa.terms)
                            && *i.name == **time_var
                            && i.idx == *time_idx as u64
                    }
                    _ => false,
                })
                .cloned()
        }
        GoalSpec::Premise {
            fact,
            prem_idx,
            time_var,
            time_idx,
            ..
        } => {
            // `PremiseG (i, v) fa` under the same one-`M.member`-test-split-
            // in-three reading as the Action arm above (shape, then exact
            // terms, then the FULL node LVar); the extra conjunct is the
            // `PremIdx v`.
            open_goals(sys)
                .find(|g| match g {
                    Goal::Premise((node, prem), fa) => {
                        name_matches(&fa.tag, &fact.name)
                            && fa.terms.len() == fact.args.len()
                            && tag_persistent(&fa.tag) == fact.persistent
                            && prem.0 == *prem_idx
                            && fact_terms_match_exact(&fact.args, &fa.terms)
                            && *node.name == **time_var
                            && node.idx == *time_idx as u64
                    }
                    _ => false,
                })
                .cloned()
        }
        GoalSpec::Disj { alts, alt_texts } => {
            // HS-faithful: HS parses the `solve(...)` text into a
            // `DisjG (Disj [GuardedFormula])` value via
            // `disjSplitGoal` (Theory/Text/Parser/Proof.hs:39-72, see line 61), then
            // dispatches `SolveGoal goal` against `sys.goals` (HS
            // ProofMethod.hs:374: `guard (goal \`M.member\` sGoals)`).
            //
            // Our skeleton parser only captures each alt's structural
            // SIGNATURE (top-level shape — see `DisjAlt`), so the first
            // filter keeps every open `Goal::Disj(d)` whose `d.0` list has
            // the same length AND the same per-alt signature as the
            // skeleton's `alts`.  See HS Proof.hs:61.
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
            // alt into a `Guarded` (Proof.hs:39-72, see line 61) and the
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
            // source order (creation order in `sGoals`).  Mirrors the
            // Action/Premise ambiguity-resolution policy above.
            Some(shape_matches[0].clone())
        }
        GoalSpec::Chain {
            src_var,
            conc_idx,
            tgt_var,
            prem_idx,
        } => {
            // HS dispatch: `solve( (#i, n) ~~> (#j, m) )` parses to
            // `ChainG (i, ConcIdx n) (j, PremIdx m)` (Proof.hs:59) and
            // matches by structural equality against an open
            // `Goal::Chain(...)` in `sys.goals` (HS ProofMethod.hs:374:
            // `goal `M.member` sGoals`).  HS's open chain-goal carries
            // concrete LVar identities — same skeleton-vs-runtime LVar
            // suffix-idx mismatch as Action/Premise.  We match by var
            // ROOT name + conc/prem idx, ignoring suffix idxs.
            open_goals(sys)
                .find(|g| match g {
                    Goal::Chain((src, c), (tgt, p)) => {
                        *src.name == **src_var
                            && *tgt.name == **tgt_var
                            && c.0 == *conc_idx as usize
                            && p.0 == *prem_idx as usize
                    }
                    _ => false,
                })
                .cloned()
        }
        GoalSpec::Subterm { small_raw, big_raw } => {
            // HS `stSplitGoal` (Proof.hs:63-66) parses to
            // `SubtermG (small, big)` over LNTerm and dispatches via
            // structural Map lookup in `sys.goals` (HS ProofMethod.hs:253-274, see line 258).
            // We compare by canonical pretty-printed text — see HS
            // `prettyGoal (SubtermG (l,r))` at Constraints.hs:281-282
            // which prints `prettyLNTerm l ⊏ prettyLNTerm r`.  Pretty
            // representations are stable across the skeleton-vs-runtime
            // boundary for ground terms; for terms containing free
            // LVars the skeleton-text and runtime indices may diverge,
            // so as a fallback we accept the sole open Subterm goal when
            // there is exactly one.
            use tamarin_term::pretty::pretty_lnterm;
            let want_small = canonicalise_term_text(small_raw);
            let want_big = canonicalise_term_text(big_raw);
            let by_text = open_goals(sys)
                .find(|g| match g {
                    Goal::Subterm((l, r)) => {
                        canonicalise_term_text(&pretty_lnterm(l)) == want_small
                            && canonicalise_term_text(&pretty_lnterm(r)) == want_big
                    }
                    _ => false,
                })
                .cloned();
            if by_text.is_some() {
                return by_text;
            }
            // Fallback: if exactly one open Subterm goal exists, use
            // it (the skeleton text uniquely identifies it by being
            // the only Subterm in `sys.goals`).
            let mut subterms = open_goals(sys).filter(|g| matches!(g, Goal::Subterm(_)));
            let first = subterms.next();
            match subterms.next() {
                None => first.cloned(),
                Some(_) => None,
            }
        }
        GoalSpec::Split { split_id } => {
            // HS `eqSplitGoal` (Proof.hs:70-72) parses to
            // `SplitG (SplitId N)` and dispatches via structural Map
            // lookup in `sys.goals`.  Split ids are stable (minted by
            // `EquationStore::add_disj`), so an exact id-match is
            // correct here — no variable-renaming concerns.
            let want = crate::constraint::constraints::SplitId(*split_id);
            open_goals(sys)
                .find(|g| matches!(g, Goal::Split(id) if *id == want))
                .cloned()
        }
        GoalSpec::Raw(_) => None,
    }
}

/// Normalise spaces in a pretty-printed term/text fragment so that
/// equality between skeleton-text and runtime-pretty doesn't fail on
/// whitespace differences (HS's `fsep`/`PrettyPrint` and our
/// `pretty_lnterm` produce slightly different spacing around commas
/// and operators).  Collapses any run of ASCII whitespace into a single
/// space and trims.
///
/// Additionally removes whitespace that sits *immediately inside* a
/// bracket / paren delimiter — i.e. directly after `<`, `(` or directly
/// before `>`, `)`.  The skeleton text comes from the STORED proof,
/// whose `solve(...)` terms are pretty-printed by HughesPJ with line
/// wrapping: a pair `<a, b>` that overflows the ribbon wraps to
/// `<\n        a,\n        b\n      >`, and after the whitespace-collapse
/// above that becomes `< a, b >`.  The runtime `render_lnterm` renders
/// the same term un-wrapped as `<a, b>` (no inner space).  Without this
/// extra normalisation the two strings differ only by those wrap-induced
/// `< `/` >`/`( `/` )` spaces, the term-text disambiguation in
/// `match_goal` returns 0 matches, and the fallback time-var tie-break
/// then mis-selects the smallest-idx `#vk` knowledge goal (e.g.
/// `!KU($USR)`) in place of the skeleton's intended `!KU(hmac(...))`.
/// The spacing is purely cosmetic (it only ever arises from wrapping),
/// so stripping it is structure-preserving and HS-faithful.
fn canonicalise_term_text(s: &str) -> String {
    // Pass 1: collapse runs of ASCII whitespace to a single space, trim.
    let mut collapsed = String::with_capacity(s.len());
    let mut last_ws = true; // suppress leading whitespace
    for c in s.chars() {
        if c.is_whitespace() {
            if !last_ws {
                collapsed.push(' ');
                last_ws = true;
            }
        } else {
            collapsed.push(c);
            last_ws = false;
        }
    }
    if collapsed.ends_with(' ') {
        collapsed.pop();
    }
    // Pass 2: drop a space that immediately follows `<`/`(` (opening
    // delimiter) or immediately precedes `>`/`)` (closing delimiter).
    let chars: Vec<char> = collapsed.chars().collect();
    let mut out = String::with_capacity(chars.len());
    let mut prev: Option<char> = None;
    for (idx, &c) in chars.iter().enumerate() {
        if c == ' ' {
            if matches!(prev, Some('<') | Some('(')) {
                continue; // space right after an opening delimiter
            }
            if matches!(chars.get(idx + 1), Some('>') | Some(')')) {
                continue; // space right before a closing delimiter
            }
        }
        out.push(c);
        prev = Some(c);
    }
    out
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
/// equality.  See HS `prettyGuarded` (Guarded.hs:822-864).
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
        // Guarded.hs:856-857 for the negation rendering.
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

fn name_matches(tag: &FactTag, want: &str) -> bool {
    fact_tag_name(tag) == want
}

fn tag_persistent(tag: &FactTag) -> bool {
    // `KU`/`KD` knowledge facts are persistent (Fact.hs:353-357;
    // `factTagMultiplicity` → Persistent), and the skeleton pretty-prints
    // them with the `!` prefix (e.g. `solve( !KU( ~n ) @ #vk )`), so the
    // parsed spec's `persistent` flag is `true` and must match here.
    matches!(
        tag,
        FactTag::Proto(Multiplicity::Persistent, _, _) | FactTag::Ku | FactTag::Kd
    )
}

#[cfg(test)]
#[path = "replay_tests.rs"]
mod tests;
