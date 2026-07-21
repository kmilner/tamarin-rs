// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, felixlinker, jdreier, PhilipLukertWork, rkunnema, beschmi,
//   rsasse, racoucho1u, charlie-j, niklasmedinger, Nynko, yavivanov,
//   ValentinYuri, robert.kunnemann@cased.de, xaDxelA, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/Solver/Simplify.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Tools/SubtermStore.hs, src/Web/Theory.hs

//! Port of `Theory.Constraint.Solver.ProofMethod`.
//!
//! `ProofMethod` is the small-step interface to the constraint
//! solver. The high-level loop in Haskell is:
//!
//! ```text
//! exec(method, sys) -> Map<CaseName, System>
//!     - Sorry / Finished / Invalidated → trivial
//!     - Simplify  → simplify the system once
//!     - SolveGoal → reduce a specific open goal, possibly producing
//!                   multiple cases
//!     - Induction → split into base/step cases
//! ```
//!
//! All arms are fully ported: the trivial cases (Sorry / Finished /
//! Invalidated), `Simplify` (with the per-step simplify fan-out and
//! dedup/distinguish case naming), `SolveGoal` (full goal dispatch via
//! `solve_*_goal`), and `Induction` (base/step split via `ginduct`).
//! `None` results mean "no applicable method", not unfinished stubs.

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::contradictions::{contradictions, Contradiction};
use crate::constraint::system::System;

/// Each case in a proof tree gets a unique name.
pub type CaseName = String;

/// Outcome of a finished proof method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Result {
    /// A dependency graph was found that satisfies the system.
    Solved,
    /// A contradiction could be derived.
    Contradictory(Option<Contradiction>),
    /// The proof can't be finished — typically because of reducible
    /// operators in subterms or a solution after weakening.
    Unfinishable,
}

/// One small-step transformation of a sequent.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofMethod {
    Sorry(Option<String>),
    Simplify,
    SolveGoal(Goal),
    Induction,
    Finished(Result),
    Invalidated,
    /// Display-only: `solve( <raw_inner> )`.  Used for HS-faithful
    /// unannotated subtree display (replay.rs `parsed_to_unannotated`)
    /// where we have the original skeleton text but no live Goal object.
    /// HS `noSystemPrf` (Proof.hs:447-467, see line 467) clears the per-node system info
    /// (`mapProofInfo (\i -> (Just i, Nothing))`); the ProofMethod itself
    /// is preserved by the proof-tree node, not by `noSystemPrf`.  RS uses
    /// raw inner text as the closest equivalent.
    RawSolve(String),
}

/// `isFinished`: returns the appropriate `Result` if the system is in
/// a terminal state — solved, contradictory, or unfinishable.
pub fn is_finished(ctx: &ProofContext, sys: &System) -> Option<Result> {
    if sys.is_initial() { return None; }
    let cs = contradictions(ctx, sys);
    if let Some(c) = cs.into_iter().next() {
        // Mirror Haskell `contradictorySystem`: any contradiction
        // closes the branch as `Contradictory`.  Haskell's `isFinished`
        // does not gate this on incomplete-source consumption —
        // `Source.incomplete` only affects diagnostic warnings, not the
        // search verdict.
        return Some(Result::Contradictory(Some(c)));
    }
    // Direct port of Haskell `isFinished` (ProofMethod.hs):
    //   | null ogs && stFinished     = Just Solved
    //   | null ogs && not stFinished = Just Unfinishable
    //   | otherwise                  = Nothing
    // where `ogs = openGoals sys` — the FILTERED list (with the
    // auto-solve KU heuristic applied), not just the unsolved-status
    // count.  Our `open_goals` does the same filtering, so we check IT
    // for emptiness rather than the status flags.
    // (gfalse is caught as a FormulasFalse contradiction above, so we
    // don't need an explicit `no_false_formula` guard here.)
    use crate::constraint::solver::goals::open_goals;
    let no_open_goals = open_goals(sys).is_empty();
    let sub_finished = finished_subterms(ctx, sys);
    if no_open_goals && sub_finished {
        // Haskell's `isFinished` doesn't gate Solved on `incomplete`
        // source consumption — `Source.incomplete` is diagnostic-only
        // there.  Match that.
        Some(Result::Solved)
    }
    else if no_open_goals && !sub_finished { Some(Result::Unfinishable) }
    else { None }
}

/// Direct port of Haskell `finishedSubterms`
/// (`Theory.Tools.SubtermStore:130`):
///   hasReducibleOperatorsOnTop reducible sst =
///     all (topIsNotReducible . snd) allSubterms
///     where allSubterms = posSubterms ∪ negSubterms ∪ solvedSubterms
///           topIsNotReducible (FApp f _) = f ∉ reducible
///           topIsNotReducible _          = True
///
/// True iff every subterm's RHS has a top-level function symbol that
/// is NOT in the reducible set.  If any subterm's RHS has a reducible
/// top symbol, the proof cannot finish (further rewriting could
/// reduce it).
pub fn finished_subterms(ctx: &ProofContext, sys: &System) -> bool {
    use tamarin_term::term::Term;
    let msig = ctx.maude.maude_sig();
    let top_is_not_reducible = |t: &tamarin_term::lterm::LNTerm| -> bool {
        match t {
            // HS `topIsNotReducible (FApp f _) = f \`S.notMember\` reducible`
            // (SubtermStore.hs:134-135).  `reducible_fun_syms` is a
            // `FunSig = BTreeSet<FunSym>`, so `contains` does the exact
            // structural `FunSym` equality test in O(log n).
            Term::App(f, _) => !msig.reducible_fun_syms.contains(f),
            // Variables and constants are never reducible at the top.
            _ => true,
        }
    };
    // HS `hasReducibleOperatorsOnTop` walks posSubterms ∪ negSubterms ∪
    // solvedSubterms (SubtermStore.hs:131-133).
    sys.subterm_store.subterms.iter().all(|s| top_is_not_reducible(&s.big))
        && sys.subterm_store.solved_subterms.iter().all(|s| top_is_not_reducible(&s.big))
        && sys.subterm_store.neg_subterms.iter().all(|(_, big)| top_is_not_reducible(big))
}

/// Render/index applicability — the evaluation depth HS's
/// `mapMaybe execProofMethod` forces when building the web UI's
/// "Applicable Proof Methods" list, WITHOUT the `SolveGoal` fan-out.
///
/// HS (`ProofMethod.hs:751-756`) forces each `execProofMethod` result
/// only to WHNF (`Just`/`Nothing`); the `SolveGoal` arm is
/// `… (return tracedCases)` (`ProofMethod.hs:429-447`) — ALWAYS `Just`,
/// with the whole case fan-out an unforced thunk the node page never
/// demands (`Web/Theory.hs:593-597` binds the cases to `_`; the
/// "N sub-case(s)" count comes from the persisted tree, `:599`).  Only
/// `Simplify` (bounded simplify + single-case guard, `:419-427`) and
/// `Induction` (structural `ginduct` guard, `:428`) can drop a method at
/// render, and those ARE forced — keep the full exec for them.  The
/// fan-out is paid only when a method is APPLIED (`oneStepProver`'s
/// `M.map` forces the spine, `Proof.hs:584-587`) — RS's `apply_at_path`,
/// unchanged.
///
/// Eagerly exec'ing every candidate here made rendering one bilinear
/// node cost 129s (ake/bilinear/Joux; HS renders it in 0.09s and takes
/// 146.85s only when the method is clicked) — the Joux/Joux_EphkRev/siv
/// web-crawl timeouts.  Also more faithful on the deadline: HS never
/// drops a SolveGoal at render; the eager exec's deadline entry-guard
/// could.
pub fn is_applicable_for_display(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> bool {
    match method {
        // `return tracedCases` — unconditionally `Just` in HS; do NOT
        // call exec_proof_method (that forces the fan-out).
        ProofMethod::SolveGoal(_) => true,
        // Forced by HS at render too; cheap and can legitimately drop
        // the method (no-op Simplify / non-initial Induction).
        ProofMethod::Simplify | ProofMethod::Induction =>
            exec_proof_method(ctx, method, sys).is_some(),
        ProofMethod::Sorry(_) | ProofMethod::Finished(_) => true,
        ProofMethod::Invalidated | ProofMethod::RawSolve(_) => false,
    }
}

/// HS `uniqueListBy (comparing fst) id distinguish` (ProofMethod.hs:462-463, see line 465,
/// 527-532): singleton case names stay bare; each duplicate group of
/// size `n` is rewritten to `<name>_case_<i>` with the running index `i`
/// (1,2,3…) zero-padded to the width of `show n`.  Input order is
/// preserved.  Shared by the `SolveGoal` and `Induction` arms of
/// [`exec_proof_method`].
///
/// HS-faithful zero-padding: `distinguish`
///   distinguish n =
///     [ (\(x,y) -> (... x ++ "_case_" ++ pad (show i), y)) | i <- [1..] ]
///     where l = length (show n); pad cs = replicate (l - length cs) '0' ++ cs
/// so total<10 → width 1 (no padding); total>=10 → width 2 ("01"..); etc.
// case-name counters; output order follows the ordered cases Vec, maps keyed only;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn distinguish_case_names(cases: Vec<(String, System)>) -> Vec<(String, System)> {
    use std::collections::HashMap;
    let mut counts: HashMap<String, usize> = HashMap::new();
    for (name, _) in &cases {
        *counts.entry(name.clone()).or_default() += 1;
    }
    let mut seen: HashMap<String, usize> = HashMap::new();
    let mut out = Vec::with_capacity(cases.len());
    for (name, s) in cases.into_iter() {
        let total = counts[&name];
        let key = if total > 1 {
            let n = seen.entry(name.clone()).or_default();
            *n += 1;
            let width = total.to_string().len();
            format!("{}_case_{:0width$}", name, *n, width = width)
        } else {
            name
        };
        out.push((key, s));
    }
    out
}

/// HS-faithful `removeRedundantCases ctxt [] <get_sys>` wrapper: captures the
/// `maude_sig()`/`enable_bp`/`enable_mset`/empty-`stable_vars` boilerplate the
/// three arms of [`exec_proof_method`] share.  HS passes `[]` for stable_vars
/// and gates the whole dedup on BP/MSet inside `remove_redundant_cases`.
fn remove_redundant_cases_ctx<T>(
    ctx: &ProofContext,
    get_sys: impl Fn(&T) -> &System,
    cases: Vec<T>,
) -> Vec<T> {
    let msig = ctx.maude.maude_sig();
    let empty_stable: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    crate::constraint::solver::sources::remove_redundant_cases(
        msig.enable_bp,
        msig.enable_mset,
        &empty_stable,
        get_sys,
        cases,
    )
}

/// HS `process` tail shared by the `SolveGoal` and `Induction` arms:
/// BP/MSet-gated structural dedup (`removeRedundantCases ctxt [] snd`)
/// followed by `uniqueListBy (comparing fst) id distinguish` naming.
fn process_cases(ctx: &ProofContext, cases: Vec<(String, System)>) -> Vec<(String, System)> {
    distinguish_case_names(remove_redundant_cases_ctx(ctx, |p: &(String, System)| &p.1, cases))
}

/// Opt-in hit/miss counters for the Simplify no-op shortcut
/// (`TAM_RS_SIMP_NOOP_STATS=1`); prints every 1000 Simplify execs.
fn simp_noop_stat(hit: bool) {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
    static CALLS: AtomicU64 = AtomicU64::new(0);
    static HITS: AtomicU64 = AtomicU64::new(0);
    if !tamarin_utils::env_gate!("TAM_RS_SIMP_NOOP_STATS") {
        return;
    }
    if hit {
        HITS.fetch_add(1, Relaxed);
    }
    let calls = CALLS.fetch_add(1, Relaxed) + 1;
    if calls % 1_000 == 0 {
        let h = HITS.load(Relaxed);
        eprintln!("[SIMP_NOOP_STATS] simplify_execs={} noop_hits={} ({:.1}%)",
            calls, h, 100.0 * h as f64 / calls as f64);
    }
}

/// Execute a proof method against `sys`, returning the resulting
/// case list in dispatch order. `Sorry` / `Finished` produce empty
/// cases; `Simplify` runs the simplify fan-out and returns one case
/// per surviving branch; `SolveGoal(g)` dispatches via `solve_*_goal`
/// and converts `GoalCases` to a case list; `Induction` splits the
/// first formula into base/step cases via `ginduct`.
///
/// The case list is returned as a `Vec` in the order branches were
/// produced, but callers do not rely on that order: both `search.rs`
/// and `replay.rs` re-sort the cases by name before walking them, to
/// reproduce Haskell's `Data.Map` (alphabetical) iteration order from
/// `execProofMethod`'s `M.fromListWith`.
pub fn exec_proof_method(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> Option<Vec<(CaseName, System)>> {
    use crate::constraint::solver::reduction::{GoalCases, Reduction};

    // Deadline short-circuit (entry-guard).  Without this, a single
    // `exec_proof_method` invocation that internally enumerates many
    // Maude unifiers / source-case branches (e.g. bilinear-pairing
    // examples with large variant tables) can run for many seconds
    // before any caller checks the deadline.  Returning `None` signals
    // "no method applicable" — the caller in `expand_inner` then walks
    // the rest of the candidate list, all of which also return `None`,
    // and the node becomes `Sorry: no method`.  The next call up the
    // recursion checks the deadline at the top of `search::expand_inner`
    // and bails to `Sorry: deadline reached`.
    // Combined, this bounds the post-deadline runtime to O(depth) rather
    // than O(remaining-work-in-current-method).
    if crate::constraint::solver::search::deadline_reached() {
        return None;
    }

    // HS-faithful per-step Maude counter reset (ProofMethod.hs):
    //   `runReduction (m <* simplifySystem) ctxt sys (avoid sys)`
    // The FreshT counter starts at `avoid sys` for EVERY proof step
    // (`avoid = maybe 0 (succ . snd) . boundsVarIdx`, LTerm.hs:656-657 —
    // 0 for a frees-less system such as a lemma's ROOT step, else
    // max idx + 1; `avoid_fresh_state` mirrors that exactly).
    // Without this, Rust's Maude counter advances monotonically across all
    // proof steps — so witness idxs grow to hundreds where HS stays in
    // the ~20-30 range.  Beyond cosmetics, the unbounded growth surfaces
    // SubstVFresh same-target collisions: when a variant's lifted witness
    // gets a target idx that collides with another raw entry's target,
    // the collision pattern encodes an unintended unification that
    // cascades downstream (KAS_key_secrecy: `~ltkA.0` and `~ltkA.349`
    // both → `~ltkA.425` after lifting forces $R=$I via setNodes merge).
    let avoid = crate::constraint::solver::reduction::avoid_fresh_state(sys);
    ctx.maude.reset_counter_to(avoid);

    let dbg_sua = tamarin_utils::env_gate!("TAM_RS_DBG_SUA");
    if dbg_sua {
        let mname = match method {
            ProofMethod::Sorry(_) => "Sorry",
            ProofMethod::Finished(_) => "Finished",
            ProofMethod::Invalidated => "Invalidated",
            ProofMethod::RawSolve(_) => "RawSolve",
            ProofMethod::Simplify => "Simplify",
            ProofMethod::Induction => "Induction",
            ProofMethod::SolveGoal(_) => "SolveGoal",
        };
        eprintln!("[EXECPM] enter method={} goals={} nodes={} avoid={}",
            mname, sys.goals.iter().count(), sys.nodes.iter().count(), avoid);
    }
    let _execpm_exit = if dbg_sua {
        struct ExitLog(std::time::Instant);
        impl Drop for ExitLog {
            fn drop(&mut self) {
                eprintln!("[EXECPM] exit after {:?}", self.0.elapsed());
            }
        }
        Some(ExitLog(std::time::Instant::now()))
    } else { None };

    match method {
        ProofMethod::Sorry(_) | ProofMethod::Finished(_) => Some(Vec::new()),
        ProofMethod::Invalidated | ProofMethod::RawSolve(_) => None,
        ProofMethod::Simplify => {
            // HS-faithful: `simplifySystem` (Simplify.hs:65-67) emits
            // its `traceExecM "simplifySystem"` ONCE per call; its
            // internal `go`-loop runs CR-rules to a fixpoint without
            // re-tracing.  We mirror that by tracing here (the logical
            // invocation site) and leaving `simplify_system` un-traced,
            // so the outer fixpoint loop below doesn't duplicate the
            // line.
            crate::constraint::solver::trace::trace_exec("simplifySystem");
            // HS-faithful simplify-time fan-out.  When
            // `solveUniqueActions` calls `solveGoal (ActionG i fa)`,
            // the `Reduction = StateT System (FreshT (DisjT ...))`
            // monad lets `disjunctionOfList` (over source-cases /
            // variants / Maude unifiers) fan out the entire enclosing
            // `simplifySystem` into N branches — one per fan-out case.
            // Each branch continues independently through the rest of
            // the simplify loop and post-loop, and surfaces here as a
            // sibling `Simplify` case.  HS's `process` then renders
            // them as `case 1`/`case 2`/... via `distinguish n`.
            //
            // Without fan-out, RS collapses 7 HS siblings to 1 on
            // Yubikey's `no_replay` (and 50 → 1 on
            // `slightly_weaker_invariant`), because `solve_action_goal`'s
            // Cases outcome was discarded.
            let case_systems: Vec<System> =
                crate::constraint::solver::simplify::simplify_system_with_fanout(ctx, sys.clone());
            // No-op shortcut: mid-proof, every case system was already
            // simplified+cleaned at production, so `simplifySystem` usually
            // fixpoints immediately — one output case value-equal to the
            // input.  The arm's remaining work is then fully determined:
            // the is_false filter drops the case (empty case-map => Simplify
            // succeeds with zero cases, see below) or, `cleanup` being a
            // pure function of the System value, `cleaned[0] ==
            // cleaned_input` holds and the single-case check returns None.
            // Skipping straight to those answers elides two full
            // `rename_precise` passes, a System clone, and the final O(S)
            // compare per open node (Simplify is ranked first at EVERY
            // node).  The value compare is cheap on the hit path: a no-op
            // simplify never triggered COW, so the Arcs are shared and Term
            // eq takes the ptr fast path.  `TAM_RS_NO_SIMP_NOOP_SKIP=1`
            // disables the shortcut (A/B oracle); `TAM_RS_SIMP_NOOP_STATS=1`
            // reports the hit rate.
            if !tamarin_utils::env_gate!("TAM_RS_NO_SIMP_NOOP_SKIP")
                && case_systems.len() == 1
                && case_systems[0] == *sys
            {
                simp_noop_stat(true);
                return if sys.eq_store.is_false() { Some(Vec::new()) } else { None };
            }
            simp_noop_stat(false);
            // HS-faithful `cleanup` (ProofMethod.hs): EVERY
            // proof method's cases pass through `map (fmap cleanup .
            // fst)`, and `Simplify` goes through `process` — so its
            // output is ALSO cleaned.
            let cleanup = |s: &System| -> System {
                let mut s2 = s.clone();
                crate::constraint::solver::rename_precise::rename_precise_system(
                    &mut s2);
                s2.eq_store_mut().subst =
                    tamarin_term::subst::Subst::from_list(Vec::new());
                s2
            };
            // HS-faithful filter: cases whose eq_store is false were
            // mzero'd by `contradictoryIf` during simplify; they don't
            // show up in HS's surviving Disj.  (Other contradiction
            // reasons surface as explicit Finished(Contradictory) leaves.)
            let cleaned: Vec<System> = case_systems.into_iter()
                .filter(|s| !s.eq_store.is_false())
                .map(|mut s| {
                    // HS-faithful `cleanup` (ProofMethod.hs) applied in
                    // place: `case_systems` is owned here (from
                    // `simplify_system_with_fanout`'s into_iter), so we
                    // rename and clear the subst on the owned System
                    // directly.  Value-identical to `cleanup(&s)`; that
                    // closure only clones because its callers hand it a
                    // `&System` (the borrowed `cleanup(sys)` site below).
                    crate::constraint::solver::rename_precise::rename_precise_system(
                        &mut s);
                    s.eq_store_mut().subst =
                        tamarin_term::subst::Subst::from_list(Vec::new());
                    s
                })
                .collect();
            // HS-faithful `removeRedundantCases ctxt [] snd`
            // (ProofMethod.hs `process`): applies it to EVERY proof
            // method's Disj fan-out, including `Simplify` (which uses
            // `process (return "")`).
            // When `simplifySystem`'s `solveUniqueActions` fans out an action
            // whose AC-multiset unification yields several unifiers that
            // are equal up to variable renaming (e.g. alethea's
            // `Learn_A_Ys(A,S,<'ys',<y1,no1>++<y2,no2>>)` — the straight
            // vs swapped pairing), HS collapses them via
            // `compareSystemsUpToNewVars` to a SINGLE surviving case (no
            // top-level `case N`), whereas RS surfaced both as `case 1`/
            // `case 2`.  Gated on BP/MSet by `remove_redundant_cases`'s
            // own guard (HS short-circuits to `cases0` otherwise), and
            // empty stable_vars (HS passes `[]`).  Runs BEFORE the
            // single-case `sys' /= cleanup sys` check, matching HS's order
            // (the check inspects the post-dedup `M.toList cases`).
            let cleaned: Vec<System> =
                remove_redundant_cases_ctx(ctx, |s: &System| s, cleaned);
            // Empty case-map: `simplifySystem` mzero'd every branch (the
            // restriction / formula set is contradictory).  HS's `Simplify`
            // arm (ProofMethod.hs:421-427) inspects `M.toList cases`; the
            // empty list matches the `_ -> return cases` branch, so it
            // returns `Just M.empty` — Simplify SUCCEEDS with zero cases.
            // `proveSystemDFS` (Proof.hs:1034-1044, see line 1043) then takes Simplify as the
            // head method and builds a childless node, which `prettyProof`
            // (Proof.hs:1080-1101, see line 1084) renders as a `by simplify` leaf closing the
            // (exists-trace) proof.  Returning `None` here instead would
            // drop Simplify from the ranked list and let `Induction` win —
            // the divergence this arm must avoid.
            if cleaned.is_empty() { return Some(Vec::new()); }
            let cleaned_input = cleanup(sys);
            if cleaned.len() == 1 {
                // Single-case path: HS's `Simplify` arm (ProofMethod.hs)
                // checks whether the simplified system equals the cleaned
                // input — if so, the method "failed" and we return None.
                // Multi-case fan-out trivially can't satisfy that condition.
                if cleaned[0] == cleaned_input { return None; }
                return Some(vec![("".to_string(), cleaned.into_iter().next().unwrap())]);
            }
            // HS-faithful naming: `distinguish n` (ProofMethod.hs)
            // with empty case name renders as `show i` ("1", "2", "3", ...)
            // with NO `_case_` prefix and NO zero-padding (the `pad`
            // call only runs in the else branch when the prefix is
            // non-empty).
            //
            // Inner duplicate detection: HS's `M.fromListWith (error
            // "case names not unique")` plus `uniqueListBy` dedups
            // exact-name duplicates structurally; for our empty-name
            // case all siblings get unique numeric names so no real
            // dedup is needed.
            let out: Vec<(String, System)> = cleaned.into_iter()
                .enumerate()
                .map(|(i, s)| ((i + 1).to_string(), s))
                .collect();
            Some(out)
        }
        ProofMethod::SolveGoal(g) => {
            // State snapshot BEFORE dispatch — paired with HS's
            // `[STATE]` line in `Theory.Constraint.Solver.ProofMethod.solve`.
            // Emits the canonical open-goal / node set so we can see what
            // ranking decision was available at this proof step.
            crate::constraint::solver::trace::trace_state(sys);
            crate::constraint::solver::trace::trace_pick(g);
            let mut r = Reduction::new(ctx, sys.clone());
            let outcome = crate::constraint::solver::goals::dispatch_solve_goal(&mut r, g);
            // HS FreshT-threading (task #16): per-case branch counters for
            // the post-solve simplify continuation.  Single-case adoptions
            // already reset `r.maude`; multi-case outcomes recorded their
            // per-branch counters in `last_case_counters`.
            let goal_case_counters = std::mem::take(&mut r.last_case_counters);
            let adopted_counter = r.maude.fresh_counter_peek();
            // Run simplify after every goal-solving step — mirrors
            // Haskell's `m <* simplifySystem` pattern in `process`
            // (ProofMethod.hs).  Filter out cases that simplify
            // to a contradictory system — Haskell's Disj-monad does the
            // same via `mzero` on `contradictoryIf`, so contradictory
            // cases never make it into the children map.  This keeps
            // our proof tree the same shape as Haskell's: when every
            // case fires a contradiction, the SolveGoal node has 0
            // children (rendered as a leaf "by solve(...)" in Haskell
            // / "by contradiction /* closed */" in our normalised diff).
            //
            // Returns `Vec<System>` to surface simplify-time fan-out: when
            // `simplifySystem` internally fans out (via
            // `solveUniqueActions → solveAction → solveFactEqs SplitNow`
            // or any `insertFormula → insertAtom EqE → solveTermEqs
            // SplitNow` whose Maude AC unification returns multiple
            // arms), the DisjT-monad in HS's `runReduction` replicates
            // the case once per arm.  Our `simplify_system_with_fanout`
            // mirrors that, returning N systems.  Each is then cleaned
            // (renamePrecise + clear subst) per HS's `cleanup`.
            let simplify = |sys: System, seed: u64| -> Vec<System> {
                let raw_systems: Vec<System> =
                    crate::constraint::solver::simplify::simplify_system_with_fanout_seeded(
                        ctx, sys, seed);
                // Cleanup each surviving system per HS
                // `cleanup` (ProofMethod.hs):
                //   cleanup s = L.set sSubst emptySubst
                //                       (renamePrecise s)
                let mut out: Vec<System> = Vec::with_capacity(raw_systems.len());
                for mut s in raw_systems {
                    crate::constraint::solver::rename_precise::rename_precise_system(
                        &mut s);
                    if !s.eq_store.is_false() {
                        s.invalidate_max_var_idx_cache();
                        s.eq_store_mut().subst =
                            tamarin_term::subst::Subst::from_list(Vec::new());
                    }
                    out.push(s);
                }
                out
            };
            // Filter cases the same way Haskell's `runReduction` does:
            // when a CR-rule called `contradictoryIf` during simplify
            // (e.g. solveFactEqs / solveRuleEqs / solveSubstEqs hitting
            // an incompatible unification, or Maude returning the empty
            // unifier set on a sort/tag mismatch), the Disj entry for
            // that case becomes `mzero` and disappears.  In our port
            // these failures surface as `Contradiction::IncompatibleEqs`
            // (eq_store.is_false / sort-conflation / edge-tag mismatch).
            // We mirror Haskell by pruning only those cases.
            //
            // Cases with *other* contradictions (FormulasFalse, Cyclic,
            // NodeAfterLast, …) survive `runReduction` in Haskell and
            // are picked up by the next iteration's contradictions
            // check as explicit `Finished(Contradictory(_))` leaves.
            // Do *not* filter those here, or the proof tree loses
            // siblings whose contradiction reason Haskell renders.
            // Filter cases where the eq_store has been marked false.
            // This is the most-direct Haskell-faithful proxy for `mzero`
            // from `contradictoryIf` during simplify (the eq-store flips
            // to false when solveSubstEqs/solveTermEqs/solveFactEqs hit
            // an incompatible unification, or when Maude returns the
            // empty unifier set).  Other `Contradiction`-list signals
            // (sort-conflation, edge-fact-tag mismatch, Cyclic, …) are
            // post-simplify detections in our port — Haskell either
            // catches them earlier (before the case is even built) or
            // leaves them as explicit `Finished(Contradictory(_))`
            // leaves.  Mirror the latter shape by *not* filtering them.
            let keep = |sys: &System, name: &str| -> bool {
                let r = !sys.eq_store.is_false();
                let op = if r { "case_keep" } else { "case_drop" };
                crate::state_trace::emit_case(op, name, Some(g), sys);
                r
            };
            // HS-faithful: `processLabeled` (ProofMethod.hs:453-465) treats
            // EVERY `solveGoal` result UNIFORMLY — the solve yields ONE
            // `CaseName`, then `runReduction (m <* simplifySystem)` fans the
            // DisjT continuation out into N branches that ALL carry that same
            // name, after which `removeRedundantCases` + `uniqueListBy ...
            // distinguish` dedups and suffixes same-named survivors
            // (`_case_1`/`_case_2`/...).  A `Linear`/`LinearNamed` outcome is
            // therefore NOT special: it is simply a single-element case list
            // whose post-`simplify` fan-out must run through the very same
            // dedup+distinguish pipeline as `Cases`.  Normalise all three
            // outcomes to a `Vec<(name, System)>` and share the
            // dedup+distinguish pipeline.  Pushing each fanned-out system
            // with a bare, un-`distinguish`ed name would drop the `_case_N`
            // suffixes when a lone source-case fans out at simplify time —
            // e.g. Yubikey's `eventInitStuff...` premise, where 4
            // identically-named siblings would let the exists-trace DFS
            // commit to `otc=('one'++'zero')` (14 steps) instead of HS's
            // `_case_2` (`otc='zero'`, 10 steps).
            let cases: Vec<(String, System, u64)> = match outcome {
                GoalCases::Linear => vec![("".to_string(), r.sys, adopted_counter)],
                GoalCases::LinearNamed(name) => vec![(name, r.sys, adopted_counter)],
                GoalCases::Cases(cases) => cases.into_iter().enumerate()
                    .map(|(ci, (n, s))| {
                        let seed = goal_case_counters.get(ci).copied()
                            .unwrap_or(adopted_counter);
                        (n, s, seed)
                    })
                    .collect(),
                GoalCases::Contradictory => return Some(Vec::new()),
            };
            {
                    // De-duplicate identical case names by appending
                    // `_case_1`/`_case_2`/... — mirrors Haskell's
                    // `groupSortOn casName` printing convention
                    // (e.g. `R_1_case_1`, `R_1_case_2` for two
                    // distinct unifications against rule `R_1`).
                    //
                    // The dedup must run on the *kept* cases only.  If
                    // we count before `keep` and one of two `Create`
                    // cases gets dropped (e.g. eq_store false after
                    // simplify), we end up with a lone `Create_case_1`
                    // where Haskell shows a bare `Create` — a pure
                    // naming divergence with no proof-shape difference.
                    // So: simplify + keep first, then dedup the
                    // survivors.
                    //
                    // **Order preservation**: Vec<(name, sys)> output
                    // preserves the order from `dispatch_solve_goal`,
                    // which matches Haskell's `disjunctionOfList`
                    // iteration order (rule order in `joinAllRules`).
                    // simplify can fan out per case — flat-map.
                    let kept_raw: Vec<(String, System)> = cases.into_iter()
                        .flat_map(|(name, sys, seed)| {
                            // `TAM_RS_TRACE_CASE_SIMP=1`: bracket each
                            // per-case simplify so interleaved trace hooks
                            // (EDGES/SIMP_CONTRA/SET_NODES) attribute to a
                            // named case.
                            let dbg = tamarin_utils::env_gate!("TAM_RS_TRACE_CASE_SIMP");
                            if dbg {
                                eprintln!("[CASE_SIMP] begin name={} path={}",
                                    name,
                                    crate::constraint::solver::trace::case_path_string());
                            }
                            let systems = simplify(sys, seed);
                            let n_arms = systems.len();
                            let out: Vec<(String, System)> = systems.into_iter()
                                .filter(|s| keep(s, &name))
                                .map(|s| (name.clone(), s))
                                .collect();
                            if dbg {
                                eprintln!("[CASE_SIMP] end name={} arms={} kept={}",
                                    name, n_arms, out.len());
                            }
                            out
                        })
                        .collect();
                    // HS `process` (ProofMethod.hs) dedups cases
                    // ONLY via `removeRedundantCases ctxt [] snd` — gated
                    // on BP/MSet, comparing systems up-to-new-vars
                    // (Sources.hs).  There is no unconditional
                    // exact-(name,system) dedup: any surviving same-named
                    // cases are renamed by `uniqueListBy ... distinguish`
                    // (ProofMethod.hs) to `name_case_1`/`name_case_2`,
                    // never dropped.  Variant enumeration is threaded
                    // through SplitG by `reduction::rule_insts_with_constrs`,
                    // so each distinct variant arrives as its own
                    // RuleACInst case here.  Empty stable_vars (HS passes
                    // `[]`); the helper is a no-op outside BP/MSet.
                    // HS `uniqueListBy ... distinguish` — rename duplicate
                    // case names to `name_case_N`.
                    Some(process_cases(ctx, kept_raw))
            }
        }
        ProofMethod::Induction => {
            // Take the first formula and try `ginduct`.
            let fm = sys.formulas.first()?.clone();
            let (base, step) = match crate::guarded::ginduct(&fm) {
                Ok(p) => p,
                Err(_) => return None,
            };
            // HS-faithful: mirror Haskell's `induction` (ProofMethod.hs):
            //   induction (baseCase, stepCase) = do
            //     (caseName, caseFormula) <- disjunctionOfList
            //         [("empty_trace", baseCase), ("non_empty_trace", stepCase)]
            //     L.setM sFormulas (S.singleton caseFormula)
            //     return caseName
            // HS uses `setM` — direct field write into `sFormulas`, NOT
            // `insertFormula`.  Calling `insertFormula` here would route
            // through HS's GDisj insertion arm (`insertFormula`/`insert'`,
            // Reduction.hs) which adds the
            // empty DisjG goal to `sGoals`; HS's `reduceFormulas`
            // (Simplify.hs) filters by `reducibleFormula`
            // (Reduction.hs `reducibleFormula`) which returns False for `GDisj _`, so
            // an `empty_trace` formula `Disj([])` (gfalse) stays in
            // `sFormulas` untouched and never produces a DisjG goal —
            // `FormulasFalse` contradiction picks it up directly.
            // (Routing through insert_formula would insert the empty DisjG
            // goal at gsNr=0, shifting every subsequent gsNr in every
            // sibling branch and diverging from HS at the first insertGoal
            // call.)
            // HS `process . induction` (ProofMethod.hs:348-459, see line 428, 521-525):
            // `runReduction (induction <* simplifySystem)` under the DisjT
            // monad.  `simplifySystem` CAN fan out at induction time — a
            // step-case formula that `reduceFormulas` decomposes into
            // unique-action goals (e.g. eCK lemmas whose formula carries
            // several `Accept(...)` atoms, TAK1_eCK_like) makes
            // `solveUniqueActions` fan out over the AC unifiers of each
            // action.  An in-place `simplify_system` here would discard
            // that `Cases` outcome without marking the goal solved, so the
            // simplify fixpoint would re-solve the same action forever (the
            // TAK1 web proof-page spin, since `write_applicable_methods`
            // execs Induction while the batch search does not).
            // Route through `simplify_system_with_fanout` exactly like the
            // `Simplify` and `SolveGoal` arms.
            let cleanup = |s: &mut System| {
                crate::constraint::solver::rename_precise::rename_precise_system(s);
                s.invalidate_max_var_idx_cache();
                s.eq_store_mut().subst =
                    tamarin_term::subst::Subst::from_list(Vec::new());
            };
            // HS branch order: `disjunctionOfList [("empty_trace", base),
            // ("non_empty_trace", step)]` — base first, then step; each
            // branch's simplify sub-branches keep DisjT order (the same
            // order `simplify_system_with_fanout` returns, validated by the
            // `Simplify` arm's byte parity).
            let mut named: Vec<(String, System)> = Vec::new();
            for (name, fm_case) in [("empty_trace", base), ("non_empty_trace", step)] {
                // HS `induction` uses `setM sFormulas` — a direct field
                // write, NOT `insertFormula` (see the `insert_formula`
                // rationale above).
                let mut case_sys = sys.clone();
                case_sys.invalidate_max_var_idx_cache();
                case_sys.formulas_mut().clear();
                case_sys.formulas_mut().push(std::sync::Arc::new(fm_case));
                let sub_systems: Vec<System> =
                    crate::constraint::solver::simplify::simplify_system_with_fanout(
                        ctx, case_sys);
                for mut s in sub_systems {
                    // mzero'd branches (eq-store false) don't survive HS's
                    // Disj — same filter as the Simplify/SolveGoal arms.
                    if s.eq_store.is_false() { continue; }
                    // HS-faithful `cleanup` (ProofMethod.hs `process`):
                    // renamePrecise with an empty Precise supply + clear
                    // subst.  Without it the IH disjunction's free vars
                    // keep their high `.N` indices (e.g. `last(#z.7)`)
                    // instead of the canonical idx-0 form (`last(#z)`).
                    cleanup(&mut s);
                    named.push((name.to_string(), s));
                }
            }
            // HS `process` tail: `removeRedundantCases ctxt [] snd`
            // (BP/MSet-gated structural dedup, before naming) followed by
            // `uniqueListBy (comparing fst) id distinguish`
            // (ProofMethod.hs:462-463, see line 465, 527-532): singleton names stay bare;
            // duplicate groups get `<name>_case_<i>`.  (The empty-name
            // branch of `distinguish` is unreachable here — both
            // induction case names are non-empty.)
            Some(process_cases(ctx, named))
        }
    }
}

/// `checkAndExecProofMethod`: structurally validates the method
/// against `sys` before delegating to `exec_proof_method`. Mirrors
/// Haskell's pre-conditions:
///
/// - `Finished r` → `is_finished` must return a result with the same
///   reason kind.
/// - `Induction` → only valid on a fresh system with a single formula.
/// - `SolveGoal g` → `g` must be in `sys.goals`.
/// - `Simplify` / `Sorry` → always valid.
pub fn check_and_exec_proof_method(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> Option<Vec<(CaseName, System)>> {
    match method {
        ProofMethod::Finished(r) => {
            let actual = is_finished(ctx, sys)?;
            if !same_kind(r, &actual) { return None; }
        }
        ProofMethod::Induction => {
            // Direct port of Haskell `canApplyInduction` (ProofMethod.hs):
            //   guard (M.null sNodes); guard (S.null sSolvedFormulas);
            //   guard (M.null sGoals); (_, t) <- uncons sFormulas; guard (null t)
            // i.e. no nodes, no solved formulas, no open goals, exactly one
            // formula.  No gfalse check (do NOT call is_initial_system here).
            if !sys.nodes.is_empty() { return None; }
            if !sys.solved_formulas.is_empty() { return None; }
            if !sys.goals.is_empty() { return None; }
            if sys.formulas.len() != 1 { return None; }
        }
        ProofMethod::SolveGoal(g) => {
            if !sys.goals.iter().any(|(existing, _)| existing == g) { return None; }
        }
        ProofMethod::Simplify | ProofMethod::Sorry(_) | ProofMethod::Invalidated => {}
        ProofMethod::RawSolve(_) => return None,
    }
    exec_proof_method(ctx, method, sys)
}

fn same_kind(a: &Result, b: &Result) -> bool {
    matches!(
        (a, b),
        (Result::Solved, Result::Solved)
            | (Result::Unfinishable, Result::Unfinishable)
            | (Result::Contradictory(_), Result::Contradictory(_))
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        let candidates = [
            "/usr/local/bin/maude",
            "maude",
        ];
        for c in &candidates {
            if std::path::Path::new(c).exists() { return Some((*c).to_string()); }
        }
        None
    }

    fn ctx() -> Option<ProofContext> {
        let path = maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).ok()?;
        Some(ProofContext::new(h, Vec::new()))
    }

    #[test]
    fn empty_system_is_not_finished() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        assert!(is_finished(&ctx, &s).is_none(), "initial system shouldn't be finished");
    }

    #[test]
    fn solved_when_no_goals_and_subterms_done() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut s = System::empty();
        // Force the system out of its initial state by recording a
        // solved formula (Haskell `isInitialSystem` checks
        // `solved_formulas.is_empty() && no_gfalse`; setting one to
        // gtrue makes the system non-initial).
        s.solved_formulas_mut().push(std::sync::Arc::new(crate::guarded::gtrue()));
        // Add a placeholder node too so the structure is non-trivial.
        let nid = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
        use crate::rule::{
            IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
            RuleInfo, RuleACInst, Rule,
        };
        let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Test"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        let rule: RuleACInst = Rule::new(info, Vec::new(), Vec::new(), Vec::new());
        s.add_node(nid, rule);
        match is_finished(&ctx, &s) {
            Some(Result::Solved) => {}
            r => panic!("expected Solved, got {:?}", r),
        }
    }

    #[test]
    fn gfalse_formula_is_contradictory_not_unfinishable() {
        // HS `isFinished` (ProofMethod.hs) routes any
        // contradiction — including `gfalse ∈ sFormulas`
        // (`FormulasFalse`) — to `Contradictory`, BEFORE the
        // `null ogs && not stFinished => Unfinishable` arm.  A negated
        // false lemma collapses to `gfalse`, closes the branch as
        // Contradictory, and the prover reports `falsified - found
        // trace` (verified against the v1.13.0 binary on a minimal
        // `Setup() @ i ==> F` lemma).  This pins that routing so the
        // gfalse-in-formulas path can never be misread as Unfinishable.
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut s = System::empty();
        // gfalse in formulas makes the system non-initial AND yields a
        // `FormulasFalse` contradiction.
        s.formulas_mut().push(std::sync::Arc::new(crate::guarded::gfalse()));
        match is_finished(&ctx, &s) {
            Some(Result::Contradictory(Some(Contradiction::FormulasFalse))) => {}
            r => panic!("expected Contradictory(FormulasFalse), got {:?}", r),
        }
    }

    #[test]
    fn exec_sorry_is_empty_cases() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        let cases = exec_proof_method(&ctx, &ProofMethod::Sorry(None), &s).unwrap();
        assert!(cases.is_empty());
    }

    #[test]
    fn induction_on_open_formula_returns_none() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        // No formula → ginduct can't run.
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s);
        assert!(r.is_none());
    }

    #[test]
    fn induction_creates_two_cases() {
        let ctx = match ctx() { Some(c) => c, None => return };
        // Build a closed action-bearing formula:
        //   Ex k #i. Setup(k) @ #i
        // tracked as a guarded GGuarded::Ex with a single Action guard.
        use tamarin_parser::ast::{Atom, Fact, SortHint, Term, VarSpec};
        let mkvar = |n: &str, sort: SortHint| Term::Var(VarSpec {
            name: n.to_string(), idx: 0, sort, typ: None,
        });
        let action_atom = Atom::Action(
            Fact {
                persistent: false,
                annotations: Vec::new(),
                name: "Setup".into(),
                args: vec![mkvar("k", SortHint::Msg)],
            },
            mkvar("i", SortHint::Node),
        );
        let body = crate::guarded::Guarded::Conj(Vec::new());
        // Build with close_guarded so the binder's `k` and `i` are
        // properly substituted to `Bound` in the guard atom.
        let fm = crate::guarded::close_guarded(
            crate::guarded::Quant::Ex,
            vec![
                VarSpec { name: "k".into(), idx: 0, sort: SortHint::Msg, typ: None },
                VarSpec { name: "i".into(), idx: 0, sort: SortHint::Node, typ: None },
            ],
            vec![action_atom],
            body,
        );
        let mut s = System::empty();
        s.formulas_mut().push(std::sync::Arc::new(fm));
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s).expect("induction");
        // Two case names: empty_trace and non_empty_trace.
        assert_eq!(r.len(), 2);
        assert!(r.iter().any(|(n, _)| n == "empty_trace"));
        assert!(r.iter().any(|(n, _)| n == "non_empty_trace"));
    }

    #[test]
    fn check_solve_goal_rejects_unknown() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        // Goal not in sys.goals → check should fail.
        let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        let g = Goal::Action(v, f);
        let r = check_and_exec_proof_method(&ctx, &ProofMethod::SolveGoal(g), &s);
        assert!(r.is_none());
    }
}
