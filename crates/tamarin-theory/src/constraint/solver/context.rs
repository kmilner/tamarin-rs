// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Jannik Dreier, Hong-Thai Luu, Benedikt Schmidt, Kevin
//   Morio, Robert Künnemann, Felix Linker, "Pops" (github racoucho1u), Ralf
//   Sasse, Charlie Jacomme, Artur Cygan, Philip Lukert, Yavor Ivanov,
//   symphorien, "gilcu3" (github), "Nynko" (github), "ValentinYuri"
//   (github), Felix Yan, "Tom" (github BTom-GH), Katriel Cohn-Gordon, Jérôme
//   (github Azurios-git), Nick Moore, Adrian Dapprich, Cas Cremers,
//   Alexander Dax, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Maude/Parser.hs, lib/theory/src/ClosedTheory.hs,
//   lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Model/Fact.hs, lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Sapic.hs, lib/theory/src/Theory/Text/Parser.hs,
//   lib/theory/src/Theory/Tools/IntruderRules.hs,
//   lib/theory/src/Theory/Tools/LoopBreakers.hs,
//   lib/theory/src/Theory/Tools/RuleVariants.hs, src/Main/Mode/Intruder.hs,
//   src/Main/TheoryLoader.hs

//! Solver context — port of the `ProofContext` data type from
//! `Theory.Constraint.System`.
//!
//! The Haskell `ProofContext` is a fat record carrying every piece of
//! per-theory information the solver needs:
//!
//! - The underlying signature (with Maude handle).
//! - The protocol rules and their AC variants.
//! - Sources / case-distinctions used to bias goal solving.
//! - Heuristic / tactic configuration.
//! - Whether to use induction, whether diff mode is on, etc.
//!
//! The Rust port carries all of these, split across two structs: the
//! per-lemma / post-construction-mutable fields owned directly by
//! [`ProofContext`], and the immutable-after-build bundle
//! ([`ProofContextShared`]) held behind an `Arc` so a Maude-swap clone is
//! a refcount bump rather than a deep copy.

use tamarin_term::maude_proc::{MaudeHandle, MaudePool};

use crate::rule::IntrRuleAC;
use crate::theory::OpenProtoRule;

/// Read-only, immutable-after-build bundle of a `ProofContext`.
///
/// These fields are computed once at theory-load time (in
/// `ProofContext::new_with_restrictions_pool_forced`) and never
/// structurally mutated for the rest of the proof.  They are held
/// behind an `Arc<ProofContextShared>` on every `ProofContext` so that
/// [`ProofContext::with_swapped_maude`] — called once per child case at
/// every wide parallel search node — becomes an `Arc` refcount bump
/// instead of a deep clone of `full_sources` (whose `Source::clone`
/// deep-copies each case `System`, the biggest single cost on the
/// with-swapped-maude spine).
///
/// IMPORTANT — sharing vs cloning semantics:
///  * `ProofContext::clone` DEEP-COPIES this bundle (a fresh `Arc` with
///    cloned contents), so per-lemma clones (`template_ctx.clone()`) stay
///    fully independent — each lemma's `ensure_saturated` populates ITS
///    OWN `full_sources` cells under ITS OWN `typing_assumptions`, with
///    no cross-lemma contamination (byte-identical to the pre-Arc
///    behaviour).
///  * `with_swapped_maude` SHARES this bundle (`Arc::clone`).  Its clones
///    are created only DURING a lemma's proof search — after
///    `ensure_saturated` has run and set `saturate_state = Done` — so the
///    shared `full_sources` cells are already fully materialised and
///    read-only, and every shared clone's `ensure_saturated()` hits the
///    `Done => return` fast path (no re-forcing, no `InProgress` race).
///    Sharing therefore cannot change WHICH cases are computed or their
///    ORDER; it only avoids re-deep-copying identical read-only data.
#[derive(Debug)]
pub struct ProofContextShared {
    /// Special intruder rules — `Coerce`, `PubConstr`, `FreshConstr`,
    /// `ISend`, `IRecv` (and `IEquality` in diff mode). These let the
    /// solver discharge `KU(_)` / `KD(_)` goals that arise from
    /// `In(_)`-fact reasoning.
    pub intruder_rules: Vec<IntrRuleAC>,
    /// Precomputed unique sources — for each fact tag with exactly
    /// one producing rule, we cache the producer name. Lets goal
    /// solving short-circuit candidate enumeration.
    pub unique_sources: Vec<crate::constraint::solver::sources::UniqueSource>,
    /// Whether this is a diff-mode proof. Reserved for `--diff`
    /// (observational equivalence), which is not yet ported, so no code
    /// reads it to change behavior yet; it is the canonical carrier of
    /// diff-mode state.
    pub is_diff: bool,
    /// Precomputed source-case enumerations.  For each non-special
    /// protocol-fact tag, holds the disjunction of derivation cases
    /// computed once at theory-load time.  `solve_premise_goal`
    /// consults this cache before enumerating rules — finite, fixed
    /// cases let the search graft a precomputed subsystem rather than
    /// re-deriving it (and recursing through copy-rules ad infinitum).
    ///
    /// The `Vec` itself is assigned once at build; its `Source` cells
    /// are interior-mutable (`cases_cell: Mutex<…>`, `incomplete`) and
    /// filled per-lemma by `ensure_saturated` / the source cache BEFORE
    /// any `with_swapped_maude` fan-out (i.e. while the owning
    /// `ProofContext` uniquely holds this `Arc`).
    pub full_sources: Vec<crate::constraint::solver::sources::Source>,
    /// Theory-level restrictions (safety formulas), in guarded form.
    /// Mirrors Haskell's `pcRestrictions` — passed to `initialSource`
    /// so each precomputed source-case starts from a system with the
    /// restrictions installed as `sLemmas`.  Without this, restrictions
    /// like `True_is_true` never fire during precompute saturation,
    /// leaving spurious cases (e.g. Responder for `KU(senc)` in
    /// Pattern_matching::Responder_secrecy) that Haskell would have
    /// dropped via the restriction's implied-formula propagation.
    pub restrictions: Vec<crate::guarded::Guarded>,
    /// `pcTrueSubterm` — True iff every destructor rule has its
    /// RHS as a proper subterm of its LHS (`all isSubtermRule $
    /// filter isDestrRule $ intruder_rules`).  Mirrors Haskell's
    /// `_pcTrueSubterm` (System.hs:763) and gates the
    /// `has_impossible_chain` analysis: when True, only the chain-end
    /// root symbol is checked against the chain-start's possible
    /// decomposition root syms (a STRICTER test that fires more often);
    /// when False, all possible subterm syms of the chain-end are
    /// checked for intersection (a more LENIENT test).
    pub pc_true_subterm: bool,
    /// `saturate_state` — gates the lazy `ensure_saturated()` call.
    /// HS's `saturateSources` is lazy in `cdCases`: it only emits
    /// `[EXEC] solveGoal / exploitPrems / ...` traces when a consumer
    /// pattern-matches on a source's `cdCases` (forcing the thunk).
    /// To match, we defer the saturate run from `ProofContext::new`
    /// to the first `Source::cases(ctx)` call.  Sets to `Done` once
    /// run; subsequent calls no-op.  Lives here alongside the
    /// `full_sources` cells it guards so that a shared clone
    /// (`with_swapped_maude`) sees the same `Done` gate as the cells.
    pub(crate) saturate_state: std::sync::Mutex<SaturateState>,
    /// Cached saturation limit (from `IntegerParameters::default()`).
    pub(crate) saturation_limit: usize,
}

impl Clone for ProofContextShared {
    fn clone(&self) -> Self {
        let state = *self.saturate_state.lock().unwrap();
        ProofContextShared {
            intruder_rules: self.intruder_rules.clone(),
            unique_sources: self.unique_sources.clone(),
            is_diff: self.is_diff,
            full_sources: self.full_sources.clone(),
            restrictions: self.restrictions.clone(),
            pc_true_subterm: self.pc_true_subterm,
            saturate_state: std::sync::Mutex::new(state),
            saturation_limit: self.saturation_limit,
        }
    }
}

/// Minimum-viable context for the solver loop.
#[derive(Debug)]
pub struct ProofContext {
    pub maude: MaudeHandle,
    /// Optional pool of additional Maude subprocesses used at rayon
    /// parallel sites (rule-variant closure, saturate refinement) to
    /// avoid serialising every worker on the single `maude`'s internal
    /// IPC mutex.  `None` means "use the single `maude` only" (the
    /// original behaviour; byte-identical to `--processors=1`).
    ///
    /// HS uses a single Maude per ClosedTheory; this pool is a
    /// Rust-specific implementation improvement that doesn't change
    /// semantics — workers acquire a pool member at task start and
    /// reads/writes its own subprocess for the task's duration.  Each
    /// pool member's `with_fresh_counter_from(avoid_max)` still gives
    /// HS-faithful per-call witness allocation.
    pub maude_pool: Option<std::sync::Arc<MaudePool>>,
    /// All protocol rules in scope, including their AC variants.
    ///
    /// Kept as an owned field (NOT in [`ProofContextShared`]) because a
    /// handful of unit tests replace it after construction
    /// (`ctx.rules = vec![…]`); duty-3 keeps any post-construction-mutated
    /// field out of the shared bundle.
    pub rules: Vec<OpenProtoRule>,
    /// Whether the solver should attempt induction at the start of a
    /// proof. Mirrors Haskell's `pcUseInduction` flag.  Set per-lemma
    /// (`force_induction`), so owned rather than shared.
    pub use_induction: UseInduction,
    /// Set of fact tags whose instances we know to be uniquely
    /// identified by their first argument (the "injective" facts).
    /// Mirrors Haskell's `pcInjectiveFactInsts`.  Owned (not shared)
    /// because a few unit tests replace it after construction.
    pub injective_fact_insts: Vec<(crate::fact::FactTag,
        Vec<Vec<crate::tools::injective_fact_instances::MonotonicBehaviour>>)>,
    /// Set when the current proof is for an exists-trace lemma.
    /// Used by `is_finished` to decide whether the Fresh-conflation
    /// case-drop should convert Contradictory→Unfinishable: for
    /// exists-trace lemmas the dropped case might have been the
    /// witness path (sound only via Unfinishable); for all-traces
    /// lemmas the drop is harmless (no witness to lose).  Defaults
    /// to false; set by `prove_lemma` based on the lemma's
    /// trace-quantifier attribute (per-lemma, so owned).
    pub is_exists_trace: bool,
    /// The solved-leaf extraction strategy for this lemma's auto-prover,
    /// mirroring HS `apCut` (Theory/Proof.hs:702) threaded from
    /// `--stop-on-trace` (TheoryLoader.hs:356-360).  `Dfs` is the default
    /// (`fromMaybe CutDFS`); consumed once per lemma by `run_proof_search`
    /// (search.rs).  Per-lemma / theory-global, so owned.
    pub cut: CutStrategy,
    /// Pending typing assumptions (from `[sources]`-tagged lemmas)
    /// applied during `ensure_saturated`'s refinement step.  Set by
    /// `prove_lemma` before any source-case access; refinement is
    /// deferred to keep `ensure_saturated`'s trace emissions
    /// interleaved with the lemma proof's first source-case access
    /// (HS-faithful: `refineWithSourceAsms` operates on lazy `Source`
    /// thunks; its work only fires when a downstream consumer forces
    /// a `cdCases` thunk).  Per-lemma, so owned.
    pub typing_assumptions: Vec<crate::guarded::Guarded>,
    /// The goal ranking list for this lemma, mirroring HS's
    /// `Heuristic ProofContext = Heuristic [GoalRanking ProofContext]`
    /// (System.hs:522).  `None` ⇒ HS's `defaultHeuristic False`
    /// (`defaultRankings False = [SmartRanking False]`, System.hs:527).
    /// Resolved per-lemma in `prove_lemma`
    /// (per-lemma `[heuristic=..]` overrides the theory-level directive,
    /// matching `apDefaultHeuristic <|> pcHeuristic`).
    /// Round-robin scheduling: depth d → `rankings[d % n]`
    /// (ProofMethod.hs).  Per-lemma, so owned.
    pub heuristic: Option<Vec<crate::constraint::solver::goals::GoalRanking>>,
    /// The name of the lemma being proved.  Passed as `argv[1]` to
    /// the oracle script (HS `L.get pcLemmaName ctxt`, ProofMethod.hs).
    /// Per-lemma, so owned.
    pub lemma_name: String,
    /// Path to the theory file being proved.  Used to resolve the
    /// oracle script path as `takeDirectory theory_file </> oracle_rel_path`
    /// (HS Parser.hs:304, System.hs:574-575).  Stored as the absolute
    /// path passed to `--prove`.  Per-lemma, so owned.
    pub theory_file: String,
    /// The read-only, immutable-after-build bundle
    /// (`intruder_rules`, `unique_sources`, `full_sources`,
    /// `restrictions`, …).  Shared behind an `Arc` so
    /// [`ProofContext::with_swapped_maude`] is a refcount bump rather
    /// than a deep clone.  Field access to the bundle's members is
    /// transparent via the [`std::ops::Deref`] impl below, so call
    /// sites keep writing `ctx.full_sources`, `ctx.intruder_rules`, ….
    pub shared: std::sync::Arc<ProofContextShared>,
}

/// Transparent read access to the shared bundle: `ctx.full_sources`,
/// `ctx.intruder_rules`, `ctx.restrictions`, `ctx.is_diff`,
/// `ctx.pc_true_subterm`, `ctx.saturate_state`, `ctx.saturation_limit`,
/// and `ctx.unique_sources` all resolve here.  We deliberately do NOT
/// implement `DerefMut`: the shared bundle is immutable-after-build, and
/// the few build-time / per-lemma writes go through `Arc::get_mut` on a
/// uniquely-owned `Arc` (see the constructor and the source-cache
/// restore in `prove.rs`).
impl std::ops::Deref for ProofContext {
    type Target = ProofContextShared;
    fn deref(&self) -> &ProofContextShared {
        &self.shared
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SaturateState { Pending, InProgress, Done }

impl Clone for ProofContext {
    /// DEEP clone: the owned fields are cloned by value and the shared
    /// bundle is re-materialised into a FRESH `Arc` (`Arc::new(…clone)`),
    /// NOT refcount-bumped.  This keeps per-lemma clones
    /// (`template_ctx.clone()`) fully independent — byte-identical to the
    /// pre-Arc behaviour — so each lemma saturates its own
    /// `full_sources` under its own `typing_assumptions`.  The cheap
    /// refcount-bump form lives only in [`Self::with_swapped_maude`].
    fn clone(&self) -> Self {
        ProofContext {
            maude: self.maude.clone(),
            maude_pool: self.maude_pool.clone(),
            rules: self.rules.clone(),
            use_induction: self.use_induction,
            injective_fact_insts: self.injective_fact_insts.clone(),
            is_exists_trace: self.is_exists_trace,
            cut: self.cut,
            typing_assumptions: self.typing_assumptions.clone(),
            heuristic: self.heuristic.clone(),
            lemma_name: self.lemma_name.clone(),
            theory_file: self.theory_file.clone(),
            shared: std::sync::Arc::new((*self.shared).clone()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseInduction { UseInduction, AvoidInduction }

/// How the auto-prover cuts the proof tree around solved leaves,
/// mirroring HS `SolutionExtractor` (Theory/Proof.hs:695) as selected
/// by `runAutoProver` (Theory/Proof.hs:736-741).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CutStrategy {
    /// HS `CutDFS` → `cutOnSolvedDFS` (Theory/Proof.hs:856-886): parallel
    /// iterative-deepening DFS, doubling `dMax` from 4.  Selects the leftmost
    /// (preorder, CaseName order) solved leaf among those shallower than the
    /// first `dMax` (4, 8, 16, …) to admit any solved leaf — within that
    /// depth bucket a deeper-but-leftmost leaf beats a shallower one further
    /// right, so this is NOT globally-shallowest.  The default when
    /// `--stop-on-trace` is absent
    /// (HS `constructAutoProver`: `fromMaybe CutDFS`, TheoryLoader.hs:705).
    Dfs,
    /// HS `CutSingleThreadDFS` → `cutOnSolvedSingleThreadDFS`
    /// (Theory/Proof.hs:795-816): single-thread depth-first with NO depth
    /// bound and NO iterative deepening.  `findSolved`'s `foldMap` over the
    /// children map descends the leftmost branch (CaseName order) to
    /// completion before its siblings and stops at the first solved leaf, so
    /// a deep solved leaf under the leftmost branch wins over a shallower one
    /// further right even when the shallower leaf sits inside `Dfs`'s first
    /// depth bucket (where `Dfs` would cut the deep branch off and pick it).
    SeqDfs,
    /// HS `CutBFS` → `cutOnSolvedBFS` (Theory/Proof.hs:930-957): iterative
    /// level-deepening over the DFS proof tree.  At each level `l` the tree
    /// is forced to depth `l` and walked in CaseName order with threaded
    /// state: a Solved leaf at exactly depth `l` flips TraceFound; a node
    /// still pending at depth `l` is cut to `sorry /* bound reached */`
    /// (`sorry /* ignored (attack exists) */` once TraceFound).  On
    /// TraceFound the CUT tree is the result — those sorry leaves are part
    /// of the printed proof; a level that completes with nothing pending
    /// returns the full tree unchanged.
    Bfs,
    /// HS `CutNothing` → `id` (Theory/Proof.hs:740): no cut at all — the
    /// full proof tree is built and printed; sibling exploration does not
    /// stop when a trace is found.
    Nothing,
    /// HS `CutAfterSorry` → `cutAfterFirstSorry` (Theory/Proof.hs:989-999):
    /// preorder walk in CaseName order; the first `Sorry` or Solved leaf
    /// aborts, and every node visited after the abort becomes a bare
    /// `sorry` leaf (children dropped, system annotation kept).  Under the
    /// unbounded default prover the only aborter is a Solved leaf, so this
    /// reads as "stop at the first trace, sorry out the remainder".
    AfterSorry,
}

impl ProofContext {
    pub fn new(maude: MaudeHandle, rules: Vec<OpenProtoRule>) -> Self {
        Self::new_with_restrictions(maude, rules, Vec::new())
    }

    /// Cheap clone with `maude` replaced.  Used at the rayon parallel
    /// sites where each worker wants its own subprocess (acquired from
    /// `maude_pool`) for the duration of one task, so workers don't
    /// serialise on a single Maude's IPC mutex.
    ///
    /// This is an `Arc` refcount bump of the read-only bundle
    /// ([`ProofContextShared`] — `full_sources`, `intruder_rules`,
    /// `unique_sources`, `restrictions`, …), NOT a deep clone.  A deep
    /// clone would re-copy every read-only `Vec` — notably each
    /// `Source`'s `cases_cell` (a `Mutex<Option<Vec<(Vec<String>,
    /// System)>>>`, each `System` heavy) — once per child case inside
    /// `cases.into_par_iter()` in search.rs, the top `System::clone`
    /// cost on this spine; the `Arc` bump avoids that.
    /// Sharing is safe here: `with_swapped_maude` clones are created only
    /// DURING a lemma's proof search — after `ensure_saturated` has run
    /// and set `saturate_state = Done` — so the shared `full_sources`
    /// cells are already materialised and read-only, and every clone's
    /// `ensure_saturated()` hits the `Done => return` fast path.  See
    /// [`ProofContextShared`] for the full sharing-vs-cloning argument.
    ///
    /// The small owned fields (`rules`, `injective_fact_insts`,
    /// per-lemma `typing_assumptions` / `heuristic` / names) are still
    /// cloned by value, exactly as before.
    ///
    /// The new context drops `maude_pool` (set to None): the worker
    /// already owns a per-task subprocess for the task's duration, and
    /// dropping the pool here keeps the nested fan-out (`search.rs`) on
    /// its non-blocking `try_acquire` + `ctx.maude` fallback, which is
    /// what prevents deadlock when the pool is smaller than the rayon
    /// worker count.
    pub fn with_swapped_maude(&self, maude: MaudeHandle) -> Self {
        ProofContext {
            maude,
            maude_pool: None,
            rules: self.rules.clone(),
            use_induction: self.use_induction,
            injective_fact_insts: self.injective_fact_insts.clone(),
            is_exists_trace: self.is_exists_trace,
            cut: self.cut,
            typing_assumptions: self.typing_assumptions.clone(),
            heuristic: self.heuristic.clone(),
            lemma_name: self.lemma_name.clone(),
            theory_file: self.theory_file.clone(),
            shared: std::sync::Arc::clone(&self.shared),
        }
    }

    /// HS-faithful lazy `saturateSources` (Sources.hs:373).  Runs at
    /// most once per `ProofContext`: forces `initial_source_cases`
    /// for each source in `full_sources`, then drives
    /// `saturate_sources_with_simp` to convergence.  Subsequent
    /// calls no-op via the `saturate_state` flag.
    ///
    /// Triggered by `Source::cases(ctx)` on first force.  Trivial
    /// protocols whose lemma proofs never pattern-match on source
    /// cases (e.g. Var-headed `KU(t:Fresh)` source on an existence
    /// lemma) never call this, so zero saturate-time `[EXEC]` lines
    /// fire — matching HS's lazy-thunk behaviour.
    pub fn ensure_saturated(&self) {
        {
            let mut state = self.saturate_state.lock().unwrap();
            match *state {
                SaturateState::Done => return,
                SaturateState::InProgress => {
                    // Re-entrant call from inside saturate's own
                    // source-case grafting.  Return without re-running
                    // — the caller sees the partially-populated cells,
                    // matching HS's lazy fix-point semantics where
                    // iteration N forces iteration N-1's cached value.
                    return;
                }
                SaturateState::Pending => {
                    *state = SaturateState::InProgress;
                }
            }
        }
        // HS-FAITHFUL PURITY: source refinement (`precomputeSources` /
        // `saturateSources` / `refineWithSourceAsms`, Sources.hs) is a PURE
        // `[Source] -> [Source]` computation with LOCAL `evalFresh (avoid
        // goalTerm)` scopes — it does NOT thread the per-proof `MonadFresh`
        // counter.  Each proof step independently resets fresh to `avoid sys`
        // (ProofMethod.hs:457 `runReduction (m <* simplifySystem) ctxt sys
        // (avoid sys)`), and source cases are re-freshened on apply.  RS's
        // saturation, by contrast, advances the shared `maude` counter while
        // computing cases; that advance is HS-invisible and its magnitude is
        // parallelism- and source-structure-dependent (large for SAPiC state
        // facts), which leaks into the proof when the cache skips/replays it.
        // Snapshot the counter and restore it after saturation so the refine
        // is counter-neutral exactly as in HS — making the post-saturation
        // counter (hence cache reuse vs recompute) byte-identical regardless.
        let saturate_cnt_before = self.maude.fresh_counter_peek();
        // Pre-populate every source's cell with `Some(vec![])` BEFORE
        // running `initial_source_cases` on any of them.  This breaks
        // the recursion: when `initial_source_cases` for source A
        // calls `solve_with_source_cases_action` against source B
        // (forcing B.cases() recursively), B's cell is already
        // `Some(empty)`, so the recursive call returns empty rather
        // than re-entering `initial_source_cases` for B.  After this
        // pass we run the second pass that fills each cell with the
        // actual unsaturated `initialSource` cases — HS's `mapM`
        // over the lazy list under the iterative fix-point.
        for src in &self.full_sources {
            if src.cases_cell.lock().unwrap().is_none() {
                src.cases_set(Vec::new());
            }
        }
        for src in &self.full_sources {
            let init = crate::constraint::solver::sources::initial_source_cases_pub(
                &src.goal, self);
            src.cases_set(init);
        }
        // HS-faithful `saturate_sources_with_simp` (mirrors HS's
        // `saturateSources` driven by `solveAllSafeGoals` as the
        // proofStep): each iteration performs HS's per-step
        // `insertEdges`/`solveTermEqs`/`exploitPrems` work, so the
        // emitted trace matches HS's saturation rather than collapsing
        // it into a single graft operation.
        let raw: Vec<crate::constraint::solver::sources::Source> =
            self.full_sources.to_vec();
        let saturated = crate::constraint::solver::sources::saturate_sources_with_simp_public(
            raw, self.saturation_limit, self);
        // HS-faithful: apply `refineWithSourceAsms` AFTER saturate.
        // HS does this lazily — `refineWithSourceAsms` produces
        // updated `Source` thunks that only fire their inner saturate
        // when forced.  We approximate by running both inside
        // `ensure_saturated` (which itself is lazy at the first
        // `cases(ctx)` call), so the refinement traces still
        // interleave with the lemma proof's first source-case access
        // rather than firing during `prove_lemma` setup.
        let refined = if self.typing_assumptions.is_empty() {
            saturated
        } else {
            crate::constraint::solver::sources::refine_with_source_asms(
                saturated, &self.typing_assumptions, self)
        };
        // Match saturated sources back to originals BY GOAL.  Saturate
        // may drop sources whose cases all `mzero` during `refineSource`
        // (HS's `runReduction proofStep ctxt se fs` returns Disj.empty),
        // so the saturated list can be SHORTER than `full_sources`.  HS
        // keeps `cdGoal` stable across saturate iters (only `cdCases`
        // changes), so `cdGoal` is the join key.
        for orig in &self.full_sources {
            let sat = refined.iter().find(|s| s.goal == orig.goal);
            // HS-faithful: `saturateSources` (Sources.hs:498) keeps ONE
            // source per input (`set cdCases newCases th`), so every
            // `orig.goal` has a match in `refined` — including sources whose
            // refine produced ZERO cases (the case list is just empty).  We
            // overwrite the cell with the refined cases (possibly empty),
            // matching HS's `cdCases = []` for goals with no source (e.g. the
            // builtin destructors `check_rep`/`get_rep`).  The `if let Some`
            // remains a defensive guard: should a future refine path ever
            // drop a source from the list, we leave the initial cases rather
            // than blanking an unrelated cell — but on the HS-faithful path
            // the match always succeeds.
            if let Some(s) = sat {
                orig.cases_set(s.cases_or_empty());
            }
        }
        // Restore the fresh counter to its pre-saturation value (see the
        // HS-FAITHFUL PURITY note above): the refine consumed idxs only for
        // the stored cases, which are re-freshened from `avoid(live_sys)` on
        // every apply, so the global counter must not retain the advance.
        self.maude.reset_counter_to(saturate_cnt_before);
        *self.saturate_state.lock().unwrap() = SaturateState::Done;
    }

    /// Mark this context's sources as already saturated, bypassing the
    /// `ensure_saturated` pass.  Used by the session-level refined-source
    /// cache (lever #3): when the cases have been restored from a sibling
    /// lemma's identical computation, set the state to `Done` so later
    /// `cases(ctx)` calls read the restored cells directly instead of
    /// re-running the (expensive) `saturate_sources_with_simp` pass.
    pub fn mark_saturated_done(&self) {
        *self.saturate_state.lock().unwrap() = SaturateState::Done;
    }

    /// Variant that accepts the theory-level restrictions.  Mirrors
    /// Haskell's `precomputeSources parameters ctxt restrictions`
    /// which threads restrictions into each `initialSource`'s system
    /// via `insertLemmas`.  Restrictions then fire on rule actions
    /// during saturate, dropping cases that violate them — e.g.
    /// `True_is_true` on Responder's `IsTrue(z)` action drops the
    /// Responder case for `KU(senc(...))` in Pattern_matching.
    pub fn new_with_restrictions(
        maude: MaudeHandle,
        rules: Vec<OpenProtoRule>,
        restrictions: Vec<crate::guarded::Guarded>,
    ) -> Self {
        Self::new_with_restrictions_and_pool(maude, None, rules, restrictions)
    }

    /// Like [`new_with_restrictions`] but also installs a
    /// `MaudePool` on the constructed context so the precompute /
    /// saturate phase (which happens INSIDE this constructor via
    /// `precompute_full_sources`) can dispatch work across the pool
    /// rather than serialising on the single shared Maude.
    ///
    /// Callers without a pool should keep calling
    /// `new_with_restrictions` — the precompute will use the single
    /// `maude` for every parallel task, which is correct (just
    /// contended).
    pub fn new_with_restrictions_and_pool(
        maude: MaudeHandle,
        maude_pool: Option<std::sync::Arc<MaudePool>>,
        rules: Vec<OpenProtoRule>,
        restrictions: Vec<crate::guarded::Guarded>,
    ) -> Self {
        Self::new_with_restrictions_pool_forced(maude, maude_pool, rules, restrictions, &[])
    }

    /// HS-faithful assembly of the intruder-rule cache
    /// (`addMessageDeductionRuleVariants`, TheoryLoader.hs:776-791): subterm
    /// rules, per-rule `closeIntrRule`, special rules, then the theory-specific
    /// Nat/MSet/Xor/DH/BP variants — all in HS order.  Depends only on `sig`
    /// and `maude`.
    ///
    /// Order: subterm rules FIRST, then special rules.  Mirrors
    /// Haskell's `addMessageDeductionRuleVariants` (TheoryLoader.hs:784-789):
    ///     rules = subtermIntruderRules False msig
    ///          ++ specialIntruderRules False
    ///          ++ ...
    /// The ORDER MATTERS for solveAction's `disjunctionOfList rules` —
    /// a `KU(aenc(t1,t2))` goal is matched against c_aenc BEFORE
    /// coerce, producing cdCases = [c_aenc, coerce] instead of
    /// [coerce, c_aenc].  This downstream determines which case
    /// applies first in the proof renderer (e.g. NSPK3 injective_agree
    /// picks `case c_aenc` like Haskell does).
    fn assemble_intruder_rules(
        sig: &tamarin_term::maude_sig::MaudeSig,
        maude: &MaudeHandle,
    ) -> Vec<IntrRuleAC> {
        let mut intruder_rules = crate::intruder_rules::subterm_intruder_rules(false, sig);
        // HS-faithful: run `closeIntrRule` over EACH intr rule BEFORE
        // `special_intruder_rules` are appended.  Mirrors Haskell
        // `Rule.closeRuleCache` (lib/theory/src/Rule.hs:160):
        //     intrRulesAC = concat $ map (closeIntrRule hnd) intrRules
        //
        // `closeIntrRule` does two things:
        //   (a) For `DestrRule subterm=True` it computes the per-rule
        //       `paciRemainingApplications` budget (number of consecutive
        //       chain applications).
        //   (b) For `DestrRule subterm=False` (convergent-equation
        //       destructors like `d_0_comb` in issue216) it invokes
        //       `variantsIntruder` to enumerate Maude variants and add
        //       them to the pool.  Without this, the chain pool for
        //       issue216 has `nRules=6` instead of HS's `nRules=9`, and
        //       all 4 issue216 lemmas fail to close.
        //
        // Per HS, `closeIntrRule` runs AFTER `minimizeIntruderRules`
        // (already done inside `subterm_intruder_rules`) and BEFORE the
        // `special_intruder_rules` append (since HS appends specials
        // separately in `addMessageDeductionRuleVariants`).
        intruder_rules = intruder_rules.into_iter()
            .flat_map(|ir| crate::intruder_rules::close_intr_rule(maude, &ir))
            .collect();
        intruder_rules.extend(crate::intruder_rules::special_intruder_rules(false));
        // HS-faithful: theory-specific intruder rules (Nat, MSet, Xor) —
        // port of `Main.TheoryLoader.addMessageDeductionRuleVariants`
        // (src/Main/TheoryLoader.hs:786-789):
        //
        // ```haskell
        // rules =
        //   subtermIntruderRules False msig
        //   ++ specialIntruderRules False
        //   ++ (if enableNat  msig then natIntruderRules     else [])
        //   ++ (if enableMSet msig then multisetIntruderRules else [])
        //   ++ (if enableXor  msig then xorIntruderRules     else [])
        // ```
        //
        // For nat: the single `nat` constructor
        // `[] --[ KU(%x) ]-> [ KU(%x) ]` (natIntruderRules,
        // IntruderRules.hs:113-120).  Without it the precomputed
        // source-cases for nat-sorted `KU` goals are empty ("0 cases"
        // where HS shows the `nat` source) and the `/main/message`
        // page omits the rule.  Ordered between special and mset as in
        // the HS list above.
        if sig.enable_nat {
            intruder_rules.extend(crate::intruder_rules::nat_intruder_rules());
        }
        // For multiset: adds `_union` destructor (`KD(x++y) → KD(x)`,
        // subterm=True, budget=0) and `_union` constructor.  Without these,
        // the precomputed `KU(t)` source-cases miss the chain-extension
        // path through union-decomposition, causing `hasImpossibleChain`
        // to fire on legitimate chains from `KD(t1++t2)` to `KD(t1)`.
        // Root cause of the `minimal_multiset::Reachable`/`issue519` cluster.
        if sig.enable_mset {
            intruder_rules.extend(crate::intruder_rules::multiset_intruder_rules());
        }
        // XOR intruder rules — port of HS `xorIntruderRules`
        // (IntruderRules.hs:345-349) wired in `addMessageDeduction
        // RuleVariants` (TheoryLoader.hs:790).  Two destructor rules
        // for XOR cancellation (KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z) and
        // KD(x⊕y) ∧ KU(y) → KD(x)), one constructor (KU(x⊕y) from
        // KU(x), KU(y)), plus the `zero` constructor.  Without
        // these every XOR-using theory was unsound: the canonical
        // adversary attack `(x⊕y) ⊕ y = x` was unreachable, so
        // `xor.spthy::Secret` and all `recentalive_tag`-style lemmas
        // wrongly verified.  Mirrors HS's enableXor branch.
        if sig.enable_xor {
            intruder_rules.extend(crate::intruder_rules::xor_intruder_rules());
        }
        // DH / BP intruder variants — port of HS
        // `Main.TheoryLoader.addMessageDeductionRuleVariants`
        // (src/Main/TheoryLoader.hs:776-791):
        //
        // ```haskell
        // addMessageDeductionRuleVariants thy0
        //   | enableBP msig = addIntruderVariants
        //                       [mkDhIntruderVariants, mkBpIntruderVariants]
        //   | enableDH msig = addIntruderVariants [mkDhIntruderVariants]
        //   | otherwise     = thy
        // ```
        //
        // HS's `mkDhIntruderVariants` (TheoryLoader.hs:766-769)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`
        // (Template-Haskell `embedFile`), not the runtime
        // `dhIntruderRules` generator.  HS's `Main.Mode.Intruder.run`
        // is what PRODUCES that cache file in the first place
        // (Main/Mode/Intruder.hs:48), but the production theory-load
        // path always reads the cache.
        //
        // The cached-file parser (`mk_dh_intruder_variants` /
        // `mk_bp_intruder_variants` from `crate::intruder_variants`)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`,
        // matching HS's `mkDhIntruderVariants` (TheoryLoader.hs:766-769)
        // and making us mechanism-identical to HS.  The runtime
        // generator (`dh_intruder_rules`) is retained as the regenerator
        // (callable when one wants to refresh the cache from local
        // Maude); a bridge test in `intruder_variants.rs` flags any
        // divergence.
        //
        // Ordering matches HS exactly: DH BEFORE BP, both AFTER
        // subterm + special rules.  When BP is enabled HS adds DH
        // FIRST (the list `[mkDhIntruderVariants, mkBpIntruderVariants]`
        // — TheoryLoader.hs:777).
        if sig.enable_bp {
            intruder_rules.extend(
                crate::intruder_variants::mk_dh_intruder_variants(sig)
            );
            intruder_rules.extend(
                crate::intruder_variants::mk_bp_intruder_variants(sig)
            );
        } else if sig.enable_dh {
            intruder_rules.extend(
                crate::intruder_variants::mk_dh_intruder_variants(sig)
            );
        }
        intruder_rules
    }

    /// Like [`new_with_restrictions_and_pool`] but also unions the FORCED
    /// injective fact tags into `injective_fact_insts` BEFORE source
    /// precomputation — mirroring HS `closeRuleCache` (Rule.hs:147-157), where
    /// `injFactInstances` (forced ∪ simple) seeds `ctxt0`, which then drives
    /// `precomputeSources`.  Used for the SAPIC state-channel optimisation
    /// (`setforcedInjectiveFacts {L_PureState, L_CellLocked}`, Sapic.hs:84).
    pub fn new_with_restrictions_pool_forced(
        maude: MaudeHandle,
        maude_pool: Option<std::sync::Arc<MaudePool>>,
        mut rules: Vec<OpenProtoRule>,
        restrictions: Vec<crate::guarded::Guarded>,
        forced_injective_facts: &[crate::fact::FactTag],
    ) -> Self {
        // Inherit the maude signature from the handle so we can
        // synthesise per-symbol construction rules.
        let sig = maude.maude_sig();
        let intruder_rules = Self::assemble_intruder_rules(&sig, &maude);
        // Detect injective fact instances ahead of time — mirrors
        // Haskell's `pcInjectiveFactInsts` precomputation.
        let proto_rules: Vec<crate::rule::ProtoRuleE> = rules.iter()
            .map(|r| r.rule.clone())
            .collect();
        let proto_rule_refs: Vec<&crate::rule::ProtoRuleE> = proto_rules.iter().collect();
        let mut injective_fact_insts =
            crate::tools::injective_fact_instances::simple_injective_fact_instances(
                &proto_rule_refs, &sig.reducible_fun_syms_fast);
        // HS `closeRuleCache` (Rule.hs:147-150): union the FORCED injective
        // fact tags BEFORE source precomputation reads `injective_fact_insts`.
        if !forced_injective_facts.is_empty() {
            injective_fact_insts =
                crate::tools::injective_fact_instances::union_forced_injective_fact_instances(
                    injective_fact_insts, forced_injective_facts);
        }
        // Compute loop-breakers and annotate the protocol rules in
        // place — direct port of Haskell's `useAutoLoopBreakersAC`
        // (`Theory.Tools.LoopBreakers`).  Edge `R_from → R_to.prem`
        // exists iff some conclusion of `R_from` is Maude AC-unifiable
        // with `R_to.prem`.  Loop-breaker analysis runs on
        // `(rule_name, prem_idx)` pairs.
        annotate_loop_breakers(&mut rules, &maude);
        // Compute rule variants — direct port of Haskell's
        // `variantsProtoRule` over every protocol rule.  For rules
        // containing reducible (destructor) sub-terms, Maude produces
        // multiple narrowing variants; we pre-apply each variant's
        // substitution to the rule's facts so the solver can enumerate
        // destructor-narrowed instances without further Maude calls.
        //
        // Without this, chain-fold for `KU(t:Fresh)` over a rule like
        // `Responder: ... --[ ]-> [Out(snd(sdec(msg, key)))]` cannot
        // find the narrowed instance `msg → senc(pair(_, t), key)`
        // ⇒ `Out(t)`, leaving exists-trace lemmas that need this path
        // unprovable (e.g. T&D::Public_part_public).
        // Pre-filter rules that can't have non-trivial variants: only
        // rules containing a *reducible* (destructor) function symbol
        // in some fact term could narrow. Skipping non-destructor
        // rules avoids ~N Maude round-trips at theory-load time.
        let reducible_syms: std::collections::BTreeSet<_> =
            sig.reducible_fun_syms.iter().cloned().collect();
        let term_has_reducible = |t: &tamarin_term::lterm::LNTerm| -> bool {
            fn rec(
                t: &tamarin_term::lterm::LNTerm,
                rs: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>,
            ) -> bool {
                use tamarin_term::term::Term;
                match t {
                    Term::Lit(_) => false,
                    Term::App(f, args) => {
                        rs.contains(f) || args.iter().any(|a| rec(a, rs))
                    }
                }
            }
            rec(t, &reducible_syms)
        };
        // Rules with destructors anywhere — conclusions, premises,
        // ACTIONS, or new_vars — benefit from rule-variant plumbing.
        // Haskell's `variantsProtoRule` abstracts every reducible-
        // headed subterm in `prems ++ concs ++ acts ++ nvs` into a
        // fresh `z` var and computes the disjunction of
        // substitutions Maude returns from its variant narrowing
        // (RuleVariants.hs:93-99).
        //
        // A conclusions-only filter is insufficient: rules like
        // `--[ Equality(verify(sig, ...), true) ]->` (issue193,
        // TLS_Handshake) have reducible terms in their ACTIONS:
        // without variant expansion, the equality restriction
        // `All x y. Equality(x,y) ⇒ x=y` instantiates to
        // `Eq(verify(sig:Msg, ...), true)` which Maude
        // `unify in MSG` (AC-only, no [variant] eqs) reports as
        // unifiable-free → `eq_store.is_false` → false contradiction.
        // With variants, the action is abstracted to
        // `Equality(z, true)` and the variant subst {z → true,
        // sig → revealSign(...)} provides the closing witness case.
        let rule_has_reducible = |r: &crate::rule::ProtoRuleE| -> bool {
            r.conclusions.iter()
                .chain(r.premises.iter())
                .chain(r.actions.iter())
                .any(|f| f.terms.iter().any(&term_has_reducible))
                || r.new_vars.iter().any(&term_has_reducible)
        };
        // Rule-variant plumbing: matches Haskell's `variantsProtoRule`
        // behaviour. Broadens search for protocols with destructors in
        // conclusions (e.g. T&D::Responder), which is required to find
        // destructor-narrowed exists-trace witnesses (e.g.
        // T&D::Public_part_public).
        // Compute the variants up front; they are installed onto
        // `ctx.rules` BEFORE source precomputation so that
        // `precompute_full_sources`/`precompute_sources` see the
        // variant-expanded rule set, matching HS (whose precompute runs
        // over `cprRuleAC` = the variant-expanded AC rules; Rule.hs:97,
        // Rule.hs:156).
        let mut computed_variant_substs:
            Vec<(usize, Vec<tamarin_term::subst_vfresh::LNSubstVFresh>)> = Vec::new();
        let mut computed_abstracted_rules:
            Vec<(usize, crate::rule::ProtoRuleE, Vec<tamarin_term::subst_vfresh::LNSubstVFresh>)>
            = Vec::new();
        // SplitG variants is the Haskell-faithful path
        // (`someRuleACInst` + `solveRuleConstraints` from Rule.hs:933 /
        // Reduction.hs:766-774).  Always on — there is no legacy fallback.
        //
        // HS-faithful (RuleVariants.hs:75-129): `variantsProtoRule` runs
        // UNCONDITIONALLY for every closed protocol rule.  For rules with no
        // reducible-headed sub-terms, the variant disjunction collapses to
        // `Disj [emptySubstVFresh]` (the `trueDisj` constant at
        // RuleVariants.hs:120); `someRuleACInst` (Rule.hs:940-955) then
        // returns `Just (Disj [emptySubstVFresh])` for EVERY ProtoRule, so
        // `solveRuleConstraints (Just trueDisj)` (Reduction.hs:766-773) still
        // calls `insertGoal (SplitG splitId) False` — bumping `sNextGoalNr`
        // by 1 at every `labelNodeId` call regardless of whether the rule has
        // any destructors.  Skipping the variant-substs computation for
        // non-destructor rules under-bumped that counter and desynchronised
        // RS's gsNr trace from HS's at every destructor-free `labelNodeId`
        // (e.g. Yubikey.spthy::Server, Yubikey.spthy::Setup), which the
        // smart-rank tie-breaker then resolved differently.
        for (idx, o) in rules.iter().enumerate() {
            if !o.variants.is_empty() { continue; }
            // The constraint solver reads only `abstracted_rule` +
            // `variant_substs` (`canonical_rule_inst` /
            // `rule_insts_with_constrs`, reduction.rs:2868,2895); it never
            // reads `o.variants`.  We therefore skip the RAW `get variants`
            // Maude query (the single biggest Maude cost on bilinear
            // protocols) and compute only the abstracted form + substs.
            //
            // The variant substitutions and the abstracted rule are computed
            // ONCE, HS-faithfully, by `abstract_rule_and_variants` (the
            // `abstrRule` port: it abstracts each reducible-headed sub-term to
            // a fresh `z_i`, queries Maude on the SMALL abstracted form, and
            // composes the variant substs back via `composeVFresh vsubst
            // abstractionSubst`, mirroring RuleVariants.hs:75-91).  This is
            // exactly what `populate_rule_variants` (run.rs) already ran during
            // theory elaboration, so when those fields are present we REUSE
            // them rather than re-querying Maude.
            let has_reducible = rule_has_reducible(&o.rule);
            if has_reducible {
                // Reuse the pass-1 (`populate_rule_variants`) result when it
                // already populated this rule; otherwise compute it here (e.g.
                // when `ProofContext::new` is driven on rules that never went
                // through elaboration's variant pass).  Either way the
                // abstracted form is computed AT MOST ONCE — no RAW query.
                if o.abstracted_rule.is_none() && o.variant_substs.is_empty() {
                    if let Ok(Some((abstr, av_substs))) =
                        crate::tools::rule_variants::abstract_rule_and_variants(
                            &maude, &o.rule)
                    {
                        computed_abstracted_rules.push((idx, abstr, av_substs));
                    }
                }
            } else {
                // Non-reducible rule: HS's `variantsProtoRule` still runs and
                // collapses to the trivial disjunction `[emptySubstVFresh]`
                // (`trueDisj`, RuleVariants.hs:120), BUT it FIRST applies
                // `renamePrecise` (RuleVariants.hs:78) to the rule — re-indexing
                // every variable to a PER-NAME fresh index.  This packs
                // distinct-named rule variables (e.g. a SAPiC `lock` + `v`) onto
                // the same low index (`lock.0` + `v.0`, not `lock.0` + `v.1`).
                // We must reproduce BOTH effects:
                //   (1) the renamePrecise packing → set `abstracted_rule` when
                //       it rewrites a var (the disjunction stays `[empty]`, whose
                //       empty domain cannot misalign the packed rule body); and
                //   (2) the trivial variant disjunction → `variant_substs =
                //       [empty]` so `solve_rule_constraints` still bumps
                //       `next_goal_nr` (matching HS's `insertGoal (SplitG _)`).
                // Applying only (2) left rule vars at their translation indices,
                // which spread the source-case fresh-var seed (`avoid th`, one
                // index per extra span) so saturated raw/refined source cases
                // rendered `#vr`/`~n` node ids off-by-N from HS.
                if o.abstracted_rule.is_none() && o.variant_substs.is_empty() {
                    if let Some(packed) =
                        crate::tools::rule_variants::rename_precise_rule_if_changed(&o.rule)
                    {
                        computed_abstracted_rules.push((
                            idx, packed,
                            vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()],
                        ));
                    } else if let Ok(substs) =
                        crate::tools::rule_variants::variant_substs_for_rule(&maude, &o.rule)
                    {
                        if !substs.is_empty() {
                            computed_variant_substs.push((idx, substs));
                        }
                    }
                }
            }
        }
        // `pcTrueSubterm` — `all isSubtermRule $ filter isDestrRule $
        // intruder_rules`.  Mirrors `ClosedTheory.getProofContext`
        // (`lib/theory/src/ClosedTheory.hs:112`).  When the destructor
        // set contains only subterm-rules (sdec / fst / snd / etc., as
        // opposed to constant-RHS rules like `isPair → true`), the
        // strict variant of `hasImpossibleChain` applies.
        let pc_true_subterm = intruder_rules.iter()
            .filter(|r| crate::rule::is_destr_rule_info(&r.info))
            .all(|r| crate::rule::is_subterm_rule_info(&r.info));
        let mut ctx = ProofContext {
            maude,
            maude_pool,
            rules,
            use_induction: UseInduction::AvoidInduction,
            injective_fact_insts,
            is_exists_trace: false,
            cut: CutStrategy::Dfs,
            typing_assumptions: Vec::new(),
            heuristic: None,
            lemma_name: String::new(),
            theory_file: String::new(),
            shared: std::sync::Arc::new(ProofContextShared {
                intruder_rules,
                unique_sources: Vec::new(),
                is_diff: false,
                full_sources: Vec::new(),
                restrictions,
                pc_true_subterm,
                saturate_state: std::sync::Mutex::new(SaturateState::Pending),
                saturation_limit: std::env::var("TAM_SATURATION_LIMIT").ok()
                    .and_then(|s| s.parse::<usize>().ok())
                    .unwrap_or_else(|| crate::constraint::solver::sources::IntegerParameters::default()
                        .saturation_limit as usize),
            }),
        };
        // Precompute unique sources from the protocol rules.  The shared
        // bundle is uniquely owned during construction (refcount 1, no
        // `with_swapped_maude` clone exists yet), so `Arc::get_mut`
        // always succeeds here.  `precompute_sources` borrows `&ctx`
        // immutably and returns before we take the `&mut`.
        let params = crate::constraint::solver::sources::IntegerParameters::default();
        let unique_sources = crate::constraint::solver::sources::precompute_sources(
            &params, &ctx);
        std::sync::Arc::get_mut(&mut ctx.shared)
            .expect("ProofContext shared bundle is uniquely owned during construction")
            .unique_sources = unique_sources;
        // Precompute full source-case enumerations.  Runs *after*
        // `unique_sources` so per-tag expansion can use the unique-
        // source cache; runs with an empty `full_sources` itself so
        // there's no recursive lookup during precomputation. Saturates
        // the cases via `saturate_sources` so recursive Loop-style
        // chains fold into a finite enumeration of self-contained
        // sub-systems.
        // Install rule variants BEFORE precompute, so
        // `precompute_full_sources`/`precompute_sources` see the
        // variant-expanded (abstracted) rule set, matching HS (whose
        // precompute runs over `cprRuleAC`; Rule.hs:97,156).
        //
        // Install the variant substitutions in their disjunction form.
        // These are consumed by `solve_rule_constraints` at search time
        // (`rule_insts_with_constrs`, reduction.rs:2895).  For reducible
        // rules the disjunction comes from the abstracted-rule install
        // below; for non-reducible rules it is the trivial
        // `[emptySubstVFresh]` computed above.
        for (idx, substs) in &computed_variant_substs {
            if let Some(o) = ctx.rules.get_mut(*idx) {
                o.variant_substs = substs.clone();
            }
        }
        // Install abstracted rules + their variant disjunctions.
        // Overrides `variant_substs` with the abstraction-composed
        // disjunction (whose domain is the abstracted rule's fresh
        // z_i vars) — `canonical_rule_inst` checks `abstracted_rule`
        // first when present.
        for (idx, abstr, av_substs) in &computed_abstracted_rules {
            if let Some(o) = ctx.rules.get_mut(*idx) {
                o.abstracted_rule = Some(abstr.clone());
                o.variant_substs = av_substs.clone();
            }
        }
        let raw_sources = crate::constraint::solver::sources::precompute_full_sources(&ctx);
        // (assigned into the shared bundle below via `Arc::get_mut` — still
        // uniquely owned during construction.)
        // HS-faithful lazy precompute: `saturateSources` (Sources.hs:373)
        // is *lazy in cdCases* — its `refineSource ctxt solver`
        // applications produce `Source`s whose updated `cdCases` is
        // itself a thunk that forces only when a consumer pattern-
        // matches on `(name, sys) <- get cdCases th` in a Disj-monad
        // bind.  For protocols where the lemma proof never forces a
        // particular source's `cdCases` (e.g. `Heard`-style existence
        // lemmas on a Var-headed `KU(t:Fresh)` source — HS's
        // `getMsgOneCase` short-circuits on the goal-shape pattern
        // before touching `cdCases`), the thunk never runs and zero
        // saturate-time `[EXEC] solveGoal / exploitPrems / ...` lines
        // are emitted.
        //
        // To preserve this laziness we defer saturation to the first
        // `Source::cases(ctx)` call via `ProofContext::ensure_saturated`
        // (which drives `saturate_sources_with_simp`).  `ctx.full_sources`
        // holds the unsaturated raw sources from `precompute_full_sources`
        // (each with `cases_cell = None`); no `[EXEC] solveGoal /
        // exploitPrems / ...` lines fire here — they only fire when a
        // lemma proof forces a source's cases via pattern-matching on its
        // `cdCases` (HS-faithful).
        std::sync::Arc::get_mut(&mut ctx.shared)
            .expect("ProofContext shared bundle is uniquely owned during construction")
            .full_sources = raw_sources;
        // No saturation here — `ctx.full_sources` holds unsaturated
        // raw sources.  `prove_lemma` calls `ctx.ensure_saturated()`
        // AFTER assigning `ctx.typing_assumptions` so that
        // `refine_with_source_asms` runs with the lemma's [sources]
        // assumptions in hand.  Matches HS's `refineWithSourceAsms`
        // timing where `[Saturating Sources] Done` fires after
        // assumptions are applied.
        // No post-saturate drop pass — Haskell doesn't have one.
        // Haskell relies on saturate-time `contradictoryIf` inside
        // `solveAllSafeGoals` (Sources.hs:118-133) + runtime
        // contradiction detection during proof search.
        ctx
    }
}

/// Mutate `rules` in place, populating each rule's
/// `info.loop_breakers` from the dataflow relation.  Mirrors Haskell's
/// `useAutoLoopBreakersAC`:
///
/// 1. Build a dataflow over-approximation:
///    `(ruFrom, (ruTo, premIdx))`
///    where some conclusion of `ruFrom` has the same fact tag as the
///    `premIdx`-th premise of `ruTo`.
/// 2. Lift to the premise-solving relation by pairing every `(ruTo,
///    premIdx)` with every premise of `ruFrom`:
///    `((ruTo, premIdx), (ruFrom, fromPrem))`
/// 3. `dfs_loop_breakers` returns the set of `(rule_name, prem_idx)`
///    targets to mark — the premises whose goals should be tagged
///    loop-breaker.
pub fn annotate_loop_breakers(
    rules: &mut [OpenProtoRule],
    maude: &tamarin_term::maude_proc::MaudeHandle,
) {
    use crate::rule::PremIdx;
    use crate::rule::ProtoRuleName;

    // Helper: stable string key for a rule by its `ProtoRuleName`.
    fn rule_key(r: &OpenProtoRule) -> String {
        match &r.rule.info.name {
            ProtoRuleName::Stand(s) => format!("S:{}", s),
            ProtoRuleName::Fresh => "Fresh".to_string(),
        }
    }
    // Indexed view.
    let keys: Vec<String> = rules.iter().map(rule_key).collect();

    // HS `premSolvingRelAC` builds the dataflow relation over `instances`:
    //   `instances ru fa = [ apply (subst `freshToFreeAvoiding` fa) fa
    //                       | subst <- eVariants ru ]`   (LoopBreakers.hs:55-57)
    // where `eVariants ru` is the rule's AC-VARIANT disjunction
    // (`variantsProtoRule`).  For a rule whose conclusion carries a
    // reducible/DH-laden term (e.g. GDH RecvOthers concludes
    // `!AO(.., 'g'^y^~esk)`), a variant substitution expands that term to a
    // syntactic-AC form (`z.1 = 'g'^(~esk*y)`) that Maude's plain `unify`
    // can solve against another rule's premise (`!AO(.., 'g'^y)`).  Unifying
    // the RAW E-rule facts instead — as RS did — sends the local `unifyRaw`
    // (and Maude) `exp(exp('g',y),esk) =? exp('g',y')`, a NESTED-exp
    // narrowing problem the AC unifier rejects, so the dataflow edge (and
    // hence the loop-breaker cycle) is never found.
    //
    // `populate_rule_variants` (run.rs) already computed and stored each
    // rule's variant disjunction (keyed by the *abstracted* rule's fresh
    // z-vars) on every `OpenProtoRule` BEFORE `annotate_loop_breakers`
    // runs, so reuse `o.variant_substs`/`o.abstracted_rule` rather than
    // recomputing via the narrowing-only `variant_substs_for_rule` (which
    // misses DH `exp`/`mult` variant expansion).  When variants are empty
    // (no reducible sub-terms, or this is the precompute call before
    // population) `instances` yields the bare fact, preserving prior
    // behaviour.
    let variant_substs: Vec<&Vec<tamarin_term::subst_vfresh::LNSubstVFresh>> =
        rules.iter().map(|o| &o.variant_substs).collect();

    // `instances ru fa`: apply each variant subst (as a free subst via
    // `freshToFreeAvoiding`) to `fa`.  Empty variant list ⇒ `[fa]`.
    let instances = |rule_idx: usize, fa: &crate::fact::LNFact| -> Vec<crate::fact::LNFact> {
        use tamarin_term::lterm::HasFrees;
        let substs = variant_substs[rule_idx];
        if substs.is_empty() || substs.iter().all(|s| s.is_empty()) {
            return vec![fa.clone()];
        }
        substs.iter().map(|s| {
            // HS `apply (subst `freshToFreeAvoiding` fa) fa`: rename the
            // VFresh range vars to fresh free vars avoiding `fa`'s frees,
            // then apply.  We seed the witness counter above the max idx
            // appearing in `fa` (the avoid set), matching HS's
            // `evalFreshAvoiding (frees fa)`.
            let mut avoid_max: u64 = 0;
            fa.for_each_free(&mut |v| { if v.idx + 1 > avoid_max { avoid_max = v.idx + 1; } });
            let mut next = avoid_max;
            let free = s.fresh_to_free(|_| { let i = next; next += 1; i });
            // freshToFree rename + apply — frees change; recompute the bloom.
            let terms: Vec<tamarin_term::lterm::LNTerm> = fa.terms.iter()
                .map(|t| tamarin_term::subst::apply_vterm(&free, t.clone()))
                .collect();
            crate::fact::LNFact::fresh_annotated(fa.tag.clone(), fa.annotations.clone(), terms)
        }).collect()
    };

    // Build the prem-solving relation, mirroring HS's `premSolvingRelAC`
    // (`LoopBreakers.hs:35-58`) EXACTLY, including iteration nesting —
    // `dfsLoopBreakers` walks the relation in list order, so the order
    // determines which node becomes each DFS root and therefore which
    // breakers are picked.
    //
    // HS structure:
    //   dataflowRelAC: ruFrom <- rules; ruTo <- rules;
    //                  (premIdx,premFa0) <- ePrems ruTo; [unifiable];
    //                  return (ruFrom, (ruTo, premIdx))
    //   premSolvingRelAC: (toRu=ruFrom, from=(ruTo,premIdx)) <- dataflowRelAC;
    //                     (toPrem,_) <- ePrems toRu;
    //                     return (from, (toRu, toPrem))
    //                   = ((ruTo,premIdx), (ruFrom,toPrem))
    //
    // So the nesting is: ruFrom (outer) → ruTo → premIdx(of ruTo) →
    // toPrem(of ruFrom, innermost).  Each emitted element's FIRST
    // component is (ruTo, premIdx); the relation appears grouped by
    // ruFrom because that's the outermost loop.
    // HS enumerates premises/conclusions of the AC rule, i.e. the
    // *abstracted* rule (whose reducible-headed sub-terms are replaced by
    // the fresh z-vars the variant substs are keyed on).  Use
    // `abstracted_rule` when present, falling back to the raw E-rule.
    let ac_rules: Vec<&crate::rule::ProtoRuleE> = rules.iter()
        .map(|o| o.abstracted_rule.as_ref().unwrap_or(&o.rule))
        .collect();
    let mut relation: Vec<((String, PremIdx), (String, PremIdx))> = Vec::new();
    for (i_from, _ru_from) in rules.iter().enumerate() {
        let ru_from_ac = ac_rules[i_from];
        for (i_to, _ru_to) in rules.iter().enumerate() {
            let ru_to_ac = ac_rules[i_to];
            for (to_prem_idx, prem_fa) in ru_to_ac.enumerate_premises() {
                // HS `dataflowRelAC` (LoopBreakers.hs:43-54) enumerates ALL
                // premises (`enumPrems`, Rule.hs:246-247) with no tag filter;
                // the only premise-level guard is `not (isNoSourcesFact …)`.
                // Non-Proto premises are kept here too: the tag-equality
                // (`c0.tag != prem_fa.tag`) + `unifiable_ln_facts` gates below
                // already exclude any conclusion that cannot form an edge,
                // exactly as HS's `unifiableLNFacts` does (it returns []
                // whenever `factTag fa1 /= factTag fa2`, Fact.hs:442-446).
                //
                // Haskell `LoopBreakers.hs:48`:
                //   `guard $ not (isNoSourcesFact premFa0)`
                if prem_fa.is_no_sources() {
                    continue;
                }
                // Haskell `LoopBreakers.hs:49-53`: edge exists iff some
                // conclusion of `ruFrom` is AC-UNIFIABLE with this premise
                // (not merely same-tag).  Tag-only matching over-approximates
                // and adds spurious self-edges (e.g. `I_m0`'s `St_I(<'m2'>)`
                // conclusion vs its own `St_I('m0')` premise share a tag but
                // do NOT unify), which fabricate extra cycles and over-mark
                // loop breakers.  Use real Maude unifiability, mirroring HS.
                //
                // HS `dataflowRelAC` (LoopBreakers.hs:49-53):
                //   guard $ or $ do
                //     premFa <- instances ruTo premFa0
                //     concFa <- instances ruFrom =<< (snd <$> eConcs ruFrom)
                //     let concFaFresh = rename concFa `evalFresh` avoid premFa
                //     return $ unifiableLNFacts concFaFresh premFa
                // i.e. iterate the VARIANT INSTANCES of both the premise and
                // each conclusion, rename the conclusion away from the
                // premise's frees, and check Maude AC-unifiability.
                let prem_insts = instances(i_to, prem_fa);
                let conc_unifies = ru_from_ac.conclusions.iter().any(|c0| {
                    if c0.tag != prem_fa.tag { return false; }
                    instances(i_from, c0).iter().any(|conc| {
                        prem_insts.iter().any(|prem| {
                            let mut fresh = tamarin_term::lterm::avoid(prem);
                            let conc_fresh =
                                tamarin_term::lterm::rename(conc.clone(), &mut fresh);
                            crate::rule::unifiable_ln_facts(maude, &conc_fresh, prem)
                                .unwrap_or(false)
                        })
                    })
                });
                if !conc_unifies { continue; }
                for (from_prem_idx, _) in ru_from_ac.enumerate_premises() {
                    relation.push((
                        (keys[i_to].clone(), to_prem_idx),
                        (keys[i_from].clone(), from_prem_idx),
                    ));
                }
            }
        }
    }
    // Run DFS loop-breaker selection. `dfsLoopBreakers` lives in HS
    // `Data.DAG.Simple`, ported to `tamarin_utils::dag`.
    let breakers: Vec<(String, PremIdx)> =
        tamarin_utils::dag::dfs_loop_breakers(&relation);
    // Annotate each rule's `loop_breakers` with the picked premises.
    for (k, ru) in keys.iter().zip(rules.iter_mut()) {
        ru.loop_breakers = breakers.iter()
            .filter(|(rk, _)| rk == k)
            .map(|(_, p)| *p)
            .collect();
    }
}
