// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, PhilipLukertWork, rkunnema, beschmi, racoucho1u,
//   felixlinker, rsasse, yavivanov, kevinmorio, katrielalex, arcz, Nick
//   Moore, ValentinYuri, addap, charlie-j, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Substitution/SubstVFree.hs,
//   lib/term/src/Term/Substitution/SubstVFresh.hs,
//   lib/term/src/Term/Term/Raw.hs,
//   lib/theory/src/Theory/Constraint/Solver/Goals.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/Solver/Simplify.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Sapic/Term.hs,
//   lib/theory/src/Theory/Tools/EquationStore.hs,
//   lib/theory/src/Theory/Tools/SubtermStore.hs,
//   lib/utils/src/Control/Monad/Disj/Class.hs

//! Port of `Theory.Constraint.Solver.Reduction`.
//!
//! In Haskell, `Reduction` is a state-fresh-disjunction monad over a
//! `ProofContext` reader:
//!
//! ```haskell
//! type Reduction = StateT System (FreshT (DisjT (Reader ProofContext)))
//! ```
//!
//! Each constraint-reduction rule runs as a `Reduction`, possibly
//! producing multiple cases. The monad provides primitives like
//! `insertNode`, `insertEdge`, `insertGoal`, `solveTermEqs`, etc.
//!
//! For the Rust port we model `Reduction` as a struct holding mutable
//! `System` state plus a `ProofContext` reference, with its own
//! fresh-variable supply (see `Reduction::maude`). Disjunctive results
//! are surfaced as `Vec`s rather than a monad-level `DisjT` layer. This
//! module implements the full reduction surface: `substSystem`,
//! `conjoinSystem`, the `solve*Eqs` family, `insertFormula`, and the
//! associated CR-rules.

use crate::constraint::constraints::{Disj, Edge, Goal, LessAtom};
use crate::constraint::solver::context::ProofContext;
use crate::constraint::system::System;
use crate::guarded::Guarded;
use crate::rule::RuleACInst;

/// The complete set of per-pass change signals raised by
/// [`Reduction::subst_system_once`].  Built exactly ONCE, at the pass's
/// aggregation point, from the section-local flags.  A struct LITERAL forces
/// every field to be named, so a future section that computes a new signal but
/// forgets to fold it in cannot construct this value (missing field → compile
/// error); and [`PassSignals::raised`] EXHAUSTIVELY destructures `self`, so
/// dropping a field from the OR is a compile error too.  Together these make
/// "a section raised a change but the pass reported a no-op" — a silent
/// skip-marker soundness bug — unrepresentable, at zero runtime cost (the
/// value is a stack aggregate the OR consumes immediately).
struct PassSignals {
    /// A node id was rewritten by the subst, or a node's rule terms changed
    /// value.
    nodes_value_changed: bool,
    /// Two distinct rules collapsed onto the same node id (`collisions > 0`).
    collisions: bool,
    /// A node collision produced length-mismatched premise/conclusion/action
    /// lists (no model).
    shape_mismatch: bool,
    /// An edge endpoint was rewritten.
    edges_value_changed: bool,
    /// The `last(i)` atom's node id was rewritten.
    last_atom_changed: bool,
    /// A `less` atom endpoint was rewritten.
    less_value_changed: bool,
    /// A goal's terms changed value under the subst.
    goals_value_changed: bool,
    /// A formula changed value under the subst.
    formulas_value_changed: bool,
    /// A subterm-store entry changed value.
    changed_sst: bool,
    /// Node-merge rule equalities were queued (`!rule_eqs.is_empty()`).
    had_rule_eqs: bool,
    /// KU actions were queued for re-insertion (`!to_insert_action.is_empty()`).
    had_insert_action: bool,
}

impl PassSignals {
    /// `true` iff ANY signal fired — i.e. the pass was NOT a total no-op.
    /// Exhaustively destructures `self` (no `..`) so dropping a field from the
    /// OR is a compile error.  `#[must_use]`: this verdict is the pass's whole
    /// output (it gates the verified-identity skip marker), so discarding it
    /// would silently drop the change signal.
    #[must_use]
    fn raised(self) -> bool {
        let PassSignals {
            nodes_value_changed,
            collisions,
            shape_mismatch,
            edges_value_changed,
            last_atom_changed,
            less_value_changed,
            goals_value_changed,
            formulas_value_changed,
            changed_sst,
            had_rule_eqs,
            had_insert_action,
        } = self;
        nodes_value_changed
            || collisions
            || shape_mismatch
            || edges_value_changed
            || last_atom_changed
            || less_value_changed
            || goals_value_changed
            || formulas_value_changed
            || changed_sst
            || had_rule_eqs
            || had_insert_action
    }
}

/// A reduction step takes a `System` and produces zero or more new
/// systems. We keep it simple: explicit input/output rather than a
/// monad transformer stack.
pub struct Reduction<'ctx> {
    pub ctx: &'ctx ProofContext,
    pub sys: System,
    /// Per-Reduction MaudeHandle: shares Maude's process state with
    /// `ctx.maude` but carries its own `fresh_counter` initialised from
    /// `bounds_max(&sys) + 1` at Reduction creation.  Mirrors Haskell's
    /// `runReduction m ctx sys (avoid sys)` — each runReduction call gets
    /// its own FreshState that advances within the call but doesn't leak
    /// across Reductions.  Use `self.maude` for any fresh-idx allocation
    /// inside Reduction methods (so witness allocation patterns match HS).
    pub maude: tamarin_term::maude_proc::MaudeHandle,
    /// Whether the system has been mutated since the last
    /// `whileChanging` checkpoint.
    pub changed: ChangeIndicator,
    /// Multi-arm eq-store fanout produced inside an `insert_atom`
    /// `Atom::Eq` call (or, recursively, an `insert_formula`
    /// invocation that opened to an Eq atom).  Mirrors HS's
    /// `disjunctionOfList $ performSplit eqs2 splitId` inside
    /// `solveTermEqs SplitNow` (Reduction.hs): each AC
    /// unifier arm forks the surrounding `Reduction` (`DisjT`)
    /// continuation.  Our port doesn't have a monad-level Disj layer,
    /// so we surface the extra arms here: `insert_atom` Atom::Eq
    /// installs arm[0] into `sys.eq_store` and stores arms[1..] in
    /// `pending_eq_arms`.  Callers that wrap an `insert_formula`
    /// invocation in a per-case fork (e.g. `solve_disj_goal`,
    /// `insert_implied_formulas_pass`) drain `pending_eq_arms` after
    /// the call and emit one additional case per arm with `sys`
    /// cloned and `eq_store = arm`.  This mirrors HS's behaviour
    /// where each AC unifier arm produces its own downstream
    /// `Goals.hs:393-395` `case_N` entry — i.e. `case_2` of an outer
    /// `solveDisjunction` further fans into `case_2_case_1`,
    /// `case_2_case_2` via `uniqueListBy ... distinguish`
    /// (ProofMethod.hs:283-340, see line 308).
    pub pending_eq_arms: Vec<crate::tools::equation_store::EquationStore>,
    /// Fanout of `conjoinSystem`'s step 12 `solveSubstEqs SplitNow`
    /// (Reduction.hs:669-698, see line 683).  HS runs this inside the `Reduction` monad
    /// whose `DisjT` layer replicates the surrounding `_applySource`
    /// continuation per AC unifier arm — each arm flows into its own
    /// post-conjoin `someInst`/`E.5 edge_eqs`/`close_trivial_chains`
    /// computation.
    ///
    /// RS's `solve_term_eqs` collapses multi-arm `Cases` into the bare
    /// eq_store without installing them; step 12 silently dropped the
    /// extra arms.  Empirically: HS ≅ 26 `solveSubstEqs arms=3` events
    /// on Scott::key_secrecy vs RS ≅ 18 — i.e. 8 lost fanout sites.
    ///
    /// Fix: when step 12 returns `Cases(arms)`, install `arms[0]`
    /// in-place (the main `conjoin_system` return value), and stash a
    /// per-arm clone of the post-step-13 system here, one per `arms[i]`
    /// where i ≥ 1.  The caller (`apply_source_case_action` /
    /// `apply_source_case_premise`) drains this Vec after
    /// `conjoin_system` returns and replays the post-conjoin work
    /// (E.5 edge_eqs, F close_trivial_chains, output push) per stashed
    /// system.  Each stashed system has had `subst_system` already run
    /// with that arm's eq_store, mirroring HS's per-arm `substSystem`
    /// at Reduction.hs:669-698, see line 686.
    ///
    /// HS FreshT-threading (task #23, A(ii)): the `u64` is the arm's
    /// continuation counter — the step-12 fork position plus the arm's
    /// own `substSystem` draws (node-merge `solveRuleEqs` witness
    /// mints).  HS's `disjunctionOfList` fork sits BELOW `FreshT`
    /// (Reduction.hs:115-115, see line 123), so each solveSubstEqs arm's post-conjoin
    /// continuation (E.5 / close chains / output) proceeds from an
    /// independent copy of the counter — NOT from `bounds_max` of the
    /// stashed system (which silently rewinds past every transient
    /// draw of the step so far).  The drain site
    /// (`conjoin_refine_arm`) seeds each replayed arm's Reduction
    /// from this value via `Reduction::new_inheriting`.
    pub pending_conjoin_arm_systems: Vec<(crate::constraint::system::System, u64)>,
    /// HS FreshT-threading for multi-case (`GoalCases::Cases`) outcomes:
    /// per returned case, the producing branch's final fresh-counter
    /// position (parallel to the `Cases` vec).  HS's `runReduction
    /// (solveGoal >> simplifySystem)` continues each DisjT branch's
    /// simplify with THAT branch's counter; seeding RS's per-case
    /// continuation (exec_proof_method's per-case
    /// `simplify_system_with_fanout`) from `bounds_max(case_sys)` alone
    /// would silently rewind past the branch's transient draws (task #16),
    /// so the goal solvers record each branch's final counter here.
    /// Populated alongside `Cases`; empty means "no counters recorded"
    /// (callers fall back to bounds_max seeding).
    pub last_case_counters: Vec<u64>,
    /// σ-as-`VarSubst` cache for the Atom mark=true dedup: `(subst_stamp,
    /// var_subst_from_eq_store(σ))` at the time it was built.  σ is a pure
    /// function of `sys.eq_store.subst`, and every subst mutation mints a
    /// fresh `subst_stamp` (sealed axis: `set_eq_store`/`take_eq_store`/
    /// `eq_store_mut` are the only doors), so a matching stamp proves the
    /// cached value is bit-identical to a rebuild.  Sub-Reductions start
    /// `None` and rebuild on first use (conservative miss only).
    eq_vs_cache: Option<(u64, crate::guarded::VarSubst)>,
}

/// `ChangeIndicator` mirrors the `True`/`False` flag the Haskell
/// `whenChanged` / `whileChanging` combinators thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChangeIndicator { Changed, Unchanged }

impl ChangeIndicator {
    pub fn or(self, other: Self) -> Self {
        if self == ChangeIndicator::Changed || other == ChangeIndicator::Changed {
            ChangeIndicator::Changed
        } else {
            ChangeIndicator::Unchanged
        }
    }
}

thread_local! {
    /// Source-precompute fresh-counter floor for `avoid th` faithfulness.
    ///
    /// HS's `refineSource` (Sources.hs:144-225, see line 162) seeds ONE monotonic FreshT
    /// counter at `fs = avoid th` — the max var idx over the WHOLE source
    /// `th` (all its cases) — and threads it through EVERY reduction in the
    /// refinement of each case, `simplifySystem` included.  RS breaks a
    /// refineSource into a floored main-loop reduction plus floor-0
    /// `simplify_system_with_fanout` sub-reductions; the latter reset the
    /// counter to the per-case `avoid se`, which is BELOW `avoid th` for any
    /// case whose max var is smaller than the source-wide max (e.g. NSPK3's
    /// `!KU(~t.1)` R_1 case, avoid 27 vs source-wide 29).  A first NEW draw
    /// there (the `[sources]`-lemma `Ex #j. OUT_I_1(m1)@#j` node) then lands
    /// below HS's value.  This thread-local carries `source_avoid` into
    /// those sub-reductions so they seed at `avoid th`, matching HS's single
    /// monotonic counter.  Set for the duration of one source-case
    /// refinement (`run_solve_all_safe_goals_disj_with_progress`); 0 (the
    /// default, general proving path) means "no floor".
    static REFINE_FLOOR: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Set the source-precompute fresh-counter floor, returning the previous
/// value (for RAII restore).  See [`REFINE_FLOOR`].
pub fn set_refine_floor(floor: u64) -> u64 {
    REFINE_FLOOR.with(|c| { let old = c.get(); c.set(floor); old })
}

/// Current source-precompute fresh-counter floor (`avoid th`, 0 if unset).
pub fn refine_floor() -> u64 {
    REFINE_FLOOR.with(|c| c.get())
}

impl<'ctx> Reduction<'ctx> {
    pub fn new(ctx: &'ctx ProofContext, sys: System) -> Self {
        // HS-faithful `avoid th` (Sources.hs:144-225, see line 162): during source precompute
        // a thread-local floor (`REFINE_FLOOR`) carries the source-wide
        // `avoid th` seed into EVERY reduction of the refinement — including
        // the many `Reduction::new` sub-reductions (simplify, action solve,
        // etc.) that would otherwise reseed at the per-case `avoid se` and
        // undershoot HS's single monotonic counter.  0 (default, general
        // proving path) is a no-op.
        Self::new_with_floor(ctx, sys, refine_floor())
    }

    /// Like [`new`] but seeds the per-Reduction Fresh counter from
    /// `max(bounds_max(sys), floor)` instead of `bounds_max(sys)` alone.
    ///
    /// HS-faithful `refineSource` (Sources.hs:144-225, see line 162) seeds EVERY case's
    /// `runReduction proofStep ctxt se fs` from `fs = avoid th` — the max
    /// var idx over the WHOLE source `th` (all its cases), NOT the single
    /// case `se`.  A source whose sibling case is complex (high var idx)
    /// therefore seeds even its SIMPLE cases from that high `avoid th`.
    /// RS creates each case's Reduction from `bounds_max(se)` alone
    /// (per-case `avoid se`), so simple cases in a source with a complex
    /// sibling seed too low → their solve-time allocations land below HS.
    /// Source-precompute threads `avoid th` in as `floor`; the general
    /// proving path passes `floor = 0` (a no-op) via [`new`].
    pub fn new_with_floor(ctx: &'ctx ProofContext, sys: System, floor: u64) -> Self {
        // HS-faithful per-Reduction Fresh counter: seed the NEXT-draw value
        // from `avoid sys` (LTerm.hs:656-657, via `avoid_fresh_state` — 0
        // for a frees-less system, max idx + 1 otherwise).  Matches
        // `runReduction m ctx sys (avoid sys)`.  `floor` (max-idx units,
        // source-precompute's `avoid th` whole-source seed) lifts the
        // next-draw to `floor + 1` when set; `floor == 0` means "no floor"
        // (the general proving path via [`new`]).
        let next = avoid_fresh_state(&sys)
            .max(if floor == 0 { 0 } else { floor.saturating_add(1) });
        let maude = ctx.maude.with_fresh_counter_next(next);
        // Ensure the GLOBAL ctx.maude is at least as advanced as our
        // local high-water start (counter ≥ next).  Any non-Reduction
        // allocator (`sources.rs`, etc.) that subsequently uses
        // `ctx.maude` will then start above our base, preventing
        // cross-allocator collisions on names like `~mw` that both
        // routes mint.
        if next > 0 { ctx.maude.ensure_above(next - 1); }
        Reduction {
            ctx, sys, maude,
            changed: ChangeIndicator::Unchanged,
            pending_eq_arms: Vec::new(),
            pending_conjoin_arm_systems: Vec::new(),
            last_case_counters: Vec::new(),
            eq_vs_cache: None,
        }
    }

    /// Like [`new`] but continues an ENCLOSING Reduction's fresh-counter
    /// thread: the sub-Reduction's next draw starts at
    /// `max(avoid_fresh_state(sys), inherit_next)`.
    ///
    /// HS-faithful FreshT-threading (`Reduction = StateT System (FreshT
    /// (DisjT ...))`, Reduction.hs:115-115, see line 123): within one `runReduction` there is
    /// ONE fresh counter; sub-computations (labelNodeId's exploitPrems,
    /// insertEdges' solveFactEqs, per-arm simp) all draw from it, including
    /// draws whose variables never persist in the system (transients:
    /// Fresh-narrowing witnesses, eq-store simp fold draws).  RS runs these
    /// sub-computations in child `Reduction`s; seeding a child from
    /// `bounds_max(sys)` alone silently REWINDS the thread past any
    /// transient draws, so later draws in the enclosing exec undershoot
    /// HS — the fresh/witness numbering family on web sequent panes
    /// (task #16).  `inherit_next` = the parent's
    /// `maude.fresh_counter_peek()` at the fork point.
    pub fn new_inheriting(ctx: &'ctx ProofContext, sys: System, inherit_next: u64) -> Self {
        // Respect the source-precompute floor exactly like `new` does
        // (REFINE_FLOOR is orthogonal to the in-exec thread continuation).
        let floor = refine_floor();
        let next = avoid_fresh_state(&sys)
            .max(if floor == 0 { 0 } else { floor.saturating_add(1) })
            .max(inherit_next);
        let maude = ctx.maude.with_fresh_counter_next(next);
        if next > 0 { ctx.maude.ensure_above(next - 1); }
        Reduction {
            ctx, sys, maude,
            changed: ChangeIndicator::Unchanged,
            pending_eq_arms: Vec::new(),
            pending_conjoin_arm_systems: Vec::new(),
            last_case_counters: Vec::new(),
            eq_vs_cache: None,
        }
    }

    /// Run a reduction step until it stops mutating the system. The
    /// `step` closure returns the new `ChangeIndicator`.
    pub fn while_changing<F>(&mut self, mut step: F)
    where F: FnMut(&mut Reduction<'ctx>) -> ChangeIndicator {
        loop {
            self.changed = ChangeIndicator::Unchanged;
            let _ = step(self);
            if self.changed == ChangeIndicator::Unchanged { break; }
        }
    }

    /// Mark the system contradictory via the eq-store *and* via gfalse
    /// in formulas.  Mirrors Haskell's `contradictoryIf True` /
    /// `mzero`-via-`contradictoryIf` semantics: in Haskell, hitting
    /// `contradictoryIf` in any CR-rule pass calls `mzero`, which
    /// removes the case from the surrounding `runReduction` Disj.
    /// Our port doesn't have monad-level mzero, so we have two markers:
    ///
    ///   - `gfalse` in `sys.formulas` — picked up by post-simplify
    ///     `contradictions(ctx, sys)` as `FormulasFalse`, drives
    ///     `is_finished` to return `Contradictory`.
    ///   - `eq_store.is_false` — the simplify-time filter in
    ///     `exec_proof_method`'s SolveGoal arm uses this as the Haskell-
    ///     faithful proxy for mzero, dropping the case from the resulting
    ///     case map so the proof tree mirrors Haskell's shape.
    ///
    /// Use this helper at every CR-rule failure point that corresponds
    /// to a `contradictoryIf` in Haskell (`solveFactEqs` tag/arity
    /// mismatch, `solveRuleEqs` rInfo mismatch, `solveSubstEqs`
    /// failure, `noContradictoryEqStore` firing, etc.).  Idempotent:
    /// only flags `Changed` if at least one marker actually toggled.
    pub fn mark_contradictory(&mut self) {
        let bot = crate::guarded::gfalse();
        let added_bot = if !crate::guarded::stores_contains(&self.sys.formulas, &bot) {
            self.sys.invalidate_max_var_idx_cache();
            self.sys.formulas_mut().push(std::sync::Arc::new(bot));
            true
        } else {
            false
        };
        let flipped_eq = self.set_eq_store_false();
        if added_bot || flipped_eq {
            self.changed = ChangeIndicator::Changed;
        }
    }

    /// Flip `eq_store` to its `is_false` (mzero-proxy) state: take the
    /// store out of its `Arc`, invalidate the max-var-idx cache, and
    /// reinstall the `set_false()` result. Returns `true` iff it actually
    /// flipped (the store was not already false). Callers decide whether
    /// the flip also implies a `self.changed` bump.
    fn set_eq_store_false(&mut self) -> bool {
        if !self.sys.eq_store.is_false() {
            let s = std::sync::Arc::unwrap_or_clone(self.sys.take_eq_store());
            self.sys.invalidate_max_var_idx_cache();
            self.sys.set_eq_store(std::sync::Arc::new(s.set_false()));
            true
        } else {
            false
        }
    }


    /// Insert an edge — HS-faithful port of `insertEdges` (Reduction.hs:278-281):
    /// ```haskell
    /// insertEdges edges = do
    ///     void (solveFactEqs SplitNow [Equal fa1 fa2 | (_, fa1, fa2, _) <- edges])
    ///     modM sEdges (\es -> foldr S.insert es ...)
    /// ```
    /// Order matters: HS calls `solveFactEqs SplitNow` BEFORE adding to
    /// sEdges. If the unification fails (eq_store becomes false), HS
    /// mzero's the branch via `noContradictoryEqStore` — the edge is
    /// never added to the contradicted state. We mirror this: unify
    /// first via `solve_fact_eqs`, fail-fast via `mark_contradictory`
    /// + early return, then add to `sys.edges` only on success.
    ///
    /// Returns `Ok(Contradictory)` when the fact unification fails so
    /// callers can skip the case cleanly (matches HS Disj-monad mzero
    /// semantics on the caller side).
    pub fn insert_edge_labeled(&mut self, site: &str, e: Edge)
        -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError>
    {
        if tamarin_utils::env_gate!("TAM_RS_TRACE_INSERT_EDGE") {
            let mode = if crate::constraint::solver::sources::in_precompute_mode() {
                "saturate" } else { "runtime" };
            eprintln!("[INSERT_EDGE] enter site={} mode={} src={:?} tgt={:?} eqIsFalse={}",
                site, mode, e.src, e.tgt, self.sys.eq_store.is_false());
        }
        // Rust-only execution trace (no Haskell counterpart).  Emitted
        // once per edge (we're per-edge here, n=1) before running
        // `solveFactEqs` on the edge facts, to aid divergence debugging.
        crate::constraint::solver::trace::trace_exec("insertEdges n=1");
        // Look up the conclusion fact (source) and premise fact (target).
        let fa_conc = self.sys.nodes.iter()
            .find(|(n, _)| n == &e.src.0)
            .and_then(|(_, r)| r.conclusions.get(e.src.1.0).cloned());
        let fa_prem = self.sys.nodes.iter()
            .find(|(n, _)| n == &e.tgt.0)
            .and_then(|(_, r)| r.premises.get(e.tgt.1.0).cloned());
        // When either fact is missing (rule lookup failed),
        // `insert_edge_tail`'s `None` path does a raw insert.  Shouldn't
        // happen in practice unless the caller passes an edge for a node
        // that's not in the system.
        self.insert_edge_tail(site, e, fa_conc.as_ref(), fa_prem.as_ref())
    }

    /// Shared tail of `insert_edge_labeled` / `insert_edge_labeled_with_facts`
    /// once the conclusion/premise facts are in hand.  HS step 1
    /// (`solveFactEqs SplitNow`, Reduction.hs:278-281, see line 280) followed by step 2
    /// (`modM sEdges`, Reduction.hs:278-281, see line 281).  On unification failure it
    /// mirrors `noContradictoryEqStore` (Reduction.hs:703-704) via
    /// `mark_contradictory` + early return, so the edge is never added to
    /// the contradicted state.  Facts equal (or absent) means the Maude
    /// call would trivially succeed, so we skip straight to the insert.
    fn insert_edge_tail(
        &mut self, site: &str, e: Edge,
        fa_conc: Option<&crate::fact::LNFact>,
        fa_prem: Option<&crate::fact::LNFact>,
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        let res = if let (Some(fa_c), Some(fa_p)) = (fa_conc, fa_prem) {
            if fa_c != fa_p {
                self.solve_fact_eqs(
                    SplitStrategy::SplitNow,
                    &[tamarin_term::rewriting::Equal {
                        lhs: fa_c.clone(), rhs: fa_p.clone() }],
                )
            } else {
                Ok(SolveOutcome::Linear(ChangeIndicator::Unchanged))
            }
        } else {
            Ok(SolveOutcome::Linear(ChangeIndicator::Unchanged))
        };
        if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
            if tamarin_utils::env_gate!("TAM_RS_TRACE_INSERT_EDGE_FIRE") {
                let mode = if crate::constraint::solver::sources::in_precompute_mode() {
                    "saturate" } else { "runtime" };
                eprintln!("[INSERT_EDGE_FIRE] site={} mode={}", site, mode);
            }
            self.mark_contradictory();
            return res;
        }
        let before = self.sys.edges.len();
        self.sys.add_edge(e);
        if self.sys.edges.len() != before { self.changed = ChangeIndicator::Changed; }
        res
    }

    /// Variant of `insert_edge_labeled` that takes explicit conc/prem
    /// facts rather than looking them up via `sys.nodes`.  Mirrors
    /// HS's `insertEdges [(c, faConc, faPrem, p)]` as called from
    /// `solveChain`/premise solving — the live premise's fact comes
    /// from `faPrem`, not from a node lookup (the abstract goal's NodeId
    /// has no corresponding rule in sys.nodes).  The `site` arg is a
    /// Rust-only trace label; Haskell `insertEdges` is unlabeled.
    pub fn insert_edge_labeled_with_facts(
        &mut self, site: &str,
        e: crate::constraint::constraints::Edge,
        fa_conc: &crate::fact::LNFact,
        fa_prem: &crate::fact::LNFact,
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        if tamarin_utils::env_gate!("TAM_RS_TRACE_INSERT_EDGE") {
            let mode = if crate::constraint::solver::sources::in_precompute_mode() {
                "saturate" } else { "runtime" };
            eprintln!("[INSERT_EDGE] enter site={} mode={} src={:?} tgt={:?} eqIsFalse={}",
                site, mode, e.src, e.tgt, self.sys.eq_store.is_false());
        }
        crate::constraint::solver::trace::trace_exec("insertEdges n=1");
        self.insert_edge_tail(site, e, Some(fa_conc), Some(fa_prem))
    }

    /// `insertLast` — HS-faithful port of Reduction.hs:402-407:
    /// ```haskell
    /// insertLast i = do
    ///     lst <- getM sLastAtom
    ///     case lst of
    ///       Nothing -> setM sLastAtom (Just i) >> return Unchanged
    ///       Just j  -> solveNodeIdEqs [Equal i j]
    /// ```
    /// When no last atom is set, install this one.  When one is
    /// already set, equate the new node id to the existing last via
    /// `solveNodeIdEqs` — failure routes through `mark_contradictory`
    /// to keep the mzero-proxy in sync with HS `noContradictoryEqStore`.
    pub fn insert_last(&mut self, i: crate::constraint::constraints::NodeId)
        -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError>
    {
        match self.sys.last_atom.clone() {
            None => {
                // Pure ADD (last_atom None→Some): the max can only rise
                // by this node id — bump instead of invalidating.
                self.sys.bump_cache_lvar(&i);
                self.sys.set_last_atom(Some(i));
                self.changed = ChangeIndicator::Changed;
                Ok(SolveOutcome::Linear(ChangeIndicator::Unchanged))
            }
            Some(j) if j == i => {
                Ok(SolveOutcome::Linear(ChangeIndicator::Unchanged))
            }
            Some(j) => {
                if tamarin_utils::env_gate!("TAM_DBG_INSERT_LAST") {
                    eprintln!("[insert_last] existing={:?} new={:?} → eq", j, i);
                }
                let res = self.solve_node_id_eqs(&[
                    tamarin_term::rewriting::Equal { lhs: i, rhs: j }
                ]);
                if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                    self.mark_contradictory();
                } else {
                    self.changed = ChangeIndicator::Changed;
                }
                res
            }
        }
    }

    /// `substSystem`: apply the eq-store's current substitution to
    /// every part of the constraint system that holds free variables —
    /// nodes (both ids and rule contents), edges, last-atom, less
    /// atoms, formulas, solved formulas, lemmas, and goals. Mirrors
    /// Haskell's `substSystem` from `Theory.Constraint.Solver.Reduction`.
    ///
    /// Without this, graph-based contradiction checks (cycles in `<`,
    /// edge-induced ordering) miss real contradictions and create phantom
    /// ones — Haskell avoids both by calling `substSystem` after every
    /// successful `solveTermEqs`.
    pub fn subst_system(&mut self) {
        // Haskell-faithful port of `substSystem`: substNodeIds is
        // `whileChanging`, so we loop until the eq_store stops growing
        // (substituting nodes can introduce new rule_eqs via setNodes
        // which add to eq_store, which then needs to be reapplied to
        // nodes).  Without this loop, intermediate states show stale
        // node ids that downstream `enforce_edge_uniqueness_pass`
        // mistakes for legitimate prem_idx_clash → spurious
        // Contradictory on legitimate witness paths
        // (TLS_Handshake::session_key_setup_possible root cause).
        // Verified-identity skip: if the live
        // (content_stamp, subst_stamp) still equals the marker a prior
        // zero-signal pass set, that pass is an observed proof this pass is a
        // total no-op at this exact (System, σ) — and nothing has mutated
        // either input since (else a stamp would differ) — so skip the whole
        // loop.  A plain early return touches nothing, which is exactly what a
        // genuine zero-signal pass does (no `self.changed`, no cache
        // invalidation, no eq_store growth, no goal-nr bump, no Maude).
        let stats = subst_skip_stats_enabled();
        if stats {
            use std::sync::atomic::Ordering::Relaxed;
            let calls = SUBST_SYSTEM_CALLS.fetch_add(1, Relaxed) + 1;
            if calls % 50_000 == 0 {
                eprintln!("[SUBST_SKIP_STATS] calls={} skips={}",
                    calls, SUBST_SYSTEM_SKIPS.load(Relaxed));
            }
        }
        if fp_stats_enabled() {
            use std::sync::atomic::Ordering::Relaxed;
            let calls = FP_STATS_CALLS.fetch_add(1, Relaxed) + 1;
            if calls % 5_000 == 0 {
                let d = FP_FACT_DESCENTS.load(Relaxed);
                let s = FP_FACT_SKIPS.load(Relaxed);
                eprintln!("[FP_STATS] fact_descents={} fact_skips={} ({:.1}%)",
                    d, s, if d == 0 { 0.0 } else { 100.0 * s as f64 / d as f64 });
            }
        }
        if self.sys.subst_marker_matches() {
            if stats {
                SUBST_SYSTEM_SKIPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            if verify_subst_skip_enabled() {
                self.verify_subst_skip_is_noop();
            }
            return;
        }
        let mut iter = 0u32;
        let cap = 32u32;
        // Definitely assigned on the first (always-executed) loop iteration
        // before the post-loop read.
        let mut last_raised;
        loop {
            let before_subst_len = self.sys.eq_store.subst.len();
            last_raised = self.subst_system_once();
            let after_subst_len = self.sys.eq_store.subst.len();
            if after_subst_len == before_subst_len { break; }
            iter += 1;
            if iter >= cap { break; }
        }
        // Set the marker iff the FINAL executed pass raised NO signal: that
        // pass is an observed proof that (content_stamp, subst_stamp) is a
        // no-op point.  Any later content/subst mutation bumps a stamp, so the
        // stored pair stops matching — no explicit clear needed.
        if !last_raised {
            self.sys.record_subst_marker();
        }
    }

    /// Debug harness for the verified-identity skip: when the skip WOULD fire
    /// and `TAM_RS_VERIFY_SUBST_SKIP=1`, run the full pass loop anyway and
    /// `panic!` if it is not, in fact, a total no-op (any pass raised a signal,
    /// or the resulting `System` differs by content/ORDER from the pre-pass
    /// snapshot).  `System::eq` excludes the stamp Cells and compares every
    /// `Vec`/`Option` field positionally, so this catches value, reorder AND
    /// dedup bugs.  Certifies skip-CORRECTNESS (necessary, not a completeness
    /// proof).
    fn verify_subst_skip_is_noop(&mut self) {
        // Force the cached-bloom fact skip OFF for this verification re-run:
        // otherwise a wrong bloom skip reproduces in both the live pass and
        // this re-run, so `self.sys == snapshot` would hold and mask the bug.
        // With the full descent forced, this oracle independently certifies
        // BOTH the stamp machinery and the bloom.
        let _fp_off = FpSkipDisableGuard::new();
        let snapshot = self.sys.clone();
        let mut iter = 0u32;
        let cap = 32u32;
        loop {
            let before_subst_len = self.sys.eq_store.subst.len();
            let raised = self.subst_system_once();
            let after_subst_len = self.sys.eq_store.subst.len();
            if raised {
                panic!("TAM_RS_VERIFY_SUBST_SKIP: skipped subst_system pass \
                        raised a change signal — under-bumped stamp");
            }
            if after_subst_len == before_subst_len { break; }
            iter += 1;
            if iter >= cap { break; }
        }
        if self.sys != snapshot {
            panic!("TAM_RS_VERIFY_SUBST_SKIP: skipped subst_system changed the \
                    System (value / order / dedup) — under-bumped stamp");
        }
    }

    /// One pass of substSystem.  See [`subst_system`] for the loop wrapper.
    /// Returns `true` iff this pass raised ANY change signal (value, order,
    /// collision, rule-eq, or KU re-insert).  `subst_system` sets the
    /// verified-identity skip marker only after a pass that returns `false`.
    fn subst_system_once(&mut self) -> bool {
        if self.sys.eq_store.subst.is_empty() { return false; }
        let subst = self.sys.eq_store.subst.clone();
        // Hashed leaf-lookup view over the pass-invariant `subst`
        // (`SubstView`): every term walk below probes this one fixed map at
        // every `Lit::Var` leaf, so a single FxHash probe replaces the
        // `BTreeMap` descent — same entries, same lookup results,
        // byte-identical output.  Pass-local; dropped with the pass.
        let subst_view = tamarin_term::subst::SubstView::new(&subst);
        // Cached-bloom fact skip.  `fp_skip` is the per-pass
        // master enable (thread-local, verify oracle force-disables it);
        // `verify_fp`/`fp_stats` are once-read env gates.  `dom_bloom` is the
        // once-per-pass OR of the domain vars' bits — the SAME `var_bit` the
        // cached fact bloom uses (shared site, no divergent hash).  `subst` is
        // non-empty here (early-returned above), so `dom_bloom != 0`, which is
        // why the `u64::MAX` default bloom always descends (`MAX & dom != 0`).
        let fp_skip = FP_SKIP_ENABLED.with(|c| c.get());
        let verify_fp = verify_fp_enabled();
        let fp_stats = fp_stats_enabled();
        let dom_bloom: u64 = subst.dom().fold(0u64, |b, v| b | crate::fact::var_bit(v));
        // Substitution rewrites every term/fact/rule under the current
        // subst — vars in the domain get replaced (possibly by vars
        // with smaller idx), so max-var-idx can LOWER.  Invalidation of
        // `max_var_idx_cache` is CONDITIONAL per section below: most
        // passes are idempotent re-applications (the subst was already
        // applied by an earlier pass), where every rewrite is a value
        // no-op and the pass only re-sorts / dedups EQUAL values —
        // neither of which can change the max free-var idx.  Each
        // section tracks "did any value actually change" (via the same
        // COW `None`-when-unchanged contracts the rewrites already use)
        // and invalidates only then, so an identity pass keeps both
        // caches valid and the dozens of `bounds_max` calls per proof
        // step stay O(1) hits instead of full re-walks.
        // Build the parser-AST `VarSubst` ONCE for the whole pass.  It is
        // derived purely from `subst` (fixed above), so it is identical
        // for every `Disj` goal AND the formula/lemma substitution below.
        // Building this once avoids O(num_disj_goals × subst_size) cost:
        // spdm's attack lemmas carry ~15 `All…==>#x=#y` uniqueness
        // disjuncts, so a per-goal rebuild was the single largest
        // avoidable cost in the proof/refine hot path (~7.5% of the whole
        // run in `perf`). Built once here, reused everywhere.
        //
        // Further: the parser subst is consumed ONLY by `Disj` goals (the
        // goal loop below) and the formula/solved-formula/lemma rewrites
        // (after the loop).  `build_parser_subst_from_eq_store` chain-
        // chases and `lnterm_to_term`-converts EVERY eq-store entry, which
        // is pure waste when the system carries none of those — common in
        // deep proof states where the lemma's formulas are already
        // discharged.  Gate the build so it only runs when a consumer
        // exists.
        let needs_parser_subst = !self.sys.formulas.is_empty()
            || !self.sys.solved_formulas.is_empty()
            || !self.sys.lemmas.is_empty()
            || self.sys.goals.iter().any(|(g, _)| matches!(g, Goal::Disj(_)));
        let parser_subst: crate::guarded::VarSubst = if needs_parser_subst {
            build_parser_subst_from_eq_store(&subst)
        } else {
            crate::guarded::VarSubst::default()
        };
        let map_var = |v: tamarin_term::lterm::LVar| -> tamarin_term::lterm::LVar {
            // Keyed image probe: a Var→Var binding renames the id; an
            // app-headed or absent image keeps the original var — the same
            // result `apply_vterm` gives on a `Lit::Var` term, minus the
            // temporary term construction.
            match subst_view.image_of(&v) {
                Some(tamarin_term::term::Term::Lit(
                    tamarin_term::vterm::Lit::Var(w))) => w.clone(),
                _ => v,
            }
        };
        // 1. Nodes: rewrite node ids and rule contents. When two
        //    nodes collapse to the same canonical id, queue an
        //    equality between their rules' fact lists (mirrors
        //    Haskell's `setNodes` → `solveRuleEqs`). We solve those
        //    equalities AFTER the rest of substSystem has run, so the
        //    triggered re-substitution sees a consistent state.
        let mut nodes = std::sync::Arc::unwrap_or_clone(
            std::mem::take(&mut self.sys.content_mut_untracked().nodes));
        // HS-faithful node-merge keep-order: `substNodeIds` (Reduction.hs:629-634)
        // reads `M.toList sNodes` — SORTED by node-id — so when several nodes
        // collapse to one id (eq-store node-id binding), `setNodes`'
        // stable `groupSortOn` keeps the rule of the LOWEST-OLD-ID node.  RS
        // stored nodes in a Vec in insertion order (conjoin appends the
        // freshly-grafted source case BEFORE the live nodes), so the dedup
        // below kept the GRAFTED node's rule (high idx) and eliminated the
        // live witness (low idx) — desyncing the witness multiset-nonce from
        // the lemma witness var (e.g. alethea `#a2` noSel vs the BB_2 multiset
        // nonce), which then leaves the downstream `#a3` AgSt_A3 merge a
        // disjoint 2-unifier (→ deferred `splitEqs`) instead of HS's shared
        // 1-unifier (→ direct `by contradiction`).  Sort by node-id here to
        // mirror `M.toList`, so the live/lower-idx node's rule survives.
        nodes.sort_by(|a, b| a.0.cmp(&b.0));
        let mut new_nodes: Vec<(crate::constraint::constraints::NodeId, RuleACInst)>
            = Vec::with_capacity(nodes.len());
        let mut id_to_index: tamarin_utils::FastMap<crate::constraint::constraints::NodeId, usize>
            = tamarin_utils::FastMap::default();
        // Accumulate fact-eqs split by component so we can flatten them in
        // Haskell `solveRuleEqs` order: ALL conclusions (across every colliding
        // node), THEN all premises, THEN all actions
        // (Reduction.hs:752-754: `map (fmap (get rConcs)) eqs ++
        //  map (fmap (get rPrems)) eqs ++ map (fmap (get rActs)) eqs`).
        // Building three separate vectors and concatenating at the end is the
        // faithful "batch transpose" (all conclusions, then premises, then actions).
        let mut conc_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> = Vec::new();
        let mut prem_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> = Vec::new();
        let mut act_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> = Vec::new();
        let mut shape_mismatch = false;
        // Helper: apply the full term substitution to a fact's terms.
        // `map_var` above only handles Var→Var rewrites (used for
        // node-ids), but the eq-store can also bind a var to an
        // app-headed term (e.g. `pkR → pk(ltkR)` from a !Pk-edge
        // unification).  For those entries, `map_free` falls back
        // to the original var, leaving stale `pkR` in rule actions.
        // Use `apply_vterm` on the full term to substitute through
        // app-headed bindings.  Mirrors Haskell's `substSystem`
        // which uses `apply` on rules' facts as full-term subst.
        // Port of Haskell's `normDG ctxt sys` (System.hs:1287-1289) +
        // `normRule` (Rule.hs:744-748): after the eq-store substitution
        // rewrites a fact's terms, the result may be non-normal — e.g.
        // `verify(revealSign(~r,~sk), ~r, pk(~sk))` reduces to `true`
        // via the signing builtin's [variant] equations.  Maude's
        // `unify in MSG` does NOT apply [variant] eqs during
        // unification, so downstream restrictions like
        // `Eq_check_succeed` (`All x y. Eq(x,y) ⇒ x=y`) would
        // erroneously contradict `verify(...) = true` even though
        // `reduce` would close it.  HS-faithful: HS's substSystem
        // (Reduction.hs:623-633, see line 634) does NOT normalise — `normDG` (System.hs:
        // 1283) runs only inside `impliedOrInitial`.  Normalising here
        // eagerly reduces e.g. `checksign(sign(m,k), pk(k))` to `m`,
        // which loses the head shape needed by source-case matching
        // (test4 lost c_checksign as a candidate).  Worse, the eager
        // normalise blocked HS's `hasNonNormalTerms` contradiction from
        // ever firing on a non-normal term shape (Responder_secrecy's
        // split_case_3/Initiator non-normal contradiction was lost).
        // COW walk: reuse the original Arc for every term the subst leaves
        // structurally unchanged (dropping the per-term `t.clone()`), and
        // return `None` when EVERY term is unchanged so the caller keeps the
        // original fact untouched — skipping the terms `Vec` collect and the
        // tag/annotations clones.  Byte-safe: an unchanged term is already
        // AC-normal, so a full rebuild would produce a structurally identical
        // fact — only `Arc` identity differs, and nothing output-bearing
        // observes `Arc` identity.
        let apply_to_fact = |fa: &crate::fact::LNFact| -> Option<crate::fact::LNFact> {
            if fp_stats {
                FP_FACT_DESCENTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            // Cached-bloom fast path: if no free var of the fact
            // shares a bit with any domain var, the fact contains no domain var
            // (superset invariant), so every term returns `None` — return
            // `None` (COW-unchanged), skipping the whole per-term descent.
            if fp_skip && fa.bloom() & dom_bloom == 0 {
                if verify_fp { verify_fact_unchanged(fa, &subst_view); }
                if fp_stats {
                    FP_FACT_SKIPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                return None;
            }
            let mut new_terms: Option<Vec<tamarin_term::lterm::LNTerm>> = None;
            for (i, t) in fa.terms.iter().enumerate() {
                if let Some(changed) = subst_view.apply_changed(t) {
                    new_terms.get_or_insert_with(|| fa.terms.clone())[i] = changed;
                }
            }
            new_terms.map(|terms| {
                // Subst rebuild — frees change; the computing constructor
                // recomputes the bloom from the post-subst terms internally
                // (never copy `fa`'s bloom: the rebuild changes the free-var set).
                crate::fact::LNFact::fresh_annotated(fa.tag.clone(), fa.annotations.clone(), terms)
            })
        };
        let dbg_set_nodes = tamarin_utils::env_gate!("TAM_DBG_SET_NODES");
        let nodes_in = nodes.len();
        let mut collisions = 0usize;
        let mut shape_mm = 0usize;
        // Haskell-faithful `substNodes` order (Reduction.hs:607-609):
        //   substNodes = substNodeIds <*
        //                ((modM sNodes . M.map . apply) =<< getM sSubst)
        //
        // `substNodeIds` runs FIRST: applies the eq-store subst to
        // NODE IDs only (NOT to rule contents) and calls `setNodes`,
        // which detects id collisions and emits `solveRuleEqs` on
        // the UN-SUBSTITUTED rules.  This is critical for the
        // Client_auth chain: case's Register_pk has `~ltkS` post-
        // refine, live's existing Register_pk has `~ltk`; setNodes
        // sees them at the same id after node-id rename, emits
        // rule_eqs `pk(~ltk) = pk(~ltkS)`, which then unifies them.
        //
        // After substNodeIds, HS applies subst to rule contents via
        // `M.map . apply`.
        //
        // RS mirrors HS in two passes: Pass 1 renames node-ids only (rules stay
        // un-substituted so rule_eqs at collision time see the raw rules), Pass 2
        // applies the fact-term substitution.
        // Cache-invalidation change bit for the node section: set when a
        // node id is actually renamed, two nodes collide (one entry is
        // dropped), or a rule's contents are rewritten in Pass 2.  When it
        // stays `false`, the node multiset is value-identical (Pass 1's
        // sort is order-only), so both max caches remain exact.
        let mut nodes_value_changed = false;
        let mut id_renamed_nodes: Vec<(crate::constraint::constraints::NodeId, RuleACInst)> = Vec::new();
        for (id, rule) in nodes {
            let id_orig = id.clone();
            let new_id = map_var(id);
            if new_id != id_orig { nodes_value_changed = true; }
            if tamarin_utils::env_gate!("TAM_DBG_SUBST_NODE_RENAME") && new_id != id_orig {
                let path = crate::constraint::solver::trace::case_path_string();
                let rule_name = rule_case_name(&rule);
                eprintln!("[subst_node_rename] path={} {}.{} → {}.{}  rule={}",
                    path, id_orig.name, id_orig.idx, new_id.name, new_id.idx, rule_name);
            }
            // Pass 1: node-id rename only (HS `substNodeIds` `apply subst`
            // on the id, not the rule body).  Keep the rule UN-substituted.
            id_renamed_nodes.push((new_id, rule));
        }
        // Pass 1b: dedupe by new_id, detecting collisions on RAW rules.
        let dbg_shape = tamarin_utils::env_gate!("TAM_DBG_SHAPE_MM");
        for (new_id, rule) in id_renamed_nodes {
            match id_to_index.get(&new_id).copied() {
                Some(i) => {
                    collisions += 1;
                    let kept: &RuleACInst = &new_nodes[i].1;
                    if kept.info != rule.info {
                        shape_mismatch = true;
                        shape_mm += 1;
                        if dbg_shape {
                            let cpath = crate::constraint::solver::trace::case_path_string();
                            eprintln!("[shape_mm:info] path={} collide_at={}.{} kept_rule={} new_rule={}",
                                cpath, new_id.name, new_id.idx,
                                rule_case_name(kept), rule_case_name(&rule));
                        }
                    } else if kept.premises.len() != rule.premises.len()
                        || kept.conclusions.len() != rule.conclusions.len()
                        || kept.actions.len() != rule.actions.len()
                    {
                        shape_mismatch = true;
                        if dbg_shape {
                            let cpath = crate::constraint::solver::trace::case_path_string();
                            eprintln!("[shape_mm:arity] path={} collide_at={}.{} kept={}/{}/{} new={}/{}/{}",
                                cpath, new_id.name, new_id.idx,
                                kept.premises.len(), kept.conclusions.len(), kept.actions.len(),
                                rule.premises.len(), rule.conclusions.len(), rule.actions.len());
                        }
                    } else {
                        // Collect per component; concatenated conc++prem++act
                        // after the loop to match Haskell `solveRuleEqs`.
                        for (a, b) in kept.conclusions.iter().zip(rule.conclusions.iter()) {
                            conc_eqs.push(tamarin_term::rewriting::Equal {
                                lhs: a.clone(), rhs: b.clone(),
                            });
                        }
                        for (a, b) in kept.premises.iter().zip(rule.premises.iter()) {
                            prem_eqs.push(tamarin_term::rewriting::Equal {
                                lhs: a.clone(), rhs: b.clone(),
                            });
                        }
                        for (a, b) in kept.actions.iter().zip(rule.actions.iter()) {
                            act_eqs.push(tamarin_term::rewriting::Equal {
                                lhs: a.clone(), rhs: b.clone(),
                            });
                        }
                    }
                }
                None => {
                    id_to_index.insert(new_id.clone(), new_nodes.len());
                    new_nodes.push((new_id, rule));
                }
            }
        }
        // Flatten the component-grouped fact-eqs in Haskell `solveRuleEqs`
        // order: all conclusions, then all premises, then all actions.
        let mut rule_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> =
            Vec::with_capacity(conc_eqs.len() + prem_eqs.len() + act_eqs.len());
        rule_eqs.append(&mut conc_eqs);
        rule_eqs.append(&mut prem_eqs);
        rule_eqs.append(&mut act_eqs);
        // Pass 2: NOW apply the full term substitution to the surviving
        // rules' fact terms (mirrors HS's `M.map . apply` AFTER
        // substNodeIds).
        // COW over a fact list: `None` when every fact is unchanged, so the
        // rule keeps its original `Vec` (sharing its `Arc`s) with no realloc.
        let apply_to_facts = |facts: &[crate::fact::LNFact]|
            -> Option<Vec<crate::fact::LNFact>> {
            let mut out: Option<Vec<crate::fact::LNFact>> = None;
            for (i, fa) in facts.iter().enumerate() {
                if let Some(changed) = apply_to_fact(fa) {
                    out.get_or_insert_with(|| facts.to_vec())[i] = changed;
                }
            }
            out
        };
        // COW over `new_vars`: same convention on bare terms.
        let apply_to_new_vars = |terms: &[tamarin_term::lterm::LNTerm]|
            -> Option<Vec<tamarin_term::lterm::LNTerm>> {
            let mut out: Option<Vec<tamarin_term::lterm::LNTerm>> = None;
            for (i, t) in terms.iter().enumerate() {
                if let Some(changed) = subst_view.apply_changed(t) {
                    out.get_or_insert_with(|| terms.to_vec())[i] = changed;
                }
            }
            out
        };
        for (_, rule) in new_nodes.iter_mut() {
            let new_premises = apply_to_facts(&rule.premises);
            let new_conclusions = apply_to_facts(&rule.conclusions);
            let new_actions = apply_to_facts(&rule.actions);
            let new_new_vars = apply_to_new_vars(&rule.new_vars);
            // When every component is structurally unchanged, keep the
            // original rule value — no `Rule` rebuild, no `Vec` allocations.
            // A rebuild would produce a structurally identical rule (only
            // `Arc` identity would differ), so keeping it is byte-neutral.
            if new_premises.is_none()
                && new_conclusions.is_none()
                && new_actions.is_none()
                && new_new_vars.is_none()
            {
                continue;
            }
            nodes_value_changed = true;
            *rule = crate::rule::Rule {
                info: rule.info.clone(),
                premises: new_premises.unwrap_or_else(|| rule.premises.clone()),
                conclusions: new_conclusions.unwrap_or_else(|| rule.conclusions.clone()),
                actions: new_actions.unwrap_or_else(|| rule.actions.clone()),
                new_vars: new_new_vars.unwrap_or_else(|| rule.new_vars.clone()),
            };
        }
        if dbg_set_nodes && (nodes_in > 0) {
            eprintln!("[SET_NODES_RS] nodes_in={} collisions={} shape_mismatches={} rule_eqs_queued={}",
                nodes_in, collisions, shape_mm, rule_eqs.len());
        }
        // subst_system rewrites node terms (and may merge colliding node
        // ids) — the node max can DROP, so invalidate the node component
        // too, not just the full cache.  Conditional: an identity pass
        // (no id renamed, no collision, every rule COW-unchanged) leaves
        // the node multiset value-identical, so both caches stay exact.
        if nodes_value_changed || collisions > 0 {
            self.sys.invalidate_max_var_idx_cache();
            self.sys.invalidate_node_max_cache();
        }
        self.sys.content_mut_untracked().nodes = std::sync::Arc::new(new_nodes);
        if shape_mismatch {
            // Force a `gfalse` formula so `has_false_formula` picks up
            // the contradiction in the next contradictions check.
            let bot = crate::guarded::gfalse();
            if !crate::guarded::stores_contains(&self.sys.formulas, &bot) {
                self.sys.invalidate_max_var_idx_cache();
                self.sys.formulas_mut_untracked().push(std::sync::Arc::new(bot));
                self.changed = ChangeIndicator::Changed;
            }
            // Also flip `eq_store.is_false` so the simplify-time filter
            // in `exec_proof_method`'s SolveGoal arm sees this as the
            // Haskell-faithful mzero-equivalent and drops the case from
            // the resulting case map.  Haskell's `setNodes` →
            // `solveRuleEqs` (Reduction.hs:748-749, see line 751) contradictoryIf fires
            // mzero on rInfo / fact-shape mismatch, so the case
            // disappears from `runReduction`'s Disj.  Setting is_false
            // here matches that shape on the SolveGoal proof-tree filter.
            if self.set_eq_store_false() {
                self.changed = ChangeIndicator::Changed;
            }
        }
        // 2. Edges: rewrite both endpoints' node ids.  Track value
        // changes for the conditional cache invalidation — the sort +
        // dedup below only reorder / drop EQUAL values, which cannot
        // change the max free-var idx.
        let mut edges_value_changed = false;
        for e in self.sys.content_mut_untracked().edges.iter_mut() {
            let new_src = map_var(e.src.0.clone());
            if new_src != e.src.0 { edges_value_changed = true; e.src.0 = new_src; }
            let new_tgt = map_var(e.tgt.0.clone());
            if new_tgt != e.tgt.0 { edges_value_changed = true; e.tgt.0 = new_tgt; }
        }
        // Full (non-adjacent) dedup: see comment in
        // simplify::apply_node_eqs.  Vec::dedup() only removes
        // adjacent duplicates; after var-rename the duplicates may
        // be scattered, so we must sort first.
        let mut tmp: Vec<_> = std::mem::take(&mut self.sys.content_mut_untracked().edges);
        tmp.sort();
        tmp.dedup();
        if edges_value_changed {
            self.sys.invalidate_max_var_idx_cache();
        }
        self.sys.content_mut_untracked().edges = tmp;
        // 3. Last-atom.
        let mut last_atom_changed = false;
        if let Some(last) = self.sys.content_mut_untracked().last_atom.take() {
            let new_last = map_var(last.clone());
            if new_last != last {
                last_atom_changed = true;
                self.sys.invalidate_max_var_idx_cache();
            }
            self.sys.content_mut_untracked().last_atom = Some(new_last);
        }
        // 4. Less atoms.
        //
        // HS-faithful: HS's `substLessAtoms = substPart sLessAtoms`
        // (Reduction.hs:721-740, see line 728) applies the eq-store subst to
        // `sLessAtoms :: Set LessAtom` via the `Apply s (S.Set a)`
        // instance (`SubstVFree.hs:345-346`): `S.map (apply subst)`.
        // `S.map` rebuilds the set from the post-subst image, which
        // INHERENTLY DEDUPES — two distinct pre-subst atoms whose
        // images collapse to the same `(smaller, larger, reason)`
        // tuple become one Set element.
        //
        // RS's `less_atoms: Vec<LessAtom>` doesn't auto-dedupe, so
        // post-subst duplicates survive.  Mirror HS by deduping after
        // the in-place rewrite.  Without this, `compute_compare_systems_key`
        // (used by `removeRedundantCases`) serialises duplicate
        // `s<l` entries, producing different keys for systems that
        // HS considers redundant.
        //
        // Triggering case: Scott::key_secrecy.  Two source-cases'
        // saturated systems that HS dedupes (75→73 in
        // `removeRedundantCases` at ProofMethod.hs:348-459, see line 455) survived
        // in RS, leaving 18 Reveal_ltk arms where HS shows 16.
        //
        // Source: HS `Theory.Constraint.Solver.Reduction.substLessAtoms`
        //         + `Term.Substitution.SubstVFree.SubstVFree.hs:345`.
        let mut new_less: Vec<crate::constraint::constraints::LessAtom>
            = Vec::with_capacity(self.sys.less_atoms.len());
        // Dedup by `(smaller, larger)`: `LessAtom`'s `Eq` ignores `reason`
        // (constraints.rs:92-95), so a `FastSet` of seen pairs reproduces the
        // previous `new_less.iter().any(|x| x == &la)` scan exactly — first
        // occurrence wins, insertion order preserved, bit-identical Vec — but
        // in O(1) per atom instead of O(n²) over the growing list (this scan
        // was ~half of `subst_system_once` self-time on Less-heavy systems).
        let mut seen_less: tamarin_utils::FastSet<(
            crate::constraint::constraints::NodeId,
            crate::constraint::constraints::NodeId,
        )> = tamarin_utils::FastSet::default();
        // Change bit for the conditional cache invalidation — the dedup
        // drops only atoms whose image EQUALS a kept one, so an
        // all-identity rewrite cannot change the max free-var idx.
        let mut less_value_changed = false;
        for la in std::mem::take(&mut self.sys.content_mut_untracked().less_atoms) {
            let mut la = la;
            let new_smaller = map_var(la.smaller.clone());
            if new_smaller != la.smaller { less_value_changed = true; la.smaller = new_smaller; }
            let new_larger = map_var(la.larger.clone());
            if new_larger != la.larger { less_value_changed = true; la.larger = new_larger; }
            if seen_less.insert((la.smaller.clone(), la.larger.clone())) {
                new_less.push(la);
            }
        }
        if less_value_changed {
            self.sys.invalidate_max_var_idx_cache();
        }
        self.sys.content_mut_untracked().less_atoms = new_less;
        // 5. Goals: rewrite the Goal's free vars. Goals are deduped
        //    structurally; collapsed goals merge by keeping the first
        //    occurrence.
        let mut goals = std::sync::Arc::unwrap_or_clone(
            std::mem::take(&mut self.sys.content_mut_untracked().goals));
        // HS-faithful (Reduction.hs:637-651): `substGoals` iterates
        // `M.toList sGoals` which is Goal-Ord order (NodeId-first for
        // ActionG / PremiseG / ChainG).  The order matters because
        // `insertAction` for re-inserted KU msg-var goals assigns a
        // NEW gsNr from `sNextGoalNr` (which monotonically increases),
        // so the iteration order determines which goal gets the lower
        // post-subst nr.  Iterating in insertion order (Vec push order)
        // instead diverges from HS.
        //
        // Closes CH07::executable and CRxor::executable XOR diffs
        // (8 lines each) where HS picked `KU(~nb)` first (lower
        // post-subst nr because its NodeId was smaller) while RS
        // picked `KU(~na)` first.
        goals.sort_by(|(g1, _), (g2, _)|
            crate::constraint::solver::goals::goal_cmp(g1, g2));
        // Mirror node-fact handling above: apply the eq-store
        // substitution to each goal term with no Maude normalization.
        // HS's `substGoals` applies subst via the `Apply` instance and
        // does NOT normalise; `normDG` runs only inside impliedOrInitial
        // (System.hs:1253-1283, see line 1283).
        let mut new_goals: Vec<(Goal, crate::constraint::system::GoalStatus)>
            = Vec::with_capacity(goals.len());
        // Dedup keys, kept parallel to `new_goals`: precomputing each
        // goal's `canonical_goal_for_dedup` once (rather than re-deriving
        // it for every accumulated goal on every iteration) keeps the
        // merge below from being quadratic in canonicalisation cost.
        let mut new_goal_keys: Vec<Goal> = Vec::with_capacity(goals.len());
        // Change bit for the goal section's conditional cache
        // invalidation (`Cell` because several closures below set it
        // while the main loop also writes it).  Goal merges and
        // `normalise_disj_list` dedups drop only values EQUAL to kept
        // ones, and the pre-loop sort is order-only — neither can change
        // the max free-var idx, so only genuine term/id rewrites count.
        let goals_value_changed = std::cell::Cell::new(false);
        // Apply full term substitution to a fact's term list — required
        // when the eq-store maps a var to a non-var term (e.g.
        // `m → h(...)` from an Eq restriction), in which case
        // `map_var` falls back to identity and the goal's terms never
        // get rewritten.  Mirrors Haskell's `substFacts` in
        // `substSystem`.
        // COW: rewrite only the terms the subst actually changes and keep
        // the original fact when none do — a full rebuild would be
        // value-identical (mirrors `apply_to_fact` in the node section) —
        // and let a performed rebuild double as the change bit.
        let apply_fact = |fa: crate::fact::LNFact| -> crate::fact::LNFact {
            if fp_stats {
                FP_FACT_DESCENTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            // Cached-bloom fast path: unchanged fact ⇒ return `fa`
            // as-is and do NOT set `goals_value_changed` (identical to the loop
            // producing all-`None`).
            if fp_skip && fa.bloom() & dom_bloom == 0 {
                if verify_fp { verify_fact_unchanged(&fa, &subst_view); }
                if fp_stats {
                    FP_FACT_SKIPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                return fa;
            }
            let mut new_terms: Option<Vec<tamarin_term::lterm::LNTerm>> = None;
            for (i, t) in fa.terms.iter().enumerate() {
                if let Some(changed) = tamarin_term::subst::apply_vterm_changed(&subst, t) {
                    new_terms.get_or_insert_with(|| fa.terms.clone())[i] = changed;
                }
            }
            match new_terms {
                Some(terms) => {
                    goals_value_changed.set(true);
                    // Subst rebuild — frees change; the computing constructor
                    // recomputes the bloom from the post-subst terms internally
                    // (never copy `fa`'s bloom: the rebuild changes the free-var set).
                    crate::fact::Fact::fresh_annotated(fa.tag, fa.annotations, terms)
                }
                None => fa,
            }
        };
        // `map_var` twin that records a genuine node-id rewrite.  Direct
        // binding lookup, value-equivalent to `map_var` on a bare var:
        // no binding, or a non-Var image, keeps `v` (exactly `map_var`'s
        // `else { v }` fallback); a Var image is a genuine rename
        // (`from_list` drops trivial `x ~> x` entries, so `w != v`).
        let map_var_tracked = |v: crate::constraint::constraints::NodeId|
            -> crate::constraint::constraints::NodeId {
            match subst.image_of(&v) {
                Some(tamarin_term::term::Term::Lit(
                    tamarin_term::vterm::Lit::Var(w))) => {
                    goals_value_changed.set(true);
                    w.clone()
                }
                _ => v,
            }
        };
        // Mirrors Haskell's `substGoals` (Reduction.hs:637-651) — for
        // KU action goals whose pre-subst term is a msg-var, product,
        // or union AND whose term actually changes via substitution,
        // re-insert via `insert_action`-equivalent so the pair/inv/prod
        // auto-decomp fires retroactively.  This re-insert path is sound
        // only because `system_max_idx` walks goals/formulas/eq_store: an
        // incomplete max-idx lets `freshen_system` assign colliding idxs
        // across grafted instances, conflating Maude witnesses in
        // chain-saturated graft cases.
        let mut to_insert_action: Vec<(crate::constraint::constraints::NodeId,
                                       crate::fact::LNFact,
                                       crate::constraint::system::GoalStatus)>
            = Vec::new();
        for (g, st) in goals {
            // SKIP-SOUNDNESS PIN: the `!st.solved`
            // read below is the SOLE consumer of goal STATUS anywhere in
            // subst_system_once.  The verified-identity skip's `goals_mut`
            // status-flip carve-out (status flips do NOT bump `content_stamp`)
            // is sound ONLY because this guard also requires an ACTUAL apply
            // change to the KU term (`apply_changed(...).is_some_and(m_post !=
            // m_pre)`), which is impossible while σ is frozen and the term is
            // already fully propagated — so a status flip alone can never alter
            // pass output.  If you add a goal-STATUS read here or elsewhere in
            // the pass, or relax the `apply_changed` gate, this carve-out's
            // soundness argument no longer holds — either re-establish it or
            // bump `content_stamp` on the `goals_mut` handout.
            let needs_reinsert = if let Goal::Action(_, fa) = &g {
                if fa.tag == crate::fact::FactTag::Ku && !st.solved {
                    if let Some(m_pre) = fa.terms.first() {
                        // Guard-first COW probe: `apply_changed == None`
                        // means the applied term equals `m_pre` (the original
                        // is reused), so no deep compare is needed there; the
                        // `m_post != m_pre` compare runs only on an actual
                        // rebuild (a rebuild can still be value-equal via
                        // an AC re-sort,
                        // so the compare itself is kept).
                        (tamarin_term::lterm::is_msg_var(m_pre) || is_product_or_union(m_pre))
                            && subst_view.apply_changed(m_pre)
                                .is_some_and(|m_post| m_post != *m_pre)
                    } else { false }
                } else { false }
            } else { false };
            // Disj goal rewriting: Disjs carry a `Guarded` body whose
            // free variables are `VarSpec` (parser-AST), same form
            // used in `formulas`/`lemmas`.  Route through
            // `subst_guarded` so saturate-time Disj goals get their
            // bodies re-narrowed when runtime unification populates
            // the eq_store — mirrors Haskell's `substSystem`
            // (System.hs) applying the substitution to ALL goal
            // bodies including Disjs.  Without this, a Disj goal
            // added to `sys.goals` at saturate-time retains the
            // saturate-time vars even after runtime narrowing
            // populates `eq_store`; downstream `is_open_in_sys` then
            // auto-solves the stale Msg-var KU arm.  Net +3 lemmas
            // in corpus (NSLPK3_untagged::session_key_setup_possible
            // + Destroy_charn + Loop_charn).
            let g2 = match g {
                Goal::Action(i, fa) =>
                    Goal::Action(map_var_tracked(i), apply_fact(fa)),
                Goal::Premise(p, fa) =>
                    Goal::Premise((map_var_tracked(p.0), p.1), apply_fact(fa)),
                Goal::Chain(c, p) =>
                    Goal::Chain(
                        (map_var_tracked(c.0), c.1),
                        (map_var_tracked(p.0), p.1)),
                Goal::Disj(d) => {
                    if parser_subst.is_empty() {
                        Goal::Disj(d)
                    } else {
                        let new_alts: Vec<_> = d.0.into_iter()
                            .map(|alt| {
                                // COW mirror of the store rewrite's
                                // `apply_to_fixpoint` (below): `subst_guarded_cow
                                // == None` ⇔ the fixpoint loop broke immediately
                                // (`nxt == cur`), so reuse the owned `alt` with
                                // zero clones when both the subst and the trailing
                                // AC-canon are no-ops.  Byte-identical to the eager
                                // 16-round `subst_guarded` + `canonicalize_ac`.
                                let mut cur = match crate::guarded::subst_guarded_cow(
                                    &alt, &parser_subst)
                                {
                                    None => return match crate::guarded::
                                        canonicalize_ac_in_guarded_cow(&alt)
                                    {
                                        Some(c) => {
                                            goals_value_changed.set(true);
                                            c
                                        }
                                        None => alt,
                                    },
                                    Some(s0) => {
                                        goals_value_changed.set(true);
                                        s0
                                    }
                                };
                                for _ in 0..15 {
                                    match crate::guarded::subst_guarded_cow(
                                        &cur, &parser_subst)
                                    {
                                        None => break,
                                        Some(nxt) => cur = nxt,
                                    }
                                }
                                // Re-canonicalise AC after substitution so the
                                // substituted Disj-goal body matches the
                                // flat-sorted re-derived form for the goal-store
                                // dedup (see the formula-subst comment in
                                // `subst_system_once`).
                                crate::guarded::canonicalize_ac_in_guarded_cow(&cur)
                                    .unwrap_or(cur)
                            })
                            .collect::<Vec<_>>();
                        // Normalise the disjunct LIST in lockstep with the
                        // GDisj formula twin (HS 150f5eba substGoals DisjG
                        // arm: `DisjG (normaliseDisjList (apply subst
                        // disj))`) — a subst that identifies two variables
                        // can make two alts equal; the formula twin's list
                        // is deduplicated by `normalise_stored_formula`, so
                        // the goal key must be too or the twin stores
                        // desynchronise (gcm livelock class).
                        let new_alts = crate::guarded::normalise_disj_list(&new_alts);
                        Goal::Disj(crate::constraint::constraints::Disj(new_alts))
                    }
                },
                Goal::Split(s) => Goal::Split(s),
                Goal::Subterm((s, t)) => {
                    // COW twin of `apply_term` with change tracking (same
                    // `None`-when-unchanged contract as `apply_fact`).
                    let ns = match tamarin_term::subst::apply_vterm_changed(&subst, &s) {
                        Some(n) => { goals_value_changed.set(true); n }
                        None => s,
                    };
                    let nt = match tamarin_term::subst::apply_vterm_changed(&subst, &t) {
                        Some(n) => { goals_value_changed.set(true); n }
                        None => t,
                    };
                    Goal::Subterm((ns, nt))
                }
            };
            if needs_reinsert {
                if let Goal::Action(i, fa) = &g2 {
                    to_insert_action.push((i.clone(), fa.clone(), st.clone()));
                }
            } else {
                // HS-faithful merge: mirror `M.insertWith combineGoalStatus`
                // (Reduction.hs:612-615, 648, 812).  When subst rewrites
                // two pre-subst goals to the same post-subst form, merge
                // their statuses:
                //   solved  = solved_old  || solved_new
                //   gsNr    = min age_old age_new        ← HS-faithful!
                //   looping = looping_old || looping_new
                //
                // HS uses `Data.Map.insertWith combineGoalStatus`: when
                // the key matches an existing entry, `combineGoalStatus`
                // is called with the OLD value and the NEW value, and
                // its `min age1 age2` chooses the SMALLER nr regardless
                // of iteration order.
                //
                // Comparison key: `canonical_goal_for_dedup` (mirrors
                // HS's Map-key equality on Goal, which is structural Eq
                // — but Rust's `VarSpec`-bound Disjs need
                // `normalize_bound_lvars` to match HS's DeBruijn
                // semantics, see system.rs::canonical_goal_for_dedup).
                let canon_g2 = crate::constraint::system::canonical_goal_for_dedup(&g2);
                if let Some(i) = new_goal_keys.iter().position(|k| *k == *canon_g2) {
                    let st_old = &mut new_goals[i].1;
                    let merged_solved = st_old.solved || st.solved;
                    let merged_looping = st_old.looping || st.looping;
                    let merged_nr = std::cmp::min(st_old.nr, st.nr);
                    // A status merge that changes a kept
                    // goal's status is a real System mutation with no term
                    // signal.  Flag it so the "zero change" verdict is exact.
                    if merged_solved != st_old.solved
                        || merged_looping != st_old.looping
                        || merged_nr != st_old.nr
                    {
                        goals_value_changed.set(true);
                    }
                    st_old.solved = merged_solved;
                    st_old.looping = merged_looping;
                    st_old.nr = merged_nr;
                } else {
                    // `new_goal_keys` is a parallel comparison-key cache; the
                    // ACTUAL goal stored is the original `g2` (into `new_goals`).
                    // Materialise the owned key BEFORE moving `g2` — since
                    // canonicalisation is the identity, this key `==` `g2`.
                    let key = canon_g2.into_owned();
                    new_goals.push((g2, st));
                    new_goal_keys.push(key);
                }
            }
        }
        // Conditional: a `needs_reinsert` removal always implies a changed
        // Action fact (`m_post != m_pre`), so it is covered by the flag.
        if goals_value_changed.get() {
            self.sys.invalidate_max_var_idx_cache();
        }
        self.sys.content_mut_untracked().goals = std::sync::Arc::new(new_goals);
        let had_insert_action = !to_insert_action.is_empty();
        for (i, fa, st) in to_insert_action {
            self.insert_goal_with_loop_flag(Goal::Action(i, fa), st.looping);
        }
        // Formulas / solved formulas / lemmas: port of Haskell's
        // `substFormulas`, `substSolvedFormulas`, `substLemmas` (all
        // run inside `substSystem`).  Our formulas are stored as
        // `Guarded` over parser-AST `VarSpec`, while the eq-store's
        // substitution is over `LVar`s.  Build a parser-AST `VarSubst`
        // by converting each LVar→LNTerm entry to (name, idx)→Term,
        // then apply via `subst_guarded` (which already respects
        // quantifier shadowing).  Without this, free variables in
        // formulas (e.g. a lemma's outer Skolem `key` after the
        // proof has unified `key = ~k15`) never get substituted, and
        // simplify-time formula-evaluation (eval_formula_atoms,
        // insert_implied_formulas) misses contradictions like a
        // surviving `All r. Rev(?key) @ r ==> ⊥` when the trace
        // contains `Rev(~k15) @ vr_14` — that's a soundness gap.
        let formula_subst: &crate::guarded::VarSubst = &parser_subst;
        // Hoisted out of the `if` below so it is in scope for the `raised`
        // return: set true iff a formula/solved-formula/lemma value changed.
        let mut formulas_value_changed = false;
        if !formula_subst.is_empty() {
            // Iterate per-formula until subst_guarded reaches a fixpoint
            // — eq-store entries can form chains (e.g. `x:1 → x:13`,
            // `x:13 → ~n:28`); a single application only reduces by one
            // step.  Haskell's `substSystem` operates on a transitively-
            // closed substitution by construction; our `compose` is
            // closed at insert time but later `restrict_*` / cleanup
            // passes can prune intermediate entries leaving a
            // partially-applied formula-subst.  Bounded loop (16 steps)
            // to defend against degenerate cycles.
            // Copy-on-write: returns `None` when the formula is wholly
            // unchanged (subst touches no leaf AND no AC node needs re-sorting),
            // so the caller skips the store entirely with zero allocation.  This
            // replaces three unconditional deep rebuilds (clone + subst + canon)
            // per stored formula per `subst_system` call — the dominant residual
            // guarded-clone cost after the dedup-canon hoist.  Byte-identical:
            // `subst_guarded_cow == None` ⇔ the original loop broke immediately
            // (`nxt == cur`), and `canonicalize_ac_in_guarded_cow == None` ⇔ the
            // original `canonicalize` returned a value `== cur`.
            let apply_to_fixpoint = |f: &Guarded| -> Option<Guarded> {
                let mut cur = match crate::guarded::subst_guarded_cow(f, formula_subst) {
                    // Subst is a structural no-op; the only possible change is
                    // the trailing canonicalisation (mirror `canonicalize(f)`).
                    // A canon change can equalise sibling connectives, so
                    // re-normalise the changed result (150f5eba boundary).
                    None => return crate::guarded::canonicalize_ac_in_guarded_cow(f)
                        .map(crate::guarded::normalise_stored_formula_owned),
                    Some(s0) => s0,
                };
                // One subst pass already applied; continue to the fixpoint
                // (the original ran up to 16 passes total).
                for _ in 0..15 {
                    match crate::guarded::subst_guarded_cow(&cur, formula_subst) {
                        None => break,
                        Some(nxt) => cur = nxt,
                    }
                }
                // Re-canonicalise AC operators after substitution.  Substituting
                // an AC-valued var into an AC context (`rest ++ matchingComm`
                // with `matchingComm := <a>++<b>`) leaves a nested/unsorted
                // `Union(rest, Union(a,b))` that no longer structurally matches
                // the flat-sorted form `impliedFormulas` produces
                // (`canonicalize_ac_in_guarded`, simplify.rs:1545) — defeating
                // the `solved_formulas` dedup, so the prover re-derives and
                // re-solves a disjunction HS already discharged
                // (UM_three_pass `CK_secure_UM3`).  HS's AC constructors
                // (`fAppAC`) flatten+sort on construction, so HS never sees the
                // nested form; mirror that here.  (Tuple pairs are already
                // canonicalised inside `subst_gterm_cow` via `mk_gpair`.)
                let cur = crate::guarded::canonicalize_ac_in_guarded_cow(&cur).unwrap_or(cur);
                // Re-normalise the connective structure — the stored-state
                // substitution boundary of HS 150f5eba (substFormulas =
                // `S.map (normaliseStoredFormula . apply subst)`): a subst
                // that identifies two variables can make sibling conjuncts
                // equal, and the raw rebuild keeps both copies.
                Some(crate::guarded::normalise_stored_formula_owned(cur))
            };
            // Change bit for the conditional cache invalidation — the
            // `dedup_preserve_order` calls below drop only formulas EQUAL
            // to kept ones, which cannot change the max free-var idx.
            // (Declared above the enclosing `if` for the `raised` return.)
            for f in self.sys.formulas_mut_untracked().iter_mut() {
                if let Some(new_f) = apply_to_fixpoint(f) {
                    if new_f != **f {
                        *f = std::sync::Arc::new(new_f);
                        self.changed = ChangeIndicator::Changed;
                        formulas_value_changed = true;
                    }
                }
            }
            for f in self.sys.solved_formulas_mut_untracked().iter_mut() {
                if let Some(new_f) = apply_to_fixpoint(f) {
                    if new_f != **f {
                        *f = std::sync::Arc::new(new_f);
                        self.changed = ChangeIndicator::Changed;
                        formulas_value_changed = true;
                    }
                }
            }
            for f in self.sys.content_mut_untracked().lemmas.iter_mut() {
                if let Some(new_f) = apply_to_fixpoint(f) {
                    if new_f != **f {
                        *f = std::sync::Arc::new(new_f);
                        self.changed = ChangeIndicator::Changed;
                        formulas_value_changed = true;
                    }
                }
            }
            if formulas_value_changed {
                self.sys.invalidate_max_var_idx_cache();
            }
            // HS-faithful: `substFormulas`/`substSolvedFormulas`/`substLemmas`
            // apply via `Apply LNSubst (Set Guarded)` (Reduction.hs:593-595),
            // which in Haskell is `S.map (apply subst)`.  `S.map` rebuilds the
            // Set, dropping entries that collide post-substitution.  Without
            // this dedup, RS's Vec retains structurally-identical formulas
            // produced by substitution-induced equality — e.g. two
            // `impliedFormulas` matches that produced distinct
            // `Ex.PCR_Write(h(<'pcr0',~n#1>))` and
            // `Ex.PCR_Write(h(<'pcr0',~n#0>))` formulas which collapse to
            // the same `Ex.PCR_Write(h(<'pcr0',~n#0>))` once eq_store binds
            // `~n#1 → ~n#0`.  HS dedups via Set semantics; RS now mirrors.
            //
            // Concrete trigger: Envelope.spthy::Secret_and_Denied_exclusive
            // at path `/.../PCR_Quote/PCR_Extend/Alice2` — two distinct
            // `Ex.PCR_Write(h(<'pcr0',~n#1>))` / `...~n#0` formulas collapse
            // to the same formula once eq_store binds `~n#1 → ~n#0`; without
            // dedup, both survive in RS's Vec though HS's Set stores one.
            //
            // Note: the Envelope proof-tree diff is unchanged by this fix
            // alone — the divergent goal pick at the cascading
            // `/Alice2/CreateLockedKey` state involves additional state
            // differences (HS has Action(PCR_Write('pcr0')) goal RS lacks;
            // upstream the smart-ranker tie-breaker on Premise(PCR/1) NRs
            // also differs).  This fix is a real HS-faithfulness gap that
            // happens to be load-bearing for many other lemmas via
            // formula-count parity.
            dedup_preserve_order(self.sys.formulas_mut_untracked());
            dedup_preserve_order(self.sys.solved_formulas_mut_untracked());
            dedup_preserve_order(&mut self.sys.content_mut_untracked().lemmas);
        }
        // 5b. SubtermStore substitution — port of Haskell's
        // `instance Apply LNSubst SubtermStore` (`SubtermStore.hs:560-561`):
        // ```haskell
        // apply subst (SubtermStore a b c d e) =
        //   SubtermStore (apply subst a) (apply subst b) (apply subst c) d e
        // ```
        // HS's `substSystem` (Reduction.hs:623-633, see line 634) applies the substitution
        // to the whole `System` via the `Apply` instance, which threads
        // through every component including the subterm store.  Without
        // this, an eq-store binding like `a → $x` (introduced by unifying
        // a lemma's `a` with a rule's `PubValue($x)` conclusion) never
        // gets propagated to `subterm_store.subterms`, so a constraint
        // `(b, a)` remains as `(b, a:Msg)` even after `a` should be
        // `$x:Pub`.  Downstream `propagate_subterm_obvious` then misses
        // the pub-var trivially-false case → spurious "trace found"
        // verdict on `Sinvalid`-class lemmas (HS reports `simplify, by
        // contradiction /* contradictory subterm store */`).
        //
        // Use a direct subst application (not the `apply_term` closure
        // above) so the borrow of `self.maude` from `apply_term` doesn't
        // outlive the `self.insert_goal_with_loop_flag` call above.  HS's
        // `Apply LNSubst SubtermStore` doesn't normalise — neither do
        // we.  (`apply_term`'s normalise path is only used when the
        // eager-normalise env var is set; HS-default is non-normalising.)
        // COW probe + compare-on-rebuild: `apply_changed == None` means
        // applying the subst leaves the term unchanged, so an `!=` compare
        // could not hold — both the pre-apply clone and the deep compare
        // are skipped on unchanged terms.  On `Some`, the value compare is
        // KEPT (an AC re-sort can rebuild a value-equal term, and
        // `changed_sst` must track VALUE change exactly as before).
        let mut changed_sst = false;
        let pos_subs = std::mem::take(&mut self.sys.subterm_store_mut().subterms);
        let mut new_subs = Vec::with_capacity(pos_subs.len());
        for mut c in pos_subs {
            if let Some(new_small) = subst_view.apply_changed(&c.small) {
                if new_small != c.small { changed_sst = true; }
                c.small = new_small;
            }
            if let Some(new_big) = subst_view.apply_changed(&c.big) {
                if new_big != c.big { changed_sst = true; }
                c.big = new_big;
            }
            new_subs.push(c);
        }
        let solved = std::mem::take(&mut self.sys.subterm_store_mut().solved_subterms);
        let mut new_solved = Vec::with_capacity(solved.len());
        for mut c in solved {
            if let Some(new_small) = subst_view.apply_changed(&c.small) {
                if new_small != c.small { changed_sst = true; }
                c.small = new_small;
            }
            if let Some(new_big) = subst_view.apply_changed(&c.big) {
                if new_big != c.big { changed_sst = true; }
                c.big = new_big;
            }
            new_solved.push(c);
        }
        // negSubterms (HS field `a`) get substituted too; oldNegSubterms
        // (field `e`) do NOT — this is what re-arms the simpSplitNegSt
        // change-detection (`negSubterms \ oldNegSubterms`) after a
        // substitution alters a stored negative subterm.
        let negs = std::mem::take(&mut self.sys.subterm_store_mut().neg_subterms);
        let mut new_negs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)> =
            Vec::with_capacity(negs.len());
        for (mut s, mut t) in negs {
            if let Some(new_s) = subst_view.apply_changed(&s) {
                if new_s != s { changed_sst = true; }
                s = new_s;
            }
            if let Some(new_t) = subst_view.apply_changed(&t) {
                if new_t != t { changed_sst = true; }
                t = new_t;
            }
            let pair = (s, t);
            if !new_negs.contains(&pair) { new_negs.push(pair); }
        }
        self.sys.subterm_store_mut().subterms = new_subs;
        self.sys.subterm_store_mut().solved_subterms = new_solved;
        // `rebuild_from` establishes the sorted-unique set invariant on the
        // rewritten pairs (the `contains` guard above already drops duplicates,
        // so this contributes the sort).
        self.sys.subterm_store_mut().neg_subterms =
            crate::tools::subterm_store::SortedPairSet::rebuild_from(new_negs);
        if changed_sst {
            self.sys.invalidate_max_var_idx_cache();
            self.changed = ChangeIndicator::Changed;
        }
        // 6. Drain the queued rule-eqs from node merges. We resolve
        //    them by routing through `solve_fact_eqs` (Haskell uses
        //    `solveRuleEqs SplitLater`). This may add new substitutions
        //    to the eq-store; if so we won't recurse here — the next
        //    simplify-loop iteration will pick them up.
        let had_rule_eqs = !rule_eqs.is_empty();
        if had_rule_eqs {
            if tamarin_utils::env_gate!("TAM_DBG_SUBST_RULE_EQS") {
                let path = crate::constraint::solver::trace::case_path_string();
                eprintln!("[subst_rule_eqs] path={} queueing {} rule_eqs from setNodes-style collision",
                    path, rule_eqs.len());
                for (i, e) in rule_eqs.iter().enumerate() {
                    eprintln!("[subst_rule_eqs]   eq[{}]: lhs={:?} rhs={:?}", i,
                        format!("{:?}", e.lhs).chars().take(180).collect::<String>(),
                        format!("{:?}", e.rhs).chars().take(180).collect::<String>());
                }
            }
            // Tag/arity mismatches mean two distinct rule instances
            // collapsed to the same node id but their facts disagree
            // — the system has no model (Haskell `setNodes` →
            // `solveRuleEqs` would fail).  The shape_mismatch flag
            // above only checks LIST LENGTHS (premise/conclusion/
            // action counts), so two same-length but differently-
            // typed rules (e.g. Setup_Key `[Fr]→[!Key]/[IsKey]` vs
            // c_fresh `[Fr]→[KU]/[KU]`) pass that check while their
            // individual facts disagree on tag.  Detect those here
            // and force gfalse, mirroring Haskell's contradictory
            // outcome for `solveFactEqs` on incompatible facts.
            let mut tag_mismatch = false;
            let mut safe_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>>
                = Vec::with_capacity(rule_eqs.len());
            for e in rule_eqs {
                if e.lhs.tag != e.rhs.tag
                    || e.lhs.terms.len() != e.rhs.terms.len()
                {
                    tag_mismatch = true;
                } else {
                    safe_eqs.push(e);
                }
            }
            if tag_mismatch {
                // Mirrors Haskell `setNodes` → `solveRuleEqs` →
                // `solveFactEqs` (Reduction.hs:743-745, see line 745) where a fact-tag
                // mismatch fires `contradictoryIf True` → mzero.  We
                // funnel through `mark_contradictory` so BOTH the
                // gfalse-in-formulas marker AND `eq_store.is_false`
                // get set (SolveGoal-arm mzero proxy + post-simplify
                // FormulasFalse).
                self.mark_contradictory();
            }
            // Use SplitLater so we don't recurse into perform_split
            // (which can itself call subst_system).  Track the
            // outcome — Haskell's `solveRuleEqs` propagates failure
            // (`solveFactEqs` returns Contradictory if unification
            // fails on same-tag facts with incompatible terms, e.g.
            // !Key(~k) = !Key(some_other_term)).
            let res = self.solve_fact_eqs(SplitStrategy::SplitLater, &safe_eqs);
            if tamarin_utils::env_gate!("TAM_DBG_SUBST_RULE_EQS") {
                eprintln!("[subst_rule_eqs] solve_fact_eqs returned: {:?}",
                    res.as_ref().map(|o| match o {
                        SolveOutcome::Linear(_) => "Linear",
                        SolveOutcome::Cases(_) => "Cases",
                        SolveOutcome::Contradictory => "Contradictory",
                    }).map_err(|e| format!("Err({:?})", e)));
            }
            if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                // Mirrors Haskell `solveFactEqs` -> `solveTermEqs`
                // ending in `noContradictoryEqStore` (Reduction.hs:669-698, see line 704)
                // which fires mzero on `eqsIsFalse`.  Set both
                // markers via the helper.
                self.mark_contradictory();
            }
        }
        // Did THIS pass raise ANY change signal?  The complete signal set is:
        // value flags for all nine fields, the node-collision / shape /
        // rule-eq / KU-reinsert signals, and the last-atom rewrite.
        // `self.changed` alone is INSUFFICIENT (node/edge/less/goal/collision/
        // last-atom rewrites do not set it), so OR the full list.  A `false`
        // result certifies a total no-op (value AND order).  The section-local
        // flags aggregate through the `PassSignals` literal (every field must
        // be named) + `raised()` (exhaustive OR), so a section whose signal is
        // not wired into the aggregate is a compile error, not a silent
        // marker bug.
        let raised = PassSignals {
            nodes_value_changed,
            collisions: collisions > 0,
            shape_mismatch,
            edges_value_changed,
            last_atom_changed,
            less_value_changed,
            goals_value_changed: goals_value_changed.get(),
            formulas_value_changed,
            changed_sst,
            had_rule_eqs,
            had_insert_action,
        }
        .raised();
        // Safe over-bump: a raised pass
        // already bumped `content_stamp` via a cache helper / subterm_store_mut,
        // but bump again for clarity so no stale marker can survive it.
        if raised {
            self.sys.bump_content_stamp();
        }
        raised
    }

    /// Install a rule's variant disjunction as a SplitG goal — mirrors
    /// Haskell's `solveRuleConstraints` (Reduction.hs:766-774):
    /// ```haskell
    /// solveRuleConstraints (Just eqConstr) = do
    ///     (eqs, splitId) <- addRuleVariants eqConstr <$> getM sEqStore
    ///     insertGoal (SplitG splitId) False
    ///     setM sEqStore =<< simp hnd ...
    /// solveRuleConstraints Nothing = return ()
    /// ```
    ///
    /// Adds `substs` as a new disjunction to the eq-store, allocates a
    /// fresh `SplitId`, and inserts a `Goal::Split(id)` so the search
    /// (or simplify) layer enumerates the variant choice lazily. A `None`
    /// or empty `substs` is a no-op returning `false`.
    ///
    /// Returns `true` when the resulting eq_store is false (the caller
    /// should mzero — drop the branch). Mirrors HS `solveRuleConstraints`'
    /// final `noContradictoryEqStore` (Reduction.hs:703-704, called at
    /// Reduction.hs:767-772, see line 773). HS's mzero here kills rule branches whose variants
    /// conflict with the live eq_store — so `exploitPrems`/`solveGoal`
    /// never fires for them.
    pub fn solve_rule_constraints(
        &mut self,
        substs: Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>,
    ) -> bool {
        let substs = match substs {
            Some(v) if !v.is_empty() => v,
            _ => return false,
        };
        if tamarin_utils::env_gate!("TAM_RS_DBG_SOLVE_RULE_CONSTRAINTS") {
            eprintln!("[RS_SOLVE_RULE_CONSTRAINTS] n_substs={}", substs.len());
        }
        // Haskell `addRuleVariants` errors if domain of variants
        // intersects with eq-store free subst — that case isn't
        // supported there either. We don't enforce it; the worst case
        // is a redundant SplitG entry that simplify will discharge.
        if tamarin_utils::env_gate!("TAM_DBG_VS_DUMP") {
            let path = crate::constraint::solver::trace::case_path_string();
            eprintln!("[vs-dump] path={} solve_rule_constraints: {} substs", path, substs.len());
            for (i, s) in substs.iter().enumerate() {
                let pairs: Vec<String> = s.to_list().iter()
                    .map(|(k, v)| {
                        let trunc = if tamarin_utils::env_gate!("TAM_DBG_VS_DUMP_FULL") { 500 } else { 120 };
                        format!("{:?}→{:?}", k, v).chars().take(trunc).collect::<String>()
                    })
                    .collect();
                eprintln!("[vs-dump]   [{}]: {}", i, pairs.join(" ; "));
            }
        }
        if crate::tools::equation_store::impure_dbg_enabled() {
            for s in &substs {
                crate::tools::equation_store::dbg_register_subst_origin(
                    "solveRuleConstraints", s);
            }
        }
        let id = self.sys.eq_store_mut().add_disj(substs);
        // HS-faithful order (Reduction.hs:766-774): `solveRuleConstraints
        // (Just eqConstr)` is
        //   (eqs, splitId) <- addRuleVariants eqConstr <$> getM sEqStore
        //   insertGoal (SplitG splitId) False               -- BEFORE simp!
        //   setM sEqStore =<< simp hnd (const (const False)) eqs
        //   noContradictoryEqStore                          (Reduction.hs:767-772, see line 773)
        // — the `insertGoal` happens BEFORE `simp` and ALWAYS bumps
        // `sNextGoalNr`, even when simp later folds the singleton variant
        // disj into the free subst (`simpSingleton` collapses
        // `Disj [emptySubstVFresh]` for non-destructor rules, so the
        // SplitG ends up orphaned and `removeSolvedSplitGoals` deletes
        // it later — but the gsNr bump persists).  Doing simp FIRST and
        // skipping `insert_goal` when folded under-bumps the counter,
        // desynchronising RS's gsNr trace from HS's at every
        // destructor-free `labelNodeId` call.
        //
        // Do NOT call apply_eq_store(maude, empty_subst) here to drop
        // variants conflicting with the existing free subst: that is
        // HS-unfaithful: HS lets simp's own passes (simp_singleton +
        // friends) handle the propagation.
        //
        // simp_abstract_sorted_var (EquationStore.hs:471-504) no-ops on
        // protocol variants until the Maude bridge returns Fresh-sorted
        // `~mw`: it returns variant range vars as `~mw:Msg`, so the
        // `sortCompare(v.sort, lx.sort)` strict-GT guard fails when both
        // are Msg.  The fix lives in the Maude bridge, not here.
        self.insert_goal(Goal::Split(id));
        let folded;
        {
            use tamarin_term::lterm::HasFrees;
            // Functionally-dead preserve set (here the deliberately narrower
            // no-goals variant): `simp_singleton_avoiding` reads it only
            // under the three debug gates — the fold calls
            // `fresh_to_free_avoiding`, which ignores it — so build it only
            // when a gate is on.  The debug-branch body performs the full
            // inline walk, so debug traces stay identical.
            let sys_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar> =
                if preserve_dbg_gates_enabled() {
                    let mut sys_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar>
                        = std::collections::BTreeSet::new();
                    let mut visit = |v: &tamarin_term::lterm::LVar| { sys_vars.insert(v.clone()); };
                    for (id, rule) in self.sys.nodes.iter() {
                        id.for_each_free(&mut visit);
                        rule.for_each_free(&mut visit);
                    }
                    for e in &self.sys.edges {
                        e.src.0.for_each_free(&mut visit);
                        e.tgt.0.for_each_free(&mut visit);
                    }
                    for l in &self.sys.less_atoms {
                        l.smaller.for_each_free(&mut visit);
                        l.larger.for_each_free(&mut visit);
                    }
                    if let Some(la) = &self.sys.last_atom { la.for_each_free(&mut visit); }
                    sys_vars
                } else {
                    std::collections::BTreeSet::new()
                };
            let maude = self.maude.clone();
            let store = std::sync::Arc::unwrap_or_clone(self.sys.take_eq_store());
            self.sys.invalidate_max_var_idx_cache();
            if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
                eprintln!("[rs-fold] ARV-SIMP counter={}", maude.fresh_counter_peek());
            }
            self.sys.set_eq_store(std::sync::Arc::new(store.simp_with_fresh_avoiding(
                |_, _| false,
                |n| maude.reserve_idxs(n),
                &sys_vars,
                Some(&maude),
            )));
            // eq_store simp can rewrite/drop subst entries → max may lower.
            self.sys.invalidate_max_var_idx_cache();
            // Check if our disj was folded (singleton case).  HS leaves
            // the orphaned SplitG goal in `sGoals` until the next
            // `removeSolvedSplitGoals` call (Reduction.hs:666-671) which
            // is invoked from the simplifier loop — so we don't strip
            // the goal here, matching HS's lazy cleanup.
            folded = !self.sys.eq_store.conj.iter().any(|d| d.split_id == id);
            // HS-faithful: `solveRuleConstraints` (Reduction.hs:766-774) is
            //   addRuleVariants → insertGoal (SplitG …) → setM sEqStore =<< simp …
            //   → noContradictoryEqStore
            // — it does NOT call `substSystem`, even when `simp` folds the
            // singleton variant disjunction into the free subst.  The
            // goal/node re-key from the new free-subst bindings is DEFERRED
            // to the next simplify-loop `substSystem` pass (Simplify.hs:56-158, see line 99).
            //
            // Deferring the re-key (matching HS) keeps the `GoalStatus.nr`
            // ordering of graft-minted witnesses ahead of re-keyed KU
            // msg-var goals, preserving `smartRanking`'s min-nr tie-break
            // order for fresh-nonce KU goals.
        }
        self.changed = ChangeIndicator::Changed;
        // HS-faithful: `noContradictoryEqStore` (Reduction.hs:703-704,
        // called from solveRuleConstraints at Reduction.hs:767-772, see line 773) fires
        // mzero if the eq_store ended up
        // contradictory after adding variants + simp.  Return that
        // signal so the caller can drop the rule branch BEFORE
        // exploit_prems fires — matching HS's behavior where
        // `exploitPrems rule=X` trace never emits for rules whose
        // variants conflict with the live state.
        let contra = self.sys.eq_store.is_false();
        if tamarin_utils::env_gate!("TAM_DBG_VARIANT_CONTRA") && contra {
            eprintln!("[variant_contra] solve_rule_constraints contradiction fired");
        }
        if tamarin_utils::env_gate!("TAM_DBG_VS_POST") {
            for (id, ru) in self.sys.nodes.iter() {
                let nm = crate::constraint::solver::reduction::rule_case_name(ru);
                if nm == "Serv_1" {
                    eprintln!("[vs_post] AFTER solve_rule_constraints: id={}.{} folded={}",
                        id.name, id.idx, folded);
                    for (i, p) in ru.premises.iter().enumerate() {
                        eprintln!("[vs_post]   prem[{}]: {:?}", i,
                            format!("{:?}", p).chars().take(400).collect::<String>());
                    }
                    for (i, c) in ru.conclusions.iter().enumerate() {
                        eprintln!("[vs_post]   conc[{}]: {:?}", i,
                            format!("{:?}", c).chars().take(400).collect::<String>());
                    }
                    eprintln!("[vs_post]   eq_store.subst ({} entries):",
                        self.sys.eq_store.subst.to_list().len());
                    for (v, t) in self.sys.eq_store.subst.to_list().iter().take(15) {
                        eprintln!("[vs_post]     {}.{}/{:?} → {:?}", v.name, v.idx, v.sort,
                            format!("{:?}", t).chars().take(120).collect::<String>());
                    }
                    eprintln!("[vs_post]   eq_store.conj ({} disjs):",
                        self.sys.eq_store.conj.len());
                }
            }
        }
        contra
    }

    /// Insert a `<` atom.
    pub fn insert_less(&mut self, l: LessAtom) {
        let before = self.sys.less_atoms.len();
        self.sys.add_less(l);
        if self.sys.less_atoms.len() != before { self.changed = ChangeIndicator::Changed; }
    }

    /// Add a new goal.
    pub fn insert_goal(&mut self, g: Goal) {
        self.insert_goal_with_loop_flag(g, false);
    }

    /// Add a new goal with an explicit loop-breaker flag, matching
    /// Haskell's `insertGoal goal isLoopBreaker`. The flag controls
    /// `gsLoopBreaker` in the resulting status — used by the smart
    /// ranker to deprioritise premises that would otherwise loop.
    pub fn insert_goal_with_loop_flag(&mut self, g: Goal, looping: bool) {
        // Auto-decompose `KU(pair(a,b))` / `KU(inv(x))` / `KU(prod(...))`
        // into sub-KU goals on the components, each at a fresh
        // pre-ordered node (mirrors Haskell's `insertAction` in
        // `Reduction.hs` which inserts sub-KU actions at fresh
        // node-ids with a `i_sub < i_outer` less-atom before
        // marking the outer KU goal solved).  Without this,
        // `is_open` (which marks pair/inv-topped KU goals as
        // not-open assuming the decomposition already happened)
        // would hide the actual unsolved sub-goals, leaving the
        // search stuck with "no method".
        if let Goal::Action(node_id, fa) = &g {
            if fa.tag == crate::fact::FactTag::Ku {
                if let Some(top) = fa.terms.first() {
                    if let Some(sub_terms) = ku_decomp_subterms(top) {
                        // Skip if outer goal already present (avoid
                        // re-decomposition on re-insertion).
                        if self.sys.goals.iter().any(|(eg, _)| eg == &g) {
                            return;
                        }
                        let outer_node = node_id.clone();
                        // HS-faithful order (Reduction.hs:364-366):
                        //   insertGoal goal False                     -- outer FIRST
                        //   requiresKU m1 *> requiresKU m2 ...        -- sub-goals after
                        let before = self.sys.goals.len();
                        self.sys.add_goal_with_loop_flag(g.clone(), looping);
                        if self.sys.goals.len() != before {
                            self.changed = ChangeIndicator::Changed;
                        }
                        for sub in sub_terms {
                            let next_idx = std::cmp::max(
                                bounds_max(&self.sys),
                                outer_node.idx,
                            ).saturating_add(1);
                            let sub_node = tamarin_term::lterm::LVar::new(
                                "vk",
                                tamarin_term::lterm::LSort::Node,
                                next_idx,
                            );
                            // HS-faithful counter side-effect: HS's
                            // `requiresKU` (Reduction.hs:458-469, insertAction
                            // pair/inv/mult decomposition) draws each sub-KU
                            // node id via `freshLVar "vk" LSortNode`, ADVANCING
                            // the ambient FreshT counter past the drawn idx.
                            // RS derives the same VALUE from
                            // `max(bounds_max, outer.idx)+1`, but must also
                            // advance the shared counter so every LATER
                            // counter draw in the same Reduction (in
                            // particular simp's `freshToFree` fold of a
                            // singleton variant disj, which feeds the
                            // eqsSubst RANGE) stays aligned with HS.
                            self.maude.ensure_above(next_idx);
                            // TAM_RS_TRACE_VK_CREATE: mirror of the HS
                            // `TAM_HS_TRACE_VK_CREATE` hook (Reduction.hs /
                            // Goals.hs `requiresKU` + `exploitPrem`).  Logs
                            // every `vk` fresh-node allocation so the HS-vs-RS
                            // allocation sequences can be diffed when a `#vk.N`
                            // index diverges.  `cnt`/`bm` expose the maude
                            // fresh-counter and bounds_max at allocation — this
                            // path (`ku_decomp_subterms`) derives the index
                            // arithmetically from `max(bm, outer.idx)+1` rather
                            // than by an HS-`freshLVar`-style counter draw, then
                            // advances the counter past it via the `ensure_above`
                            // above (so `cnt` here already reflects the
                            // post-advance value).
                            if tamarin_utils::env_gate!("TAM_RS_TRACE_VK_CREATE") {
                                let path = crate::constraint::solver::trace::case_path_string();
                                eprintln!("[RS_VK_CREATE] path={} site=ku_decomp_subterms vk.{} cnt={} bm={}",
                                    path, next_idx, self.maude.fresh_counter_peek(), bounds_max(&self.sys));
                            }
                            let sub_fa = crate::fact::ku_fact(sub);
                            self.insert_goal_with_loop_flag(
                                Goal::Action(sub_node.clone(), sub_fa),
                                looping,
                            );
                            self.insert_less(
                                crate::constraint::constraints::LessAtom::new(
                                    sub_node, outer_node.clone(),
                                    crate::constraint::constraints::Reason::Adversary,
                                ),
                            );
                        }
                        return;
                    }
                }
            }
        }
        let before = self.sys.goals.len();
        self.sys.add_goal_with_loop_flag(g, looping);
        if self.sys.goals.len() != before { self.changed = ChangeIndicator::Changed; }
    }

    /// Compute a fresh-var baseline — the max var idx across all vars in
    /// nodes' rules, stored & solved formulas, lemmas, edges, less-atoms,
    /// subterm store, goals and the eq-store substitution (everything
    /// folded by `bounds_max`/`bounds_max_uncached`, which already includes
    /// `formulas.chain(solved_formulas).chain(lemmas)` via `max_var_idx`).
    ///
    /// Returns the plain max — no extra headroom is added. Used by `Ex`
    /// decomposition to pick fresh var indices.
    pub fn fresh_var_baseline(&self) -> u64 {
        bounds_max(&self.sys)
    }

    /// Insert a parser-AST `Atom` into the system following Haskell's
    /// `insertAtom` semantics:
    ///
    /// - `Eq(x, y)`     → `solve_term_eqs` (Maude AC unification)
    /// - `Less(i, j)`   → push a `LessAtom` (Formula reason)
    /// - `Last(t)`      → set `last_atom` if `t` is a node variable
    /// - `Action(fa,t)` → push a `Goal::Action(node_id, lnfact)`
    /// - `Subterm(s,b)` → push a subterm-store entry
    /// - `Pred(_)`      → returns `false`: predicates are pre-expanded
    ///   during translation and have no `LNAtom` form
    /// - `LessMset(_,_)`→ returns `false`: multiset ordering is not a
    ///   temporal `LNAtom`, so it never reaches here
    ///
    /// HS's `LNAtom` (Reduction.hs `insertAtom`) only has
    /// `EqE`/`Subterm`/`Action`/`Less`/`Last`/`Syntactic`; the two
    /// parser-AST shapes above have no counterpart and are rejected.
    ///
    /// Returns `true` if the atom was successfully decomposed,
    /// `false` if it was a shape with no `LNAtom` counterpart.
    pub fn insert_atom(&mut self, a: &tamarin_parser::ast::Atom) -> bool {
        use tamarin_parser::ast::Atom;
        match a {
            Atom::Eq(x, y) => {
                let (Some(tx), Some(ty)) = (
                    crate::elaborate::term_to_lnterm(x),
                    crate::elaborate::term_to_lnterm(y),
                ) else { return false; };
                // KNOWN COMPENSATING DIVERGENCE (pending a faithful
                // rule-variant / normalisation pass).
                //
                // HS's `insertAtom (EqE x y)` does NOT reduce x/y — it is
                // literally `void $ solveTermEqs SplitNow [Equal x y]`
                // (Reduction.hs:411-418, see line 413).  HS reaches this point with both
                // sides already in Maude normal form, so a `reduce` here
                // would be idempotent for HS.  The pre-normalisation is
                // NOT from `normDG`/`normRule`: those run only in the
                // diff-mode mirror path (`getMirrorDG`, System.hs:1292-1398, see line 1293)
                // and inside `impliedOrInitial`'s implied systems
                // (System.hs:1253-1283, see line 1283) — neither is on the standard `--prove`
                // solving path (the only `normRule` callers are
                // System.hs:1286-1289, see line 1289 `normDG` + IntruderRules variant
                // computation).  The true reason HS's EqE terms are
                // pre-normal is rule-variant computation (`variants in
                // MSG` yields reduced action terms) plus eq-store
                // bindings being Maude-unifier outputs.  HS's
                // `substSystem`/`setNodes` deliberately does NOT
                // normalise — documented at the `apply_to_fact` comment
                // above (eager-normalise in `substNodes` was tried and
                // reverted: it lost source-case head shapes in test4 and
                // blocked the `hasNonNormalTerms` contradiction in
                // Responder_secrecy).
                //
                // Because Rust does not yet compute reduced rule variants,
                // a fact's terms can still carry non-normal shapes (e.g.
                // `verify(sign(...),...,pk(...))`) when this atom fires.
                // We therefore reduce the two sides HERE so a restriction
                // like `Equality(verify(sign(...),...,pk(...)), true)` is
                // seen as `Eq(true, true)` and closes as it does in HS.
                // For HS-normal inputs this `reduce` is a no-op; it only
                // corrects Rust-specific residual non-normality.  Remove
                // these two reduces once a faithful variant/normalisation
                // pass lands.
                let maude = self.maude.clone();
                let tx = maude.reduce(&tx).unwrap_or(tx);
                let ty = maude.reduce(&ty).unwrap_or(ty);
                // Haskell `insertAtom (EqE x y) = void (solveTermEqs
                // SplitNow [Equal x y])`.  The monadic `void` ignores
                // the ChangeIndicator but the monad propagates
                // Contradictory via mzero/MonadPlus (the inner
                // `noContradictoryEqStore` at Reduction.hs:669-698, see line 704 fires
                // mzero on `eqsIsFalse`).  In our pass form, route
                // both markers via `mark_contradictory` so the
                // SolveGoal-arm mzero proxy AND post-simplify
                // contradictions check both fire.
                let res = self.solve_term_eqs(
                    SplitStrategy::SplitNow,
                    &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }],
                );
                match res {
                    Err(_) | Ok(SolveOutcome::Contradictory) => {
                        self.mark_contradictory();
                    }
                    Ok(SolveOutcome::Linear(_)) => {}
                    Ok(SolveOutcome::Cases(arms)) => {
                        // HS-faithful fanout (Reduction.hs):
                        // `disjunctionOfList $ performSplit eqs2 splitId`
                        // forks the surrounding `Reduction` continuation
                        // once per AC unifier arm.  We install arm[0]
                        // as the current eq_store and stash arms[1..]
                        // in `pending_eq_arms` for the outer-case caller
                        // (e.g. `solve_disj_goal`) to drain.
                        let mut it = arms.into_iter();
                        if let Some(first) = it.next() {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.set_eq_store(std::sync::Arc::new(first));
                        }
                        for rest in it {
                            self.pending_eq_arms.push(rest);
                        }
                        if tamarin_utils::env_gate!("TAM_RS_DBG_INSERT_ATOM_EQ_FANOUT") {
                            eprintln!("[insert_atom_eq_fanout] stashed {} extra arms",
                                self.pending_eq_arms.len());
                        }
                    }
                }
                self.changed = ChangeIndicator::Changed;
                true
            }
            Atom::Less(i, j) => {
                let (Some(ni), Some(nj)) = (term_to_node_id(i), term_to_node_id(j))
                    else { return false; };
                // Normalise through the eq-store substitution so any
                // earlier node-id merges propagate to this fresh atom.
                let ni = normalise_node_id(ni, &self.sys.eq_store.subst);
                let nj = normalise_node_id(nj, &self.sys.eq_store.subst);
                self.insert_less(crate::constraint::constraints::LessAtom::new(
                    ni, nj, crate::constraint::constraints::Reason::Formula));
                true
            }
            Atom::Last(t) => {
                let Some(n) = term_to_node_id(t) else { return false; };
                // HS-faithful insertLast (Reduction.hs:402-407).
                let _ = self.insert_last(n);
                true
            }
            Atom::Action(fact, t) => {
                let Ok(lnfact) = crate::elaborate::fact_to_lnfact(fact) else { return false; };
                let Some(n) = term_to_node_id(t) else { return false; };
                self.insert_goal(Goal::Action(n, lnfact));
                true
            }
            Atom::Subterm(s, b) => {
                let (Some(ts), Some(tb)) = (
                    crate::elaborate::term_to_lnterm(s),
                    crate::elaborate::term_to_lnterm(b),
                ) else { return false; };
                // Pure ADD (`SubtermStore::add` is a plain push, no
                // removal): the max can only rise by the two new terms —
                // bump both sides instead of invalidating.
                self.sys.bump_cache_term(&ts);
                self.sys.bump_cache_term(&tb);
                self.sys.subterm_store_mut().add(ts, tb);
                self.changed = ChangeIndicator::Changed;
                true
            }
            Atom::Pred(_) | Atom::LessMset(_, _) => false,
        }
    }

    /// Decompose a guarded formula via the structural cases of
    /// `insertFormula` from `Theory.Constraint.Solver.Reduction`.
    ///
    /// Implemented cases (mark-as-solved on the *outermost* call only):
    /// - `Conj fms`     → recurse on each subformula (CR-rule *S_∧*)
    /// - `Disj`         → store + insert `Goal::Disj` (defer split, CR *S_∨*)
    /// - `Atom`         → `insert_atom` via `gatom_to_atom` (atom insertion)
    /// - `Ex`           → CR-rule *S_∃*: allocate fresh LVars, `substBound`,
    ///   recurse on `gconj([guards…, body])`
    /// - `All` (¬, single guard, body=⊥) → CR-rules for `Less`/`Eq`/`Last`
    ///   (split into ordering disjunctions), `Subterm`
    ///   (`insertNegSubterm`); otherwise kept in `formulas`
    pub fn insert_formula(&mut self, g: Guarded) {
        // Normalise at the insertion boundary so the stored-formula state
        // is ALWAYS in `normalise_stored_formula` normal form — the dedup
        // checks inside `insert_formula_inner` compare against the
        // (post-substitution, normalised) stored sets.  Port of HS
        // insertFormula entry normalisation (150f5eba).
        let g = crate::guarded::normalise_stored_formula_owned(g);
        self.insert_formula_inner(g, true);
    }

    fn insert_formula_inner(&mut self, g: Guarded, mark: bool) {
        if tamarin_utils::env_gate!("TAM_DBG_INSERT_FORM") {
            let head = match &g {
                Guarded::Atom(_) => "Atom",
                Guarded::Conj(_) => "Conj",
                Guarded::Disj(items) if items.is_empty() => "Disj-EMPTY",
                Guarded::Disj(_) => "Disj",
                Guarded::GGuarded { qua: crate::guarded::Quant::Ex, .. } => "Ex",
                Guarded::GGuarded { qua: crate::guarded::Quant::All, .. } => "All",
            };
            let dup_f = crate::guarded::stores_contains(&self.sys.formulas, &g);
            let dup_s = crate::guarded::stores_contains(&self.sys.solved_formulas, &g);
            eprintln!("[INSERT_FORM] mark={} head={} dup_f={} dup_s={}",
                mark, head, dup_f, dup_s);
        }
        if crate::guarded::stores_contains(&self.sys.formulas, &g) || crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
            return;
        }
        match g.clone() {
            Guarded::Conj(items) => {
                // A marked Conj can carry σ-domain free vars pushed between two
                // simplify-loop `subst_system` calls; routing the push through
                // `solved_formulas_mut()` bumps `content_stamp` on handout,
                // breaking a stale skip marker.
                if mark {
                    self.sys.solved_formulas_mut().push(std::sync::Arc::new(g));
                }
                for it in items { self.insert_formula_inner(it, false); }
                self.changed = ChangeIndicator::Changed;
            }
            Guarded::Disj(items) if items.is_empty() => {
                // Empty disjunction = ⊥ — store the formula so a
                // downstream contradictions check can detect it.
                //
                // HS-faithful: `insertFormula` (Reduction.hs:473-482) for
                // GDisj does NOT branch on emptiness — it always traces
                // `Disj`, inserts into sFormulas, AND inserts the DisjG
                // goal.  When the disj is empty, the DisjG goal becomes
                // `solveDisjunction (Disj [])` = mzero (Goals.hs:393-395)
                // — a structurally-explicit contradiction that the goal
                // ranker can pick.  Mirror by emitting the trace event,
                // adding to formulas, AND inserting the empty DisjG goal
                // alongside.  Both contradictions-check and goal-ranker
                // can then close the case (HS picks whichever fires first).
                // The entry guard returned when `g` was already in
                // `formulas`/`solved_formulas`, and the only statement since
                // (`match g.clone()`) does not mutate `self.sys`, so `g` is
                // provably not yet in `formulas` here: always trace "Disj"
                // and push.  Mirrors HS `insertFormula` (Reduction.hs:473-482),
                // which likewise inserts without re-checking membership.
                debug_assert!(!crate::guarded::stores_contains(&self.sys.formulas, &g),
                    "insert_formula_inner empty-Disj arm: the entry guard \
                     already excludes formulas-membership");
                crate::constraint::solver::trace::trace_form(
                    "Disj",
                    || crate::constraint::solver::trace::guarded_repr(&g));
                if tamarin_utils::env_gate!("TAM_RS_TRACE_GFALSE") {
                    eprintln!("[RS_GFALSE] path={} gfalse inserted",
                        crate::constraint::solver::trace::case_path_string());
                }
                // Pure ADD (formula push): bump.
                self.sys.bump_cache_guarded(&g);
                self.sys.formulas_mut().push(std::sync::Arc::new(g.clone()));
                self.changed = ChangeIndicator::Changed;
                let goal = Goal::Disj(crate::constraint::constraints::Disj::new(items));
                self.insert_goal(goal);
            }
            Guarded::Disj(items) => {
                // Store the formula AND insert a corresponding split
                // goal. The goal itself uses the same vector, allowing
                // `solve_disj_goal` to resume later.
                // The entry guard returned when `g` was already in
                // `formulas`/`solved_formulas`, and the only statement since
                // (`match g.clone()`) does not mutate `self.sys`, so `g` is
                // provably not yet in `formulas` here: always trace "Disj"
                // and push.  Mirrors HS `insertFormula` (Reduction.hs:473-482),
                // which likewise inserts without re-checking membership.
                debug_assert!(!crate::guarded::stores_contains(&self.sys.formulas, &g),
                    "insert_formula_inner Disj arm: the entry guard \
                     already excludes formulas-membership");
                crate::constraint::solver::trace::trace_form(
                    "Disj",
                    || crate::constraint::solver::trace::guarded_repr(&g));
                // Pure ADD (formula push): bump.
                self.sys.bump_cache_guarded(&g);
                self.sys.formulas_mut().push(std::sync::Arc::new(g.clone()));
                let goal = Goal::Disj(crate::constraint::constraints::Disj::new(items));
                self.insert_goal(goal);
                self.changed = ChangeIndicator::Changed;
            }
            Guarded::Atom(ref ga) => {
                // Try to decompose into a constraint via insert_atom.
                // Top-level Guarded::Atom has no Bound vars; round-trip
                // to parser AST for the legacy `insert_atom` interface.
                let a = crate::guarded::gatom_to_atom(ga);
                let _ = self.insert_atom(&a);
                // Haskell-faithful: only mark the OUTER formula as
                // solved (mark=True at top-level `insert_formula`).
                // Inner recursion (mark=False, from Conj/Ex body) does
                // NOT add the atom to solved_formulas — mirrors HS
                // `GAto ato -> markAsSolved; insertAtom ...` where
                // `markAsSolved = when mark $ modM sSolvedFormulas`
                // (Reduction.hs:424-491, see line 445).
                //
                // Why bother: tracks lockstep with HS for the
                // `[STATE] solved_formulas=N` count and avoids
                // accumulating per-Conj-child duplicates that don't
                // semantically need tracking — Conj bodies aren't
                // "re-inserted" anywhere; only top-level impl_formulas
                // outputs reach the Atom branch with mark=True.
                //
                // Dedup-by-normalize still applies at mark=True: Maude
                // unification mints fresh `~mw#N` witnesses per call,
                // so structurally-identical derivations from
                // impl_formulas would otherwise accumulate.  Compare
                // normalized form (apply eq-store, then normalize
                // witness LVars `~mw#N → ~mw#0`, then alpha-canon
                // GGuarded bound vars).
                if mark {
                    // σ rebuilt only when the subst axis moved since the
                    // cached copy (see `eq_vs_cache`); a stamp hit is
                    // bit-identical to `var_subst_from_eq_store` here.
                    let stamp = self.sys.subst_stamp();
                    if !matches!(&self.eq_vs_cache, Some((s, _)) if *s == stamp) {
                        self.eq_vs_cache = Some((stamp,
                            crate::guarded::var_subst_from_eq_store(&self.sys.eq_store)));
                    }
                    let eq_vs = &self.eq_vs_cache.as_ref().expect("just ensured").1;
                    // COW canon.  `normalize_bound_lvars` is an identity clone
                    // applied to BOTH sides of the `==`, so it never changes the
                    // dedup boolean — drop it (matching the `implied_apply_canon`
                    // twin in simplify.rs, which deliberately skips it).  The two
                    // remaining stages reuse the borrowed input when they touch no
                    // leaf, so an already-canonical formula pays zero clones.
                    // (Nested `fn` with an explicit lifetime so the returned `Cow`
                    // can borrow the input `f`; a closure cannot express that.)
                    fn apply_canon<'f>(
                        f: &'f crate::guarded::Guarded,
                        eq_vs: &crate::guarded::VarSubst,
                    ) -> std::borrow::Cow<'f, crate::guarded::Guarded> {
                        let f1: std::borrow::Cow<crate::guarded::Guarded> =
                            if eq_vs.is_empty() {
                                std::borrow::Cow::Borrowed(f)
                            } else {
                                match crate::guarded::subst_guarded_cow(f, eq_vs) {
                                    None => std::borrow::Cow::Borrowed(f),
                                    Some(g) => std::borrow::Cow::Owned(g),
                                }
                            };
                        match crate::guarded::normalize_witness_lvars_cow(f1.as_ref()) {
                            None => f1,
                            Some(g) => std::borrow::Cow::Owned(g),
                        }
                    }
                    let canon = apply_canon(&g, eq_vs);
                    let already_solved = self.sys.solved_formulas.iter().any(|f|
                        apply_canon(f, eq_vs).as_ref() == canon.as_ref());
                    if !already_solved {
                        // Pure ADD (solved-formula push under
                        // !already_solved): bump.
                        self.sys.bump_cache_guarded(&g);
                        self.sys.solved_formulas_mut().push(std::sync::Arc::new(g));
                        self.changed = ChangeIndicator::Changed;
                    }
                }
            }
            Guarded::GGuarded { qua: crate::guarded::Quant::Ex, vars, guards, body } => {
                // CR-rule *S_∃*: openGuarded — allocate fresh LVars for
                // the bound vars, substitute Bound → Free in guards/body,
                // and recurse on `gconj([atoms..., body])`.
                let outer = g.clone();
                if tamarin_utils::env_gate!("TAM_RS_DBG_EX_INSERT") {
                    eprintln!("[RS_EX_INSERT] path={} mark={} fm={}",
                        crate::constraint::solver::trace::case_path_string(),
                        mark,
                        crate::constraint::solver::trace::guarded_repr(&outer));
                }
                if tamarin_utils::env_gate!("TAM_DBG_EX_DECOMP") {
                    eprintln!("[EX-DECOMP] ENTER mark={} vars={:?}",
                        mark,
                        vars.iter().map(|b| (b.name.clone(), b.sort)).collect::<Vec<_>>());
                }
                if crate::guarded::stores_contains(&self.sys.solved_formulas, &outer) {
                    if tamarin_utils::env_gate!("TAM_DBG_EX_DECOMP") {
                        eprintln!("[EX-DECOMP] SKIP (already solved) vars={:?}",
                            vars.iter().map(|b| (b.name.clone(), b.sort)).collect::<Vec<_>>());
                    }
                    return;
                }
                // Pure ADD (solved-formula push, guarded by the
                // `contains(&outer)` early-return above): bump.
                self.sys.bump_cache_guarded(&outer);
                self.sys.solved_formulas_mut().push(std::sync::Arc::new(outer));
                // HS (Reduction.hs:571-592, see line 573) draws `xs <- mapM (uncurry freshLVar) ss`
                // straight from the ambient MonadFresh counter — no clamp; the
                // threaded counter is above every system var by construction
                // (seeded from `avoid sys`, monotone thereafter).  RS's clamp
                // compensates for its non-threaded counter and must preserve
                // exactly that invariant: counter ≥ max idx + 1 ONLY when free
                // vars exist; a frees-less system (lemma ROOT step: HS seeds 0)
                // must stay unclamped — `ensure_above(0)` would force ≥ 1,
                // shifting the root existentials (#i/#j/tid/key) +1 vs HS.
                let avoid_max = self.fresh_var_baseline();
                if avoid_max > 0 || system_has_any_free_var(&self.sys) {
                    self.maude.ensure_above(avoid_max);
                }
                let base = self.maude.reserve_idxs(vars.len() as u64);
                // Fresh LVars (HS `freshLVar`-style), one per binding in
                // the original lexical order.
                let xs: Vec<tamarin_parser::ast::VarSpec> = vars.iter().enumerate()
                    .map(|(i, b)| tamarin_parser::ast::VarSpec {
                        name: b.name.clone(),
                        idx: base + i as u64,
                        sort: b.sort,
                        typ: None,
                    })
                    .collect();
                if tamarin_utils::env_gate!("TAM_DBG_EX_DECOMP") {
                    eprintln!("[EX-DECOMP] FIRE avoid_max={} base={} xs={:?}",
                        avoid_max, base,
                        xs.iter().map(|v| (v.name.clone(), v.idx)).collect::<Vec<_>>());
                }
                // HS `subst xs = zip [0..] (reverse xs)`: Bound 0 → xs[k-1].
                let open_s = crate::guarded::open_subst(&xs);
                let mut items: Vec<Guarded> = guards.iter()
                    .map(|a| Guarded::Atom(crate::guarded::subst_bound_atom_at_depth(a, &open_s, 0)))
                    .collect();
                items.push(crate::guarded::subst_bound_guarded(&body, &open_s));
                let new_body = crate::guarded::gconj(items);
                self.insert_formula_inner(new_body, false);
                self.changed = ChangeIndicator::Changed;
            }
            Guarded::GGuarded { qua: crate::guarded::Quant::All, ref vars, ref guards, ref body }
                if vars.is_empty() && guards.len() == 1
                   && **body == crate::guarded::gfalse() =>
            {
                // CR-rules from Haskell `insertFormula`
                // (Reduction.hs:461-486) for single-guard, body=⊥
                // universals:
                //
                //   ∀[].[Less i j].⊥        → i = j ∨ j < i
                //   ∀[].[Eq i j].⊥          → i < j ∨ j < i        (i,j: Node)
                //   ∀[].[Subterm i j].⊥     → insertNegSubterm
                //   ∀[].[Last i].⊥          → last < i ∨ i < last
                //
                // Empty-binder universals: guards have no Bound vars so
                // we can safely round-trip to parser AST for the legacy
                // matching code below.
                use tamarin_parser::ast::Atom as AAtom;
                let guard_pa = crate::guarded::gatom_to_atom(&guards[0]);
                match &guard_pa {
                    AAtom::Less(i, j) if term_to_node_id(i).is_some()
                                       && term_to_node_id(j).is_some() => {
                        // Haskell decomposes ∀[].[Less i j].⊥ into
                        // `i = j ∨ j < i` (Reduction.hs:461-486).
                        // Without firing this, we end up labelling
                        // proof leaves with `/* from formulas */`
                        // (the kept universal-with-True-guard
                        // simplifies to ⊥) instead of `/* cyclic */`
                        // (the order graph closes via i<j ∧ j<i).
                        // Verdict-equivalent but breaks proof-trace
                        // match against tamarin's output.
                        //
                        // HS-faithful: `markAsSolved = when mark $
                        // modM sSolvedFormulas $ S.insert fm`
                        // (Reduction.hs:424-491, see line 491) — only mark when called
                        // at the TOP level.  Children of a Conj/Ex
                        // body recurse with mark=False, so the
                        // negated-atom CR-rule must NOT mark itself
                        // solved in that case.  Yubikey
                        // slightly_weaker_invariant: when the IH-body
                        // Conj decomposes, the nested ¬Less / ¬Eq
                        // arrive here with mark=False; HS keeps
                        // sSolvedFormulas at 3, and without the `mark`
                        // guard RS would bump it to 4 (+ ¬Less, ¬Eq) →
                        // IH-Disj reads as already-solved, skeleton
                        // replay picks the wrong open goal.
                        if mark && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.solved_formulas_mut().push(std::sync::Arc::new(g.clone()));
                        }
                        let d = crate::guarded::Guarded::Disj(vec![
                            crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&AAtom::Eq(i.clone(), j.clone()))),
                            crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&AAtom::Less(j.clone(), i.clone()))),
                        ]);
                        self.insert_formula_inner(d, false);
                        self.changed = ChangeIndicator::Changed;
                    }
                    AAtom::Less(_, _) => {
                        // Less on non-node terms — keep as formula.
                        if !crate::guarded::stores_contains(&self.sys.formulas, &g)
                            && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.formulas_mut().push(std::sync::Arc::new(g));
                            self.changed = ChangeIndicator::Changed;
                        }
                    }
                    AAtom::Eq(i, j)
                        if term_to_node_id(i).is_some() && term_to_node_id(j).is_some() =>
                    {
                        // i = j is false (i,j are node ids) ⇒ i < j ∨ j < i
                        // HS-faithful: only mark when called from top-level
                        // (`mark=True`), mirroring `markAsSolved = when mark
                        // ...` (Reduction.hs:424-491, see line 491).
                        if mark && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.solved_formulas_mut().push(std::sync::Arc::new(g.clone()));
                        }
                        let d = crate::guarded::Guarded::Disj(vec![
                            crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&AAtom::Less(i.clone(), j.clone()))),
                            crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&AAtom::Less(j.clone(), i.clone()))),
                        ]);
                        self.insert_formula_inner(d, false);
                        self.changed = ChangeIndicator::Changed;
                    }
                    AAtom::Last(i) => {
                        // Haskell `insertFormula` for `∀[].[Last i].⊥`
                        // (Reduction.hs:478-486):
                        //   markAsSolved
                        //   lst <- getM sLastAtom
                        //   j <- case lst of
                        //          Nothing -> do j <- freshLVar "last" LSortNode
                        //                        insertLast j; return j
                        //          Just j  -> return j
                        //   insert (gdisj [Less last_term i, Less i last_term])
                        //
                        // Haskell ALWAYS allocates fresh if `last_atom` is
                        // None; guarding this to only fire when already set
                        // makes `last_atom` get set later (during simplify)
                        // instead, emitting an extra visible `simplify` step
                        // where Haskell shows none.
                        // HS-faithful: only mark when called from top-level
                        // (`mark=True`), mirroring `markAsSolved = when mark
                        // ...` (Reduction.hs:424-491, see line 491).
                        if mark && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.solved_formulas_mut().push(std::sync::Arc::new(g.clone()));
                        }
                        let last_node = match &self.sys.last_atom {
                            Some(j) => j.clone(),
                            None => {
                                let baseline = self.fresh_var_baseline();
                                let j = tamarin_term::lterm::LVar::new(
                                    "last",
                                    tamarin_term::lterm::LSort::Node,
                                    baseline.saturating_add(1));
                                self.sys.invalidate_max_var_idx_cache();
                                self.sys.set_last_atom(Some(j.clone()));
                                j
                            }
                        };
                        let last_term = tamarin_parser::ast::Term::Var(
                            tamarin_parser::ast::VarSpec {
                                name: last_node.name.to_string(),
                                idx: last_node.idx,
                                sort: tamarin_parser::ast::SortHint::Node,
                                typ: None,
                            });
                        let d = crate::guarded::Guarded::Disj(vec![
                            crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&AAtom::Less(last_term.clone(), i.clone()))),
                            crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&AAtom::Less(i.clone(), last_term))),
                        ]);
                        self.insert_formula_inner(d, false);
                        self.changed = ChangeIndicator::Changed;
                    }
                    AAtom::Subterm(s, b) => {
                        // ¬(s ⊏ b) — HS `insertFormula` "negative Subterm"
                        // arm (Reduction.hs:567-570):
                        //   markAsSolved
                        //   insertNegSubterm (bTermToLTerm i) (bTermToLTerm j)
                        // The formula is CONSUMED into the subterm store's
                        // negSubterms — it never enters sFormulas, so the
                        // atom-valuation pass can't collapse it to ⊥ and the
                        // eventual contradiction is attributed to the store
                        // ("contradictory subterm store"), exactly as HS.
                        // HS-faithful: only mark when called from top-level
                        // (`mark=True`), mirroring `markAsSolved = when mark
                        // ...` (Reduction.hs:424-491, see line 491).
                        if mark && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.solved_formulas_mut().push(std::sync::Arc::new(g.clone()));
                        }
                        if let (Some(ts), Some(tb)) = (
                            crate::elaborate::term_to_lnterm(s),
                            crate::elaborate::term_to_lnterm(b),
                        ) {
                            self.sys.invalidate_max_var_idx_cache();
                            if self.sys.subterm_store_mut().add_neg(ts, tb) {
                                self.changed = ChangeIndicator::Changed;
                            }
                        } else if !crate::guarded::stores_contains(&self.sys.formulas, &g) {
                            // Defensive fallback for terms our LNTerm
                            // conversion can't represent — keep visible
                            // as a formula rather than dropping.
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.formulas_mut().push(std::sync::Arc::new(g));
                            self.changed = ChangeIndicator::Changed;
                        }
                    }
                    _ => {
                        // Unhandled single-guard universal: keep in formulas.
                        if !crate::guarded::stores_contains(&self.sys.formulas, &g)
                            && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                            self.sys.invalidate_max_var_idx_cache();
                            self.sys.formulas_mut().push(std::sync::Arc::new(g));
                            self.changed = ChangeIndicator::Changed;
                        }
                    }
                }
            }
            Guarded::GGuarded { .. } => {
                // Universal quantification: store in `sFormulas` so
                // `insert_implied_formulas_pass` can iterate and
                // instantiate it against system actions.  Mirrors
                // Haskell's `insertFormula` for `All`-quantified
                // guarded formulas — those go into `sFormulas`, not
                // `sSolvedFormulas`. Without this, lemmas reduce
                // their universals into a dead store and the body
                // never fires (Start_before_Loop &c. mistakenly
                // reach Solved).
                if !crate::guarded::stores_contains(&self.sys.formulas, &g)
                    && !crate::guarded::stores_contains(&self.sys.solved_formulas, &g) {
                    self.sys.invalidate_max_var_idx_cache();
                    self.sys.formulas_mut().push(std::sync::Arc::new(g));
                    self.changed = ChangeIndicator::Changed;
                }
            }
        }
    }

    /// Mark a goal as solved (if present). Mirrors
    /// `markGoalAsSolved`.
    pub fn mark_goal_as_solved(&mut self, g: &Goal) {
        // Mirrors Haskell `markGoalAsSolved` (Reduction.hs:527-547):
        //   ActionG / Premise(non-KD) / Split / Subterm → updateStatus
        //   Premise(KD) / Chain                          → DELETE
        //   Disj → move formula to solved_formulas + updateStatus
        let should_delete = match g {
            Goal::Chain(_, _) => true,
            Goal::Premise(_, fa) => matches!(fa.tag, crate::fact::FactTag::Kd),
            _ => false,
        };
        if should_delete {
            let before = self.sys.goals.len();
            self.sys.invalidate_max_var_idx_cache();
            self.sys.goals_mut().retain(|(eg, _)| eg != g);
            if self.sys.goals.len() != before {
                self.changed = ChangeIndicator::Changed;
            }
            return;
        }
        // Disjunction goals also move the formula from formulas →
        // solved_formulas (Haskell `markGoalAsSolved` DisjG branch).
        if let Goal::Disj(d) = g {
            use crate::guarded::Guarded;
            let f = Guarded::Disj(d.0.clone());
            let pos = self.sys.formulas.iter().position(|x| **x == f);
            if let Some(idx) = pos {
                self.sys.invalidate_max_var_idx_cache();
                self.sys.formulas_mut().remove(idx);
                if !crate::guarded::stores_contains(&self.sys.solved_formulas, &f) {
                    self.sys.invalidate_max_var_idx_cache();
                    self.sys.solved_formulas_mut().push(std::sync::Arc::new(f));
                }
                self.changed = ChangeIndicator::Changed;
            }
        }
        for (existing, status) in self.sys.goals_mut().iter_mut() {
            if existing == g && !status.solved {
                status.solved = true;
                self.changed = ChangeIndicator::Changed;
                break;
            }
        }
    }

    /// Remove all `Split` goals whose split id is no longer valid in
    /// the equation store. Matches Haskell's `removeSolvedSplitGoals`
    /// at `Reduction.hs:558-561`:
    ///
    /// ```haskell
    /// removeSolvedSplitGoals = do
    ///     goals    <- getM sGoals
    ///     existent <- splitExists <$> getM sEqStore
    ///     sequence_ [ modM sGoals $ M.delete goal
    ///               | goal@(SplitG i) <- M.keys goals, not (existent i) ]
    /// ```
    ///
    /// HS removes EVERY `SplitG i` whose `i` is no longer in the eq
    /// store — regardless of the goal's solved-status flag.  An
    /// earlier `simp` pass on the eq store can drop disjunctions
    /// (e.g. via `simpRemoveRenamings`, `simpEmptyDisj`, or by
    /// substituting one disj's content into the global subst), which
    /// leaves the `SplitG i` goal behind referring to a no-longer-
    /// existent split-id.  When HS prunes those, the goal-rank input
    /// shrinks, which on exists-trace lemmas like CH07::executable
    /// changes which `split_case_N` the DFS picks first.
    pub fn remove_solved_split_goals(&mut self) {
        use crate::constraint::constraints::Goal as G;
        let valid: std::collections::BTreeSet<_> = self.sys.eq_store.conj.iter()
            .map(|d| d.split_id)
            .collect();
        let before = self.sys.goals.len();
        self.sys.invalidate_max_var_idx_cache();
        self.sys.goals_mut().retain(|(g, _status)| match g {
            // HS-faithful: drop the goal whenever the split_id no
            // longer backs an eq-store disjunction (ignore solved
            // flag).
            G::Split(id) => valid.contains(id),
            _ => true,
        });
        if self.sys.goals.len() != before {
            self.changed = ChangeIndicator::Changed;
        }
    }
}


// =============================================================================
// Equality solving — bridges into the equation store
// =============================================================================

/// Whether to perform a case-split immediately or defer it as a goal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SplitStrategy { SplitNow, SplitLater }

/// Outcome of an equality-solving step.
#[derive(Debug)]
pub enum SolveOutcome {
    /// Single case — the same `Reduction` continues.
    Linear(ChangeIndicator),
    /// Multiple cases — the caller picks one and continues. Mirrors
    /// the disjunctive branching of the Haskell `Reduction` monad.
    Cases(Vec<crate::tools::equation_store::EquationStore>),
    /// Equation store became contradictory.
    Contradictory,
}

impl<'ctx> Reduction<'ctx> {
    /// `solveTermEqs` — add a list of term equalities to the equation
    /// store, optionally splitting if the unifier produced more than
    /// one disjunct. Mirrors the Haskell function in
    /// `Theory.Constraint.Solver.Reduction`.
    #[track_caller]
    pub fn solve_term_eqs(
        &mut self,
        strategy: SplitStrategy,
        eqs: &[tamarin_term::rewriting::Equal<tamarin_term::lterm::LNTerm>],
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        // Filter out trivially-equal equations.
        let pending: Vec<_> = eqs.iter()
            .filter(|e| e.lhs != e.rhs)
            .cloned()
            .collect();
        // TAM_RS_DBG_SOLVE_TERM_EQS=1 dumps every solve_term_eqs call's
        // caller location (via #[track_caller]), split strategy,
        // equation count, and the equations.  Pair with HS's
        // TAM_HS_DBG_SOLVE_TERM_EQS for HS↔Rust diffing of the
        // goal-by-goal solver flow.
        if tamarin_utils::env_gate!("TAM_RS_DBG_SOLVE_TERM_EQS") {
            let loc = std::panic::Location::caller();
            let site = format!("{}:{}", loc.file(), loc.line());
            if pending.is_empty() {
                eprintln!("[rs-ste-tick] zero-eqs site={} (filtered {} trivial)",
                          site, eqs.len());
            } else {
                eprintln!("[rs-ste] === call site={} split={:?} n={}",
                          site, strategy, pending.len());
                for (i, eq) in pending.iter().enumerate() {
                    eprintln!("  eq[{}]: {:?} = {:?}", i, eq.lhs, eq.rhs);
                }
            }
        }
        if pending.is_empty() {
            return Ok(SolveOutcome::Linear(ChangeIndicator::Unchanged));
        }
        if crate::constraint::solver::trace::exec_enabled() {
            crate::constraint::solver::trace::trace_exec(
                &format!("solveTermEqs n={}", pending.len()));
        }

        // Take eq_store out of self, mutate it, put it back, then
        // borrow Maude — this avoids overlapping borrows of self.
        let maude = self.maude.clone();
        // Pass the system-wide max idx so Maude witnesses get renamed
        // above ANY existing variable in the system (not just in the
        // eq-store).  Without this, witnesses collide with rule vars,
        // goal vars, formula vars, etc., conflating distinct semantic
        // variables.
        let avoid = bounds_max(&self.sys);
        // Set op label so apply_eq_store's [rs-aes-tick] trace
        // attributes calls to solveTermEqs (matches HS's
        // `addEqsLabeled "solveTermEqs"` site naming).
        let _op_guard = crate::constraint::solver::trace::OpLabelGuard::new("solveTermEqs");
        let split = self.sys.eq_store_mut().add_eqs_with_avoid(&maude, &pending, avoid)?;
        // Run simp with substCreatesNonNormalTerms as the is_contr
        // predicate.  Without it, SplitG variants that would
        // introduce non-normal terms (e.g. verify=sign(...)) aren't
        // filtered; Haskell uses this exact check.  Gated to non-
        // empty reducible signatures — pair-only theories never
        // produce non-normal subterms structurally so the check is
        // pure overhead.  See contradictions.rs::subst_creates_non_normal_terms.
        let has_reducible = !maude.maude_sig().reducible_fun_syms.is_empty();
        // The checker is consumed ONLY by the `if has_reducible` arm of
        // `do_simp` below.  It snapshots the `maybeNonNormalTerms` walk
        // of `self.sys` ONCE here — mirroring HS's curried
        // `substCreatesNonNormalTerms hnd se` (Reduction.hs:944), which
        // captures `se` at the `simp` call and shares the walk across
        // every candidate subst probed (see `SubstNfChecker`).  Gated on
        // `has_reducible` so pair-only signatures pay nothing on this hot
        // unification path.
        let nf_checker = has_reducible.then(||
            crate::constraint::solver::contradictions::SubstNfChecker::new(
                &maude, &self.sys));
        // Collect live system vars so `simp_singleton`'s `fresh_to_free`
        // doesn't rename them.  Mirrors `solve_split_goal`'s approach.
        // Functionally dead in production: `simp_singleton_avoiding` reads
        // this set ONLY inside its three debug gates (the fold itself calls
        // `fresh_to_free_avoiding`, which ignores it), so only pay the
        // whole-System walk when a gate is on — see
        // `preserve_dbg_gates_enabled`.
        let system_vars = if preserve_dbg_gates_enabled() {
            collect_live_system_vars(&self.sys)
        } else {
            std::collections::BTreeSet::new()
        };
        let store = std::sync::Arc::unwrap_or_clone(self.sys.take_eq_store());
        // Use `simp_with_fresh_avoiding` so singleton SplitG disjunctions
        // get folded into `subst` via `simp_singleton`.  Haskell's `simp`
        // (EquationStore.hs:354-369, see line 361) calls `simpSingleton` as part of the
        // main loop, so by the time the search sees the goal list, a
        // singleton variant subst is already in `subst`.  Without this,
        // we leave a stale SplitG goal in `sys.goals` and the search
        // emits an extra `solve` step for it (e.g. issue193::debug).
        let maude_alloc = maude.clone();
        // Closure-style helper: simp one EquationStore with the same
        // non-normal-terms predicate + system_vars.  Reused for both
        // the no-split branch and the per-arm SplitNow loop below.
        // `nf_checker.is_some()` iff `has_reducible` (built via
        // `has_reducible.then(...)`), so the checker's presence IS the
        // reducible-symbol dispatch: `as_ref()` is `Some` exactly when
        // the non-normal-terms check must run.
        let do_simp = |s: crate::tools::equation_store::EquationStore|
                -> crate::tools::equation_store::EquationStore {
            simp_store(s, nf_checker.as_ref(), &maude_alloc, &system_vars)
        };

        match (split, strategy) {
            (Some(id), SplitStrategy::SplitNow) => {
                // HS-faithful: perform_split FIRST, then simp + is_false
                // check PER ARM.  Mirrors Haskell `solveTermEqs`
                // (Reduction.hs:712-731):
                //   setM sEqStore =<< simp ... =<<
                //       case (maySplitId, splitStrat) of
                //         (Just splitId, SplitNow) -> disjunctionOfList
                //                $ performSplit eqs2 splitId
                //         ...
                //   noContradictoryEqStore
                // The `disjunctionOfList performSplit` returns each arm
                // in the Disj monad; `simp` and `noContradictoryEqStore`
                // then run per arm.  Arm-specific subst can trigger
                // contradictions that the un-split pre-simp store
                // doesn't show (the subst composition into existing
                // disjs may produce empty disjs in some arms but not
                // others).  Without per-arm simp, those arms slip
                // through to downstream consumers as live cases.
                let arms = store.perform_split(id)
                    .ok_or_else(|| crate::tools::equation_store::AddEqsError::Maude(
                        format!("split id {:?} not found", id)))?;
                let raw_count = arms.len();
                let mut live_arms: Vec<crate::tools::equation_store::EquationStore> = Vec::new();
                // HS-faithful per-arm counter fork.  HS `solveTermEqs`
                // (Reduction.hs:712-731) runs
                //   `disjunctionOfList (performSplit eqs2 splitId)` and THEN
                //   `simp` per arm — the `disjunctionOfList` sits in the
                // DisjT layer BELOW FreshT (`Reduction = StateT System
                // (FreshT (DisjT ...))`, Reduction.hs:115-115, see line 123), so each arm's
                // `simp` (whose `simpSingleton` fold draws fresh idxs via
                // `freshToFree`) starts from an independent COPY of the
                // counter at the fan-out point.  RS's `do_simp` allocs via
                // the ONE shared `maude_alloc` counter, so consecutive arms
                // threaded each other's fold draws: on RYY_PFS's
                // `KU(em(t.1,t.2))` source the two C-unifier arms folded at
                // t.7/t.8 and t.9/t.10 where HS has t.7/t.8 in BOTH
                // (hs_ryy.err SAT-STEP: case2 = same t.7/t.8, premises
                // swapped).  Rewind to the pre-fork base before each arm and
                // restore the high-water mark after the loop, exactly as
                // `solve_action_goal` does around its candidate fork.
                let arm_fork_base = maude_alloc.fresh_counter_peek();
                let mut arm_high_water = arm_fork_base;
                for arm in arms {
                    maude_alloc.reset_counter_to(arm_fork_base);
                    if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
                        eprintln!("[rs-fold] STE-ARM fork_base={}", arm_fork_base);
                    }
                    let simped = do_simp(arm);
                    arm_high_water = arm_high_water.max(maude_alloc.fresh_counter_peek());
                    if simped.is_false() { continue; }
                    live_arms.push(simped);
                }
                maude_alloc.ensure_above(arm_high_water.saturating_sub(1));
                if tamarin_utils::env_gate!("TAM_RS_DBG_STE_RAW") {
                    let loc = std::panic::Location::caller();
                    eprintln!("[STE_RAW] raw={} live={} site={}:{} pending_eqs={}",
                        raw_count, live_arms.len(), loc.file(), loc.line(),
                        pending.len());
                }
                if live_arms.is_empty() {
                    // All arms contradicted under per-arm simp.
                    // Install a false store so downstream is_false
                    // checks see it (mirrors HS noContradictoryEqStore
                    // firing mzero on every arm).
                    self.sys.invalidate_max_var_idx_cache();
                    self.sys.set_eq_store(std::sync::Arc::new(crate::tools::equation_store::EquationStore::default()
                        .set_false()));
                    return Ok(SolveOutcome::Contradictory);
                }
                self.changed = ChangeIndicator::Changed;
                if live_arms.len() == 1 {
                    // Single arm survived: install as the current
                    // eq_store and return Linear (no caller-side fork
                    // needed).
                    self.sys.invalidate_max_var_idx_cache();
                    self.sys.set_eq_store(std::sync::Arc::new(live_arms.into_iter().next().unwrap()));
                    Ok(SolveOutcome::Linear(ChangeIndicator::Changed))
                } else {
                    if tamarin_utils::env_gate!("TAM_RS_DBG_STE_MULTI") {
                        let loc = std::panic::Location::caller();
                        eprintln!("[STE_MULTI] arms={} site={}:{} pending_eqs={}",
                            live_arms.len(), loc.file(), loc.line(), pending.len());
                    }
                    Ok(SolveOutcome::Cases(live_arms))
                }
            }
            (Some(id), SplitStrategy::SplitLater) => {
                // No split fanout — simp once on the combined store.
                self.sys.invalidate_max_var_idx_cache();
                self.sys.set_eq_store(std::sync::Arc::new(do_simp(store)));
                if self.sys.eq_store.is_false() {
                    return Ok(SolveOutcome::Contradictory);
                }
                self.insert_goal(crate::constraint::constraints::Goal::Split(id));
                self.changed = ChangeIndicator::Changed;
                Ok(SolveOutcome::Linear(ChangeIndicator::Changed))
            }
            (None, _) => {
                // No split — simp once.
                self.sys.invalidate_max_var_idx_cache();
                self.sys.set_eq_store(std::sync::Arc::new(do_simp(store)));
                if self.sys.eq_store.is_false() {
                    return Ok(SolveOutcome::Contradictory);
                }
                self.changed = ChangeIndicator::Changed;
                Ok(SolveOutcome::Linear(ChangeIndicator::Changed))
            }
        }
    }

    /// `solveNodeIdEqs` — equalities between node-id variables.
    pub fn solve_node_id_eqs(
        &mut self,
        eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        if tamarin_utils::env_gate!("TAM_DBG_NODE_EQS") {
            for e in eqs {
                eprintln!("[node_eqs] {:?} = {:?}", e.lhs, e.rhs);
            }
        }
        let term_eqs: Vec<tamarin_term::rewriting::Equal<tamarin_term::lterm::LNTerm>> =
            eqs.iter()
                .map(|e| tamarin_term::rewriting::Equal {
                    lhs: Term::Lit(Lit::Var(e.lhs.clone())),
                    rhs: Term::Lit(Lit::Var(e.rhs.clone())),
                })
                .collect();
        self.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs)
    }

    /// `solveNodeIdEqs` applied to arm0 (`self.sys`) AND to every arm
    /// stashed in `pending_eq_arms`.
    ///
    /// HS `enforceNodeUniqueness`/`enforceFreshAndKuNodeUniqueness`
    /// (Simplify.hs:273-276, 356-360) merges each candidate group with
    /// `solver <*> solveTermEqsLabeled SplitNow (node-id-eqs)`: the fact/
    /// rule `solver` runs FIRST (and, on AC-multiunifiers, forks the whole
    /// `DisjT` continuation via `disjunctionOfList $ performSplit`,
    /// Reduction.hs:981-991), and the node-id equalities are then solved
    /// INSIDE each forked arm's continuation.  So every arm of the fact/
    /// rule split gets the same node-id merges applied.
    ///
    /// RS lacks lazy `DisjT`: a fact/rule split stashes arms in
    /// `pending_eq_arms` and only `self.sys` (arm0) continues in place, so
    /// the node-id eqs that HS runs per arm would reach arm0 ONLY.  A
    /// pending arm then re-enters `simplify` missing those node-id
    /// bindings; its first `subst_system` sees fewer node collisions and
    /// re-cascades the setNodes drain differently, re-emitting a duplicate
    /// multiset split (Joux Session_Key_Secrecy_PFS Proto1: the pending KD-
    /// merge arm re-drained the $B/$C `Union` disjunction as a second
    /// `splitEqs(10)` byte-identical to `splitEqs(9)`, so `removeRedundant-
    /// Cases` kept 18 cases where HS keeps 10).  Broadcasting the node-id
    /// eqs to the pending arms makes each arm's store carry the identical
    /// node-id bindings HS's per-arm continuation applies.
    ///
    /// Node-id (Var=Var) unification never forks (single unifier) and draws
    /// no fresh witness indices, so the per-arm application is counter-
    /// neutral (the shared counter is restored afterwards; the pending arms
    /// re-seed from the fan-out fork counter in any case).
    pub fn solve_node_id_eqs_broadcast(
        &mut self,
        eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        // Fork base: the counter position BEFORE arm0's own node-id
        // merge, i.e. the position HS's `DisjT` copies to every arm at the
        // preceding fact/rule split.  Each arm's node-id merge must start
        // from this same base (HS threads an independent FreshT copy per
        // arm), so rewind to it before each pending arm and restore arm0's
        // post-merge position at the end.
        let fork_base = self.maude.fresh_counter_peek();
        let out = self.solve_node_id_eqs(eqs);
        if self.pending_eq_arms.is_empty() {
            return out;
        }
        let arm0_end = self.maude.fresh_counter_peek();
        let arm0_store = self.sys.take_eq_store();
        let pending = std::mem::take(&mut self.pending_eq_arms);
        let mut new_pending = Vec::with_capacity(pending.len());
        for arm in pending {
            self.maude.reset_counter_to(fork_base);
            self.sys.invalidate_max_var_idx_cache();
            self.sys.set_eq_store(std::sync::Arc::new(arm));
            // Ignore the outcome: a contradictory arm keeps its `is_false`
            // store and is dropped at the `fan_out_on_pending_eq_arms`
            // is_false filter, exactly as HS's per-arm `noContradictory-
            // EqStore` mzero drops that arm from the `DisjT`.
            let _ = self.solve_node_id_eqs(eqs);
            let updated = self.sys.take_eq_store();
            new_pending.push(std::sync::Arc::unwrap_or_clone(updated));
        }
        self.sys.invalidate_max_var_idx_cache();
        self.sys.set_eq_store(arm0_store);
        self.pending_eq_arms = new_pending;
        // Restore arm0's post-merge counter (fan-out then re-seeds every
        // arm from this position, matching arm0's continuation).
        self.maude.reset_counter_to(arm0_end);
        out
    }

    /// `solveFactEqs` — equate two fact lists. Returns
    /// `Contradictory` if any pair of facts has different tags or
    /// arities.
    ///
    /// Mirrors Haskell `solveFactEqs` (Reduction.hs:743-746):
    /// ```haskell
    /// solveFactEqs split eqs = do
    ///     contradictoryIf (not $ all evalEqual $ map (fmap factTag) eqs)
    ///     solveListEqs (solveTermEqs split) $ ...
    /// ```
    /// The `contradictoryIf` fires mzero on tag/arity mismatch.  We
    /// emulate mzero by flipping `eq_store.is_false` AND returning
    /// `Contradictory` — the proof_method.rs SolveGoal arm uses
    /// `eq_store.is_false` as the mzero proxy when filtering cases,
    /// so without the flip a tag-mismatch case would slip through.
    #[track_caller]
    pub fn solve_fact_eqs(
        &mut self,
        strategy: SplitStrategy,
        eqs: &[tamarin_term::rewriting::Equal<crate::fact::LNFact>],
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        for e in eqs {
            if e.lhs.tag != e.rhs.tag || e.lhs.terms.len() != e.rhs.terms.len() {
                // Set eq_store.is_false so the SolveGoal-arm mzero
                // proxy filter (the SolveGoal-arm eq_store.is_false()
                // case-drop in exec_proof_method, proof_method.rs:584)
                // sees the contradiction even if the caller `let _ = ...`s
                // our result.  Mirrors Haskell's `contradictoryIf`
                // (Reduction.hs:743-745, see line 745) firing mzero on tag mismatch.
                self.set_eq_store_false();
                return Ok(SolveOutcome::Contradictory);
            }
        }
        let mut flat = Vec::new();
        for e in eqs {
            for (a, b) in e.lhs.terms.iter().zip(e.rhs.terms.iter()) {
                flat.push(tamarin_term::rewriting::Equal {
                    lhs: a.clone(), rhs: b.clone(),
                });
            }
        }
        self.solve_term_eqs(strategy, &flat)
    }

    /// `solveRuleEqs` — equate two rule instances.  Mirrors
    /// `Reduction.hs:749-754`: checks rInfo equality, then runs
    /// `solveFactEqs` on conclusions, premises, actions.
    ///
    /// Mirrors Haskell `solveRuleEqs` (Reduction.hs:749-754):
    /// ```haskell
    /// solveRuleEqs split eqs = do
    ///     contradictoryIf (not $ all evalEqual $ map (fmap (get rInfo)) eqs)
    ///     solveListEqs (solveFactEqs split) ...
    /// ```
    /// `contradictoryIf` fires mzero on rInfo mismatch.  Set
    /// `eq_store.is_false` here so the SolveGoal-arm mzero proxy
    /// catches the contradiction, mirroring the helper for
    /// `solve_fact_eqs`.
    pub fn solve_rule_eqs(
        &mut self,
        strategy: SplitStrategy,
        eqs: &[tamarin_term::rewriting::Equal<RuleACInst>],
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        // Rule infos must match (rule names, intruder-info, etc.).
        for e in eqs {
            if e.lhs.info != e.rhs.info {
                self.set_eq_store_false();
                return Ok(SolveOutcome::Contradictory);
            }
        }
        // Haskell `solveRuleEqs` (Reduction.hs:752-754) feeds `solveFactEqs`
        // `map (fmap (get rConcs)) eqs ++ map (fmap (get rPrems)) eqs
        //  ++ map (fmap (get rActs)) eqs`, i.e. ALL conclusions across every
        // eq, THEN all premises, THEN all actions (a batch transpose, not a
        // per-eq conc/prem/act interleave).
        let mut conc_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>>
            = Vec::new();
        let mut prem_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>>
            = Vec::new();
        let mut act_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>>
            = Vec::new();
        for e in eqs {
            for (a, b) in e.lhs.conclusions.iter().zip(e.rhs.conclusions.iter()) {
                conc_eqs.push(tamarin_term::rewriting::Equal {
                    lhs: a.clone(), rhs: b.clone(),
                });
            }
            for (a, b) in e.lhs.premises.iter().zip(e.rhs.premises.iter()) {
                prem_eqs.push(tamarin_term::rewriting::Equal {
                    lhs: a.clone(), rhs: b.clone(),
                });
            }
            for (a, b) in e.lhs.actions.iter().zip(e.rhs.actions.iter()) {
                act_eqs.push(tamarin_term::rewriting::Equal {
                    lhs: a.clone(), rhs: b.clone(),
                });
            }
        }
        let mut fact_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>>
            = Vec::with_capacity(conc_eqs.len() + prem_eqs.len() + act_eqs.len());
        fact_eqs.append(&mut conc_eqs);
        fact_eqs.append(&mut prem_eqs);
        fact_eqs.append(&mut act_eqs);
        self.solve_fact_eqs(strategy, &fact_eqs)
    }

    /// `setNodes` — normalise node list so node ids are unique,
    /// updating `sNodes` and emitting rule-eqs for collisions.
    /// Mirrors `Reduction.hs:614-624`.
    ///
    /// Takes the FULL desired node list (caller is responsible for
    /// concatenating case + live nodes).  Groups by id; for each
    /// group, keeps the first as canonical and emits rule-eqs for
    /// the rest.  Runs `solveRuleEqs SplitLater` on accumulated eqs.
    pub fn set_nodes(
        &mut self,
        nodes: Vec<(crate::constraint::constraints::NodeId, RuleACInst)>,
    ) -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError> {
        use std::collections::BTreeMap;
        // Group by id, preserving first-occurrence order for "keep".
        let mut groups: BTreeMap<crate::constraint::constraints::NodeId, Vec<RuleACInst>>
            = BTreeMap::new();
        let mut order: Vec<crate::constraint::constraints::NodeId> = Vec::new();
        for (id, ru) in nodes {
            if !groups.contains_key(&id) { order.push(id.clone()); }
            groups.entry(id).or_default().push(ru);
        }
        let mut canonical: Vec<(crate::constraint::constraints::NodeId, RuleACInst)>
            = Vec::with_capacity(order.len());
        let mut rule_eqs: Vec<tamarin_term::rewriting::Equal<RuleACInst>> = Vec::new();
        for id in order {
            let mut bucket = groups.remove(&id).expect("groups");
            let keep = bucket.remove(0);
            for remove in bucket {
                rule_eqs.push(tamarin_term::rewriting::Equal {
                    lhs: keep.clone(), rhs: remove,
                });
            }
            canonical.push((id, keep));
        }
        // Canonical node merge dedups colliding ids (dropping duplicate
        // rules) — node max can DROP, invalidate the node component too.
        self.sys.invalidate_max_var_idx_cache();
        self.sys.invalidate_node_max_cache();
        self.sys.content_mut_untracked().nodes = std::sync::Arc::new(canonical);
        if rule_eqs.is_empty() {
            return Ok(SolveOutcome::Linear(ChangeIndicator::Unchanged));
        }
        self.changed = ChangeIndicator::Changed;
        self.solve_rule_eqs(SplitStrategy::SplitLater, &rule_eqs)
    }

    /// `conjoinSystem` — port of `Reduction.hs:660-689`.  Merges the
    /// information in `sys` (typically a freshened source-case) into
    /// `self.sys`, faithfully following Haskell's step order:
    ///
    /// 1. joinSets sSolvedFormulas
    /// 2. joinSets sLemmas
    /// 3. joinSets sEdges
    /// 4. insertLast for each lastAtom (unifies if already set)
    /// 5. insertLess for each lessAtom
    /// 6. insertGoalStatus for each non-split goal
    /// 7. insertFormula for each formula
    /// 8. setNodes on (case_nodes ++ live_nodes) — emits rule-eqs on
    ///    id collisions, runs solveRuleEqs SplitLater
    /// 9. addDisj for each conj-disj-eq entry
    /// 10. conjoinSubtermStores
    /// 11. insertGoal(Split) for each new disj-id
    /// 12. solveSubstEqs SplitNow on case's subst
    /// 13. substSystem
    pub fn conjoin_system(&mut self, sys: &System)
        -> Result<SolveOutcome, crate::tools::equation_store::AddEqsError>
    {
        crate::state_trace::emit("conjoin_in", None, &self.sys);
        crate::state_trace::emit("conjoin_with", None, sys);
        if tamarin_utils::env_gate!("TAM_RS_TRACE_CONJOIN") {
            let path = crate::constraint::solver::trace::case_path_string();
            let live_fresh: Vec<String> = self.sys.nodes.iter()
                .filter(|(_, r)| matches!(&r.info,
                    crate::rule::RuleInfo::Proto(p) if p.name == crate::rule::ProtoRuleName::Fresh))
                .map(|(id, r)| format!("{}.{}={:?}", id.name, id.idx,
                    r.conclusions.first().map(|f| format!("{:?}", f.terms))))
                .collect();
            let case_fresh: Vec<String> = sys.nodes.iter()
                .filter(|(_, r)| matches!(&r.info,
                    crate::rule::RuleInfo::Proto(p) if p.name == crate::rule::ProtoRuleName::Fresh))
                .map(|(id, r)| format!("{}.{}={:?}", id.name, id.idx,
                    r.conclusions.first().map(|f| format!("{:?}", f.terms))))
                .collect();
            let case_subst: Vec<String> = sys.eq_store.subst.to_list().into_iter()
                .map(|(v, t)| format!("{}.{}/{:?}→{:?}", v.name, v.idx, v.sort, t))
                .collect();
            let live_subst: Vec<String> = self.sys.eq_store.subst.to_list().into_iter()
                .map(|(v, t)| format!("{}.{}/{:?}→{:?}", v.name, v.idx, v.sort,
                    format!("{:?}", t).chars().take(70).collect::<String>()))
                .collect();
            eprintln!("[CONJOIN] path={} live_fresh={:?} case_fresh={:?} case_subst={:?} live_subst={:?}",
                path, live_fresh, case_fresh, case_subst, live_subst);
            // ALL live nodes summary
            eprintln!("[CONJOIN]   live_all_nodes:");
            for (id, r) in self.sys.nodes.iter() {
                eprintln!("[CONJOIN]     {}.{} = {}", id.name, id.idx,
                    crate::constraint::solver::reduction::rule_case_name(r));
            }
            eprintln!("[CONJOIN]   live_edges:");
            for e in &self.sys.edges {
                eprintln!("[CONJOIN]     {}.{}.c{} → {}.{}.p{}",
                    e.src.0.name, e.src.0.idx, e.src.1.0,
                    e.tgt.0.name, e.tgt.0.idx, e.tgt.1.0);
            }
            eprintln!("[CONJOIN]   case_all_nodes:");
            for (id, r) in sys.nodes.iter() {
                eprintln!("[CONJOIN]     {}.{} = {}", id.name, id.idx,
                    crate::constraint::solver::reduction::rule_case_name(r));
            }
            eprintln!("[CONJOIN]   case_edges:");
            for e in &sys.edges {
                eprintln!("[CONJOIN]     {}.{}.c{} → {}.{}.p{}",
                    e.src.0.name, e.src.0.idx, e.src.1.0,
                    e.tgt.0.name, e.tgt.0.idx, e.tgt.1.0);
            }
            // Also dump Serv_1/Register_pk-like nodes from BOTH live and case.
            for (id, r) in self.sys.nodes.iter() {
                let nm = crate::constraint::solver::reduction::rule_case_name(r);
                if nm == "Serv_1" || nm == "Register_pk" {
                    eprintln!("[CONJOIN]   live {:?} → {}: prems={:?} concs={:?} acts={:?}",
                        id, nm,
                        r.premises.iter().map(|f| format!("{:?}", f.terms).chars().take(70).collect::<String>()).collect::<Vec<_>>(),
                        r.conclusions.iter().map(|f| format!("{:?}", f.terms).chars().take(70).collect::<String>()).collect::<Vec<_>>(),
                        r.actions.iter().map(|f| format!("{:?}", f.terms).chars().take(70).collect::<String>()).collect::<Vec<_>>());
                }
            }
            for (id, r) in sys.nodes.iter() {
                let nm = crate::constraint::solver::reduction::rule_case_name(r);
                if nm == "Serv_1" || nm == "Register_pk" {
                    eprintln!("[CONJOIN]   case {:?} → {}: prems={:?} concs={:?} acts={:?}",
                        id, nm,
                        r.premises.iter().map(|f| format!("{:?}", f.terms).chars().take(70).collect::<String>()).collect::<Vec<_>>(),
                        r.conclusions.iter().map(|f| format!("{:?}", f.terms).chars().take(70).collect::<String>()).collect::<Vec<_>>(),
                        r.actions.iter().map(|f| format!("{:?}", f.terms).chars().take(70).collect::<String>()).collect::<Vec<_>>());
                }
            }
        }
        // 1-3. joinSets: solved_formulas, lemmas, edges.  Use sets so
        // duplicates are collapsed (HasFrees-based dedup not needed —
        // syntactic equality is sufficient for these sets).
        for f in &sys.solved_formulas {
            if !crate::guarded::stores_contains(&self.sys.solved_formulas, f) {
                // Pure ADD (joinSets solved-formula merge under
                // !contains): bump.
                self.sys.bump_cache_guarded(f);
                self.sys.solved_formulas_mut().push(f.clone());
            }
        }
        for l in &sys.lemmas {
            if !crate::guarded::stores_contains(&self.sys.lemmas, l) {
                self.sys.invalidate_max_var_idx_cache();
                self.sys.lemmas_mut().push(l.clone());
            }
        }
        for e in &sys.edges {
            // Route through System::add_edge so the EXEC trace fires
            // (mirrors HS's `insertEdges` trace on the conjoin path).
            self.sys.add_edge(e.clone());
        }
        // 4. insertLast: HS-faithful (Reduction.hs:402-407 + conjoinSystem
        // Reduction.hs:669-698, see line 676 `F.mapM_ insertLast $ get sLastAtom sys`).
        if let Some(case_last) = &sys.last_atom {
            let r = self.insert_last(case_last.clone());
            if matches!(r, Err(_) | Ok(SolveOutcome::Contradictory)) {
                return r;
            }
        }
        // 5. insertLess.
        for l in &sys.less_atoms {
            self.insert_less(l.clone());
        }
        // 6. insertGoalStatus: skip split goals (their split-ids are
        // not valid in the merged system).  Mirrors Haskell's
        // `mapM_ (uncurry insertGoalStatus) $ filter (not . isSplitGoal . fst)
        //   $ M.toList $ get sGoals sys`.
        // For already-present goals, combine status: `solved = solved1 || solved2`,
        // `looping = loops1 || loops2`.  Direct port of
        // `combineGoalStatus` (Reduction.hs:510-513).
        //
        // HS iterates `M.toList` (Goal-derived Ord), so the freshly
        // assigned `gsNr`s for NEW goals follow Goal-Ord — within a
        // single graft batch an `ActionG` therefore gets a smaller nr
        // than a `PremiseG`.  Iterate in `goal_cmp` order to match
        // (RS's `sys.goals` is a Vec in production/push order, which
        // would otherwise assign the nrs in the wrong relative order).
        let mut conjoin_goals: Vec<&(crate::constraint::constraints::Goal,
            crate::constraint::system::GoalStatus)> = sys.goals.iter().collect();
        conjoin_goals.sort_by(|a, b|
            crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
        for (g, st) in conjoin_goals {
            if matches!(g, crate::constraint::constraints::Goal::Split(_)) {
                continue;
            }
            // HS `insertGoalStatus` runs `succ sNextGoalNr` on EVERY
            // non-split goal — even when the goal key already exists,
            // where `insertWith combineGoalStatus` keeps the smaller nr.
            // Route both the new and the already-present case through
            // `add_goal_with_loop_flag` so the counter advances
            // unconditionally, keeping RS's `next_goal_nr` (and the
            // goalNrRanking tie-break) aligned with HS on every conjoin
            // that hits a shared goal.
            // Then OR-in `solved` (combineGoalStatus) on the canonically
            // matching slot.
            self.sys.add_goal_with_loop_flag(g.clone(), st.looping);
            if st.solved {
                let canon = crate::constraint::system::canonical_goal_for_dedup(g);
                if let Some((_, slot)) = self.sys.goals_mut().iter_mut()
                    .find(|(eg, _)| crate::constraint::system::canonical_goal_for_dedup(eg) == canon)
                {
                    slot.solved = true;
                }
            }
        }
        // 7. insertFormula.  Haskell-faithful: `insertFormula` in
        // `conjoinSystem` (Reduction.hs:669-698, see line 673) DECOMPOSES guarded formulas
        // via the full CR-rule dispatch (Reduction.hs:425-490) — GAto →
        // insertAtom, GConj → recurse on conjuncts, GDisj → insertGoal
        // DisjG, GGuarded Ex → freshen + substBound, GGuarded All []
        // [Less|Subterm|EqE|Last] gf | gf==gfalse → markAsSolved +
        // negative-atom decomposition.  Without this dispatch, a
        // grafted case's `GGuarded All [] [Less i j] gfalse` formula
        // (the canonical encoding of `¬(i<j)`) stays raw in
        // `sys.formulas` instead of becoming the disjunction
        // `EqE i j ∨ Less j i`, so downstream FormulasFalse /
        // cyclic-LessAtom checks miss the contradiction even though
        // the algebra is already incompatible.
        for f in &sys.formulas {
            self.insert_formula(f.as_ref().clone());
        }
        // 8. setNodes (case_nodes ++ live_nodes).
        let mut all_nodes: Vec<_> = (*sys.nodes).clone();
        all_nodes.extend(self.sys.nodes.iter().cloned());
        let r = self.set_nodes(all_nodes);
        if matches!(r, Err(_) | Ok(SolveOutcome::Contradictory)) {
            return r;
        }
        // 9. addDisj for each case conjDisjEq entry.  Track new split-ids.
        let mut new_split_ids: Vec<crate::tools::equation_store::SplitId> = Vec::new();
        for disj in &sys.eq_store.conj {
            // TAM_DBG_CONJOIN_DISJ=1: dump each disj being added.
            if tamarin_utils::env_gate!("TAM_DBG_CONJOIN_DISJ") {
                for (j, s) in disj.substs.iter().enumerate() {
                    let pairs: Vec<String> = s.to_list().iter()
                        .map(|(k, v)| format!("{}.{}/{:?}→{:?}", k.name, k.idx, k.sort,
                            format!("{:?}", v).chars().take(60).collect::<String>()))
                        .collect();
                    eprintln!("[conjoin_disj] sid={:?} subst[{}] entries=[{}]",
                        disj.split_id, j, pairs.join(", "));
                }
            }
            if crate::tools::equation_store::impure_dbg_enabled() {
                for s in &disj.substs {
                    crate::tools::equation_store::dbg_register_subst_origin(
                        "conjoinSystem", s);
                }
            }
            let id = self.sys.eq_store_mut().add_disj(disj.substs.clone());
            new_split_ids.push(id);
        }
        // 10. conjoinSubtermStores — HS-faithful (SubtermStore.hs:108-110).
        // Mirrors HS `modM sSubtermStore (conjoinSubtermStores (get sSubtermStore sys))`
        // at Reduction.hs:669-698, see line 698.
        self.sys.subterm_store_mut().conjoin(&sys.subterm_store);
        // 11. insertGoal(SplitG) for each new split-id.
        for id in new_split_ids {
            self.insert_goal(crate::constraint::constraints::Goal::Split(id));
        }
        // 12. solveSubstEqs SplitNow on case's flat subst.
        //
        // HS-faithful fanout (Reduction.hs:669-698, see line 683): `solveSubstEqs SplitNow`
        // routes through `solveTermEqs SplitNow` which calls
        // `disjunctionOfList $ performSplit eqs2 splitId` — the `DisjT`
        // layer of the `Reduction` monad replicates the surrounding
        // `_applySource` continuation per AC unifier arm.  In our port
        // `solve_term_eqs` may return `Cases(arms)`.  We mirror the HS
        // semantics by snapshotting the post-step-11 system (this is the
        // `Reduction` state at the moment `solveSubstEqs` is entered, so
        // it's what each arm's `DisjT` branch sees), installing arm[0]
        // for the main return path, and stashing per-arm snapshots
        // (with `substSystem` already applied) in
        // `pending_conjoin_arm_systems` for the caller to drain.
        let case_subst_eqs: Vec<_> = sys.eq_store.subst.to_list().into_iter()
            .map(|(v, t)| tamarin_term::rewriting::Equal {
                lhs: tamarin_term::term::Term::Lit(
                    tamarin_term::vterm::Lit::Var(v)),
                rhs: t,
            })
            .collect();
        // Snapshot pre-step-12 sys for per-arm fanout.  Only taken when
        // we have any case_subst_eqs to feed (otherwise solve_term_eqs
        // returns Linear-trivial and there's nothing to fan out).
        let conjoin_fanout_enabled = !case_subst_eqs.is_empty();
        let pre_step12_snapshot: Option<crate::constraint::system::System> =
            if conjoin_fanout_enabled { Some(self.sys.clone()) } else { None };
        if tamarin_utils::env_gate!("TAM_RS_DBG_CONJOIN_STEP12") {
            eprintln!("[conjoin_step12] n_eqs={} fanout_enabled={}",
                case_subst_eqs.len(), conjoin_fanout_enabled);
        }
        let r = self.solve_term_eqs(SplitStrategy::SplitNow, &case_subst_eqs);
        match r {
            Err(_) | Ok(SolveOutcome::Contradictory) => { return r; }
            Ok(SolveOutcome::Linear(_)) => {
                // Single-arm path: solve_term_eqs already installed
                // arm[0]; just proceed to step 13.
            }
            Ok(SolveOutcome::Cases(arms)) => {
                // Multi-arm fanout.  solve_term_eqs returned Cases
                // without installing any arm; install arm[0] here,
                // then build per-arm snapshots for arms[1..].
                if tamarin_utils::env_gate!("TAM_RS_DBG_CONJOIN_FANOUT") {
                    eprintln!("[conjoin_fanout] arms={} (step 12 solveSubstEqs)",
                        arms.len());
                }
                let mut arm_iter = arms.into_iter();
                let arm0 = arm_iter.next().expect("Cases has >=2 arms");
                self.sys.invalidate_max_var_idx_cache();
                self.sys.set_eq_store(std::sync::Arc::new(arm0));
                // Build per-arm fanout snapshots from the pre-step-12 sys.
                // Each snapshot gets the arm's eq_store installed and
                // step 13 (substSystem) applied locally.
                if let Some(snapshot) = &pre_step12_snapshot {
                    // HS FreshT-threading (task #23, A(ii)): each
                    // solveSubstEqs arm is a DisjT branch BELOW FreshT
                    // (Reduction.hs:946-956 `disjunctionOfList arms`),
                    // so its substSystem (and everything after) draws
                    // from a fork-point COPY of the counter — not from
                    // `bounds_max(arm_sys)`.  `self.maude` here sits at
                    // the step-12 across-arm high water (solve_term_eqs
                    // restored it after its per-arm rewind loop); use
                    // that as the interim fork seed (faithful would be
                    // fork + arm_i's OWN eq-simp draws; the high water
                    // differs only when sibling arms draw unequal
                    // amounts).  Record each arm's continuation (seed +
                    // its substSystem node-merge witness draws) next to
                    // the stashed system for the drain site.
                    let step12_cont = self.maude.fresh_counter_peek();
                    for arm_i in arm_iter {
                        let mut arm_sys = snapshot.clone();
                        arm_sys.invalidate_max_var_idx_cache();
                        arm_sys.set_eq_store(std::sync::Arc::new(arm_i));
                        // Replicate step 13 substSystem locally on the
                        // arm-i sys by spinning a transient Reduction
                        // that CONTINUES the step's counter thread.
                        let mut arm_red = Reduction::new_inheriting(
                            self.ctx, arm_sys, step12_cont);
                        arm_red.subst_system();
                        if !arm_red.sys.eq_store.is_false() {
                            let arm_cont = arm_red.maude.fresh_counter_peek();
                            self.pending_conjoin_arm_systems.push(
                                (arm_red.sys, arm_cont));
                        }
                    }
                }
            }
        }
        // 13. substSystem.
        self.subst_system();
        if tamarin_utils::env_gate!("TAM_DBG_CONJOIN_POST") {
            let path = crate::constraint::solver::trace::case_path_string();
            eprintln!("[conjoin_post] path={} eq_store after step 13 ({} entries):",
                path, self.sys.eq_store.subst.to_list().len());
            for (v, t) in self.sys.eq_store.subst.to_list().iter().take(20) {
                eprintln!("[conjoin_post]   {}.{}/{:?} → {:?}", v.name, v.idx, v.sort,
                    format!("{:?}", t).chars().take(80).collect::<String>());
            }
        }
        Ok(SolveOutcome::Linear(ChangeIndicator::Changed))
    }
}

// =============================================================================
// Helpers used by goal solving.
// =============================================================================

/// Build the canonical `RuleACInst` for an `OpenProtoRule`.
///
/// Uses the abstracted form (Haskell `variantsProtoRule`'s output with
/// reducible-headed sub-terms abstracted to fresh `z_i` vars) so the
/// equality-restriction firing during simplify doesn't contradict on
/// the un-narrowed form.  Mirrors Haskell's `someRuleACInst`
/// (Rule.hs:925-934, see line 933) extracting the `RuleACInst` half from a `RuleAC`.
fn canonical_rule_inst(o: &crate::theory::OpenProtoRule) -> RuleACInst {
    // Always prefer the abstracted rule (reducible-headed sub-terms
    // narrowed to fresh `z_i` vars) when present, falling back to the
    // raw rule otherwise.
    let src: &crate::rule::ProtoRuleE =
        o.abstracted_rule.as_ref().unwrap_or(&o.rule);
    crate::rule::Rule {
        info: crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: src.info.name.clone(),
            attributes: src.info.attributes.clone(),
            loop_breakers: o.loop_breakers.clone(),
        }),
        premises: src.premises.clone(),
        conclusions: src.conclusions.clone(),
        actions: src.actions.clone(),
        new_vars: src.new_vars.clone(),
    }
}

/// `someRuleACInst`-style rule enumeration (Rule.hs:925-934, see line 933): one canonical
/// `RuleACInst` per `OpenProtoRule`, paired with its variant disjunction
/// (`Maybe RuleACConstrs`). Callers should add the disjunction to the
/// eq-store as a SplitG via `solve_rule_constraints` after labeling the
/// node. Intruder rules are added with `None` constraints (they have no
/// variants).
///
/// This is the Haskell-faithful path — there is no legacy fallback.
fn rule_insts_with_constrs<F: Fn(&RuleACInst) -> bool>(
    open: &[crate::theory::OpenProtoRule], keep: F,
) -> Vec<(RuleACInst, Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>)> {
    let mut out = Vec::new();
    for o in open {
        let inst = canonical_rule_inst(o);
        if !keep(&inst) { continue; }
        let constrs = if o.variant_substs.is_empty() {
            None
        } else {
            Some(o.variant_substs.clone())
        };
        out.push((inst, constrs));
    }
    out
}

/// SplitG-faithful non-silent rule enumeration: returns the
/// canonical rule per `OpenProtoRule` plus its variant disjunction.
/// Intruder rules carry `None` (no variants).
///
/// HS-faithful ordering: `joinAllRules (ClassifiedRules a b c) = a ++ b ++ c`
/// where (a, b, c) = (crProtocol, crDestruct, crConstruct).
/// `crProtocol` is `rulesAC` filtered to rules that are NEITHER
/// `isConstrRule` NOR `isDestrRule` — and `rulesAC = intruder ++ proto`,
/// so within `crProtocol` the non-constr-non-destr intruder rules
/// (ISend, IRecv) come BEFORE the protocol rules.  See `Rule.hs:163-176`.
///
/// HS's `isConstrRule` matches `ConstrRule _ | FreshConstrRule |
/// PubConstrRule | NatConstrRule | CoerceRule` (Model/Rule.hs:684-691);
/// `isDestrRule` matches `DestrRule _ _ _ _ | IEqualityRule`
/// (Model/Rule.hs:671-675).  We use HS-local predicates here so the
/// existing `is_constr_rule_info` / `is_destr_rule_info` callers
/// (dot.rs, context.rs's pc_true_subterm, chain handling) keep their
/// current — narrower — behaviour pending a separate audit.
fn non_silent_rule_insts_with_constrs(
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(RuleACInst, Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>)> {
    use crate::rule::IntrRuleACInfo;
    let is_constr_hs = |info: &IntrRuleACInfo| matches!(info,
        IntrRuleACInfo::ConstrRule(_)
        | IntrRuleACInfo::FreshConstr
        | IntrRuleACInfo::PubConstr
        | IntrRuleACInfo::NatConstr
        | IntrRuleACInfo::Coerce);
    let is_destr_hs = |info: &IntrRuleACInfo| matches!(info,
        IntrRuleACInfo::DestrRule(_, _, _, _)
        | IntrRuleACInfo::IEquality);

    // crProtocol arm: intruder-non-cd ++ protocol (rulesAC order).
    let mut cr_protocol: Vec<(RuleACInst, Option<_>)> = Vec::new();
    for ir in &ctx.intruder_rules {
        if ir.actions.is_empty() { continue; }
        if is_constr_hs(&ir.info) || is_destr_hs(&ir.info) { continue; }
        cr_protocol.push((intr_rule_to_rule_ac_inst(ir.clone()), None));
    }
    cr_protocol.extend(rule_insts_with_constrs(&ctx.rules, |r| !r.actions.is_empty()));

    // crDestruct + crConstruct: walk intruder_rules once, partition.
    let mut cr_destruct: Vec<(RuleACInst, Option<_>)> = Vec::new();
    let mut cr_construct: Vec<(RuleACInst, Option<_>)> = Vec::new();
    for ir in &ctx.intruder_rules {
        if ir.actions.is_empty() { continue; }
        if is_destr_hs(&ir.info) {
            cr_destruct.push((intr_rule_to_rule_ac_inst(ir.clone()), None));
        } else if is_constr_hs(&ir.info) {
            cr_construct.push((intr_rule_to_rule_ac_inst(ir.clone()), None));
        }
    }

    let mut out = cr_protocol;
    out.extend(cr_destruct);
    out.extend(cr_construct);
    out
}

fn intr_rule_to_rule_ac_inst(ir: crate::rule::IntrRuleAC) -> RuleACInst {
    crate::rule::Rule {
        info: crate::rule::RuleInfo::Intr(ir.info),
        premises: ir.premises,
        conclusions: ir.conclusions,
        actions: ir.actions,
        new_vars: ir.new_vars,
    }
}

/// Build the implicit `Fresh` rule instance: `[] --[]-> [Fr(m)]`
/// with `m` as the new-vars. Mirrors Haskell's `mkFreshRuleAC`.
fn make_fresh_rule(m: tamarin_term::lterm::LNTerm) -> RuleACInst {
    let info = crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
        name: crate::rule::ProtoRuleName::Fresh,
        attributes: crate::rule::RuleAttributes::empty(),
        loop_breakers: Vec::new(),
    });
    let conc = crate::fact::fresh_fact(m.clone());
    crate::rule::Rule::new(info, vec![], vec![conc], vec![])
        .with_new_vars(vec![m])
}

/// Dedup a Vec in place while preserving the FIRST occurrence's position.
///
/// Mirrors HS's `S.map` behaviour on `Set Guarded` in `substFormulas` /
/// `substSolvedFormulas` / `substLemmas` (Reduction.hs:593-595): when two
/// formulas become structurally equal after substitution, `S.map` rebuilds
/// the Set and only one survives.  Our `Vec<Guarded>` storage does NOT
/// auto-dedup, so we need to mirror this explicitly after subst.
fn dedup_preserve_order<T: PartialEq>(v: &mut Vec<T>) {
    // Keep the FIRST occurrence of each distinct element (preserving
    // first-occurrence order).  Two-pointer in-place compaction: for each
    // candidate, keep it only if it differs from every already-kept
    // element in the prefix `v[..kept]`.  This is O(n^2) comparisons with
    // no tail-shifting `Vec::remove`.  Requires only `T: PartialEq` (no Clone).
    let len = v.len();
    let mut kept = 0usize;
    for i in 0..len {
        let is_dup = (0..kept).any(|k| v[k] == v[i]);
        if !is_dup {
            if i != kept {
                v.swap(kept, i);
            }
            kept += 1;
        }
    }
    v.truncate(kept);
}

/// Convert an eq-store `LSubst` (LVar → LNTerm) into a parser-AST
/// `VarSubst` keyed by `(name, idx)`.  Used by `subst_system` to push
/// the eq-store substitution into formulas / solved_formulas /
/// lemmas — Haskell's `substFormulas` / `substSolvedFormulas` /
/// `substLemmas`.  Each LVar in the subst's domain maps via its
/// `(name, idx)` to a parser-AST term obtained from
/// `lnterm_to_term`.  Only entries that change are recorded
/// (skipping identity mappings keeps the per-step subst small).
fn build_parser_subst_from_eq_store(
    subst: &crate::tools::equation_store::LNSubst,
) -> crate::guarded::VarSubst {
    // Chain-chase to a canonical representative.  If the eq-store has both
    // `a → b` and `b → c`, the formula should rewrite `a` to `c` (not `b`).
    // Mirrors Haskell's `applyVTerm` behaviour where applying a composed
    // subst transitively follows var→var bindings to the canonical end.
    //
    // Concrete trigger: Minimal_HashChain::Loop_Start.  Check0's rule
    // produces `Loop(loopId, kOrig, kOrig)` — repeated arg.  Unifying
    // with lemma's `Loop(lid, k, kOrig)` binds both `k_lemma` and
    // `kOrig_lemma` to the rule's `kOrig`.  Subsequent compose may
    // funnel one through the other (e.g. `k_lemma → kOrig_rule →
    // kOrig_lemma`); without chain-chase in the parser_subst the
    // lemma's universal `Start(lid, kOrig)` doesn't get its `kOrig`
    // rewritten to match the rule action's canonical form, so
    // `structural_match` fails and `impliedFormulas` misses the
    // discharge, leaving FormulasFalse unfired — wrong-Solved.
    let lookup_chain = |start: &tamarin_term::lterm::LVar| -> tamarin_term::lterm::LNTerm {
        let mut cur = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(start.clone()));
        // Bound chain length to avoid pathological cycles (shouldn't
        // happen post-compose, but defensive).  Borrowing COW step: the
        // helper returns `None` exactly when applying `subst` leaves `cur`
        // structurally unchanged — the chain fixpoint — so we return `cur`
        // with no clone and no deep compare.
        for _ in 0..32 {
            match tamarin_term::subst::apply_vterm_changed(subst, &cur) {
                None => return cur,
                Some(next) => cur = next,
            }
        }
        cur
    };
    // Pre-size for the keyed-lookup-only output map (capacity is
    // output-invisible: nothing output-bearing iterates it).  Iterate
    // `dom()` (borrowed keys, same BTreeMap order) instead of `to_list()`,
    // which deep-clones every `(var, term)` pair we never read.
    let mut out = crate::guarded::VarSubst::with_capacity_and_hasher(
        subst.len(), Default::default());
    for lv in subst.dom() {
        let final_term = lookup_chain(lv);
        // Identity mappings are no-ops; skip.
        if let tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(w)) = &final_term {
            if w == lv { continue; }
        }
        let term = crate::elaborate::lnterm_to_term(&final_term);
        // `lv.name` is an interned `&'static str` — zero-alloc key.
        out.insert((lv.name, lv.idx), term);
    }
    out
}

/// Build the implicit `ISend` rule instance:
/// `[KU(m)] --[K(m)]-> [In(m)]`. Mirrors Haskell's `mkISendRuleAC`
/// at `Reduction.hs:217-270, see line 232`: `[kuFactAnn ann m] [inFact m] [kLogFact m]`.
///
/// `kLogFact` in Haskell is `protoFact Linear "K"` — a regular
/// ProtoFact tag named "K", *not* `DedFact`.  So ISend's action is
/// a ProtoFact.  A user-written `K(t) @ j` (which also parses to
/// `protoFact "K"` per the parser's fall-through) matches the ISend
/// action directly — that's how `K(t)` atoms in lemmas get satisfied
/// through adversary forwarding (Out → IRecv → KD → Coerce → KU →
/// ISend).
fn make_isend_rule(m: tamarin_term::lterm::LNTerm) -> RuleACInst {
    let info = crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend);
    let prem = crate::fact::ku_fact(m.clone());
    let act = crate::fact::k_log_fact(m.clone());
    let conc = crate::fact::in_fact(m);
    crate::rule::Rule::new(info, vec![prem], vec![conc], vec![act])
}

/// Apply an eq-store substitution to a node-id. Returns the new
/// representative if the subst maps `id` to a node-sort variable; else
/// the input unchanged.
fn normalise_node_id(
    id: crate::constraint::constraints::NodeId,
    subst: &crate::tools::equation_store::LNSubst,
) -> crate::constraint::constraints::NodeId {
    let id_term = tamarin_term::term::Term::Lit(
        tamarin_term::vterm::Lit::Var(id.clone()));
    let mapped = tamarin_term::subst::apply_vterm(subst, id_term);
    if let tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) = mapped {
        v
    } else {
        id
    }
}

/// Convert a parser-AST term to an `LVar` of node sort (for the time
/// argument of an action atom or the operands of a `Less`/`Last`).
/// Accepts either a `#i`-sorted variable or any unsorted variable in
/// a position requiring a node — the sort hint check is loose to
/// match Haskell's `ltermNodeId'`.
fn term_to_node_id(
    t: &tamarin_parser::ast::Term,
) -> Option<crate::constraint::constraints::NodeId> {
    use tamarin_parser::ast::{SortHint, SuffixSort, Term as AstTerm};
    let v = match t {
        AstTerm::Var(v) => v,
        _ => return None,
    };
    // Mirror Haskell `bltermNodeId` (Reduction.hs ~480): returns `Just`
    // only when the term is a Var with sort `LSortNode`. Returning
    // `Some` for non-Node sorts causes the Eq/Less→Disj CR-rules to
    // fire on msg-var `¬(a=b)` formulas — which Haskell leaves as
    // formulas, producing the SOLVED vs solve divergence on
    // MinValueEq/WrongEquality.
    match v.sort {
        SortHint::Node | SortHint::Suffix(SuffixSort::Node) => {
            Some(tamarin_term::lterm::LVar::new(
                v.name.clone(),
                tamarin_term::lterm::LSort::Node,
                v.idx,
            ))
        }
        _ => None,
    }
}

/// `forbiddenEdge` — port of the chain-goal forbidden edge shapes.
fn forbidden_edge(c_rule: &RuleACInst, p_rule: &RuleACInst) -> bool {
    use crate::rule::{is_d_exp_rule, is_d_pmult_rule, is_d_emap_rule,
                       get_remaining_rule_applications, rule_name_string};
    if is_d_exp_rule(c_rule) && is_d_exp_rule(p_rule) { return true; }
    if is_d_pmult_rule(c_rule) && is_d_pmult_rule(p_rule) { return true; }
    if is_d_pmult_rule(c_rule) && is_d_emap_rule(p_rule) { return true; }
    let cn = rule_name_string(c_rule);
    let pn = rule_name_string(p_rule);
    if !cn.is_empty() && cn == pn && get_remaining_rule_applications(c_rule) == 1 {
        return true;
    }
    false
}

/// `illegalCoerce` — port of the chain-goal illegal coerce check
/// (Goals.hs:365-368).  Returns `true` if `p_rule` is a Coerce rule and
/// the chain-conclusion's down-K message `mPrem` is a pair / inverse /
/// product (which N2 forbids).  Haskell tests the bare term `mPrem`
/// (`= case kFactView faConc of Just (DnK, m') -> m'`); the caller
/// passes the chain-conc KD fact, whose sole term is `mPrem`.
fn illegal_coerce(p_rule: &RuleACInst, fa_conc: &crate::fact::LNFact) -> bool {
    use crate::rule::is_coerce_rule_inst;
    if !is_coerce_rule_inst(p_rule) { return false; }
    if fa_conc.terms.len() != 1 { return false; }
    let t = &fa_conc.terms[0];
    tamarin_term::term::is_pair(t)
        || tamarin_term::term::is_inverse(t)
        || tamarin_term::term::is_product(t)
}

/// SplitG-aware premise-solving rule enumeration: returns the
/// canonical (possibly abstracted) rule per `OpenProtoRule` plus its
/// variant disjunction.  Intruder rules carry `None` (no variants).
/// For non-K premises this favours protocol rules with non-K
/// conclusions and honours the `UniqueSource` source-cache
/// short-circuit (Haskell's `solveWithSource`); for K-premises it
/// includes the intruder rules.
fn premise_solving_rule_insts_with_constrs(
    ctx: &crate::constraint::solver::context::ProofContext,
    _fa_prem: &crate::fact::LNFact,
) -> Vec<(RuleACInst, Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>)> {
    // HS-faithful: `solvePremise (crProtocol ++ crConstruct)` iterates
    // crProtocol intruder rules (ISend, IRecv, IEquality) regardless of
    // conclusion-tag — the `labelNodeId` trace `exploitPrems rule=Send`/
    // `Recv` fires before the conclusion unification mzero's.
    //
    // HS-faithful: HS iterates ALL `crProtocol ++ crConstruct` rules
    // per `solveGoal kind=Premise ...` (Goals.hs:200-212, see line 211).  With single-
    // threaded HS (`+RTS -N1`) the lazy ListT enumeration is
    // deterministic and forces all branches.  Mirror that ordering
    // and inclusion set here:
    //   crProtocol  = non-destr, non-constr intruder rules (ISend,
    //                  IRecv, IEquality) ++ protocol rules
    //   crConstruct = constructor intruder rules (Coerce, PubConstr,
    //                  FreshConstr, NatConstr, ConstrRule(*))
    // Note: crDestruct (destructor rules) is NOT iterated for Premise
    // goals — those are reserved for `solveChain` (Goals.hs:200-212, see line 212).
    let mut out: Vec<(RuleACInst, Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>)>
        = Vec::new();
    // crProtocol intruder rules first.
    for ir in &ctx.intruder_rules {
        let is_crprotocol_intr = !crate::rule::is_destr_rule_info(&ir.info)
            && !crate::rule::is_constr_rule_info(&ir.info)
            && !crate::rule::is_pub_constr_rule_info(&ir.info)
            && !crate::rule::is_nat_constr_rule_info(&ir.info)
            && !crate::rule::is_fresh_constr_rule_info(&ir.info)
            && !crate::rule::is_coerce_rule_info(&ir.info);
        if is_crprotocol_intr {
            out.push((intr_rule_to_rule_ac_inst(ir.clone()), None));
        }
    }
    // Then all protocol rules.
    out.extend(rule_insts_with_constrs(&ctx.rules, |_| true));
    // Then crConstruct intruder rules (Coerce, PubConstr, FreshConstr,
    // NatConstr, ConstrRule).
    for ir in &ctx.intruder_rules {
        let is_constr = crate::rule::is_constr_rule_info(&ir.info)
            || crate::rule::is_pub_constr_rule_info(&ir.info)
            || crate::rule::is_nat_constr_rule_info(&ir.info)
            || crate::rule::is_fresh_constr_rule_info(&ir.info)
            || crate::rule::is_coerce_rule_info(&ir.info);
        if is_constr {
            out.push((intr_rule_to_rule_ac_inst(ir.clone()), None));
        }
    }
    out
}

/// Find the largest free LVar index used anywhere in the system, so
/// fresh-renaming doesn't collide.
///
/// **Must scan every field of `System` that holds free LVars** — not
/// just `nodes`.  In particular, the lemma's free existentials live in
/// `goals` and `formulas` *before any rule is added*, so a `bounds_max`
/// that ignores them will return `0`, causing `freshen_rule`'s shift
/// of `+1` to land directly on the lemma's variable indices.  Result:
/// the freshly-added rule's vars (e.g. Secrecy_claim's `A:Msg idx 0`
/// shifted to `idx 1`) collide with the lemma's existential `A:Msg
/// idx 1`, identifying them by structural equality and conflating
/// downstream substitutions across what should be distinct variables.
// Specialised, statically-dispatched walkers for the system's concrete
// types (`LVar` / `LNTerm` / `LNFact` / `RuleACInst` / `Goal`): the
// compiler inlines the recursion and folds the per-node "is this idx
// larger?" check into a register op, avoiding the `&mut dyn FnMut(&LVar)`
// vtable dispatch a generic `HasFrees::for_each_free` walk pays on every
// node (~8.5% of CPU on the wireguard `--prove` profile; `bounds_max` is
// hot — called many times per proof-step).
#[inline(always)]
fn bm_term(t: &tamarin_term::lterm::LNTerm, max: &mut u64) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => {
            if v.idx > *max { *max = v.idx; }
        }
        Term::Lit(Lit::Con(_)) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                bm_term(a, max);
            }
        }
    }
}

#[inline(always)]
fn bm_fact(fa: &crate::fact::LNFact, max: &mut u64) {
    // Per-fact cached max-var-idx fast-path: `Fact::fresh`/`fresh_annotated`
    // compute the EXACT max free-var idx of `fa.terms` in the same
    // `for_each_free` walk that builds the bloom (fact.rs `fact_fingerprints`),
    // and the value survives every unchanged pass.  On a cache hit fold that
    // single `u64` — a cached `0` (no frees, or a free var at idx 0) folds to
    // the same no-op the per-term descent performs.  The `u64::MAX` sentinel
    // (the no-`HasFrees` `Fact::new`/`map` constructors) falls back to the walk.
    match fa.max_var_cached() {
        Some(m) => {
            if tamarin_utils::env_gate!("TAM_RS_VERIFY_FACT_MAX") {
                // Opt-in independent oracle for the `Fact::max_var` cache
                // (`TAM_RS_VERIFY_FACT_MAX=1`): recompute the fact's own max
                // via the real per-term walk and panic on any mismatch with
                // the cached value.
                let mut walked = 0u64;
                for t in &fa.terms { bm_term(t, &mut walked); }
                if walked != m {
                    panic!(
                        "TAM_RS_VERIFY_FACT_MAX: cached max_var {} != walked max {} \
                         — stale/wrong per-fact max cache",
                        m, walked,
                    );
                }
            }
            if m > *max { *max = m; }
        }
        None => {
            for t in &fa.terms {
                bm_term(t, max);
            }
        }
    }
}

#[inline(always)]
fn bm_lvar(v: &tamarin_term::lterm::LVar, max: &mut u64) {
    if v.idx > *max { *max = v.idx; }
}

#[inline(always)]
fn bm_rule(r: &crate::rule::RuleACInst, max: &mut u64) {
    for f in &r.premises  { bm_fact(f, max); }
    for f in &r.conclusions { bm_fact(f, max); }
    for f in &r.actions    { bm_fact(f, max); }
    for t in &r.new_vars   { bm_term(t, max); }
}

// Public re-exports so `system.rs`'s incremental cache bumpers can
// reuse the inline walkers.
#[inline(always)]
pub fn bm_term_pub(t: &tamarin_term::lterm::LNTerm, max: &mut u64) {
    bm_term(t, max);
}
#[inline(always)]
pub fn bm_fact_pub(fa: &crate::fact::LNFact, max: &mut u64) {
    bm_fact(fa, max);
}
#[inline(always)]
pub fn bm_rule_pub(r: &crate::rule::RuleACInst, max: &mut u64) {
    bm_rule(r, max);
}

/// Cached entry point for the max free-var idx walk over the system.
///
/// Hot path: many sites (`Reduction::new`, `insert_goal_with_loop_flag`'s
/// auto-decompose, `solve_chain_goal`, `freshen_rule`, etc.) call this
/// dozens of times per proof-step.  `System` maintains an exact-max
/// cache (`max_var_idx_cache`) maintained incrementally on additive
/// mutations and invalidated on substitution / eq-store simp / node
/// removal.  Cache hit = O(1); miss = full walk.
pub fn bounds_max(sys: &System) -> u64 {
    // Fast path — full cache hit returns the exact max unchanged.
    if let Some(v) = sys.max_var_idx_cache.get() {
        if bounds_max_verify_enabled() {
            let actual = bounds_max_uncached(sys);
            if v != actual {
                bounds_max_dump_fields(sys);
                panic!(
                    "bounds_max cache mismatch: cache={}, actual={} (nodes={}, rest={})",
                    v, actual, bounds_max_nodes(sys), bounds_max_rest(sys),
                );
            }
        }
        return v;
    }
    // Full-cache miss.  The node component is the dominant cost and
    // survives the ~82 non-node mutation sites (they clear only the full
    // cache), so consult `node_max_cache` first; the `rest` component is
    // always cheap enough to re-walk fresh.  `max(node, rest)` reproduces
    // the full walk exactly.
    let node_component = if let Some(nc) = sys.node_max_cache.get() {
        if bounds_max_verify_enabled() {
            let actual_nc = bounds_max_nodes(sys);
            if nc != actual_nc {
                panic!(
                    "node_max cache mismatch: cache={}, actual={}",
                    nc, actual_nc,
                );
            }
        }
        nc
    } else {
        let nc = bounds_max_nodes(sys);
        if !bounds_max_disable_enabled() {
            sys.node_max_cache.set(Some(nc));
        }
        nc
    };
    let v = node_component.max(bounds_max_rest(sys));
    if !bounds_max_disable_enabled() {
        sys.max_var_idx_cache.set(Some(v));
    }
    v
}

/// Verify-failure diagnostic: print the per-field max breakdown so a
/// cache mismatch identifies WHICH field the stale cache missed.  Only
/// called from the `TAM_RS_VERIFY_BOUNDS_CACHE` panic paths.
fn bounds_max_dump_fields(sys: &System) {
    let mut m_edges = 0u64;
    for e in &sys.edges {
        bm_lvar(&e.src.0, &mut m_edges);
        bm_lvar(&e.tgt.0, &mut m_edges);
    }
    let mut m_less = 0u64;
    for l in &sys.less_atoms {
        bm_lvar(&l.smaller, &mut m_less);
        bm_lvar(&l.larger, &mut m_less);
    }
    let mut m_last = 0u64;
    if let Some(la) = &sys.last_atom { bm_lvar(la, &mut m_last); }
    let mut m_st = 0u64;
    for c in sys.subterm_store.subterms.iter()
        .chain(sys.subterm_store.solved_subterms.iter())
    {
        bm_term(&c.small, &mut m_st);
        bm_term(&c.big, &mut m_st);
    }
    for (s, t) in &sys.subterm_store.neg_subterms {
        bm_term(s, &mut m_st);
        bm_term(t, &mut m_st);
    }
    let mut m_goals = 0u64;
    for (g, _) in sys.goals.iter() {
        use crate::constraint::constraints::Goal;
        match g {
            Goal::Action(i, fa) => { bm_lvar(i, &mut m_goals); bm_fact(fa, &mut m_goals); }
            Goal::Premise(p, fa) => { bm_lvar(&p.0, &mut m_goals); bm_fact(fa, &mut m_goals); }
            Goal::Chain(c, p) => { bm_lvar(&c.0, &mut m_goals); bm_lvar(&p.0, &mut m_goals); }
            Goal::Subterm((s, t)) => { bm_term(s, &mut m_goals); bm_term(t, &mut m_goals); }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }
    let mut m_formulas = 0u64;
    for f in sys.formulas.iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        let n = crate::guarded::max_var_idx(f);
        if n > m_formulas { m_formulas = n; }
    }
    let mut m_eq = 0u64;
    for v in sys.eq_store.subst.dom() {
        if v.idx > m_eq { m_eq = v.idx; }
    }
    for t in sys.eq_store.subst.range() { bm_term(t, &mut m_eq); }
    let mut m_conj = 0u64;
    for d in &sys.eq_store.conj {
        for s in &d.substs {
            for v in s.dom() {
                if v.idx > m_conj { m_conj = v.idx; }
            }
        }
    }
    eprintln!(
        "[BOUNDS_VERIFY] nodes={} edges={} less={} last={} subterm={} goals={} formulas={} eq_subst={} eq_conj_dom={}",
        bounds_max_nodes(sys), m_edges, m_less, m_last, m_st, m_goals,
        m_formulas, m_eq, m_conj,
    );
}

#[inline]
fn bounds_max_verify_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_VERIFY_BOUNDS_CACHE")
}

/// Opt-in verifier for the verified-identity `subst_system` skip: when
/// set, every would-skip runs the full pass on a clone and panics if
/// it was not a total no-op.
#[inline]
fn verify_subst_skip_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_VERIFY_SUBST_SKIP")
}

/// Opt-in skip-effectiveness counters (`TAM_RS_SUBST_SKIP_STATS=1`).  Gated so
/// there is ZERO hot-path cost (one `OnceLock` bool load) when disabled.
#[inline]
fn subst_skip_stats_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_SUBST_SKIP_STATS")
}
pub(crate) static SUBST_SYSTEM_CALLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static SUBST_SYSTEM_SKIPS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

thread_local! {
    /// Master enable for the cached-bloom fact skip in `subst_system_once`.
    /// Default `true`.  The verify oracle
    /// `verify_subst_skip_is_noop` force-DISABLES it for its re-run so the
    /// full per-term descent runs during verification — otherwise a wrong
    /// bloom skip would reproduce identically in both the live pass and the
    /// verify pass, masking itself.  With it disabled in verification, the
    /// round-4 marker verifier is a TRUE independent oracle for the bloom.
    static FP_SKIP_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

/// RAII guard: force the bloom skip off for the current thread, restoring the
/// previous value on drop.  Used by [`verify_subst_skip_is_noop`].
#[must_use = "dropping this guard immediately ends the scope it protects"]
struct FpSkipDisableGuard(bool);
impl FpSkipDisableGuard {
    fn new() -> Self {
        let prev = FP_SKIP_ENABLED.with(|c| { let p = c.get(); c.set(false); p });
        FpSkipDisableGuard(prev)
    }
}
impl Drop for FpSkipDisableGuard {
    fn drop(&mut self) { FP_SKIP_ENABLED.with(|c| c.set(self.0)); }
}

/// Opt-in verifier for the cached-bloom fact skip (`TAM_RS_VERIFY_FP=1`).
/// Read once per pass; when set, every bloom-miss skip ALSO runs
/// the real per-term descent and panics on any real change — an independent
/// oracle that fires at the skip site regardless of what the bloom said.
#[inline]
fn verify_fp_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_VERIFY_FP")
}

/// Opt-in descent-skip counters for the cached-bloom fact skip
/// (`TAM_RS_FP_STATS=1`).  Zero hot-path cost when unset.
#[inline]
fn fp_stats_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_FP_STATS")
}
/// Total fact descents reached in the two skippable sections (node + goal).
pub(crate) static FP_FACT_DESCENTS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Descents the bloom fast-path skipped (`bloom & dom == 0`).
pub(crate) static FP_FACT_SKIPS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// `subst_system` call counter for the FP-stats print cadence.
pub(crate) static FP_STATS_CALLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Verify oracle for one bloom-miss skip: run the real per-term
/// descent via the pass `SubstView` and panic if any term actually changes —
/// i.e. the fingerprint missed a domain var (unsound bit assignment).  Calls
/// `apply_changed` DIRECTLY (never the bloom), so it is independent of the
/// bloom decision it is checking.
fn verify_fact_unchanged(
    fa: &crate::fact::LNFact,
    view: &tamarin_term::subst::SubstView<'_, tamarin_term::lterm::Name, tamarin_term::lterm::LVar>,
) {
    for t in &fa.terms {
        if let Some(c) = view.apply_changed(t) {
            if c != *t {
                panic!("TAM_RS_VERIFY_FP: bloom-skip dropped a real change \
                        (fact contained a domain var the fingerprint missed) \
                        — unsound bit assignment");
            }
        }
    }
}

#[inline]
fn bounds_max_disable_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DISABLE_BOUNDS_CACHE")
}

/// HS `avoid` (LTerm.hs:656-657): `avoid = maybe 0 (succ . snd) . boundsVarIdx`
/// — the `FreshState` (= NEXT index to draw) avoiding `sys`'s free vars:
/// **0 when the system has NO free variables**, max idx + 1 otherwise.
/// `bounds_max` alone returns 0 for both "no frees" and "frees at idx 0",
/// so an unconditional `bounds_max + 1` seed off-by-ones every allocation
/// at a lemma's root step (closed formula, no nodes ⇒ HS seeds 0) — the
/// uniform +1 witness-index shift visible on web sequent pages (proven on
/// cav13/DH_example: RS lemma existentials tid.3/key.4 vs HS tid.2/key.3
/// at the first substantive applyEqStore call).
pub fn avoid_fresh_state(sys: &System) -> u64 {
    let bm = bounds_max(sys);
    if bm > 0 || system_has_any_free_var(sys) { bm + 1 } else { 0 }
}

/// TRUE iff the system has at least one free variable — the existence
/// companion to `bounds_max`, mirroring HS `boundsVarIdx` returning
/// `Nothing` (LTerm.hs:649-651) over the same traversal domain as
/// `bounds_max_uncached`.  Only consulted when `bounds_max(sys) == 0`
/// (in practice: lemma-root systems), so the walk is cheap.
pub fn system_has_any_free_var(sys: &System) -> bool {
    use tamarin_term::lterm::HasFrees;
    // Nodes / edges / less-atoms / last carry LVar node-ids structurally.
    if !sys.nodes.is_empty() || !sys.edges.is_empty()
        || !sys.less_atoms.is_empty() || sys.last_atom.is_some()
    {
        return true;
    }
    fn term_has_var(t: &tamarin_term::lterm::LNTerm) -> bool {
        let mut seen = false;
        t.for_each_free(&mut |_| { seen = true; });
        seen
    }
    for c in sys.subterm_store.subterms.iter()
        .chain(sys.subterm_store.solved_subterms.iter())
    {
        if term_has_var(&c.small) || term_has_var(&c.big) { return true; }
    }
    for (s, t) in &sys.subterm_store.neg_subterms {
        if term_has_var(s) || term_has_var(t) { return true; }
    }
    for (g, _) in sys.goals.iter() {
        use crate::constraint::constraints::Goal;
        match g {
            // These carry a node-id LVar structurally.
            Goal::Action(..) | Goal::Premise(..) | Goal::Chain(..) => return true,
            Goal::Subterm((s, t)) => {
                if term_has_var(s) || term_has_var(t) { return true; }
            }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }
    for f in sys.formulas.iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        if !crate::guarded::free_vars(f).is_empty() { return true; }
    }
    // eq-store: subst dom vars are frees; conj counts DOMAIN keys only
    // (HS `foldFrees (SubstVFresh) = foldFrees f . M.keys`, matching the
    // `bounds_max_uncached` walk).
    if !sys.eq_store.subst.is_empty() { return true; }
    for d in &sys.eq_store.conj {
        for s in &d.substs {
            if s.dom().next().is_some() { return true; }
        }
    }
    false
}

/// Node-component of the max walk (the `sNodes` map: ids + rule frees).
/// This is the dominant cost of `bounds_max`, cached separately in
/// `System::node_max_cache` so the ~82 non-node mutation sites (which
/// clear only the full cache) don't force a re-walk of the node map.
pub fn bounds_max_nodes(sys: &System) -> u64 {
    let mut max = 0u64;
    for (id, rule) in sys.nodes.iter() {
        bm_lvar(id, &mut max);
        bm_rule(rule, &mut max);
    }
    max
}

/// Full-walk implementation of `bounds_max` — bypass for the cache.
/// Kept as the exact `max(nodes, rest)` full walk so the verify path
/// (`TAM_RS_VERIFY_BOUNDS_CACHE`) and the cache-disabled path stay
/// byte-faithful.
pub fn bounds_max_uncached(sys: &System) -> u64 {
    bounds_max_nodes(sys).max(bounds_max_rest(sys))
}

/// Non-node component of the max walk: edges / less / last / subterm
/// store / goals / formulas / eq-store.  Walked fresh on every
/// `bounds_max` miss (these fields are cheap relative to nodes and are
/// mutated by the majority of call sites, so caching them separately
/// would not pay off).
pub fn bounds_max_rest(sys: &System) -> u64 {
    let mut max = 0u64;
    for e in &sys.edges {
        bm_lvar(&e.src.0, &mut max);
        bm_lvar(&e.tgt.0, &mut max);
    }
    for l in &sys.less_atoms {
        bm_lvar(&l.smaller, &mut max);
        bm_lvar(&l.larger,  &mut max);
    }
    if let Some(la) = &sys.last_atom {
        bm_lvar(la, &mut max);
    }
    // HS-faithful: `HasFrees System` folds field `e` = `_sSubtermStore`
    // (System.hs:1834-1847), and `HasFrees SubtermStore` (SubtermStore.hs:
    // 546-548) folds `negSt <> st <> solvedSt`.  RS's SubtermStore is a
    // 3-field subset (subterms = HS's `st`, solved_subterms = HS's
    // `solvedSt`), so walk both here.  Without this, `avoid sys` (the
    // per-step Maude-counter reset seed, proof_method.rs:265 ≈ HS
    // `runReduction … (avoid sys)`) under-counts when a lemma has live
    // subterm constraints (e.g. `Ex x. x << t`), so RS could mint a
    // witness colliding with a subterm-store var that HS's `avoid`
    // reserves above.
    for c in &sys.subterm_store.subterms {
        bm_term(&c.small, &mut max);
        bm_term(&c.big,   &mut max);
    }
    for c in &sys.subterm_store.solved_subterms {
        bm_term(&c.small, &mut max);
        bm_term(&c.big,   &mut max);
    }
    // HS `HasFrees SubtermStore` folds `negSt` too (and skips
    // `oldNegSubterms` — SubtermStore.hs:546-548).
    for (s, t) in &sys.subterm_store.neg_subterms {
        bm_term(s, &mut max);
        bm_term(t, &mut max);
    }
    for (g, _) in sys.goals.iter() {
        use crate::constraint::constraints::Goal;
        match g {
            Goal::Action(i, fa) => {
                bm_lvar(i, &mut max);
                bm_fact(fa, &mut max);
            }
            Goal::Premise(p, fa) => {
                bm_lvar(&p.0, &mut max);
                bm_fact(fa, &mut max);
            }
            Goal::Chain(c, p) => {
                bm_lvar(&c.0, &mut max);
                bm_lvar(&p.0, &mut max);
            }
            Goal::Subterm((s, t)) => {
                bm_term(s, &mut max);
                bm_term(t, &mut max);
            }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }
    for f in sys.formulas.iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        let n = crate::guarded::max_var_idx(f);
        if n > max { max = n; }
    }
    for v in sys.eq_store.subst.dom() {
        if v.idx > max { max = v.idx; }
    }
    for t in sys.eq_store.subst.range() {
        bm_term(t, &mut max);
    }
    // Walk eq_store.conj (disjunctive substitutions).  HS-faithful:
    // `avoid sys = freshAvoiding (frees sys)`, and `frees` over the variant
    // disj uses `foldFrees (SubstVFresh n LVar) = foldFrees f . M.keys`
    // (SubstVFresh.hs:196-202) — i.e. ONLY the DOMAIN keys, NOT the range
    // (witnesses).  Walking the range here over-counted `avoid sys`, so the
    // per-step Maude-counter reset (proof_method.rs:265 ≈ HS
    // `runReduction … (avoid sys)`) seeded too high, inflating witnesses
    // minted by `someInst`/`applyBound` (e.g. Responder_secrecy: the
    // Setup_Key `~k` nonce came out at ~k.31 vs HS ~k.3, rotating the
    // 3-way split via `Ord LNSubstVFresh`).  Match `rename_precise.rs:
    // 98-109` and count keys only.
    for d in &sys.eq_store.conj {
        for s in &d.substs {
            for v in s.dom() {
                if v.idx > max { max = v.idx; }
                // Range vars NOT counted (HS-faithful: foldFrees over keys).
            }
        }
    }
    max
}

/// Fresh-rename a `RuleACInst` so its free variables don't collide
/// with anything below `avoid_max`.
///
/// **Haskell-faithful counter**: shifts use the MaudeHandle's global
/// `fresh_counter` (mirrors `MonadFresh`).  Without a global counter,
/// two sequential freshen_rule calls with the same `avoid_max` (e.g.
/// during parallel source-case enumeration where the system isn't
/// updated between calls) shift to identical idx ranges — producing
/// the cross-call `~mw:Pub:N` / `~mw:Msg:N` collision class that
/// breaks TESLA::authentic_reachable.  Drawing from the global
/// counter guarantees every freshen produces a globally-unique idx
/// range.
/// Freshen a `(RuleACInst, Option<Vec<LNSubstVFresh>>)` pair, applying
/// the same idx-shift to both the rule's free vars and the substs'
/// domains+ranges. Mirrors Haskell's `someRuleACInst`'s use of
/// `fmap extractInsts . rename` (Rule.hs:933-945): the `rename` runs
/// over the whole rule+constrs pair via `MonadFresh`, so the
/// disjunction's vars stay aligned with the renamed rule.
fn freshen_rule_with_constrs(
    rule: RuleACInst,
    constrs: Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>,
    avoid_max: u64,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> (RuleACInst, Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>) {
    use tamarin_term::lterm::{HasFrees, LVar};
    // Combined bounds across rule + constrs.
    //
    // HS-faithful: `someRuleACInst` calls `rename` on the whole
    // `Rule (ProtoInfo i)` where the variants Disj sits INSIDE info.
    // `rename` uses `boundsVarIdx` (LTerm.hs:642-643), which folds via
    // `HasFrees`. For `SubstVFresh n LVar` (SubstVFresh.hs:196-198),
    // `foldFrees f = foldFrees f . M.keys . svMap` — DOMAIN only.
    // Likewise `mapFrees` (line 199-202) maps the domain and leaves the
    // range untouched.  Walking + shifting the range too
    // produces different idxs on AC-narrowed variants vs HS
    // (e.g. Mult(lkI.X, lkR.Y) sorted differently than HS's
    // Mult(lkI.N, lkR.N)).
    let mut min = u64::MAX;
    let mut max = 0u64;
    let mut any = false;
    let mut acc = |v: &LVar| {
        any = true;
        if v.idx < min { min = v.idx; }
        if v.idx > max { max = v.idx; }
    };
    rule.for_each_free(&mut acc);
    if let Some(cs) = &constrs {
        for s in cs {
            for k in s.dom() {
                acc(k);
                // Range NOT walked (HS-faithful keys-only fold).
            }
        }
    }
    if !any { return (rule, constrs); }
    maude.ensure_above(avoid_max);
    let span = max.saturating_sub(min).saturating_add(1);
    let base = maude.reserve_idxs(span);
    let shift = (base as i128) - (min as i128);
    let shift_idx = |idx: u64| -> u64 { ((idx as i128) + shift) as u64 };
    // HS `someRuleACInst` = `rename` (Rule.hs:940-955, see line 944, LTerm.hs:614-621, see line 619) is Monotone:
    // the uniform index shift preserves AC arg order (`unsafefApp`).
    let new_rule = rule.map_free_monotone(&mut |LVar { name, sort, idx }| LVar {
        name, sort, idx: shift_idx(idx),
    });
    let new_constrs = constrs.map(|cs| {
        cs.into_iter().map(|s| {
            let pairs: Vec<_> = s.to_list().into_iter().map(|(k, v)| {
                let new_k = LVar {
                    name: k.name,
                    sort: k.sort,
                    idx: shift_idx(k.idx),
                };
                // HS-faithful: SubstVFresh.hs:199-202 leaves range terms
                // unchanged — `(,t) <$> mapFrees f v` only maps domain.
                (new_k, v)
            }).collect();
            tamarin_term::subst_vfresh::LNSubstVFresh::from_list(pairs)
        }).collect()
    });
    (new_rule, new_constrs)
}

fn freshen_rule(rule: RuleACInst, avoid_max: u64, maude: &tamarin_term::maude_proc::MaudeHandle) -> RuleACInst {
    // Identical to `freshen_rule_with_constrs` with no constrs: a `None`
    // constraints arg contributes nothing to the bounds fold and yields a
    // `None` `new_constrs`, so the two share the exact same
    // bounds/ensure_above/reserve_idxs/monotone-shift arithmetic.  Keep
    // that one copy in lockstep by delegating here.
    freshen_rule_with_constrs(rule, None, avoid_max, maude).0
}

/// True iff one of the three debug gates that actually READ the
/// `system_vars` / `external_preserve` set is enabled: `TAM_DBG_APPLY_EQ`,
/// `TAM_DBG_FOLD_VARIANT`, or `TAM_RS_DBG_IMPURE_FOLD`.  Everywhere else the
/// set is functionally dead: `EquationStore::simp_singleton_avoiding` reads
/// `external_preserve` ONLY inside those three gates, and the actual fold
/// calls `SubstVFresh::fresh_to_free_avoiding`, which builds its own (empty)
/// preserve and ignores the passed-in set (HS has no "preserve" concept).
/// Gating the whole-System live-var walk on this keeps production `--prove`
/// output byte-identical while reproducing identical debug traces when a
/// flag is on.
fn preserve_dbg_gates_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_APPLY_EQ")
        || tamarin_utils::env_gate!("TAM_DBG_FOLD_VARIANT")
        || crate::tools::equation_store::impure_dbg_enabled()
}

/// Collect the LIVE free system vars — node ids, rule
/// premise/conclusion/action vars, edges, less atoms, last atom, and
/// goals — into an (order-insensitive) `BTreeSet`.  Passed to
/// `simp_with_fresh_avoiding` as `system_vars` so the singleton fold's
/// `fresh_to_free` doesn't rename them.  Shared verbatim by
/// `solve_term_eqs` and `solve_split_goal`; `solve_rule_constraints`
/// keeps a deliberately narrower no-goals variant inline (adding goal
/// vars there would change its `fresh_to_free` renaming), so it is NOT
/// folded in here.
fn collect_live_system_vars(sys: &System)
    -> std::collections::BTreeSet<tamarin_term::lterm::LVar>
{
    use tamarin_term::lterm::HasFrees;
    let mut s = std::collections::BTreeSet::new();
    let mut visit = |v: &tamarin_term::lterm::LVar| { s.insert(v.clone()); };
    for (id, rule) in sys.nodes.iter() {
        id.for_each_free(&mut visit);
        rule.for_each_free(&mut visit);
    }
    for e in &sys.edges {
        e.src.0.for_each_free(&mut visit);
        e.tgt.0.for_each_free(&mut visit);
    }
    for l in &sys.less_atoms {
        l.smaller.for_each_free(&mut visit);
        l.larger.for_each_free(&mut visit);
    }
    if let Some(la) = &sys.last_atom { la.for_each_free(&mut visit); }
    for (g, _) in sys.goals.iter() {
        match g {
            crate::constraint::constraints::Goal::Action(n, fa) => {
                n.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                p.0.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            crate::constraint::constraints::Goal::Chain(c, p) => {
                c.0.for_each_free(&mut visit);
                p.0.for_each_free(&mut visit);
            }
            _ => {}
        }
    }
    s
}

/// Fan a solve outcome into one system per equation-store arm.  `Cases`
/// clones `base` per arm and installs that arm's eq_store (same order,
/// same `Arc` wrapping); every other outcome yields the single `base`.
/// Shared by the `solve_chain` direct/union/extend producers and
/// `solve_premise`.
fn fanout_arm_systems(outcome: SolveOutcome, base: System) -> Vec<System> {
    match outcome {
        SolveOutcome::Cases(arms) => {
            arms.into_iter().map(|arm_eq| {
                let mut s = base.clone();
                // The arm store carries fresh Maude witnesses (and lost
                // `base`'s taken-out store), so `base`'s copied max-var
                // cache is stale in BOTH directions — invalidate.
                s.invalidate_max_var_idx_cache();
                s.set_eq_store(std::sync::Arc::new(arm_eq));
                s
            }).collect()
        }
        _ => vec![base],
    }
}

/// simp one `EquationStore` with `simp_with_fresh_avoiding`, using the
/// shared `system_vars` fresh-avoid set and the same `reserve_idxs`
/// counter draw.  `Some(checker)` wires the `substCreatesNonNormalTerms`
/// predicate; `None` disables it (`|_,_| false`), mirroring the
/// `has_reducible` gate at the call sites.  Shared by `solve_term_eqs`'s
/// `do_simp` and `solve_split_goal`'s `simplify_picked`.
fn simp_store(
    store: crate::tools::equation_store::EquationStore,
    checker: Option<&crate::constraint::solver::contradictions::SubstNfChecker>,
    maude: &tamarin_term::maude_proc::MaudeHandle,
    vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> crate::tools::equation_store::EquationStore {
    match checker {
        Some(checker) => store.simp_with_fresh_avoiding(
            |fs, vfs| checker.check(fs, vfs),
            |n| maude.reserve_idxs(n),
            vars,
            Some(maude),
        ),
        None => store.simp_with_fresh_avoiding(
            |_, _| false,
            |n| maude.reserve_idxs(n),
            vars,
            Some(maude),
        ),
    }
}

// =============================================================================
// splitSubterm (HS Theory.Tools.SubtermStore.splitSubterm) — singleStep
// variant used by `solveSubterm`.
// =============================================================================

/// One leaf of `splitSubterm` — direct port of HS `SubtermSplit`
/// (SubtermStore.hs:250-255).  The disjunction-over-list ordering in
/// `solveSubterm` (`SubtermSplit{i}` case names) depends on the
/// constructor order being preserved, so the variants and their
/// `Ord` (derived) must follow HS exactly:
/// `SubtermD < NatSubtermD < EqualD < ACNewVarD < TrueD`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum SubtermSplit {
    SubtermD(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm),
    NatSubtermD(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm),
    EqualD(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm),
    /// `((small+newVar, big), newVar)` — HS `ACNewVarD`.
    AcNewVarD(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm,
              tamarin_term::lterm::LVar),
    TrueD,
}

/// `processACSubterm f (small, big)` — HS SubtermStore.hs:313-328.
/// Returns `Err(false)` / `Err(true)` for the trivially-false /
/// trivially-true reductions, or `Ok((nSmall, nBig))` for the
/// terms with common AC children removed (both re-wrapped under `f`).
pub(crate) fn process_ac_subterm(
    f: tamarin_term::function_symbols::AcSym,
    small: &tamarin_term::lterm::LNTerm,
    big: &tamarin_term::lterm::LNTerm,
) -> Result<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm), bool> {
    use tamarin_term::lterm::flattened_ac_terms;
    use tamarin_term::term::f_app_ac;
    let mut l_small: Vec<tamarin_term::lterm::LNTerm> =
        flattened_ac_terms(f, small).into_iter().cloned().collect();
    let mut l_big: Vec<tamarin_term::lterm::LNTerm> =
        flattened_ac_terms(f, big).into_iter().cloned().collect();
    l_small.sort();
    l_big.sort();
    // removeSame over the two sorted lists.
    let mut s_rem: Vec<tamarin_term::lterm::LNTerm> = Vec::new();
    let mut b_rem: Vec<tamarin_term::lterm::LNTerm> = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;
    while i < l_small.len() && j < l_big.len() {
        match l_small[i].cmp(&l_big[j]) {
            std::cmp::Ordering::Equal => { i += 1; j += 1; }
            std::cmp::Ordering::Less => { s_rem.push(l_small[i].clone()); i += 1; }
            std::cmp::Ordering::Greater => { b_rem.push(l_big[j].clone()); j += 1; }
        }
    }
    while i < l_small.len() { s_rem.push(l_small[i].clone()); i += 1; }
    while j < l_big.len() { b_rem.push(l_big[j].clone()); j += 1; }
    // case lists of (_, []) -> Right False; ([], _) -> Right True; ...
    if b_rem.is_empty() { return Err(false); }
    if s_rem.is_empty() { return Err(true); }
    Ok((f_app_ac(f, s_rem), f_app_ac(f, b_rem)))
}

/// `isTrueFalse reducible Nothing (small, big)` — HS SubtermStore.hs:335-355.
/// Returns `Some(true)`/`Some(false)` for trivially true/false subterms,
/// `None` when undecidable.
fn subterm_is_true_false(
    reducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
    small: &tamarin_term::lterm::LNTerm,
    big: &tamarin_term::lterm::LNTerm,
) -> Option<bool> {
    use crate::tools::subterm_store::elem_not_below_reducible;
    use tamarin_term::lterm::{flattened_ac_terms, is_fresh_var, is_msg_var,
        is_pub_var, sort_of_lnterm, LSort};
    use tamarin_term::term::{f_app_ac, Term};
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::{nat_one_sym, AcSym, FunSym};
    // First guarded equation group (lines 335-346).
    let small_nat_or_msg = sort_of_lnterm(small) == LSort::Nat || is_msg_var(small);
    let big_nat = sort_of_lnterm(big) == LSort::Nat;
    // onlyOnes small && l small < l big && big::Nat  (line 336)
    let small_flat_np = flattened_ac_terms(AcSym::NatPlus, small);
    let big_flat_np = flattened_ac_terms(AcSym::NatPlus, big);
    let only_ones = small_flat_np.iter().all(|t|
        matches!(t, Term::App(FunSym::NoEq(s), args)
            if args.is_empty() && *s == nat_one_sym()));
    if only_ones && small_flat_np.len() < big_flat_np.len() && big_nat {
        return Some(true);
    }
    if small_nat_or_msg && big_nat {
        // CR-rule S_nat (delayed): processACSubterm NatPlus
        match process_ac_subterm(AcSym::NatPlus, small, big) {
            Err(res) => return Some(res),
            Ok(_) => return None,
        }
    }
    // big `redElem` small -> False (includes big == small)
    if elem_not_below_reducible(reducible, big, small) { return Some(false); }
    // small `redElem` big -> True
    if elem_not_below_reducible(reducible, small, big) { return Some(true); }
    // nothing can be a strict subterm of a constant (line 347)
    if let Term::Lit(Lit::Con(_)) = big { return Some(false); }
    // CR-rule S_invalid (lines 348-349)
    if let Term::Lit(Lit::Var(_)) = big {
        let invalid = is_pub_var(big) || is_fresh_var(big)
            || (!small_nat_or_msg && big_nat);
        if invalid { return Some(false); }
    }
    // CR-rule S_subterm-ac-recurse (lines 350-354)
    if let Term::App(FunSym::Ac(f), _) = big {
        let f = *f;
        if !reducible.contains(&FunSym::Ac(f)) {
            let big_flat: Vec<tamarin_term::lterm::LNTerm> =
                flattened_ac_terms(f, big).into_iter().cloned().collect();
            let big_norm = f_app_ac(f, big_flat);
            match process_ac_subterm(f, small, &big_norm) {
                Err(res) => return Some(res),
                Ok(_) => return None,
            }
        }
    }
    None
}

/// `step` of HS `splitSubterm` (SubtermStore.hs:279-305).  Allocates a
/// fresh `newVar` for the AC-recurse arm via `mk_fresh` (a closure
/// mirroring `MonadFresh`'s `freshLVar "newVar" (sortOfLNTerm big)`).
/// Returns `None` when `(small, big)` cannot be decomposed further, or
/// `Some(set)` (deduped, HS uses `S.Set` so duplicates collapse but
/// iteration is sorted — we keep insertion order then sort+dedup at the
/// call site to mirror `S.toList`).
fn subterm_step(
    reducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
    small: &tamarin_term::lterm::LNTerm,
    big: &tamarin_term::lterm::LNTerm,
    mk_fresh: &mut dyn FnMut(tamarin_term::lterm::LSort) -> tamarin_term::lterm::LVar,
) -> Option<Vec<SubtermSplit>> {
    use tamarin_term::lterm::{flattened_ac_terms, is_msg_var, sort_of_lnterm, LSort};
    use tamarin_term::term::{f_app_ac, Term};
    use tamarin_term::vterm::{var_term, Lit};
    use tamarin_term::function_symbols::{AcSym, FunSym};
    // isTrueFalse arms (lines 280-281).
    match subterm_is_true_false(reducible, small, big) {
        Some(true) => return Some(vec![SubtermSplit::TrueD]),
        Some(false) => return Some(vec![]),
        None => {}
    }
    // CR-rule S_nat delayed (lines 282-286).
    let small_nat_or_msg = sort_of_lnterm(small) == LSort::Nat || is_msg_var(small);
    if small_nat_or_msg && sort_of_lnterm(big) == LSort::Nat {
        return match process_ac_subterm(AcSym::NatPlus, small, big) {
            Ok((s, t)) => Some(vec![SubtermSplit::NatSubtermD(s, t)]),
            // HS: Right _ -> error "isTrueFalse did not catch this case 1".
            // isTrueFalse already handled the reducible cases above; treat
            // as undecidable rather than panicking to stay total.
            Err(_) => None,
        };
    }
    match big {
        // variable big: do not recurse further (line 287).
        Term::Lit(Lit::Var(_)) => None,
        // AC big, non-reducible head: S_subterm-ac-recurse (lines 289-296).
        Term::App(FunSym::Ac(f), _) if !reducible.contains(&FunSym::Ac(*f)) => {
            let f = *f;
            let big_flat: Vec<tamarin_term::lterm::LNTerm> =
                flattened_ac_terms(f, big).into_iter().cloned().collect();
            let big_norm = f_app_ac(f, big_flat.clone());
            match process_ac_subterm(f, small, &big_norm) {
                // Right _ -> error "isTrueFalse did not catch this case 2".
                Err(_) => None,
                Ok((n_small, n_big)) => {
                    let new_var = mk_fresh(sort_of_lnterm(big));
                    let small_plus = f_app_ac(f,
                        vec![n_small, var_term(new_var.clone())]);
                    let mut out: Vec<SubtermSplit> = Vec::new();
                    out.push(SubtermSplit::AcNewVarD(small_plus, n_big, new_var));
                    // map (curry SubtermD small) (flattenedACTerms f big)
                    for child in &big_flat {
                        out.push(SubtermSplit::SubtermD(small.clone(), child.clone()));
                    }
                    Some(out)
                }
            }
        }
        // NoEq big, non-reducible head: S_subterm-recurse (lines 297-299).
        Term::App(fs @ FunSym::NoEq(_), ts) if !reducible.contains(fs) => {
            let mut out: Vec<SubtermSplit> = Vec::new();
            for ti in ts.iter() {
                // eqOrSubterm small ti (line 307-308).
                out.push(SubtermSplit::SubtermD(small.clone(), ti.clone()));
                out.push(SubtermSplit::EqualD(small.clone(), ti.clone()));
            }
            Some(out)
        }
        // C (commutative but not associative) — reducible (line 300).
        Term::App(FunSym::C(_), _) => None,
        // List (line 302).
        Term::App(FunSym::List, _) => None,
        // reducible function symbol observed (line 304).
        _ => None,
    }
}

/// `splitSubterm reducible True subterm` — singleStep variant
/// (SubtermStore.hs:262-266).  Returns the sorted-deduped leaf list
/// (HS `S.toList`).  `mk_fresh` allocates fresh vars for the AC arm,
/// mirroring `MonadFresh`.
fn split_subterm_single(
    reducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
    small: &tamarin_term::lterm::LNTerm,
    big: &tamarin_term::lterm::LNTerm,
    mk_fresh: &mut dyn FnMut(tamarin_term::lterm::LSort) -> tamarin_term::lterm::LVar,
) -> Vec<SubtermSplit> {
    // singleStep (SubtermStore.hs:264-266):
    //   fromMaybe (S.singleton (SubtermD st)) <$> step st
    let set = match subterm_step(reducible, small, big, mk_fresh) {
        Some(v) => v,
        None => vec![SubtermSplit::SubtermD(small.clone(), big.clone())],
    };
    // Mirror `S.toList`: sort + dedup by the derived Ord.
    let mut out = set;
    out.sort();
    out.dedup();
    out
}

/// Build `closeGuarded Ex [newVar] [EqE l r] gtrue` (HS Goals.hs `closeGuarded`).
/// `newVar` is the single existentially-bound variable; `l`/`r` are the
/// equation sides (`lTermToBTerm`-lifted to the parser AST, becoming
/// free then bound by `close_guarded`).
fn close_guarded_ex_eq(
    new_var: &tamarin_term::lterm::LVar,
    l: &tamarin_term::lterm::LNTerm,
    r: &tamarin_term::lterm::LNTerm,
) -> crate::guarded::Guarded {
    let var_lt: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(new_var.clone()));
    let vs = match crate::elaborate::lnterm_to_term(&var_lt) {
        tamarin_parser::ast::Term::Var(v) => v,
        _ => unreachable!("var_term elaborates to a Var"),
    };
    let l_ast = crate::elaborate::lnterm_to_term(l);
    let r_ast = crate::elaborate::lnterm_to_term(r);
    crate::guarded::close_guarded(
        crate::guarded::Quant::Ex,
        vec![vs],
        vec![tamarin_parser::ast::Atom::Eq(l_ast, r_ast)],
        crate::guarded::gtrue(),
    )
}

// =============================================================================
// Goal solving — concrete cases that don't need typed-rule unification
// =============================================================================

/// Outcome of `solve_*_goal` — mirrors the disjunctive branching of
/// the Haskell `Reduction` monad's case-split.
#[derive(Debug)]
pub enum GoalCases {
    /// One continuation, no case name; `self.sys` was mutated in
    /// place.  Used for trivial collapses (Disj-singleton, mark-as-
    /// solved) where Haskell's printer emits no `case` heading.
    Linear,
    /// One continuation tagged with a case name; `self.sys` was
    /// mutated in place.  Used for rule-instantiation goals whose
    /// candidate enumeration narrowed to exactly one rule — Haskell
    /// still prints `case <RuleName>` + `qed`.
    LinearNamed(String),
    /// Several continuations; each carries a case name plus the
    /// forked `System`. Case names match Haskell's `prettyProof`:
    /// rule-instantiation cases use the rule name; disjunction /
    /// other splits use `case_1`/`case_2`/...
    Cases(Vec<(String, System)>),
    /// Dead branch — the goal is false.
    Contradictory,
}

/// Returns true if the system has two distinct non-AC-unifiable
/// nodes consuming the same Fresh value as their `Fr(~x)` premise.
/// Such a state is logically inconsistent (Fresh is linear, so the
/// same fresh value can have at most one consumer) — but our
/// source-case graft pipeline can produce it via Maude-witness
/// conflation across chain-saturated cases.  Detecting it lets the
/// caller skip the conflated case so the search doesn't close a
/// branch as Cyclic on the spurious shared-fresh ordering and roll
/// up to Verified.
fn has_fresh_consumer_conflation(
    sys: &crate::constraint::system::System,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> bool {
    use crate::fact::FactTag;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let subst = &sys.eq_store.subst;
    // Capture the rule reference alongside each consumer at build time —
    // it is exactly the node's rule we are already iterating, so the
    // inner pair loop need not re-scan `sys.nodes` (O(consumers^2 * nodes)
    // → O(consumers^2)).
    let mut consumers: Vec<(crate::constraint::constraints::NodeId, LVar, &crate::rule::RuleACInst)> =
        Vec::new();
    for (id, rule) in sys.nodes.iter() {
        for prem in &rule.premises {
            if !matches!(prem.tag, FactTag::Fresh) { continue; }
            let t = match prem.terms.first() { Some(t) => t, None => continue };
            let t_norm = tamarin_term::subst::apply_vterm(subst, t.clone());
            if let Term::Lit(Lit::Var(v)) = t_norm {
                if v.sort == LSort::Fresh {
                    consumers.push((id.clone(), v, rule));
                }
            }
        }
    }
    // Look for two consumers with the same fresh-var, non-unifiable rules.
    for i in 0..consumers.len() {
        for j in (i + 1)..consumers.len() {
            if consumers[i].1 != consumers[j].1 { continue; }
            if consumers[i].0 == consumers[j].0 { continue; }
            let (ri, rj) = (consumers[i].2, consumers[j].2);
            match crate::rule::unifiable_rule_ac_insts(maude, ri, rj) {
                Ok(true) => continue,  // could be merged; not a conflation
                Ok(false) => return true,  // distinct rules, same fresh → conflation
                Err(_) => continue,  // be conservative on Maude errors
            }
        }
    }
    false
}

/// True iff the term is an AC product (Mult) or union.
fn is_product_or_union(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    matches!(t, Term::App(FunSym::Ac(AcSym::Mult), _)
              | Term::App(FunSym::Ac(AcSym::Union), _))
}

fn ku_decomp_subterms(t: &tamarin_term::lterm::LNTerm)
    -> Option<Vec<tamarin_term::lterm::LNTerm>>
{
    use tamarin_term::function_symbols::{AcSym, FunSym, INV_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::NoEq(s), args)
            if s.name == b"pair" && args.len() == 2
                => Some(args.to_vec()),
        Term::App(FunSym::NoEq(s), args)
            if s.name == INV_SYM_STRING && args.len() == 1
                => Some(args.to_vec()),
        // For AC operators (Mult, Union) HS reads the decomposition
        // sub-terms via `viewTerm2 -> FMult ms` / `FUnion ms`, where `ms`
        // is the operator's multiset normal form — ALWAYS sorted by the
        // term `Ord` (idx-first), because every AC term is built through
        // `fAppAC` which does `sort (...)` (Term/Term/Raw.hs:121-122).
        // HS's `insertAction` then allocates one fresh `vk` node per
        // sub-term in that SORTED order (`mapM_ requiresKU ms`,
        // Reduction.hs:411-429).  A substituted/Maude-derived AC term can
        // reach this point in RS with its args in Maude's (unsorted)
        // order; reading `args.to_vec()` verbatim would allocate the
        // `vk` nodes in a different order than HS, shifting the surviving
        // KU-node index by the position delta (e.g. Scott key_secrecy's
        // `inv(~ex*x)` case: RS stored `[x, ~ex]` (Maude order) vs HS's
        // sorted `[~ex, x]`, so RS's surviving `KU(~ex)` landed at
        // `#vk.N+1`).  Sort to recover HS's `viewTerm2` multiset order.
        Term::App(FunSym::Ac(AcSym::Mult | AcSym::Union), args) => {
            let mut v = args.to_vec();
            v.sort();
            Some(v)
        }
        _ => None,
    }
}

/// Default case-name fallback when callers don't provide a specific
/// name: `case_1`, `case_2`, ... (1-indexed, matching Haskell's
/// printer).
pub fn default_case_name(i: usize) -> String {
    format!("case_{}", i + 1)
}

/// Haskell-faithful direct-close case name for a chain.  Mirrors
/// Haskell `caseName mPrem` (Goals.hs) where `mPrem` is the
/// chain conc's KD term:
///   * `Lit (Var v)`  → `Var_<sortSuffix>_<idx-or-name>` (see Haskell
///     `showLitName`, LTerm.hs:861-866, see line 864).
///   * `Lit (Con c)`  → `Const_<sortSuffix>_<n>` (Haskell `showLitName`
///     LTerm.hs:862-863).  Currently we don't emit constants on the
///     direct path; the variant covers it defensively.
///   * `FApp o _`     → function symbol name (e.g. `senc`).  Mirrors
///     Haskell `showFunSymName` (Term.hs:261).
///
/// Returns `None` when the fact isn't a KD-tagged fact (the chain
/// must be a destruction chain to be naming-relevant); callers should
/// fall back to `rule_case_name(c_rule)` in that case.
pub fn chain_direct_case_name(fa_conc: &crate::fact::LNFact) -> Option<String> {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use crate::fact::FactTag;
    if !matches!(fa_conc.tag, FactTag::Kd) { return None; }
    let m = fa_conc.terms.first()?;
    Some(match m {
        Term::Lit(Lit::Var(v)) => {
            // Haskell `showLitName (Var (LVar v s i))`:
            //   body | null v   = show i
            //        | i == 0   = v
            //        | otherwise = show i ++ "_" ++ v
            let body = if v.name.is_empty() {
                v.idx.to_string()
            } else if v.idx == 0 {
                v.name.to_string()
            } else {
                format!("{}_{}", v.idx, v.name)
            };
            format!("Var_{}_{}", tamarin_term::lterm::sort_suffix(v.sort), body)
        }
        Term::Lit(Lit::Con(name)) => {
            // Haskell `showLitName` (LTerm.hs:862-863):
            //   Con (Name FreshName n) -> "Const_fresh_" ++ show n
            //   Con (Name PubName   n) -> "Const_pub_"   ++ show n
            // (`show n` = the raw NameId string, LTerm.hs:237-238).
            // showLitName has no Node/Nat arm (Haskell would crash); a
            // direct close on such a constant is not expected for KD
            // facts, so emit a stable shaped fallback for those.
            use tamarin_term::lterm::NameTag;
            match name.tag {
                NameTag::Fresh => format!("Const_fresh_{}", name.id.as_str()),
                NameTag::Pub => format!("Const_pub_{}", name.id.as_str()),
                NameTag::Node => format!("Const_node_{}", name.id.as_str()),
                NameTag::Nat => format!("Const_nat_{}", name.id.as_str()),
            }
        }
        Term::App(sym, _) => {
            use tamarin_term::function_symbols::FunSym;
            match sym {
                FunSym::NoEq(noeq) => String::from_utf8_lossy(noeq.name).into_owned(),
                FunSym::Ac(op) => format!("{:?}", op),
                FunSym::C(op) => format!("{:?}", op),
                FunSym::List => "List".to_string(),
            }
        }
    })
}

/// Emit the per-premise exploitPrem traces that HS would emit for a
/// rule whose Disj-monad branch will mzero (action/conclusion mismatch
/// against the goal fact).  HS `labelNodeId` runs `exploitPrems i ru`
/// BEFORE the action-mismatch check, so each premise of every dead
/// rule still emits a `exploitPrem InFact` or `exploitPrem FreshFact
/// isFresh=...` trace.  We synthesise the matching traces here so the
/// exec-trace counts align between HS and Rust without Rust actually
/// instantiating the dead rule.
fn emit_dead_rule_premise_traces(rule: &crate::rule::RuleACInst) {
    // Entirely a trace-synthesis helper: every body statement is a
    // `trace_exec` (a no-op unless TAM_RS_TRACE_EXEC is set).  Bail out
    // before the per-premise scan / `is_fresh` computation on the common
    // untraced path.
    if !crate::constraint::solver::trace::exec_enabled() { return; }
    use crate::fact::FactTag;
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    for fa in &rule.premises {
        match &fa.tag {
            FactTag::Fresh => {
                // Check if the Fresh arg is already a Fresh-sorted
                // var to determine the isFresh flag, matching HS.
                let is_fresh = match fa.terms.first() {
                    Some(Term::Lit(Lit::Var(v))) => v.sort == LSort::Fresh,
                    Some(Term::Lit(Lit::Con(c))) =>
                        matches!(c.tag, tamarin_term::lterm::NameTag::Fresh),
                    _ => false,
                };
                crate::constraint::solver::trace::trace_exec(
                    &format!("exploitPrem FreshFact isFresh={}",
                        if is_fresh { "True" } else { "False" }));
            }
            FactTag::In => {
                crate::constraint::solver::trace::trace_exec(
                    "exploitPrem InFact");
                // HS-faithful (Reduction.hs:246-248): `exploitPrem
                // InFact` does `ruKnows <- mkISendRuleAC ann m;
                // modM sNodes (M.insert j ruKnows); modM sEdges
                // (S.insert ...); exploitPrems j ruKnows`.  The
                // recursive `exploitPrems` (Reduction.hs:217-270, see line 239) then runs
                // for the ISend supplier rule `Send`
                // — even when the OUTER rule's action mismatches
                // the goal (HS's Disj-monad branch still runs the
                // body before `solveFactEqs` mzero's the branch).
                // The dead-rule path must mirror that trace.  ISend's
                // only premise is KU(x), which goes via `insertAction`
                // and emits no exploitPrem-* trace, so no further
                // recursion needed.
                crate::constraint::solver::trace::trace_exec(
                    "exploitPrems rule=Send");
            }
            _ => { /* HS doesn't trace other premise types */ }
        }
    }
}

/// Derive a Haskell-style case name for a rule-instantiation case.
/// Matches `Theory.Constraint.Solver.Reduction.casName` conventions:
/// protocol rules use their declared name, intruder constructors use
/// `c_<head>`, destructors use `d_<head>`, fresh-construction uses
/// `fresh`, coercion uses `coerce`, IRecv/ISend use their internal
/// names.
pub fn rule_case_name(rule: &crate::rule::RuleACInst) -> String {
    use crate::rule::{IntrRuleACInfo, ProtoRuleName, RuleInfo};
    match &rule.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Fresh => "Fresh".to_string(),
            ProtoRuleName::Stand(s) => s.to_string(),
        },
        RuleInfo::Intr(i) => match i {
            IntrRuleACInfo::ConstrRule(name) => {
                // The constructor's stored name carries a leading
                // underscore (see `intruder_rules.rs`); strip it
                // here so the case label matches Haskell's printer:
                // `c_h` not `c__h`.
                let s = String::from_utf8_lossy(name);
                let trimmed = s.strip_prefix('_').unwrap_or(&s);
                format!("c_{}", trimmed)
            }
            IntrRuleACInfo::DestrRule(name, _, _, _) => {
                let s = String::from_utf8_lossy(name);
                let trimmed = s.strip_prefix('_').unwrap_or(&s);
                format!("d_{}", trimmed)
            }
            IntrRuleACInfo::Coerce => "coerce".to_string(),
            IntrRuleACInfo::IRecv => "irecv".to_string(),
            IntrRuleACInfo::ISend => "isend".to_string(),
            // Built-in constructor rules render without the `c_` prefix —
            // Haskell `prettyIntrRuleACInfo` (Rule.hs:1225-1227, see line 1229) emits "pub",
            // "nat", "fresh", reserving the `c` prefix for named user
            // constructors (ConstrRule name → 'c' : name).
            IntrRuleACInfo::PubConstr => "pub".to_string(),
            IntrRuleACInfo::NatConstr => "nat".to_string(),
            IntrRuleACInfo::FreshConstr => "fresh".to_string(),
            IntrRuleACInfo::IEquality => "iequality".to_string(),
        },
    }
}

/// HS-faithful port of `Theory.Model.Rule.getRuleName`
/// (lib/theory/src/Theory/Model/Rule.hs:767-781).  Distinct from
/// `rule_case_name` (which mirrors HS `showRuleCaseName` ≡
/// `prettyIntrRuleACInfo` — lowercase "isend", "c_fst", ...).
/// HS uses `getRuleName` ONLY at the `[EXEC] exploitPrems rule=X`
/// trace site (Reduction.hs:217-270, see line 244) and a few other internal log
/// points; everywhere else (proof tree case names, dot rendering,
/// HTML output) HS uses `showRuleCaseName`.  We mirror that split.
///
/// Naming:
///   ConstrRule x   → "Constr" ++ prefixIfReserved('c' : x)
///   DestrRule  x _ _ _ → "Destr" ++ prefixIfReserved('d' : x)
///   CoerceRule     → "Coerce"
///   IRecvRule      → "Recv"
///   ISendRule      → "Send"
///   PubConstrRule  → "PubConstr"
///   NatConstrRule  → "NatConstr"
///   FreshConstrRule→ "FreshConstr"
///   IEqualityRule  → "Equality"
///   FreshRule      → "FreshRule"
///   StandRule s    → s   (no prefixIfReserved — that's the pretty path)
///
/// The `x` for Constr/Destr is stored with HS's leading underscore
/// (see `intruder_rules.rs`), so `ConstrRule(b"_fst")` yields
/// `c` + `_fst` = `c_fst` and `prefixIfReserved` leaves it as-is.
pub fn rule_trace_name(rule: &crate::rule::RuleACInst) -> String {
    use crate::rule::{IntrRuleACInfo, ProtoRuleName, RuleInfo};
    match &rule.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Fresh => "FreshRule".to_string(),
            ProtoRuleName::Stand(s) => s.to_string(),
        },
        RuleInfo::Intr(i) => match i {
            IntrRuleACInfo::ConstrRule(name) => {
                let s = String::from_utf8_lossy(name);
                format!("Constr{}", crate::rule::prefix_if_reserved(&format!("c{}", s)))
            }
            IntrRuleACInfo::DestrRule(name, _, _, _) => {
                let s = String::from_utf8_lossy(name);
                format!("Destr{}", crate::rule::prefix_if_reserved(&format!("d{}", s)))
            }
            IntrRuleACInfo::Coerce      => "Coerce".to_string(),
            IntrRuleACInfo::IRecv       => "Recv".to_string(),
            IntrRuleACInfo::ISend       => "Send".to_string(),
            IntrRuleACInfo::PubConstr   => "PubConstr".to_string(),
            IntrRuleACInfo::NatConstr   => "NatConstr".to_string(),
            IntrRuleACInfo::FreshConstr => "FreshConstr".to_string(),
            IntrRuleACInfo::IEquality   => "Equality".to_string(),
        },
    }
}

impl<'ctx> Reduction<'ctx> {
    /// `solveDisjunction` from `Solver.Goals`:
    ///
    /// > In contrast to the paper, we use n-ary disjunctions and also
    /// > split over all of them at once.
    ///
    /// For each `gfm` in the disjunction, fork a system in which the
    /// disj-goal is marked solved and `gfm` is inserted as an open
    /// formula. The empty disjunction is `False` → `Contradictory`.
    /// A singleton disjunction continues linearly (mutating `self.sys`
    /// in place) but still carries the case name `case_1`: Haskell
    /// `solveDisjunction` (Goals.hs) has no singleton special
    /// case — `disjunctionOfList $ zip [1..] $ getDisj disj` returns
    /// `"case_" ++ show i`, so a lone alternative is `case_1`, and
    /// `ppCases` (Proof.hs:1064-1075) only elides the heading for the
    /// EMPTY name, NOT for `case_1`.  Hence `LinearNamed("case_1")`
    /// in the common case.  If the lone disjunct opens to an `Atom::Eq`
    /// that fans into multiple AC unifier arms, HS's `DisjT` monad forks
    /// the continuation per arm (the inner `disjunctionOfList` in
    /// `solveTermEqs`), so we instead return `GoalCases::Cases` with one
    /// `case_1` entry per arm — exactly like the multi-disjunct path.
    pub fn solve_disj_goal(&mut self, disj: &Disj<Guarded>) -> GoalCases {
        let g = Goal::Disj(disj.clone());
        let alts = &disj.0;
        match alts.len() {
            0 => GoalCases::Contradictory,
            1 => {
                self.mark_goal_as_solved(&g);
                // Route through the decomposing inserter so atomic /
                // existential / disjunctive alternatives generate their
                // own sub-goals (Haskell `insertFormula`).  Raw-pushing
                // leaks Disj/Ex bodies past is_finished (see the
                // companion fix in `insert_implied_formulas_pass`).
                self.insert_formula(alts[0].clone());
                // NOTE: if `insert_formula` opened to an `Atom::Eq`
                // that produced AC unifier arms, `pending_eq_arms` is
                // non-empty.  In the singleton-Disj path we cannot
                // emit additional `case_N` entries (the caller treats a
                // single LinearNamed as no-fork); the arms are lost.
                // HS reaches the branch verdict directly here (e.g.
                // `by contradiction /* from formulas */`) rather than
                // forking the lone disjunct, so draining the arms is the
                // corpus-faithful behavior (a fan-out here diverges from
                // HS on csf18-alethea individualVerifiability_sel).
                self.pending_eq_arms.clear();
                // Haskell names a lone disjunct `case_1` (no singleton
                // special-case in `solveDisjunction`), so emit the name.
                GoalCases::LinearNamed("case_1".to_string())
            }
            _ => {
                let mut cases = Vec::with_capacity(alts.len());
                for (i, gfm) in alts.iter().enumerate() {
                    // HS FreshT-threading: each disjunct branch continues
                    // the enclosing thread (see `new_inheriting`).
                    let mut sub = Reduction::new_inheriting(
                        self.ctx, self.sys.clone(), self.maude.fresh_counter_peek());
                    for (existing, status) in sub.sys.goals_mut().iter_mut() {
                        if existing == &g && !status.solved {
                            status.solved = true;
                            break;
                        }
                    }
                    // Disj-formula bookkeeping (delete from sys.formulas,
                    // insert into sys.solved_formulas) is already done by
                    // `dispatch_solve_goal`'s `mark_goal_as_solved(g)` call
                    // BEFORE delegating to us, mirroring Haskell's
                    // `solveGoal goal = markGoalAsSolved "directly" goal ...`
                    // (Goals.hs:201-213).  Each sub-clone inherits the
                    // post-move state.  No additional bookkeeping needed.
                    // Decompose the chosen alternative — see comment in
                    // singleton branch.  Mirrors Haskell `solveDisjunction`
                    // → `insertFormula alt`.
                    sub.insert_formula(gfm.clone());
                    // HS-faithful multi-arm fanout (Reduction.hs):
                    // if the chosen disjunct opened to an `Atom::Eq` whose
                    // `solveTermEqs SplitNow` returned multiple AC unifier
                    // arms, each arm forks the surrounding `Reduction`
                    // continuation.  In HS this is invisible: the `DisjT`
                    // monad replicates the rest of `solveDisjunction` per
                    // arm and `solveGoal` returns one `(case_name, sys)`
                    // entry per arm.  Sibling cases sharing `case_name`
                    // get `_case_N` suffixes via `distinguish`
                    // (ProofMethod.hs:283-340, see line 308) — that's the source of HS's
                    // `case_2_case_1` / `case_2_case_2` pair on multiset
                    // EqE disjuncts.  Drain `pending_eq_arms` and emit
                    // one extra case per arm with the same base label
                    // and the arm's eq_store installed.
                    let pending = std::mem::take(&mut sub.pending_eq_arms);
                    let base_name = default_case_name(i);
                    let post_sys = sub.sys.clone();
                    cases.push((base_name.clone(), sub.sys));
                    for arm_eq in pending {
                        let mut arm_sys = post_sys.clone();
                        arm_sys.invalidate_max_var_idx_cache();
                        arm_sys.set_eq_store(std::sync::Arc::new(arm_eq));
                        cases.push((base_name.clone(), arm_sys));
                    }
                }
                self.changed = ChangeIndicator::Changed;
                GoalCases::Cases(cases)
            }
        }
    }

    /// `exploitPrems` — port of Haskell's `labelNodeId.exploitPrems`.
    ///
    /// For each premise of a freshly-instantiated rule node `i`, expand
    /// according to the fact tag:
    ///
    /// - `Fr(m)` → allocate a fresh node `j`, instantiate the implicit
    ///   Fresh-rule with conclusion `Fr(m)`, add edge `(j,0) → (i,p)`.
    /// - `In(m)` → allocate a fresh `j`, instantiate the implicit
    ///   `ISend` rule (premise `KU(m)`, conclusion `In(m)`, action
    ///   `K(m)`), add edge.
    /// - `KU(_)` (or `K(_)`/`KD(_)` k-fact) → add a KU-action goal at a
    ///   fresh node `j` with `j < i`.
    /// - Otherwise → insert a `Goal::Premise((i, idx), fact)`.
    pub fn exploit_prems(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        rule: &RuleACInst,
    ) {
        if crate::constraint::solver::trace::exec_enabled() {
            crate::constraint::solver::trace::trace_exec(
                &format!("exploitPrems rule={}",
                    crate::constraint::solver::reduction::rule_trace_name(rule)));
        }
        // HS-faithful (Reduction.hs:241-268): `exploitPrem i ru (v, fa)`
        // uses `fa` from `enumPrems ru` directly — no substitution
        // applied at this point.  The substitution is applied later
        // via `substSystem` (or implicit lookup).  This preserves
        // fresh rule vars in vk stored action terms, enabling the
        // binding-based merge mechanism in
        // `enforce_ku_action_uniqueness` to operate on the same
        // structure as HS.
        let prems: Vec<(crate::rule::PremIdx, crate::fact::LNFact)> =
            rule.enumerate_premises().map(|(p, f)| (p, f.clone())).collect();
        // Loop-breaker premises (per Haskell `praciLoopBreakers`) are
        // those whose `PremIdx` was flagged at theory-load time by the
        // dataflow loop-breaker analysis.  Goals at these premises get
        // `looping=true`, so `isNonLoopBreakerProtoFactGoal` excludes
        // them and the smart ranker defers them.
        let breakers: std::collections::BTreeSet<crate::rule::PremIdx> =
            match &rule.info {
                crate::rule::RuleInfo::Proto(info) =>
                    info.loop_breakers.iter().cloned().collect(),
                _ => std::collections::BTreeSet::new(),
            };
        for (idx, fa) in prems {
            self.exploit_one_prem(i, idx, &fa, breakers.contains(&idx));
        }
    }

    fn exploit_one_prem(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        idx: crate::rule::PremIdx,
        fa: &crate::fact::LNFact,
        is_loop_breaker: bool,
    ) {
        use crate::fact::FactTag;
        match &fa.tag {
            FactTag::Fresh => {
                self.add_fresh_supplier_for(i, idx, fa);
            }
            FactTag::In => {
                crate::constraint::solver::trace::trace_exec(
                    "exploitPrem InFact");
                self.add_isend_supplier_for(i, idx, fa);
            }
            FactTag::Ku => {
                self.add_ku_action_before(i, fa);
            }
            // Haskell `exploitPrem`'s `otherwise` branch: store the
            // premise goal for later (`insertGoal (PremiseG (i,v) fa)
            // (v `elem` breakers)`).  Covers Kd/Ded and every other tag.
            _ => {
                self.insert_goal_with_loop_flag(
                    Goal::Premise((i.clone(), idx), fa.clone()),
                    is_loop_breaker);
            }
        }
    }

    /// Add a fresh-rule supplier node for a `Fr(m)` premise. The
    /// Fresh-rule has `[] --[]-> [Fr(m)]`.
    ///
    /// Haskell-faithful port of `exploitPrem` for FreshFact
    /// (`Reduction.hs:250-258`):
    ///
    /// ```haskell
    /// Fact FreshFact _ [m] -> do
    ///     j <- freshLVar "vf" LSortNode
    ///     modM sNodes (M.insert j (mkFreshRuleAC m))
    ///     unless (isFreshVar m) $ do
    ///         -- 'm' must be of sort fresh ==> enforce via unification
    ///         n <- varTerm <$> freshLVar "n" LSortFresh
    ///         void (solveTermEqs SplitNow [Equal m n])
    ///     modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i,v))
    /// ```
    ///
    /// The `unless (isFreshVar m)` branch narrows m's sort to Fresh
    /// via a unification equation `m = ~n` (where ~n is freshly
    /// allocated Fresh-sorted).  Without this, when a user writes
    /// `Fr(x)` (where x is the default Msg sort), the supplier
    /// rule's conclusion would carry x:Msg through the whole proof
    /// — leaving `KU(x:Msg)` goals that get auto-solved (filtered
    /// out by `is_open_in_sys`) because they look like an
    /// unconstrained Msg variable, when in fact x is the fresh
    /// value Step1 generated.  CSF12::Artificial's
    /// Keys_must_be_revealed lemma wrong-falsifies exactly because
    /// of this.
    fn add_fresh_supplier_for(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        idx: crate::rule::PremIdx,
        fa: &crate::fact::LNFact,
    ) {
        let m = match fa.terms.first() { Some(t) => t.clone(), None => return };
        let next = self.next_fresh_node_idx();
        let j = tamarin_term::lterm::LVar::new(
            "vf", tamarin_term::lterm::LSort::Node, next);
        let rule = make_fresh_rule(m.clone());
        if tamarin_utils::env_gate!("TAM_RS_TRACE_VF_CREATE") {
            let path = crate::constraint::solver::trace::case_path_string();
            eprintln!("[VF_CREATE] path={} site=add_fresh_supplier_for vf.{}", path, next);
        }
        self.sys.add_node(j.clone(), rule);
        // HS-faithful (Reduction.hs:217-270, see line 258): `exploitPrem FreshFact` does
        // a raw `modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i,v))` —
        // NO `insertEdges` (so NO solveFactEqs).  Routing through
        // `insert_edge_labeled` here was non-HS-faithful: it unified
        // the supplier's conc fact with the consumer's prem fact,
        // adding bindings to the eq_store that HS doesn't have.  On
        // NSPK3 the extra bindings transitively chained `~ltkA = ~nr`,
        // causing `enforce_fresh_node_uniqueness` (DG4) to merge two
        // distinct Fresh suppliers, which then fired a false-positive
        // `enforce_edge_uniqueness:prem_idx_clash` and dropped the
        // Lowe-attack cases as FormulasFalse.
        // Use `add_edge` (dedup + incremental cache bump) to mirror
        // Haskell's `S.insert` semantics.  `j` is freshly minted so a
        // duplicate is impossible in practice; this matches the
        // `add_isend_supplier_for` path and avoids a full cache recompute.
        self.sys.add_edge(crate::constraint::constraints::Edge {
            src: (j, crate::rule::ConcIdx(0)),
            tgt: (i.clone(), idx),
        });
        // Haskell `unless (isFreshVar m)`: narrow m:Msg → ~n:Fresh
        // via solveTermEqs.  Only fires when m is not already Fresh-
        // sorted (free var or Fresh literal).
        let is_fresh_var_or_lit = {
            use tamarin_term::lterm::{LSort, NameTag};
            use tamarin_term::term::Term;
            use tamarin_term::vterm::Lit;
            match &m {
                Term::Lit(Lit::Var(v)) => v.sort == LSort::Fresh,
                Term::Lit(Lit::Con(n)) => matches!(n.tag, NameTag::Fresh),
                _ => false,
            }
        };
        if crate::constraint::solver::trace::exec_enabled() {
            crate::constraint::solver::trace::trace_exec(
                &format!("exploitPrem FreshFact isFresh={}",
                    if is_fresh_var_or_lit { "True" } else { "False" }));
        }
        if !is_fresh_var_or_lit {
            let next_n = bounds_max(&self.sys).saturating_add(1);
            let n_var = tamarin_term::lterm::LVar::new(
                "n", tamarin_term::lterm::LSort::Fresh, next_n);
            let n_term = tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(n_var.clone()));
            crate::constraint::solver::trace::trace_exec("FrNarrow");
            if tamarin_utils::env_gate!("TAM_RS_TRACE_FR_NARROW") {
                eprintln!("[RS-FR-NARROW] Fr({}_{}:{:?}) narrowed to ~n.{}",
                    match &m {
                        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) => &v.name,
                        _ => "?",
                    },
                    match &m {
                        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) => v.idx,
                        _ => 0,
                    },
                    match &m {
                        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) => v.sort,
                        _ => tamarin_term::lterm::LSort::Msg,
                    },
                    next_n);
            }
            let eq = tamarin_term::rewriting::Equal { lhs: m, rhs: n_term };
            // Haskell `void (solveTermEqs SplitNow [Equal m n])` —
            // `void` ignores ChangeIndicator but the monadic bind
            // propagates Contradictory via mzero on
            // `noContradictoryEqStore`. Silently swallowing this failure
            // breaks the mzero proxy for shapes like `Fr(pub_var)` where
            // the narrowing `pub_var = ~n:Fresh` is sort-incompatible.
            let res = self.solve_term_eqs(SplitStrategy::SplitNow, &[eq]);
            if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                self.mark_contradictory();
            }
            // HS-faithful (Reduction.hs:255-258): `exploitPrem FreshFact`
            // ends with `unless (isFreshVar m) $ void (solveTermEqs ...)`.
            // No `substSystem` call.  The eq-store update propagates at
            // the next simplifySystem's iter-start substSystem (Simplify.hs:56-158, see line 97).
        }
        self.changed = ChangeIndicator::Changed;
    }

    /// Add an ISend-rule supplier node for an `In(m)` premise.
    /// `ISend` has `[KU(m)] --[K(m)]-> [In(m)]`.
    ///
    /// Mirrors Haskell's `labelNodeId.exploitPrem` for `InFact` — it
    /// adds the ISend node, edges it to the consuming premise, then
    /// recursively exploits the ISend's premises.  Since ISend's only
    /// premise is `KU(m)`, the recursive exploit dispatches to
    /// `add_ku_action_before` (Haskell's `requiresKU`), creating a
    /// `KU(m)` action goal at a fresh predecessor.  ISend's action is
    /// `K(m)` (the log fact, FactTag::Ded), not `KU(m)`, so the new
    /// fresh node and the ISend node don't collide via
    /// `enforce_ku_action_uniqueness`.
    fn add_isend_supplier_for(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        idx: crate::rule::PremIdx,
        fa: &crate::fact::LNFact,
    ) {
        let m = match fa.terms.first() { Some(t) => t.clone(), None => return };
        let next = self.next_fresh_node_idx();
        let j = tamarin_term::lterm::LVar::new(
            "vf", tamarin_term::lterm::LSort::Node, next);
        let rule = make_isend_rule(m.clone());
        // Mirrors Haskell `exploitPrems j ruKnows` (Reduction.hs:217-270, see line 248) —
        // after creating the ISend supplier node, HS recursively exploits
        // the supplier rule's premises (which dispatches to add_ku_action
        // for the KU(m) premise).  Rust does the equivalent inline via
        // add_ku_action_before below, so emit the matching trace here.
        if crate::constraint::solver::trace::exec_enabled() {
            crate::constraint::solver::trace::trace_exec(
                &format!("exploitPrems rule={}",
                    crate::constraint::solver::reduction::rule_trace_name(&rule)));
        }
        self.sys.add_node(j.clone(), rule);
        // HS-faithful (Reduction.hs:217-270, see line 247): `exploitPrem InFact` does a
        // RAW `modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))` —
        // NO `insertEdges` call, NO `solveFactEqs` unification, NO
        // `[EXEC] insertEdges n=1` trace.
        self.sys.add_edge(crate::constraint::constraints::Edge {
            src: (j.clone(), crate::rule::ConcIdx(0)),
            tgt: (i.clone(), idx),
        });
        // ISend's KU premise → KU action goal at fresh predecessor —
        // Haskell's `exploitPrems j ruKnows`.  Always record the goal,
        // even during precompute — grafted ISend nodes with un-tracked
        // KU premises let the runtime search mark leaves Solved while the
        // encrypted-message construction is actually un-proven.  The goal
        // is just a goal at precompute time — it doesn't recursively
        // expand within the precompute call.
        let ku = crate::fact::ku_fact(m);
        self.add_ku_action_before(&j, &ku);
        self.changed = ChangeIndicator::Changed;
    }

    /// Add a KU action goal at a fresh node before `i`.
    fn add_ku_action_before(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        fa: &crate::fact::LNFact,
    ) {
        let next = self.next_fresh_node_idx();
        let j = tamarin_term::lterm::LVar::new(
            "vk", tamarin_term::lterm::LSort::Node, next);
        // TAM_RS_TRACE_VK_CREATE: mirror of HS `TAM_HS_TRACE_VK_CREATE`.
        // This path (`add_ku_action_before`, the HS `requiresKU`/`exploitPrem`
        // analog) DOES advance the maude fresh-counter via
        // `next_fresh_node_idx` = `max(counter, bm+1)`.
        if tamarin_utils::env_gate!("TAM_RS_TRACE_VK_CREATE") {
            let path = crate::constraint::solver::trace::case_path_string();
            eprintln!("[RS_VK_CREATE] path={} site=add_ku_action_before vk.{} cnt={} bm={}",
                path, next, self.maude.fresh_counter_peek(), bounds_max(&self.sys));
        }
        self.insert_less(crate::constraint::constraints::LessAtom::new(
            j.clone(), i.clone(),
            crate::constraint::constraints::Reason::Adversary,
        ));
        self.insert_goal(Goal::Action(j, fa.clone()));
    }

    fn next_fresh_node_idx(&self) -> u64 {
        // Mirror Haskell's `freshLVar`: push the global counter past the
        // current system's max idx, then take the next idx.  Using
        // `bounds_max + 1` directly overflows when a Maude witness LVar
        // (idx near u64::MAX from order-sorted unification output) leaks
        // into the system without being re-freshed.  `freshen_rule` and
        // `freshen_witness_range` already use this pattern.
        let bm = bounds_max(&self.sys);
        self.maude.ensure_above(bm);
        self.maude.fresh_idx()
    }

    /// Collapse a computed `cases`/`case_counters` pair into a `GoalCases`
    /// result, shared by the goal solvers whose fork loops end the same
    /// way.  Empty ⇒ `Contradictory`.  Single case ⇒ adopt it in place
    /// (`self.sys` swap + `reset_counter_to` to carry the branch's HS
    /// FreshT counter forward) and return `LinearNamed(single_name)`.
    /// Two or more ⇒ record `last_case_counters` and return `Cases`.
    /// `single_name` is caller-supplied because it reaches stdout and is
    /// the rule name at some sites but the case's own name at others.
    fn finish_goal_cases(
        &mut self,
        cases: Vec<(String, System)>,
        case_counters: Vec<u64>,
        single_name: String,
    ) -> GoalCases {
        if cases.is_empty() { return GoalCases::Contradictory; }
        if cases.len() == 1 {
            self.sys = cases.into_iter().next().unwrap().1;
            self.maude.reset_counter_to(case_counters[0]);
            self.changed = ChangeIndicator::Changed;
            return GoalCases::LinearNamed(single_name);
        }
        self.changed = ChangeIndicator::Changed;
        self.last_case_counters = case_counters;
        GoalCases::Cases(cases)
    }

    /// `solveAction` — port of the Action arm of `solveGoal`.
    ///
    /// Three cases:
    /// 1. **Node `i` already exists** in the graph and `fa` is among
    ///    its actions ⇒ Linear (already satisfied).
    /// 2. **Node `i` already exists** but `fa` is *not* in its actions
    ///    ⇒ fork once per existing action, unifying `fa` against each.
    /// 3. **Node `i` doesn't exist** ⇒ fork once per non-silent rule,
    ///    fresh-instantiating the rule and unifying `fa` against each
    ///    of its actions.
    ///
    /// A `KU(t1 ⊕ t2 ⊕ …)` goal takes a dedicated XOR path ahead of the
    /// generic rule enumeration (mirrors HS `solveAction`, Goals.hs:259-272):
    /// `twoPartitions` of the summands yields one `coerce` case for the
    /// degenerate partition and one `c_xor` case per proper split.
    pub fn solve_action_goal(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        fa: &crate::fact::LNFact,
    ) -> GoalCases {
        // Tag apply_eq_store calls during KU action solving
        // with `ENU.kuActions` for KU facts, matching HS's site
        // naming (ENU = enforceUniqueKuFact).
        let label = if matches!(fa.tag, crate::fact::FactTag::Ku) {
            "ENU.kuActions"
        } else {
            "solveActionGoal"
        };
        let _op_guard = crate::constraint::solver::trace::OpLabelGuard::new(label);
        let g = Goal::Action(i.clone(), fa.clone());
        let existing = self.sys.nodes.iter()
            .find(|(nid, _)| nid == i)
            .map(|(_, ru)| ru.clone());
        if tamarin_utils::env_gate!("TAM_DBG_SAG") {
            eprintln!("[sag] ENTRY i={:?} fa.tag={:?} existing={:?}",
                i, fa.tag,
                existing.as_ref().map(rule_case_name));
        }
        if tamarin_utils::env_gate!("TAM_DBG_SRC_CASE") {
            eprintln!("[src_case] solve_action_goal ENTRY: i={:?} fa.tag={:?} existing={:?}",
                i, fa.tag,
                existing.as_ref().map(crate::constraint::solver::reduction::rule_case_name));
        }
        match existing {
            Some(ru) => {
                // HS-faithful (Goals.hs):
                //
                //   Just ru -> do
                //     unless (fa `elem` get rActs ru) $ do
                //         act <- disjunctionOfList $ get rActs ru
                //         void (solveFactEqs SplitNow [Equal fa act])
                //     return ru
                //
                // HS RETURNS THE RULE every time (the `return ru` is at
                // the bottom, after the `unless`), so the surrounding
                // `solveAction` always emits `showRuleCaseName ru` as
                // its step name.  HS uses `unless` (= `when . not`)
                // purely to SKIP the action-fork unification when
                // `fa` is already among `rActs ru` — the case-name
                // emission is unconditional.
                //
                // Do NOT short-circuit to `GoalCases::Linear` here: the
                // proof-method printer renders that as a bare `solve` with
                // NO `case <rule>` child, whereas HS renders this situation
                // as `case <rule_name>` followed by SOLVED (or the next
                // step).  Emit `LinearNamed(rule_name)` so the proof
                // skeleton matches.
                let rule_name = rule_case_name(&ru);
                if ru.actions.contains(fa) {
                    self.mark_goal_as_solved(&g);
                    return GoalCases::LinearNamed(rule_name);
                }
                // Fork: one case per action of the existing rule
                // instance, unifying that action with `fa`. All cases
                // share the same rule name; proof_method.rs dedup will
                // append `_case_1`/`_case_2`/... if multiple cases.
                //
                let mut cases = Vec::new();
                // HS FreshT-threading: per pushed case, the branch's final
                // fresh counter (see `new_inheriting`).
                let mut case_counters: Vec<u64> = Vec::new();
                for act in &ru.actions {
                    let sys = self.sys.clone();
                    let mut sub = Reduction::new_inheriting(
                        self.ctx, sys, self.maude.fresh_counter_peek());
                    let res = sub.solve_fact_eqs(
                        SplitStrategy::SplitNow,
                        &[tamarin_term::rewriting::Equal {
                            lhs: fa.clone(), rhs: act.clone() }]);
                    // HS-faithful per-arm fan-out (Goals.hs).
                    // When `solveFactEqs SplitNow` produces multiple AC
                    // unifier arms, fan-out one branch per arm; otherwise
                    // use `sub.sys`'s already-installed Linear eq_store.
                    let arm_eq_stores: Vec<crate::tools::equation_store::EquationStore> = match res {
                        Err(_) | Ok(SolveOutcome::Contradictory) => continue,
                        Ok(SolveOutcome::Cases(arms)) => arms,
                        Ok(SolveOutcome::Linear(_)) =>
                            vec![(**sub.sys.eq_store).clone()],
                    };
                    let post_sys = sub.sys.clone();
                    let branch_counter = sub.maude.fresh_counter_peek();
                    for arm_eq in arm_eq_stores {
                        let mut sys = post_sys.clone();
                        sys.invalidate_max_var_idx_cache();
                        sys.set_eq_store(std::sync::Arc::new(arm_eq));
                        for (existing, status) in sys.goals_mut().iter_mut() {
                            if existing == &g && !status.solved {
                                status.solved = true;
                                break;
                            }
                        }
                        cases.push((rule_name.clone(), sys));
                        case_counters.push(branch_counter);
                    }
                }
                // Single-case adoption mutates `self.sys` in place and
                // signals the case-name for the printer (`case <name>` +
                // qed); simplify-pass callers ignore the return and look
                // at `self.sys`.  HS FreshT-threading — see the
                // candidate-loop single-case adoption below (task #16).
                self.finish_goal_cases(cases, case_counters, rule_name)
            }
            None => {
                // Source-case dispatch for KU action goals — mirrors
                // Haskell's `solveWithSource` (ProofMethod.hs:283-340, see line 320)
                // which is called from `solve` BEFORE falling back to
                // plain `solveGoal`.  HS picks a source whose pattern
                // matches the goal, then `applySource` does
                // `markGoalAsSolved >> disjunctionOfList cases >>
                // someInst >> conjoinSystem` — i.e. grafts the case's
                // entire sub-system (nodes/edges/goals) into the live
                // system.
                //
                // Do NOT remove this path in favour of pure labelNodeId
                // rule enumeration: it regresses the corpus with many
                // timeouts.  Source-cases are the equivalent of HS's
                // `solveWithSource`; both code paths need them.
                if tamarin_utils::env_gate!("TAM_DBG_SRC_CASE") {
                    eprintln!("[src_case] solve_action_goal None-branch: precompute={} tag={:?} full_sources.len={}",
                        crate::constraint::solver::sources::in_precompute_mode(),
                        fa.tag, self.ctx.full_sources.len());
                }
                // HS-faithful (Sources.hs:202-206): KU action goals are
                // "useful" — `solveAllSafeGoals` dispatches them via
                // `solveWithSourceAndReturn` at BOTH saturate and
                // runtime.  Skipped only during HS's `initialSource`.
                let src_dispatch_ok = !crate::constraint::solver::sources::in_initial_source_cases()
                    && matches!(fa.tag, crate::fact::FactTag::Ku)
                    && !self.ctx.full_sources.is_empty();
                if tamarin_utils::env_gate!("TAM_DBG_SAG_SOURCE_GATE") {
                    eprintln!("[sag-gate] tag={:?} src_dispatch_ok={} in_initial_source_cases={} ku={} full_sources_empty={}",
                        fa.tag, src_dispatch_ok,
                        crate::constraint::solver::sources::in_initial_source_cases(),
                        matches!(fa.tag, crate::fact::FactTag::Ku),
                        self.ctx.full_sources.is_empty());
                }
                if src_dispatch_ok
                {
                    let avoid_max = bounds_max(&self.sys);
                    if let Some(case_pairs) = crate::constraint::solver::sources::solve_with_source_cases_action_with_ctx(
                        &self.ctx.full_sources,
                        &self.sys,
                        i, fa,
                        avoid_max,
                        Some(self.ctx),
                        Some(&self.maude),
                    ) {
                        // HS-faithful `solveWithSource` returned `Just []`:
                        // the source pattern MATCHED the live goal but has
                        // ZERO precomputed cases (e.g. a builtin destructor
                        // `KU(check_rep(..))` / `KU(get_rep(..))` whose only
                        // source — the `coerce`→`KD`→chain — was contradicted
                        // during saturation).  HS's `maybe (solveGoal) ... ws`
                        // takes the `Just` branch → the reduction yields 0
                        // branches → the node closes (`by`).  RS must mirror
                        // by returning `Contradictory` here, NOT falling
                        // through to runtime rule enumeration (which re-opens
                        // the `coerce` case HS prunes).  `Some([])` is emitted
                        // ONLY when the matched source has no cases at all (see
                        // `solve_with_source_cases_action_with_ctx`); a matched
                        // source with cases that all fail the live graft still
                        // returns `None` and falls through as before.
                        if case_pairs.is_empty() {
                            return GoalCases::Contradictory;
                        }
                        let live_goal = Goal::Action(i.clone(), fa.clone());
                        let mut out: Vec<(String, crate::constraint::system::System)> = Vec::new();
                        // HS FreshT-threading (task #16): per-out-case branch counters.
                        let mut out_counters: Vec<u64> = Vec::new();
                        // Runtime filterCases (mirroring Haskell's
                        // `filterCases` in
                        // `Theory.Constraint.Solver.Sources`, which skips
                        // already-used chain-saturated source cases) is
                        // disabled here.  The right fix is
                        // N5_u-driven KU action-node unification on
                        // identical terms, which surfaces a
                        // cyclic-ordering contradiction.
                        for (case_label, mut sys, case_action, branch_counter) in case_pairs.into_iter() {
                            if let Some(slot) = sys.goals_mut().iter_mut()
                                .find(|(g, _)| g == &live_goal) {
                                slot.1.solved = true;
                            }
                            // Use the saturated case's name (the
                            // chain-root rule label from
                            // `saturate_out_premise`).  Fall back to
                            // the rule at the live goal node only if
                            // the source-case carried no chain info.
                            // `coerce_case_N` (no trailing rule) is an
                            // un-folded intruder-chain artifact from
                            // our chain-fold pipeline.  Haskell's
                            // source-case enumeration doesn't produce
                            // these labels; it shows the producer
                            // rule's name directly.  Fall back to the
                            // live node's rule name when the label is
                            // empty, a default `case_N`, or a bare
                            // chain-fold marker.
                            let is_chain_fold_artifact = case_label.is_empty()
                                || case_label == "case_1"
                                || (case_label.starts_with("coerce_case_")
                                    && !case_label[12..].contains('_'));
                            let case_name = if is_chain_fold_artifact {
                                sys.nodes.iter()
                                    .find(|(nid, _)| nid == i)
                                    .map(|(_, r)| rule_case_name(r))
                                    .unwrap_or_else(|| default_case_name(out.len()))
                            } else {
                                case_label
                            };
                            // HS FreshT-threading: continue THIS branch's
                            // counter thread (the source pick's fork + the
                            // branch's OWN someInst+conjoin draws, recorded
                            // per output entry by
                            // `solve_with_source_cases_action_with_ctx`).
                            // `self.maude.fresh_counter_peek()` here would be
                            // the LAST branch's post-conjoin position — HS's
                            // DisjT fork gives every branch its own thread.
                            let mut sub = Reduction::new_inheriting(
                                self.ctx, sys, branch_counter);
                            let res = sub.solve_fact_eqs(
                                SplitStrategy::SplitNow,
                                &[tamarin_term::rewriting::Equal {
                                    lhs: case_action.clone(), rhs: fa.clone() }]);
                            // Mirror Haskell `refineSubst`'s
                            // `solveSubstEqs >> substSystem` — propagate
                            // the action-unify bindings into the grafted
                            // case's nodes/edges BEFORE computing
                            // chain_eqs.
                            //
                            // The action-unify `solveFactEqs SplitNow`
                            // can fan out into multiple AC unifier arms
                            // (HS forks the `Reduction`/`DisjT`
                            // continuation per arm via `disjunctionOfList
                            // performSplit`, Reduction.hs:712-731).  On
                            // `Cases`, `solve_term_eqs` returns the arms
                            // WITHOUT installing any into `sub.sys`
                            // (it leaves the `mem::take`'d default
                            // eq-store, equation_store.rs:2159) — so we
                            // MUST install an arm per continuation,
                            // otherwise `sub.sys` carries a wiped
                            // eq-store (conj=[], next_split=0) that drops
                            // every live disjunction (the Joux_EphkRev
                            // `splitEqs` cascade collapse).
                            let action_arm_systems: Vec<(crate::constraint::system::System, u64)> =
                                match res {
                                    Err(_) | Ok(SolveOutcome::Contradictory) => continue,
                                    Ok(SolveOutcome::Linear(_)) => {
                                        sub.subst_system();
                                        vec![(sub.sys.clone(), sub.maude.fresh_counter_peek())]
                                    }
                                    Ok(SolveOutcome::Cases(arms)) => {
                                        let template = sub.sys.clone();
                                        let post_solve_counter = sub.maude.fresh_counter_peek();
                                        let mut v = Vec::new();
                                        for arm_eq in arms {
                                            let mut arm_sys = template.clone();
                                            arm_sys.invalidate_max_var_idx_cache();
                                            arm_sys.set_eq_store(std::sync::Arc::new(arm_eq));
                                            let mut arm_red = Reduction::new_inheriting(
                                                self.ctx, arm_sys, post_solve_counter);
                                            arm_red.subst_system();
                                            if arm_red.sys.eq_store.is_false() { continue; }
                                            let c = arm_red.maude.fresh_counter_peek();
                                            v.push((arm_red.sys, c));
                                        }
                                        v
                                    }
                                };
                            // Live node ids (as of this solve_action_goal
                            // entry): chain_eqs below must NOT re-solve
                            // pre-existing live edges (HS conjoinSystem
                            // runs no edge fact-eqs; re-solving live edges
                            // re-narrows live disjunctions HS keeps).
                            let action_live_node_ids: std::collections::BTreeSet<
                                crate::constraint::constraints::NodeId> =
                                self.sys.nodes.iter().map(|(n, _)| n.clone()).collect();
                            'arm: for (arm_sys, arm_counter) in action_arm_systems {
                                    let mut sub = Reduction::new_inheriting(
                                        self.ctx, arm_sys, arm_counter);
                                    // Edge-induced fact unification over
                                    // GRAFTED edges only (skip live-live
                                    // edges — see action_live_node_ids
                                    // note above).
                                    // Build chain_eqs in a block so the
                                    // node-id → rule map (which borrows
                                    // `sub.sys.nodes`) drops before the later
                                    // `&mut sub` uses.  The map makes the
                                    // per-edge src/tgt resolution O(1) instead
                                    // of two linear `nodes.iter().find` scans
                                    // (O(arms*edges*nodes) → O(arms*(nodes+edges))).
                                    let (chain_eqs, tag_mismatch_edge): (Vec<_>, bool) = {
                                        let mut tag_mismatch_edge = false;
                                        let node_rule_map = sub.sys.node_rule_map();
                                        let chain_eqs: Vec<_> = sub.sys.edges
                                            .iter()
                                            .filter_map(|e| {
                                                if action_live_node_ids.contains(&e.src.0)
                                                    && action_live_node_ids.contains(&e.tgt.0) {
                                                    return None;
                                                }
                                                let src_rule = *node_rule_map.get(&e.src.0)?;
                                                let tgt_rule = *node_rule_map.get(&e.tgt.0)?;
                                                let fc = src_rule.conclusions
                                                    .get(e.src.1.0)?.clone();
                                                let fp = tgt_rule.premises
                                                    .get(e.tgt.1.0)?.clone();
                                                if fc.tag != fp.tag
                                                    || fc.terms.len() != fp.terms.len() {
                                                    tag_mismatch_edge = true;
                                                    return None;
                                                }
                                                if fc == fp { return None; }
                                                Some(tamarin_term::rewriting::Equal {
                                                    lhs: fc, rhs: fp,
                                                })
                                            })
                                            .collect();
                                        (chain_eqs, tag_mismatch_edge)
                                    };
                                    if tag_mismatch_edge { continue 'arm; }
                                    if !chain_eqs.is_empty() {
                                        let r2 = sub.solve_fact_eqs(
                                            SplitStrategy::SplitNow, &chain_eqs);
                                        match r2 {
                                            Err(_) | Ok(SolveOutcome::Contradictory) =>
                                                continue 'arm,
                                            Ok(SolveOutcome::Linear(_)) => {}
                                            Ok(SolveOutcome::Cases(arms2)) => {
                                                // chain_eqs fan-out: install
                                                // each arm and recurse the push.
                                                let template2 = sub.sys.clone();
                                                let post_chain_counter =
                                                    sub.maude.fresh_counter_peek();
                                                for arm2 in arms2 {
                                                    let mut s2 = template2.clone();
                                                    s2.invalidate_max_var_idx_cache();
                                                    s2.set_eq_store(std::sync::Arc::new(arm2));
                                                    let mut r3 = Reduction::new_inheriting(
                                                        self.ctx, s2, post_chain_counter);
                                                    r3.subst_system();
                                                    if r3.sys.eq_store.is_false() { continue; }
                                                    r3.sys.used_sources.push(case_name.clone());
                                                    out_counters.push(r3.maude.fresh_counter_peek());
                                                    out.push((case_name.clone(), r3.sys));
                                                }
                                                continue 'arm;
                                            }
                                        }
                                    }
                                    sub.subst_system();
                                    // Haskell-faithful: push every case
                                    // and let the next simplify+contradictions
                                    // pass catch any real impossibilities.
                                    sub.sys.used_sources.push(case_name.clone());
                                    out_counters.push(sub.maude.fresh_counter_peek());
                                    out.push((case_name.clone(), sub.sys));
                            }
                        }
                        if !out.is_empty() {
                            self.changed = ChangeIndicator::Changed;
                            if out.len() == 1 {
                                let (name, sys) = out.into_iter().next().unwrap();
                                self.sys = sys;
                                // HS FreshT-threading — single-case adoption
                                // (see the candidate-loop rationale, task #16).
                                self.maude.reset_counter_to(out_counters[0]);
                                return GoalCases::LinearNamed(name);
                            }
                            self.last_case_counters = out_counters;
                            return GoalCases::Cases(out);
                        }
                        // If source-cases yielded nothing applicable,
                        // fall back to plain rule enumeration below.
                    }
                }
                // HS-faithful XOR special case (Goals.hs:259-272 in
                // `solveAction`).  When the action goal is `KU(x⊕y⊕…)`,
                // HS does NOT use `labelNodeId` (rule enumeration with
                // AC unification on the c_xor constructor rule's bare-var
                // action), because that would lose the structural
                // partition information of the live XOR sum.  Instead,
                // HS enumerates `twoPartitions ts` and creates one case
                // per partition:
                //   - `(_, [])` (degenerate, all terms in one bucket)
                //     → CoerceRule case with `KD(m)` premise + a
                //       PremiseG goal so the proof must derive `KD(m)`.
                //   - `(a', b')` (proper split) → ConstrRule("_xor") case
                //     where `a = fAppAC Xor a'` and `b = fAppAC Xor b'`,
                //     with two new KU action goals via `requiresKU`.
                //
                // Without this special case, RS falls through to the
                // generic rule enumeration, which picks the c_xor rule
                // with abstract `KU(x:Msg) ∧ KU(y:Msg) → KU(x⊕y:Msg)`
                // action and runs AC unification `KU(live_xor) =
                // KU(x⊕y)`.  With `SplitNow`, that returns `Cases(arms)`
                // representing the AC alternatives; the caller treats
                // the `Ok(_)` result as success and pushes `sub.sys`
                // (whose eq_store still has the unsolved disj), but the
                // bare `KU(x:Msg)` / `KU(y:Msg)` premises in the rule
                // were never set up as separate action goals at
                // predecessor nodes.  When the proof method then
                // checks `is_open_in_sys`, the msg-vars `x`, `y` (still
                // free, with no node binding) auto-skip — the case
                // closes SOLVED prematurely.  Manifested as RS picking
                // `c_lh → c_xor → SOLVED` (7 steps) for
                // CH07::recentalive_tag where HS picks the full
                // `tag1 → split → ... → c_xor → ... → reader1` chain
                // (11 steps).  Same root explains CRxor + LAK06
                // divergences.
                if matches!(fa.tag, crate::fact::FactTag::Ku)
                    && fa.terms.len() == 1
                {
                    use tamarin_term::function_symbols::{FunSym, AcSym};
                    use tamarin_term::term::{Term, f_app_ac};
                    if let Some(Term::App(FunSym::Ac(AcSym::Xor), ts)) =
                        fa.terms.first().cloned()
                    {
                        let ts_vec: Vec<tamarin_term::lterm::LNTerm> =
                            ts.iter().cloned().collect();
                        let partitions = tamarin_utils::misc::two_partitions(&ts_vec);
                        let mut cases: Vec<(String, crate::constraint::system::System)>
                            = Vec::new();
                        // HS FreshT-threading (task #16): per-case branch counters.
                        let mut case_counters: Vec<u64> = Vec::new();
                        let m = fa.terms[0].clone();
                        for (a_parts, b_parts) in partitions {
                            // Each case is a fresh fork.
                            let mut sub = Reduction::new_inheriting(
                                self.ctx, self.sys.clone(),
                                self.maude.fresh_counter_peek());
                            if b_parts.is_empty() {
                                // Degenerate partition: CoerceRule.
                                //   ru = Rule (IntrInfo CoerceRule)
                                //              [kdFact m] [fa] [fa] []
                                //   insert(i, ru)
                                //   insertGoal (PremiseG (i, PremIdx 0)
                                //                        (kdFact m)) False
                                let kd_m = crate::fact::kd_fact(m.clone());
                                let coerce_ru = crate::rule::Rule::new(
                                    crate::rule::RuleInfo::Intr(
                                        crate::rule::IntrRuleACInfo::Coerce),
                                    vec![kd_m.clone()],
                                    vec![fa.clone()],
                                    vec![fa.clone()],
                                );
                                sub.sys.add_node(i.clone(), coerce_ru);
                                // PremiseG (i, PremIdx 0) (kdFact m)
                                sub.insert_goal(Goal::Premise(
                                    (i.clone(), crate::rule::PremIdx(0)),
                                    kd_m,
                                ));
                                let case_name = "coerce".to_string();
                                for (existing, status) in sub.sys.goals_mut().iter_mut() {
                                    if existing == &g && !status.solved {
                                        status.solved = true;
                                        break;
                                    }
                                }
                                case_counters.push(sub.maude.fresh_counter_peek());
                                cases.push((case_name, sub.sys));
                            } else {
                                // Proper split: ConstrRule "_xor".
                                //   let a = fAppAC Xor a'
                                //   let b = fAppAC Xor b'
                                //   ru = Rule (IntrInfo (ConstrRule "_xor"))
                                //              [kuFact a, kuFact b] [fa] [fa] []
                                //   insert(i, ru)
                                //   mapM_ requiresKU [a, b]
                                // `f_app_ac` already returns the lone
                                // element when the arg list is a singleton,
                                // so no explicit singleton special-case is
                                // needed (moves the Vecs in).
                                let a_term = f_app_ac(AcSym::Xor, a_parts);
                                let b_term = f_app_ac(AcSym::Xor, b_parts);
                                let ku_a = crate::fact::ku_fact(a_term.clone());
                                let ku_b = crate::fact::ku_fact(b_term.clone());
                                let xor_ru = crate::rule::Rule::new(
                                    crate::rule::RuleInfo::Intr(
                                        crate::rule::IntrRuleACInfo::ConstrRule(
                                            b"_xor".to_vec())),
                                    vec![ku_a.clone(), ku_b.clone()],
                                    vec![fa.clone()],
                                    vec![fa.clone()],
                                );
                                sub.sys.add_node(i.clone(), xor_ru);
                                // requiresKU a, requiresKU b
                                sub.add_ku_action_before(i, &ku_a);
                                sub.add_ku_action_before(i, &ku_b);
                                let case_name = "c_xor".to_string();
                                for (existing, status) in sub.sys.goals_mut().iter_mut() {
                                    if existing == &g && !status.solved {
                                        status.solved = true;
                                        break;
                                    }
                                }
                                case_counters.push(sub.maude.fresh_counter_peek());
                                cases.push((case_name, sub.sys));
                            }
                        }
                        if !cases.is_empty() {
                            self.changed = ChangeIndicator::Changed;
                            if cases.len() == 1 {
                                let (name, sys) = cases.into_iter().next().unwrap();
                                self.sys = sys;
                                // HS FreshT-threading — single-case adoption
                                // (task #16).
                                self.maude.reset_counter_to(case_counters[0]);
                                return GoalCases::LinearNamed(name);
                            }
                            self.last_case_counters = case_counters;
                            return GoalCases::Cases(cases);
                        }
                    }
                }
                // Haskell `someRuleACInst` (Rule.hs:925-934, see line 933): canonical rule
                // per `OpenProtoRule` + variant substs installed as a
                // SplitG goal via `solve_rule_constraints`
                // (Reduction.hs:766-774). One case per rule at the
                // action level; variant choice deferred to SplitG.
                let candidates: Vec<(RuleACInst,
                        Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>)>
                    = non_silent_rule_insts_with_constrs(self.ctx);
                if candidates.is_empty() { return GoalCases::Contradictory; }
                let avoid_max = bounds_max(&self.sys);
                // HS-faithful: `solveAction`'s `labelNodeId i rules Nothing`
                // (Goals.hs:269-290, see line 274 → Reduction.hs:217-270, see line 249) imports the chosen rule via
                // `importRule =<< disjunctionOfList rules`.  The fresh counter
                // threads ABOVE the `DisjT` layer (`FreshT (DisjT ...)`,
                // Reduction.hs:115-115, see line 123), so sibling candidate rules do NOT thread
                // each other's `someRuleACInst` renamings — EVERY candidate
                // renames from the SAME pre-fork fresh state.  RS shares one
                // `self.maude`, so consecutive `freshen_rule_with_constrs` calls
                // climbed the counter cumulatively (c_fst → c_pair → c_snd →
                // …), lifting each grafted node's rule vars — and hence the
                // source-case `#vk`/`#vf` node ids — N indices above HS's (e.g.
                // `!KU(snd(t.1))`'s premise node `#vk.6` vs HS `#vk.3`).  Reset
                // the shared counter to the pre-fork base before each candidate
                // and restore the high-water mark afterward, exactly as
                // `solve_premise_goal` already does around its `#vr` fork.
                self.maude.ensure_above(avoid_max);
                let base_counter = self.maude.fresh_counter_peek();
                let mut counter_high_water = base_counter;
                let mut cases: Vec<(String, crate::constraint::system::System)> = Vec::new();
                // HS FreshT-threading: per pushed case, the branch's fresh
                // counter position at the end of its solve work (see the
                // single-case adoption below).  Parallel to `cases`.
                let mut case_counters: Vec<u64> = Vec::new();
                for (rule, constrs) in candidates {
                    // Mirror Haskell's `labelNodeId` (Goals.hs:218-261, see line 262) which
                    // exploits every candidate rule via Disj-monad,
                    // including ones whose actions can't unify with `fa`
                    // (those branches mzero in `solveFactEqs`).
                    // Filter rules that have at least one action with
                    // matching tag/arity — cheap pre-filter that
                    // mirrors the unifiability check.
                    if !rule.actions.iter().any(|a| a.tag == fa.tag && a.terms.len() == fa.terms.len()) {
                        // For non-matching rules: synthesise the
                        // exploitPrems + per-Fresh/In premise traces
                        // HS emits in the dead Disj branch before
                        // mzero, so trace counts align.  Rust still
                        // skips the actual instantiation work.
                        if crate::constraint::solver::trace::exec_enabled() {
                            crate::constraint::solver::trace::trace_exec(
                                &format!("exploitPrems rule={}",
                                    crate::constraint::solver::reduction::rule_trace_name(&rule)));
                            emit_dead_rule_premise_traces(&rule);
                        }
                        continue;
                    }
                    // Matching rules: rely on the trace emitted from
                    // inside exploit_prems (no duplicate here).  HS
                    // emits exactly one exploitPrems per rule (matching
                    // or not), so we follow the same pattern.
                    for (act_idx, _) in rule.actions.iter().enumerate() {
                        // Fresh-rename the rule once per branch so
                        // each candidate has independent variables.
                        // When the SplitG path is on, freshen both the
                        // rule and any accompanying variant substs
                        // consistently — Haskell `someRuleACInst` runs
                        // `rename` over the whole (rule, constrs) pair
                        // via `fmap extractInsts . rename`.
                        // Independent `Disj` fork (see the base_counter note
                        // above): rewind the shared counter so THIS candidate's
                        // rename reserves its var range from the same base every
                        // sibling sees.
                        self.maude.reset_counter_to(base_counter);
                        let (renamed, renamed_constrs) = freshen_rule_with_constrs(
                            rule.clone(), constrs.clone(), avoid_max, &self.maude);
                        counter_high_water = counter_high_water.max(self.maude.fresh_counter_peek());
                        let act = renamed.actions[act_idx].clone();
                        if act.tag != fa.tag || act.terms.len() != fa.terms.len() {
                            continue;
                        }
                        let case_name = rule_case_name(&renamed);
                        let mut sys = self.sys.clone();
                        sys.add_node(i.clone(), renamed.clone());
                        let mut sub = Reduction::new(self.ctx, sys);
                        // HS-faithful order (Goals.hs:262-265): `labelNodeId
                        // i rules Nothing` returns the chosen `ru` AFTER
                        // running `exploitPrems i ru`; only AFTERWARDS
                        // does `solveAction` call
                        //   `act <- disjunctionOfList (rActs ru)`
                        //   `void (solveFactEqs SplitNow [Equal fa act])`.
                        //
                        // So `exploit_prems` must fire BEFORE
                        // `solve_fact_eqs` — otherwise the `[EXEC]
                        // solveTermEqs n=1` line emitted by
                        // `solveFactEqs`'s underlying `solveTermEqsLabeled`
                        // (Reduction.hs:767-772, see line 769) lands before the matching
                        // rule's `exploitPrems rule=X`/`exploitPrem
                        // InFact`/etc. trace, instead of after.
                        // HS-faithful: solveRuleConstraints fires BEFORE
                        // exploitPrems (Reduction.hs labelNodeId).  If
                        // it mzeros (eq_store contradictory), the
                        // entire branch dies — exploitPrems trace
                        // never fires.
                        if tamarin_utils::env_gate!("TAM_DBG_VS_DUMP") {
                            eprintln!("[vs-dump]   rule_case={} for goal={:?}",
                                rule_case_name(&renamed), fa.terms.first().map(|t| format!("{:?}", t).chars().take(80).collect::<String>()));
                        }
                        if sub.solve_rule_constraints(renamed_constrs) {
                            continue;
                        }
                        sub.exploit_prems(i, &renamed);
                        let res = sub.solve_fact_eqs(
                            SplitStrategy::SplitNow,
                            &[tamarin_term::rewriting::Equal {
                                lhs: fa.clone(), rhs: act.clone() }]);
                        // HS-faithful per-arm fan-out (Goals.hs:241-242):
                        //   act <- disjunctionOfList (rActs ru)
                        //   void (solveFactEqs SplitNow [Equal fa act])
                        // The `disjunctionOfList` and `solveFactEqs SplitNow`
                        // run in `Reduction = StateT (FreshT (DisjT ...))`
                        // — when `solveFactEqs` produces multiple AC unifier
                        // arms, the DisjT layer fans the entire enclosing
                        // `solveAction` call into one branch per arm.  Each
                        // branch's eq_store gets that arm's unifier installed.
                        //
                        // Without this fan-out RS picks the FIRST arm's
                        // eq_store and silently drops the rest, collapsing
                        // HS's N sibling simplify-cases to 1.  This is what
                        // makes TAK1::session_key_establish show only `case
                        // Proto2` after simplify where HS shows `case 17`
                        // (the 17th surviving AC-unifier arm).
                        let arm_eq_stores: Vec<crate::tools::equation_store::EquationStore> = match res {
                            Err(_) | Ok(SolveOutcome::Contradictory) => continue,
                            Ok(SolveOutcome::Cases(arms)) => arms,
                            Ok(SolveOutcome::Linear(_)) =>
                                vec![(**sub.sys.eq_store).clone()],
                        };
                        let post_sys = sub.sys.clone();
                        // Branch counter for HS FreshT-threading (see the
                        // single-case adoption below): the sub-Reduction's
                        // final fresh-counter position after exploit_prems +
                        // solve_fact_eqs (including its eq-store simp fold
                        // draws).  Multi-arm: `sub.solve_term_eqs`'s SplitNow
                        // path already restored sub's counter to the
                        // across-arm high water, so all arms share it.
                        let branch_counter = sub.maude.fresh_counter_peek();
                        for arm_eq in arm_eq_stores {
                            let mut sys = post_sys.clone();
                            sys.invalidate_max_var_idx_cache();
                            sys.set_eq_store(std::sync::Arc::new(arm_eq));
                            for (existing, status) in sys.goals_mut().iter_mut() {
                                if existing == &g && !status.solved {
                                    status.solved = true;
                                    break;
                                }
                            }
                            cases.push((case_name.clone(), sys));
                            case_counters.push(branch_counter);
                        }
                    }
                }
                // Restore the shared counter to the high-water mark reached
                // across all candidate forks so any later allocation on this
                // Reduction can't collide with a reserved rule-var range.
                self.maude.ensure_above(counter_high_water.saturating_sub(1));
                // HS FreshT-threading (Reduction = StateT System (FreshT
                // (DisjT ...)), Reduction.hs:115-115, see line 123): single-case adoption
                // carries the BRANCH's fresh counter — rule import +
                // exploitPrems + solveFactEqs draws — forward via
                // `reset_counter_to`, not the outer counter that only saw
                // the `freshen` reservation, so later draws in the
                // enclosing exec (e.g. insertImpliedFormulas' eq-store simp
                // fold draws) stay aligned with HS.  Case name reaches
                // stdout, hence passed explicitly.
                let name = cases.first().map(|(n, _)| n.clone()).unwrap_or_default();
                self.finish_goal_cases(cases, case_counters, name)
            }
        }
    }

    /// `solvePremise` (non-KD branch only).
    ///
    /// For a goal `Premise(p, faPrem)` where `p = (i, PremIdx j)`, fork
    /// once per (rule, conclusion-index) pair whose conclusion is
    /// shape-compatible with `faPrem`. In each case:
    ///   - allocate a fresh node id
    ///   - fresh-rename the chosen rule
    ///   - add the node and the edge
    ///   - unify the conclusion fact with `faPrem`
    ///
    /// The KD-fact branch (which inserts an `IRecv` learning step and
    /// a chain constraint) is deferred until `insert_chain` lands.
    pub fn solve_premise_goal(
        &mut self,
        p: &crate::constraint::constraints::NodePrem,
        fa_prem: &crate::fact::LNFact,
    ) -> GoalCases {
        // Tag apply_eq_store calls during premise-goal solving
        // with `insertEdges:solvePremise` label, matching HS's site
        // naming.
        let _op_guard = crate::constraint::solver::trace::OpLabelGuard::new(
            "insertEdges:solvePremise");
        // KD premises route through the chain machinery — direct port
        // of Haskell's `solvePremise rules p faPrem | isKDFact faPrem`:
        //   1. Allocate fresh node `iLearn`
        //   2. Insert IRecv rule `[Out(m)] → [KD(m)]` at `iLearn`
        //   3. `insertChain (cLearn, p)` — chain goal connecting IRecv
        //      conc to the live KD premise (resolved by `solveChain`)
        //   4. Mark the live KD premise solved (it's now a chain target)
        //   5. Insert the IRecv's `Out(m)` as a regular Premise goal
        //      (search will pick it up later).
        // Haskell's `solvePremise` recurses immediately on `pLearn`; we
        // defer via `insert_goal` to keep each call bounded — the
        // search driver enumerates the goal in its own `expand` step.
        if matches!(fa_prem.tag, crate::fact::FactTag::Kd) {
            if fa_prem.terms.is_empty() {
                return GoalCases::Contradictory;
            }
            // Haskell `solvePremise rules p faPrem | isKDFact faPrem`:
            //   iLearn <- freshLVar "vl" LSortNode
            //   mLearn <- varTerm <$> freshLVar "t" LSortMsg
            //   let ruLearn = Rule IRecvRule [outFact mLearn] [kdFact mLearn] [] []
            //   modM sNodes (M.insert iLearn ruLearn)
            //   insertChain (iLearn, ConcIdx 0) p
            //   solvePremise rules pLearn (outFact mLearn)
            //
            // The crucial detail is that `mLearn` is a FRESH msg-sorted
            // variable — *not* the concrete term `m` from `faPrem`.  When
            // the recursive `solvePremise` enumerates protocol rules
            // whose Out conclusion is e.g. `Out(<h(...), ~nb>)`, that
            // unifies against `Out(mLearn)` (since mLearn is fresh),
            // substituting `mLearn := <h(...), ~nb>` and giving the
            // case name of the upstream protocol rule (e.g. "responder").
            // The chain `KD(<h(...), ~nb>) → KD(h(t1))` is then closed
            // separately by `solveChain` via destructor extension
            // (d_fst → KD(h) → unifies with KD(h(t1))).
            //
            // refineSource's `combine` ([Sources.hs:135-137]) then
            // strips leading "coerce" from the accumulated case-name
            // list, leaving "responder" as the final source case name.
            //
            // Using `m` directly instead of a fresh `mLearn` would
            // pin the IRecv's Out-premise term to the concrete `m`,
            // which cannot unify with `<h(...), ~nb>` (head mismatch
            // h vs pair) — the chain-up to responder never
            // materialises and the case name stays at `coerce_irecv`.
            // HS `solvePremise` KD branch (Goals.hs:318-321):
            //   iLearn <- freshLVar "vl" LSortNode
            //   mLearn <- varTerm <$> freshLVar "t" LSortMsg
            // Both draw from — and ADVANCE — the shared MonadFresh counter,
            // in that order, so the recursive `solvePremise` (and the chain
            // extension it feeds) numbers its `#vr` / rule variables in
            // step with HS.
            let avoid = bounds_max(&self.sys);
            self.maude.ensure_above(avoid);
            let vl_idx = self.maude.fresh_idx();
            let t_idx = self.maude.fresh_idx();
            let i_learn = tamarin_term::lterm::LVar::new(
                "vl", tamarin_term::lterm::LSort::Node, vl_idx);
            let m_learn_var = tamarin_term::lterm::LVar::new(
                "t", tamarin_term::lterm::LSort::Msg, t_idx);
            let m_learn = tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(m_learn_var));
            let irecv_rule = crate::rule::Rule::new(
                crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv),
                vec![crate::fact::out_fact(m_learn.clone())],
                vec![crate::fact::kd_fact(m_learn.clone())],
                vec![],
            );
            self.sys.add_node(i_learn.clone(), irecv_rule);
            let c_learn: crate::constraint::constraints::NodeConc =
                (i_learn.clone(), crate::rule::ConcIdx(0));
            self.insert_goal(Goal::Chain(c_learn, p.clone()));
            self.mark_goal_as_solved(&Goal::Premise(p.clone(), fa_prem.clone()));
            self.changed = ChangeIndicator::Changed;
            // Recurse on the Out(mLearn) premise — Haskell does this
            // immediately, inline, before any chain solving.  This is
            // also where source-case short-circuiting will fire at
            // runtime (the Out premise routes through the `solveWithSource`
            // path below since Out is not KD).
            let p_learn: crate::constraint::constraints::NodePrem =
                (i_learn, crate::rule::PremIdx(0));
            let prem_learn = crate::fact::out_fact(m_learn);
            // HS-faithful (Goals.hs:295-307): solvePremise KD path ends
            // with `solvePremise rules pLearn premLearn` — NO substSystem
            // after the recursive solve.  HS leaves the eq-store update
            // unpropagated; the next simplify iteration's substSystem
            // (`Simplify.hs:56-158, see line 97`) handles it.
            return self.solve_premise_goal(&p_learn, &prem_learn);
        }
        // Source-case short-circuit.  Mirrors Haskell's `solveWithSource`
        // → `applySource` (Sources.hs:326-351): match the live goal
        // against the source's abstract `cdGoal`, refine the case via
        // `refineSubst`, someInst with keepVarBindings, then
        // `conjoinSystem`.  Implemented in
        // `apply_source_case_premise` (sources.rs).
        //
        // The returned systems are already fact-aligned + edge-coherent
        // (with a defensive `chain_eqs` pass).
        //
        // HS-faithful (Sources.hs:202-206): `solveAllSafeGoals` only
        // calls `solveWithSourceAndReturn` on "useful" goals (KU
        // actions).  Premise goals are "safe goals" — dispatched via
        // `solveGoal` directly (rule enumeration), NOT through
        // `solveWithSource`.  So Rust's saturate-time Premise dispatch
        // should be skipped; runtime dispatch (via ProofMethod.solve)
        // still fires.  Gate on `!in_precompute_mode()`.
        if !crate::constraint::solver::sources::in_precompute_mode()
            && !self.ctx.full_sources.is_empty()
        {
            if let Some(case_pairs) = crate::constraint::solver::sources::solve_with_source_cases_ctx(
                self.ctx,
                &self.ctx.full_sources,
                &self.sys,
                &p.0, p.1, fa_prem,
                Some(&self.maude),
            ) {
                let mut out: Vec<(String, crate::constraint::system::System)> = Vec::new();
                // HS FreshT-threading (task #23, A(ii) premise parity):
                // per-branch continuation counters, parallel to `out`.
                // HS `_applySource` forks the counter per case
                // (`disjunctionOfList cdCases` BELOW FreshT); each
                // adopted case's post-solve simplify must continue at
                // fork + THAT case's own someInst/conjoin draws — not
                // at the shared handle's post-ALL-cases position.
                let mut out_counters: Vec<u64> = Vec::new();
                for (case_name, mut sys, branch_counter) in case_pairs {
                    if has_fresh_consumer_conflation(&sys, &self.maude) {
                        continue;
                    }
                    sys.used_sources.push(case_name.clone());
                    out.push((case_name, sys));
                    out_counters.push(branch_counter);
                }
                if !out.is_empty() {
                    self.changed = ChangeIndicator::Changed;
                    if out.len() == 1 {
                        let (name, sys) = out.into_iter().next().unwrap();
                        self.sys = sys;
                        // Single-case adoption: continue THIS branch's
                        // thread (mirrors the action-path source-case
                        // adoption above).
                        self.maude.reset_counter_to(out_counters[0]);
                        return GoalCases::LinearNamed(name);
                    }
                    self.last_case_counters = out_counters;
                    return GoalCases::Cases(out);
                }
                // Fall through to plain rule enumeration if every case
                // dropped — keeps the search making progress.
            }
        }
        let g = Goal::Premise(p.clone(), fa_prem.clone());
        // Canonical (abstracted) rule + variant disjunction installed
        // as SplitG after labeling — Haskell-faithful `someRuleACInst`
        // path (Rule.hs:925-934, see line 933).
        let candidates: Vec<(RuleACInst,
                Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>)>
            = premise_solving_rule_insts_with_constrs(self.ctx, fa_prem);
        let avoid_max = bounds_max(&self.sys);
        let mut cases: Vec<(String, crate::constraint::system::System)> = Vec::new();
        // HS FreshT-threading: per pushed case, the branch's final fresh
        // counter (see `new_inheriting` and the single-case adoption below).
        let mut case_counters: Vec<u64> = Vec::new();
        // HS `insertFreshNode` (Reduction.hs:238-241): `i <- freshLVar "vr"`
        // is evaluated ONCE, in the shared prefix BEFORE the
        // `disjunctionOfList rules` inside `labelNodeId`.  So EVERY candidate
        // rule — and every conclusion of every rule — is a `Disj` fork that
        // (a) inherits this single `#vr` node id, and (b) forks the fresh
        // counter independently from the post-`freshLVar` state (the fresh
        // state threads ABOVE the Disj layer — `FreshT (DisjT ...)`,
        // Disj/Class.hs:38-45 — so sibling disjuncts do NOT see each other's
        // allocations).  `freshLVar` also ADVANCES the shared counter, which
        // is what pushes each imported rule's variables one index above the
        // `#vr` id itself (`!Ltk( $A.4, ~ltkA.4 ) ▶₀ #i` under `#vr.3`, not
        // `$A.3`).  `#vr` must be minted from the shared maude counter
        // BEFORE the rule rename so every source-case rule variable comes
        // out at the right index vs HS.
        self.maude.ensure_above(avoid_max);
        let vr_idx = self.maude.fresh_idx();
        let post_vr_counter = self.maude.fresh_counter_peek();
        let mut counter_high_water = post_vr_counter;
        for (rule, constrs) in &candidates {
            // Mirror HS `labelNodeId` in solvePremise: HS exploits every
            // candidate rule via Disj-monad, including conclusion
            // tag-mismatched ones (mzero in solveFactEqs).
            // If no conclusion matches, the inner loop emits 0 traces
            // for this dead rule's premises.  HS emits one exploitPrems
            // plus one per Fr/In premise — synthesise both here.
            let any_conc_match = rule.enumerate_conclusions().any(|(_, fc)|
                fc.tag == fa_prem.tag && fc.terms.len() == fa_prem.terms.len());
            if !any_conc_match {
                if crate::constraint::solver::trace::exec_enabled() {
                    crate::constraint::solver::trace::trace_exec(
                        &format!("exploitPrems rule={}",
                            crate::constraint::solver::reduction::rule_trace_name(rule)));
                    emit_dead_rule_premise_traces(rule);
                }
                // Rust-only trace: `insertEdges n=1` is emitted (per
                // enumerated conclusion) before `solveFactEqs` mzero's the
                // branch, mirroring the per-edge `insertEdges`
                // (Reduction.hs:278-281) called from solvePremise/solveChain
                // (Goals.hs).  Haskell emits no such trace.
                for _ in rule.enumerate_conclusions() {
                    crate::constraint::solver::trace::trace_exec(
                        "insertEdges n=1");
                }
                continue;
            }
            // HS-faithful labelNodeId order (Reduction.hs:222-230):
            //   1. solveRuleConstraints (= solve_rule_constraints)
            //   2. modM sNodes (insert rule node)
            //   3. exploitPrems i ru (emits trace, adds vf/vk nodes)
            // THEN insertFreshNodeConc's enumConcs Disj enumerates each
            // conclusion — each conclusion gets its own sub-branch with
            // its own insert_edge_labeled (Reduction.hs:290-387, see line 300) emitting
            // `insertEdges n=1`.  Tag-mismatched conclusions mzero in
            // solveFactEqs but still emit their insertEdges trace.
            // Independent `Disj` fork: reset the shared fresh counter to the
            // post-`freshLVar "vr"` state so THIS rule's `importRule`
            // (= rename, Rule.hs:940-944) reserves its var range from the
            // exact same base every sibling rule sees.  HS forks don't thread
            // the fresh state between disjuncts, so all candidate rules of one
            // premise goal rename starting at `#vr` + 1 and share the `#vr`
            // id.
            self.maude.reset_counter_to(post_vr_counter);
            let (renamed, renamed_constrs) = freshen_rule_with_constrs(
                rule.clone(), constrs.clone(), avoid_max, &self.maude);
            counter_high_water = counter_high_water.max(self.maude.fresh_counter_peek());
            let case_name = rule_case_name(&renamed);
            let new_node = tamarin_term::lterm::LVar::new(
                "vr",
                tamarin_term::lterm::LSort::Node,
                vr_idx,
            );
            // HS-faithful labelNodeId (`Reduction.hs:246-256`).
            // The branch continues the enclosing FreshT thread (post-
            // freshen counter), not a bounds_max re-derivation — see
            // `new_inheriting`.
            let mut label_sys = self.sys.clone();
            label_sys.add_node(new_node.clone(), renamed.clone());
            let mut label_sub = Reduction::new_inheriting(
                self.ctx, label_sys, self.maude.fresh_counter_peek());
            if tamarin_utils::env_gate!("TAM_RS_DBG_SOLVE_RULE_CONSTRAINTS") {
                let n = renamed_constrs.as_ref().map(|c| c.len()).unwrap_or(0);
                eprintln!("[RS_LABEL_NODE_ID] rule={} n_variant_substs={}",
                    rule_case_name(&renamed), n);
            }
            if let Some(constrs) = &renamed_constrs {
                if !constrs.is_empty() {
                    label_sub.solve_rule_constraints(Some(constrs.clone()));
                }
            }
            label_sub.exploit_prems(&new_node, &renamed);
            // Branch counter after labelNodeId (rule constraints +
            // exploitPrems) — the enumConcs Disj forks below each continue
            // from this state (HS: shared prefix of the Disj forks).
            let label_counter = label_sub.maude.fresh_counter_peek();
            let label_sys = label_sub.sys;
            // enumConcs Disj sub-branches — emit insertEdges per conc.
            for (c_idx, fa_conc) in renamed.enumerate_conclusions() {
                let conc_matches = fa_conc.tag == fa_prem.tag
                    && fa_conc.terms.len() == fa_prem.terms.len();
                if !conc_matches {
                    // Dead-conclusion sub-branch: HS still runs the
                    // per-edge `insertEdges` (Reduction.hs:278-281), whose
                    // `solveFactEqs` mzero's the branch.  Emit the Rust-only
                    // trace here to keep the per-edge count aligned.
                    crate::constraint::solver::trace::trace_exec(
                        "insertEdges n=1");
                    continue;
                }
                let mut sub = Reduction::new_inheriting(
                    self.ctx, label_sys.clone(), label_counter);
                let res = sub.insert_edge_labeled_with_facts(
                    "premise_goal_rule_enum",
                    crate::constraint::constraints::Edge {
                        src: (new_node.clone(), c_idx),
                        tgt: p.clone(),
                    },
                    fa_conc,
                    fa_prem,
                );
                match res {
                    Err(_) | Ok(SolveOutcome::Contradictory) => continue,
                    Ok(outcome) => {
                        // HS-faithful multi-arm fanout: `solvePremise`'s
                        // `insertEdges [(c, faConc, faPrem, p)]`
                        // (Goals.hs:269-290, see line 289) calls `solveFactEqs SplitNow`
                        // whose inner `solveTermEqs` runs
                        //   `disjunctionOfList $ performSplit eqs2 splitId`
                        // when the AC unifier
                        // yields multiple solutions.  Each arm becomes a
                        // separate branch in HS's `Reduction` (Disj/list)
                        // monad → `solvePremise` returns once per arm
                        // with the SAME case name (`showRuleCaseName ru`,
                        // Goals.hs:293-368, see line 313).  Sibling cases sharing a name
                        // get `_case_N` suffixes via `distinguish`
                        // (ProofMethod.hs:283-340, see line 308) — that's the source of
                        // HS's `Inc_case_1` / `Inc_case_2` pair on
                        // multiset Counter premise solving.
                        //
                        // Do NOT unconditionally `cases.push((name, sub.sys))`
                        // — that collapses all AC unifier arms into a single
                        // case.  Mirror `solve_chain_goal`'s post-edge
                        // arm enumeration (Reduction.hs) to keep
                        // the eq_store-from-arm and clone the rest of
                        // sub.sys per arm.
                        let post_edge_sys = sub.sys.clone();
                        // Branch counter after insertEdges (incl. its
                        // eq-store simp draws) — continues into each arm.
                        let post_edge_counter = sub.maude.fresh_counter_peek();
                        let arm_systems = fanout_arm_systems(outcome, post_edge_sys);
                        for mut sys in arm_systems {
                            for (existing, status) in sys.goals_mut().iter_mut() {
                                if existing == &g && !status.solved {
                                    status.solved = true;
                                    break;
                                }
                            }
                            // Subst_system per arm so the variant subst
                            // gets baked into node/edge/goal terms before
                            // saving.  Mirrors `solve_chain_goal`'s
                            // post-arm substitution.
                            let mut sub_per_arm = Reduction::new_inheriting(
                                self.ctx, sys, post_edge_counter);
                            sub_per_arm.subst_system();
                            case_counters.push(sub_per_arm.maude.fresh_counter_peek());
                            cases.push((case_name.clone(), sub_per_arm.sys));
                        }
                    }
                }
            }
        }
        // The per-candidate `reset_counter_to(post_vr_counter)` above rewinds
        // the shared counter for each independent fork; restore it to the
        // high-water mark reached across all forks so any later allocation on
        // this Reduction can't collide with a reserved rule-var range.
        self.maude.ensure_above(counter_high_water.saturating_sub(1));
        // HS FreshT-threading: single-case adoption carries the BRANCH's
        // counter (labelNodeId + insertEdges + per-arm subst draws) forward,
        // not the outer counter that only saw the freshen reservation.  See
        // `solve_action_goal`'s single-case adoption for the full rationale
        // (task #16).  Case name reaches stdout, hence passed explicitly.
        let name = cases.first().map(|(n, _)| n.clone()).unwrap_or_default();
        self.finish_goal_cases(cases, case_counters, name)
    }

    /// `solveChain` — direct port of Haskell's `Goals.solveChain`
    /// (CR-rule *DG2_chain*).
    ///
    /// For a chain goal `(c, p)` we explore two branches and return
    /// their disjunction:
    ///
    /// 1. **Direct edge.** Add an edge `c → p`, unify the conclusion
    ///    fact with the premise fact, and (for the prem-rule already
    ///    in the system) check `forbidden_edge` and `illegal_coerce`.
    /// 2. **Extend by one destructor step.** For each destructor rule
    ///    in `ctx.intruder_rules`, instantiate it as a fresh node `i`,
    ///    add an edge `c → (i, prem 0)` (unifying `fa_conc` with the
    ///    destructor's first KD premise), wire the destructor's other
    ///    premises via `exploit_prems`, mark `(i, prem 0)` solved
    ///    (the chain now feeds it directly), and insert a fresh chain
    ///    `(i, conc 0) → p` for the next step.  Skipped when
    ///    `is_msg_var fa_conc` (open chain — Haskell's
    ///    `contradictoryIf (isMsgVar m)`).
    ///
    /// Each successful case becomes one entry in `GoalCases::Cases`.
    /// The union-message (FUnion) sub-branch (Goals.hs:314-327,
    /// `viewTerm2 -> FUnion args` → `mkDUnionRule`) is handled below via
    /// the `funion_args` block.
    pub fn solve_chain_goal(
        &mut self,
        c: &crate::constraint::constraints::NodeConc,
        p: &crate::constraint::constraints::NodePrem,
    ) -> GoalCases {
        // Set op label so any apply_eq_store calls during chain
        // processing get attributed correctly (mirrors HS's
        // `insertEdges:chain_extend` / `insertEdges:chain_direct` labels).
        let _op_guard = crate::constraint::solver::trace::OpLabelGuard::new(
            "insertEdges:solveChain");
        if tamarin_utils::env_gate!("TAM_RS_TRACE_SOLVE_CHAIN") {
            let mode = if crate::constraint::solver::sources::in_precompute_mode() {
                "saturate" } else { "runtime" };
            eprintln!("[SOLVE_CHAIN] enter mode={} c={:?} p={:?}", mode, c, p);
        }
        let g = Goal::Chain(c.clone(), p.clone());
        let c_rule = match self.sys.nodes.iter().find(|(id, _)| id == &c.0) {
            Some((_, r)) => r.clone(),
            None => return GoalCases::Contradictory,
        };
        let p_rule_opt = self.sys.nodes.iter().find(|(id, _)| id == &p.0)
            .map(|(_, r)| r.clone());
        let fa_conc = match c_rule.lookup_conclusion(c.1) {
            Some(f) => f.clone(),
            None => return GoalCases::Contradictory,
        };

        // TAM_RS_TRACE_CHAINS: mirror Haskell `solveChain` enter trace
        // (Goals.hs `solveChain`).  Format kept identical so a diff between
        // [HS-CHAIN] and [RS-CHAIN] surfaces directly.
        let trace_chains = tamarin_utils::env_gate!("TAM_RS_TRACE_CHAINS");
        if trace_chains {
            let n_destr = self.ctx.intruder_rules.iter()
                .filter(|ir| crate::rule::is_destr_rule_info(&ir.info))
                .count();
            eprintln!("[RS-CHAIN] ENTER faConc={:?} nRules={}",
                fa_conc, n_destr);
        }
        crate::constraint::solver::trace::trace_exec("solveChain ENTER");

        let mut all_cases: Vec<(String, crate::constraint::system::System)> = Vec::new();
        // HS FreshT-threading: per pushed case, the branch's final fresh
        // counter (parallel to `all_cases`; see `new_inheriting` and the
        // single-case adoptions below).
        let mut all_case_counters: Vec<u64> = Vec::new();

        // ---------------- Branch 1: direct edge ----------------
        if let Some(p_rule) = &p_rule_opt {
            let fa_prem_opt = p_rule.lookup_premise(p.1).cloned();
            if let Some(_fa_prem) = fa_prem_opt {
                // Haskell (Goals.hs `illegalCoerce`) tests `illegalCoerce pRule
                // mPrem` where `mPrem = case kFactView faConc of
                // Just (DnK, m') -> m'` — i.e. the CHAIN CONCLUSION's
                // down-K message, NOT the premise fact `faPrem`.  The
                // Coerce rule's premise is the bare var `KD(x)`, so
                // testing `faPrem` would never fire; we must test the
                // chain conc's KD term, which `illegal_coerce` reads from
                // `fa_conc.terms[0]` (== mPrem, since fa_conc is a KD fact).
                if !forbidden_edge(&c_rule, p_rule)
                    && !illegal_coerce(p_rule, &fa_conc)
                {
                    // HS-faithful `insertEdges` (Reduction.hs:278-281):
                    // route through `insert_edge_labeled` so unification fires
                    // BEFORE the edge enters sEdges.  Mirrors HS's
                    // `solveFactEqs SplitNow` + `modM sEdges` order.
                    let sys_clone = self.sys.clone();
                    let mut sub = Reduction::new_inheriting(
                        self.ctx, sys_clone, self.maude.fresh_counter_peek());
                    let res = sub.insert_edge_labeled("chain_direct", crate::constraint::constraints::Edge {
                        src: c.clone(), tgt: p.clone(),
                    });
                    if !matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                        // Direct-edge chain: name by the chain conc's KD
                        // term head — not the producer rule's name
                        // (`rule_case_name`) — mirroring Haskell
                        // `caseName mPrem` (Goals.hs): `showFunSymName`
                        // for App, `showLitName` for Lit.  This matches
                        // Haskell's proof-skeleton naming
                        // (`senc`/`Var_fresh_7_ltkA` etc.).
                        let case_name = chain_direct_case_name(&fa_conc)
                            .unwrap_or_else(|| rule_case_name(&c_rule));
                        // HS-faithful per-arm fanout — mirrors the
                        // `disjunctionOfList arms` in `solveTermEqs`
                        // routed through `solveChain`'s direct-edge
                        // `insertEdges [(c, faConc, faPrem, p)]`
                        // (Goals.hs:293-368, see line 303).  Each arm becomes one
                        // independent solveChain DIRECT case.
                        let post_edge_sys = sub.sys.clone();
                        let post_edge_counter = sub.maude.fresh_counter_peek();
                        let arm_systems = match res {
                            Ok(outcome) => fanout_arm_systems(outcome, post_edge_sys),
                            _ => vec![post_edge_sys],
                        };
                        for mut arm_sys in arm_systems {
                            for (existing, status) in arm_sys.goals_mut().iter_mut() {
                                if existing == &g && !status.solved {
                                    status.solved = true;
                                    break;
                                }
                            }
                            if trace_chains {
                                eprintln!("[RS-CHAIN] DIRECT {}", case_name);
                            }
                            if crate::constraint::solver::trace::exec_enabled() {
                                crate::constraint::solver::trace::trace_exec(
                                    &format!("solveChain DIRECT {}", case_name));
                            }
                            all_cases.push((case_name.clone(), arm_sys));
                            all_case_counters.push(post_edge_counter);
                        }
                    }
                }
            }
        }

        // ---------------- Branch 2: extend by destructor ----------------
        // Skip ONLY when the chain's term is a message variable
        // (Haskell `contradictoryIf (isMsgVar m)`, Goals.hs).
        //
        // We also fire during precompute: the chain-extend branch is
        // needed here so saturate explores destructor alternatives like
        // `R_1d_0_adecd_0_sndd_0_fstRegister_pkRegister_pk`.
        // Without these alternatives, HS produces 6 cases for KU(aenc)
        // but Rust produces 4 — and the trace work-count gap stays
        // 10-30× off.  HS Goals.hs:316-380 runs both branches via
        // `disjunction` unconditionally.
        let conc_term_is_msg_var = fa_conc.terms.first()
            .map(tamarin_term::lterm::is_msg_var)
            .unwrap_or(false);
        // HS-faithful FUnion special branch (Goals.hs:314-318).  When the
        // chain conc's KD term is a literal multiset `Union(t1,...,tn)`,
        // HS bypasses the generic destructor pool and builds bespoke
        // per-arg destructors `mkDUnionRule args arg_i` for each arg.
        // Each bespoke rule has premise `KD(Union(t1..tn))` (identical
        // to faConc by construction — no AC unification, no fanout) and
        // conclusion `KD(arg_i)`.  This produces one case per arg with
        // no AC-induced sibling cases.
        //
        // Without this branch, RS routes `KD(Union(...))` through the
        // generic multiset destructor `mkDUnionRule [x_var,y_var] x_var`
        // in `multiset_intruder_rules` — AC unification of `KD(x++y)`
        // against `KD(~x++y)` produces 2 matchings (x↦~x,y↦y) and
        // (x↦y,y↦~x), giving two `_case_1`/`_case_2` siblings that HS
        // produces as a single case.  Manifests in
        // `issue519.spthy::secret_freshVar` / `::secret_msgVar`.
        let funion_args: Option<Vec<tamarin_term::lterm::LNTerm>> = match fa_conc.terms.first() {
            Some(tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::Ac(
                    tamarin_term::function_symbols::AcSym::Union),
                args)) if args.len() >= 2 => Some(args.to_vec()),
            _ => None,
        };
        if let Some(args) = funion_args {
            use tamarin_term::function_symbols::UNION_SYM_STRING;
            let avoid_max = bounds_max(&self.sys);
            // HS `solveChain` union arm (Goals.hs:293-368, see line 374): `i <- freshLVar "vr"`
            // is allocated ONCE, before `disjunctionOfList rus`, so every
            // union-decomposition case shares the same `#vr` id (and it
            // advances the shared counter).
            self.maude.ensure_above(avoid_max);
            let vr_idx = self.maude.fresh_idx();
            let xy_union = tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::Ac(
                    tamarin_term::function_symbols::AcSym::Union),
                args.clone().into(),
            );
            let mut union_name = b"_".to_vec();
            union_name.extend_from_slice(UNION_SYM_STRING);
            for arg_i in &args {
                // Build HS `mkDUnionRule args arg_i`:
                //   Rule (DestrRule "_union" 0 True False)
                //        [kdFact (Union args)] [kdFact arg_i] [] []
                let ir = crate::rule::IntrRuleAC::new(
                    crate::rule::IntrRuleACInfo::DestrRule(
                        union_name.clone(), 0, true, false),
                    vec![crate::fact::kd_fact(xy_union.clone())],
                    vec![crate::fact::kd_fact(arg_i.clone())],
                    vec![],
                );
                let ru_inst = intr_rule_to_rule_ac_inst(ir);
                // HS allocates a fresh LVar via `freshLVar "vr" LSortNode`
                // (Goals.hs:293-368, see line 352) — no labelNodeId/exploitPrems wrapping
                // since the rule has no Fresh/IRecv premises.  The premise
                // is `KD(Union(args))` which exactly equals `faConc` by
                // construction, so `insertEdges chain_extend` does no
                // AC fanout.
                let new_node = tamarin_term::lterm::LVar::new(
                    "vr",
                    tamarin_term::lterm::LSort::Node,
                    vr_idx,
                );
                let mut sys_clone = self.sys.clone();
                sys_clone.add_node(new_node.clone(), ru_inst.clone());
                let mut sub = Reduction::new_inheriting(
                    self.ctx, sys_clone, self.maude.fresh_counter_peek());
                // HS `extendAndMark i ru v faPrem faConc` (Goals.hs `extendAndMark`):
                //   insertEdges [(c, faConc, faPrem, (i, v))]
                //   markGoalAsSolved "directly" (PremiseG (i, v) faPrem)
                //   insertChain (i, ConcIdx 0) p
                let res = sub.insert_edge_labeled(
                    "chain_extend",
                    crate::constraint::constraints::Edge {
                        src: c.clone(),
                        tgt: (new_node.clone(), crate::rule::PremIdx(0)),
                    },
                );
                if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                    continue;
                }
                let case_name = rule_case_name(&ru_inst);
                let post_edge_sys = sub.sys.clone();
                let post_edge_counter = sub.maude.fresh_counter_peek();
                let arm_systems = match res {
                    Ok(outcome) => fanout_arm_systems(outcome, post_edge_sys),
                    _ => vec![post_edge_sys],
                };
                let prem0 = match ru_inst.premises.first() {
                    Some(f) => f.clone(),
                    None => continue,
                };
                for mut arm_sys in arm_systems {
                    let mut arm_sub = Reduction::new_inheriting(
                        self.ctx, arm_sys, post_edge_counter);
                    arm_sub.mark_goal_as_solved(&Goal::Premise(
                        (new_node.clone(), crate::rule::PremIdx(0)),
                        prem0.clone(),
                    ));
                    arm_sub.insert_goal(Goal::Chain(
                        (new_node.clone(), crate::rule::ConcIdx(0)),
                        p.clone(),
                    ));
                    let arm_counter = arm_sub.maude.fresh_counter_peek();
                    arm_sys = arm_sub.sys;
                    for (existing, status) in arm_sys.goals_mut().iter_mut() {
                        if existing == &g && !status.solved {
                            status.solved = true;
                            break;
                        }
                    }
                    if trace_chains {
                        eprintln!("[RS-CHAIN] UNION {}", case_name);
                    }
                    if crate::constraint::solver::trace::exec_enabled() {
                        crate::constraint::solver::trace::trace_exec(
                            &format!("solveChain UNION {}", case_name));
                    }
                    all_cases.push((case_name.clone(), arm_sys));
                    all_case_counters.push(arm_counter);
                }
            }
            // HS short-circuits the generic destructor loop in the FUnion
            // arm (case-match on `viewTerm2`).  Mirror by skipping branch 2's
            // generic loop below.
            if all_cases.is_empty() { return GoalCases::Contradictory; }
            if all_cases.len() == 1 {
                let (name, sys) = all_cases.into_iter().next().unwrap();
                self.sys = sys;
                // HS FreshT-threading — see `solve_action_goal`'s
                // single-case adoption (task #16).
                self.maude.reset_counter_to(all_case_counters[0]);
                self.changed = ChangeIndicator::Changed;
                return GoalCases::LinearNamed(name);
            }
            self.changed = ChangeIndicator::Changed;
            self.last_case_counters = all_case_counters.clone();
            return GoalCases::Cases(all_cases);
        }
        if !conc_term_is_msg_var {
            let avoid_max = bounds_max(&self.sys);
            // HS `solveChain` EXTEND (Goals.hs:393-397, see line 394): `insertFreshNode rules
            // (Just cRule)` allocates `i <- freshLVar "vr"` ONCE, before the
            // `disjunctionOfList rules` inside `labelNodeId`.  So every
            // destructor-extension case shares the same `#vr` id, and each
            // destructor's `importRule` (= rename) reserves its var range from
            // the single post-`freshLVar` counter state (independent forks).
            self.maude.ensure_above(avoid_max);
            let vr_idx = self.maude.fresh_idx();
            let post_vr_counter = self.maude.fresh_counter_peek();
            let mut counter_high_water = post_vr_counter;
            for ir in &self.ctx.intruder_rules {
                if !crate::rule::is_destr_rule_info(&ir.info) { continue; }
                let ru_inst = intr_rule_to_rule_ac_inst(ir.clone());
                // Independent Disj fork: reset to the post-`freshLVar "vr"`
                // state so this destructor renames from the same base as its
                // siblings.
                self.maude.reset_counter_to(post_vr_counter);
                let ru_renamed = freshen_rule(ru_inst, avoid_max, &self.maude);
                counter_high_water = counter_high_water.max(self.maude.fresh_counter_peek());
                // HS-faithful `labelNodeId` (Reduction.hs:219-225) — when
                // the chain conc's rule (parent) shares a name with this
                // destructor and still has > 1 remaining applications,
                // decrement the destructor's budget by 1.  This is the
                // chain-extension loop-breaker: the budget reaches 1 after
                // N consecutive same-name extensions, at which point
                // `forbiddenEdge` (Goals.hs) mzero's the branch.
                let ru_renamed = {
                    let cn = crate::rule::rule_name_string(&c_rule);
                    let pn = crate::rule::rule_name_string(&ru_renamed);
                    if !cn.is_empty() && cn == pn {
                        let parent_budget = crate::rule::get_remaining_rule_applications(&c_rule);
                        if parent_budget > 1 {
                            crate::rule::set_remaining_rule_applications(ru_renamed, parent_budget - 1)
                        } else {
                            ru_renamed
                        }
                    } else {
                        ru_renamed
                    }
                };
                // Mirror HS `insertFreshNode rules (Just cRule)` (Goals.hs `insertFreshNode`)
                // which calls labelNodeId → exploitPrems for every destructor
                // rule, BEFORE the forbiddenEdge / prem-tag mismatch checks
                // mzero the branch.  For dead-branch destructors, synthesize
                // the matching exploitPrems + per-premise traces so trace
                // counts align; HS emits exactly one exploitPrems per rule.
                let trace_dead = |ru: &crate::rule::RuleACInst| {
                    if crate::constraint::solver::trace::exec_enabled() {
                        crate::constraint::solver::trace::trace_exec(
                            &format!("exploitPrems rule={}",
                                crate::constraint::solver::reduction::rule_trace_name(ru)));
                        emit_dead_rule_premise_traces(ru);
                    }
                };
                let dbg_filter = tamarin_utils::env_gate!("TAM_RS_DBG_CHAIN_EXT_FILTER");
                let prem0 = match ru_renamed.premises.first() {
                    Some(f) => f.clone(),
                    None => {
                        if dbg_filter {
                            eprintln!("[CHAIN_EXT_FILTER] SKIP rule={} reason=no_premises",
                                rule_case_name(&ru_renamed));
                        }
                        trace_dead(&ru_renamed);
                        continue;
                    }
                };
                if prem0.tag != fa_conc.tag
                    || prem0.terms.len() != fa_conc.terms.len()
                {
                    if dbg_filter {
                        eprintln!("[CHAIN_EXT_FILTER] SKIP rule={} reason=tag/arity_mismatch prem0={:?}/{} faConc={:?}/{}",
                            rule_case_name(&ru_renamed),
                            prem0.tag, prem0.terms.len(),
                            fa_conc.tag, fa_conc.terms.len());
                    }
                    trace_dead(&ru_renamed);
                    continue;
                }
                if forbidden_edge(&c_rule, &ru_renamed) {
                    if dbg_filter {
                        eprintln!("[CHAIN_EXT_FILTER] SKIP rule={} reason=forbidden_edge c_rule={}",
                            rule_case_name(&ru_renamed),
                            rule_case_name(&c_rule));
                    }
                    trace_dead(&ru_renamed);
                    continue;
                }
                if ru_renamed.conclusions.is_empty() {
                    if dbg_filter {
                        eprintln!("[CHAIN_EXT_FILTER] SKIP rule={} reason=no_conclusions",
                            rule_case_name(&ru_renamed));
                    }
                    trace_dead(&ru_renamed);
                    continue;
                }
                if dbg_filter {
                    eprintln!("[CHAIN_EXT_FILTER] KEEP rule={} faConc={:?}",
                        rule_case_name(&ru_renamed), fa_conc);
                }
                // Matching destructor: the `exploit_prems` call below
                // will emit its own exploitPrems trace.

                let mut sys_clone = self.sys.clone();
                let new_node = tamarin_term::lterm::LVar::new(
                    "vr",
                    tamarin_term::lterm::LSort::Node,
                    vr_idx,
                );
                sys_clone.add_node(new_node.clone(), ru_renamed.clone());
                // HS FreshT-threading: continue the enclosing thread
                // (post-freshen counter of THIS destructor fork).
                let mut sub = Reduction::new_inheriting(
                    self.ctx, sys_clone, self.maude.fresh_counter_peek());
                // HS-faithful effect order (Goals.hs solveChain EXTEND
                // + Reduction.hs labelNodeId/extendAndMark):
                //   1. labelNodeId → exploitPrems        (Reduction.hs:219-228)
                //   2. contradictoryIf forbiddenEdge      (Goals.hs:293-368, see line 371 — pre-filtered above)
                //   3. extendAndMark → insertEdges chain_extend  (Goals.hs:293-368, see line 346)
                //
                // Step 1: exploit suppliers + KU action goals + Kd/Ded
                // Premise goals (HS `exploitPrems i ru` in labelNodeId).
                // Suppliers route through `insert_edge_labeled`
                // (fresh_supplier / isend_supplier) so any
                // fact-unification failure sets sub.sys.eq_store.is_false()
                // via mark_contradictory.
                //
                // Use full `exploit_prems` (NOT a supplier-only variant)
                // to be HS-faithful — Haskell's `solveChain EXTEND` path
                // calls `insertFreshNode rules (Just cRule)` →
                // `labelNodeId` → `exploitPrems` which inserts a
                // `Goal::Premise` for every non-Fr/In/KU premise (incl.
                // Kd / Ded).  Dropping these Premise goals is a
                // CORRECTNESS bug: for multi-premise destructor rules like
                // `d_em` (Bilinear-Pairing Emap-down: two Kd premises),
                // only prem 0 would be tracked (as the chain), and prem 1's
                // Kd premise would have NO goal whatsoever — so the system
                // is reported as Solved with an unsatisfied Kd input,
                // falsifying the verdict.
                sub.exploit_prems(&new_node, &ru_renamed);
                if sub.sys.eq_store.is_false() {
                    if dbg_filter {
                        eprintln!("[CHAIN_EXT_FILTER] DROP_AFTER_EXPLOIT rule={}",
                            rule_case_name(&ru_renamed));
                    }
                    continue;
                }
                // Step 2: HS-faithful `insertEdges` chain_extend
                // (Goals.hs:293-368, see line 346 extendAndMark) — solveFactEqs on
                // (faConc, faPrem) BEFORE adding to sEdges.
                let res = sub.insert_edge_labeled("chain_extend", crate::constraint::constraints::Edge {
                    src: c.clone(),
                    tgt: (new_node.clone(), crate::rule::PremIdx(0)),
                });
                if tamarin_utils::env_gate!("TAM_RS_DBG_CHAIN_EXTEND_MULTI") {
                    if let Ok(SolveOutcome::Cases(ref arms)) = res {
                        eprintln!("[CHAIN_EXTEND_MULTI] rule={} arms={} faConc={:?}",
                            rule_case_name(&ru_renamed), arms.len(), fa_conc);
                    }
                }
                if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                    if dbg_filter {
                        eprintln!("[CHAIN_EXT_FILTER] DROP_AFTER_INSERT_EDGE rule={}",
                            rule_case_name(&ru_renamed));
                    }
                    continue;
                }
                // HS-faithful: when `insertEdges chain_extend` produces
                // multiple unifier arms via `solveTermEqs SplitNow ->
                // disjunctionOfList` (Reduction.hs), HS's
                // `disjunctionOfList arms` fans out IN the surrounding
                // Disj monad — `extendAndMark` (Goals.hs:346-348) then
                // completes the markGoalAsSolved / insertChain steps
                // INDEPENDENTLY per arm, each arm carrying its own
                // unifier subst.
                //
                // Fix: collect per-arm systems.  For Cases, snapshot
                // sub.sys (which has the chain_extend edge but the
                // pre-split eq_store), then per arm install the arm's
                // eq_store into a fresh clone and complete the
                // mark_goal_as_solved / insert_goal / mark-g-solved
                // sequence.  For Linear (single arm or no split),
                // continue using `sub.sys` as before.
                let case_name = rule_case_name(&ru_renamed);
                let post_edge_sys = sub.sys.clone();
                let post_edge_counter = sub.maude.fresh_counter_peek();
                let arm_systems = match res {
                    Ok(outcome) => fanout_arm_systems(outcome, post_edge_sys),
                    _ => vec![post_edge_sys],
                };
                for mut arm_sys in arm_systems {
                    // Step 3 (HS-faithful): leave sub.sys raw post-insertEdges.
                    // HS's simplifySystem (`Simplify.hs:56-158, see line 97`) calls substSystem
                    // exactly ONCE at the start of each simplify iteration,
                    // NOT after every solveTermEqs inside a CR-rule.  So
                    // when the chain continuation goal Chain((new_node,
                    // ConcIdx 0), p) is later dispatched by solveGoal, HS
                    // reads sNodes which still holds ru's raw (pre-subst)
                    // conclusion fact — e.g. KD(~mw:Fresh) or KD(x:Msg) —
                    // and HS's `contradictoryIf (isMsgVar m)` (Goals.hs)
                    // fires mzero on the latter.
                    //
                    // The freshly-added prem-0 goal now has an incoming
                    // edge from `c`, so mark it solved (Haskell's
                    // `markGoalAsSolved "directly" (PremiseG (i, v) ...)`).
                    let mut arm_sub = Reduction::new_inheriting(
                        self.ctx, arm_sys, post_edge_counter);
                    arm_sub.mark_goal_as_solved(&Goal::Premise(
                        (new_node.clone(), crate::rule::PremIdx(0)),
                        prem0.clone(),
                    ));
                    // Insert the chain continuation (i, ConcIdx(0)) → p.
                    arm_sub.insert_goal(Goal::Chain(
                        (new_node.clone(), crate::rule::ConcIdx(0)),
                        p.clone(),
                    ));
                    let arm_counter = arm_sub.maude.fresh_counter_peek();
                    arm_sys = arm_sub.sys;
                    // Mark the original chain goal as solved in this case
                    // (it's been extended, not closed).
                    for (existing, status) in arm_sys.goals_mut().iter_mut() {
                        if existing == &g && !status.solved {
                            status.solved = true;
                            break;
                        }
                    }
                    if trace_chains {
                        eprintln!("[RS-CHAIN] EXTEND {} prem=PremIdx(0)", case_name);
                    }
                    if crate::constraint::solver::trace::exec_enabled() {
                        crate::constraint::solver::trace::trace_exec(
                            &format!("solveChain EXTEND {}", case_name));
                    }
                    all_cases.push((case_name.clone(), arm_sys));
                    all_case_counters.push(arm_counter);
                }
            }
            // Restore the shared counter to the high-water mark reached
            // across the per-destructor forks (each of which rewound it via
            // `reset_counter_to`) so later allocations can't collide.
            self.maude.ensure_above(counter_high_water.saturating_sub(1));
        }

        if all_cases.is_empty() { return GoalCases::Contradictory; }
        if all_cases.len() == 1 {
            let (name, sys) = all_cases.into_iter().next().unwrap();
            self.sys = sys;
            // HS FreshT-threading — see `solve_action_goal`'s single-case
            // adoption (task #16).
            self.maude.reset_counter_to(all_case_counters[0]);
            self.changed = ChangeIndicator::Changed;
            return GoalCases::LinearNamed(name);
        }
        self.changed = ChangeIndicator::Changed;
        self.last_case_counters = all_case_counters;
        GoalCases::Cases(all_cases)
    }

    /// `solveSubterm` — full port of Haskell `solveSubterm`
    /// (Goals.hs `solveSubterm`):
    /// ```haskell
    /// solveSubterm st = do
    ///   modM (posSubterms . sSubtermStore) (st `S.delete`)
    ///   modM (solvedSubterms . sSubtermStore) (st `S.insert`)
    ///   reducible <- reducibleFunSyms . mhMaudeSig <$> getMaudeHandle
    ///   splitList <- splitSubterm reducible True st
    ///   (i, split) <- disjunctionOfList $ zip [1..] splitList
    ///   case split of
    ///     TrueD                 -> return ()
    ///     SubtermD st1          -> modM sSubtermStore (addSubterm st1)
    ///     NatSubtermD st1@(s,t) -> if length splitList == 1
    ///                                then do newVar <- freshLVar "newVar" LSortNat
    ///                                        let sPlus = s ++: varTerm newVar
    ///                                        insertFormula $ closeGuarded Ex [newVar] [EqE sPlus t] gtrue
    ///                                else modM sSubtermStore (addSubterm st1)
    ///     EqualD (l, r)         -> insertFormula $ GAto $ EqE (lTermToBTerm l) (lTermToBTerm r)
    ///     ACNewVarD ((smallPlus, big), newVar) ->
    ///                              insertFormula $ closeGuarded Ex [newVar] [EqE smallPlus big] gtrue
    ///   return $ "SubtermSplit" ++ show i
    /// ```
    /// `disjunctionOfList` over `[]` yields no branches ⇒ the goal is
    /// contradictory (the subterm is trivially false).  A singleton list
    /// still produces one branch named `SubtermSplit1`.
    pub fn solve_subterm_goal(
        &mut self,
        st: &(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm),
    ) -> GoalCases {
        use tamarin_term::function_symbols::AcSym;
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::f_app_ac;
        use tamarin_term::vterm::var_term;
        let g = Goal::Subterm(st.clone());
        // modM posSubterms (delete st); modM solvedSubterms (insert st).
        let mut moved = false;
        self.sys.invalidate_max_var_idx_cache();
        self.sys.subterm_store_mut().subterms.retain(|c| {
            let keep = !(c.small == st.0 && c.big == st.1);
            if !keep { moved = true; }
            keep
        });
        if moved {
            self.sys.invalidate_max_var_idx_cache();
            if !self.sys.subterm_store.solved_subterms.iter()
                .any(|c| c.small == st.0 && c.big == st.1)
            {
                self.sys.subterm_store_mut().solved_subterms.push(
                    crate::tools::subterm_store::SubtermConstraint {
                        small: st.0.clone(),
                        big: st.1.clone(),
                        propagated: true,
                    });
            }
            self.changed = ChangeIndicator::Changed;
        }
        self.mark_goal_as_solved(&g);

        // splitList <- splitSubterm reducible True st.  Fresh vars for the
        // AC-recurse arm come from the maude counter (HS `freshLVar`).
        let reducible = self.maude.maude_sig().reducible_fun_syms_fast.clone();
        let split_list = {
            let avoid_max = self.fresh_var_baseline();
            self.maude.ensure_above(avoid_max);
            let maude = self.maude.clone();
            let mut mk_fresh = |sort: LSort| -> LVar {
                LVar::new("newVar", sort, maude.fresh_idx())
            };
            split_subterm_single(&reducible, &st.0, &st.1, &mut mk_fresh)
        };

        // disjunctionOfList [] -> Contradictory.
        if split_list.is_empty() {
            self.sys.subterm_store_mut().contradictory = true;
            return GoalCases::Contradictory;
        }

        let single = split_list.len() == 1;
        let base_sys = self.sys.clone();
        let mut cases: Vec<(String, crate::constraint::system::System)> = Vec::new();
        for (i, split) in split_list.iter().enumerate() {
            let case_name = format!("SubtermSplit{}", i + 1);
            // Fork the system; mutate per the split arm via a fresh
            // Reduction over the clone so insertFormula / addSubterm route
            // exactly as in HS.  `disjunctionOfList` forks the MonadFresh
            // state at the post-`splitSubterm` point: each branch starts
            // its fresh allocation above every var minted so far (incl. the
            // AC `newVar` from the split), so advance the per-branch
            // counter past the parent's current high-water mark.
            let mut sub = Reduction::new(self.ctx, base_sys.clone());
            sub.maude.ensure_above(
                self.maude.fresh_counter_peek().saturating_sub(1));
            match split {
                SubtermSplit::TrueD => { /* return () */ }
                SubtermSplit::SubtermD(s, t) => {
                    sub.sys.invalidate_max_var_idx_cache();
                    sub.sys.subterm_store_mut().add(s.clone(), t.clone());
                }
                SubtermSplit::NatSubtermD(s, t) => {
                    if single {
                        // newVar <- freshLVar "newVar" LSortNat
                        let avoid_max = sub.fresh_var_baseline();
                        sub.maude.ensure_above(avoid_max);
                        let new_var = LVar::new("newVar", LSort::Nat,
                            sub.maude.fresh_idx());
                        // sPlus = s ++: varTerm newVar
                        let s_plus = f_app_ac(AcSym::NatPlus,
                            vec![s.clone(), var_term(new_var.clone())]);
                        // insertFormula $ closeGuarded Ex [newVar] [EqE sPlus t] gtrue
                        let f = close_guarded_ex_eq(&new_var, &s_plus, t);
                        sub.insert_formula(f);
                    } else {
                        sub.sys.invalidate_max_var_idx_cache();
                        sub.sys.subterm_store_mut().add(s.clone(), t.clone());
                    }
                }
                SubtermSplit::EqualD(l, r) => {
                    // insertFormula $ GAto $ EqE (lTermToBTerm l) (lTermToBTerm r)
                    let l_ast = crate::elaborate::lnterm_to_term(l);
                    let r_ast = crate::elaborate::lnterm_to_term(r);
                    let atom = crate::guarded::atom_to_gatom_free(
                        &tamarin_parser::ast::Atom::Eq(l_ast, r_ast));
                    sub.insert_formula(crate::guarded::Guarded::Atom(atom));
                }
                SubtermSplit::AcNewVarD(small_plus, big, new_var) => {
                    // insertFormula $ closeGuarded Ex [newVar] [EqE smallPlus big] gtrue
                    let f = close_guarded_ex_eq(new_var, small_plus, big);
                    sub.insert_formula(f);
                }
            }
            sub.changed = ChangeIndicator::Changed;
            cases.push((case_name, sub.sys));
        }

        self.changed = ChangeIndicator::Changed;
        if cases.len() == 1 {
            let (name, sys) = cases.into_iter().next().unwrap();
            self.sys = sys;
            return GoalCases::LinearNamed(name);
        }
        GoalCases::Cases(cases)
    }

    /// `solveSplit` — perform a deferred equality-store split for
    /// `Goal::Split(id)`. Mirrors the relevant arm of Haskell's
    /// `solveGoal`: `splitAtPos` followed by replacing the eq-store
    /// and running `simp` so the singleton disjunction folds into the
    /// free substitution via `simpSingleton` + `applyEqStore`.
    pub fn solve_split_goal(
        &mut self,
        id: crate::tools::equation_store::SplitId,
    ) -> GoalCases {
        if tamarin_utils::env_gate!("TAM_RS_DBG_SOLVE_SPLIT_PRECOMPUTE") {
            let in_pre = crate::constraint::solver::sources::in_precompute_mode();
            eprintln!("[SOLVE_SPLIT_CALL] in_precompute={} split_id={:?}", in_pre, id);
        }
        let cases = match self.sys.eq_store.perform_split(id) {
            Some(cs) => cs,
            None => return GoalCases::Contradictory,
        };
        if cases.is_empty() { return GoalCases::Contradictory; }
        let g = Goal::Split(id);
        // After picking a case, run `simp_with_fresh` so the resulting
        // singleton disjunction (the picked variant subst) folds into
        // eq_store.subst via `simp_singleton` — matching Haskell's
        // `solveSplit`'s `simp hnd substCheck store` call (Goals.hs:375-386, see line 381).
        // Without this the picked subst stays in the conjunction and
        // never propagates to rule terms.
        //
        // The is_contr predicate is Haskell's `substCreatesNonNormalTerms hnd`:
        // it drops variants where applying the variant subst to a
        // maybe-non-NF subterm in the system produces a non-NF term.
        // Critical for SplitG variant filtering (e.g. drop verify=sign(...)
        // variants against a live Eq(verify, true) restriction).
        let maude = self.maude.clone();
        let has_reducible = !maude.maude_sig().reducible_fun_syms.is_empty();
        // One `maybeNonNormalTerms` walk of `self.sys`, shared across every
        // candidate probe below — HS's curried `substCheck` from Goals.hs:375-386, see line 381
        // (`gets (substCreatesNonNormalTerms hnd)` captures the system once).
        // See `SubstNfChecker`.
        let nf_checker = has_reducible.then(||
            crate::constraint::solver::contradictions::SubstNfChecker::new(
                &maude, &self.sys));
        // Collect the system's free vars — these are LIVE system vars
        // (node ids, rule premise/conclusion/action vars, edges, less
        // atoms, goals, formulas).  Pass to `simp_with_fresh_avoiding`
        // so the singleton fold's `fresh_to_free` doesn't rename them.
        // Pattern_matching::Responder_secrecy bug:  Setup_Key's `k:F#0`
        // got baked into the variant subst's range via `apply_eq_store`,
        // then `fresh_to_free` renamed it, desyncing the rule's two
        // premises.
        // Functionally dead in production: `simp_singleton_avoiding` reads
        // this set ONLY inside its three debug gates (the fold itself calls
        // `fresh_to_free_avoiding`, which ignores it), so only pay the
        // whole-System walk when a gate is on — see
        // `preserve_dbg_gates_enabled`.
        let system_vars = if preserve_dbg_gates_enabled() {
            collect_live_system_vars(&self.sys)
        } else {
            std::collections::BTreeSet::new()
        };
        // `nf_checker.is_some()` iff `has_reducible`, so `as_ref()` is
        // `Some` exactly when the non-normal-terms check must run.
        let simplify_picked = |store: crate::tools::equation_store::EquationStore|
            -> crate::tools::equation_store::EquationStore
        {
            simp_store(store, nf_checker.as_ref(), &maude, &system_vars)
        };
        if cases.len() == 1 {
            if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
                eprintln!("[rs-fold] SPLITG-SINGLE id={:?} counter={}",
                    id, self.maude.fresh_counter_peek());
            }
            self.sys.invalidate_max_var_idx_cache();
            self.sys.set_eq_store(std::sync::Arc::new(simplify_picked(
                cases.into_iter().next().unwrap())));
            self.mark_goal_as_solved(&g);
            // Push the resulting free subst back into the system.
            self.subst_system();
            return GoalCases::Linear;
        }
        let mut out = Vec::with_capacity(cases.len());
        let n_cases = cases.len();
        let fold_dbg = tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS");
        if fold_dbg {
            eprintln!("[rs-fold] SPLITG-ENTER id={:?} n_cases={} counter={}",
                id, n_cases, self.maude.fresh_counter_peek());
        }
        // HS FreshT-threading (`solveSplit`, Goals.hs:436-447):
        // `disjunctionOfList split` forks the DisjT layer, which sits
        // BELOW FreshT in `Reduction = StateT System (FreshT (DisjT ...))`
        // (Reduction.hs:115-115, see line 123) — so each arm's subsequent `simp` (whose
        // `simpSingleton` fold draws fresh idxs via `freshToFree`) starts
        // from an independent COPY of the counter at the fan-out point.
        // RS's `simplify_picked` allocs via the ONE shared `self.maude`
        // counter, so consecutive cases threaded each other's fold draws:
        // on csf18-xor/CH07's `splitEqs(0)` (9 xor-unifier variants) the
        // per-case folds drew 6→8, 8→12, 12→16, 16→19, ... where HS draws
        // 6.. in EVERY case (TAM_{HS,RS}_DBG_FOLD_DRAWS traces).  The
        // folded range vars persist in each case's system, so every case
        // after the first carried a cumulative +offset in its whole var
        // numbering — the growing ∃-witness index drift on CH07 /
        // sapic feature-xor CH07 web proof pages.  Rewind to the fork
        // base before each case and record the per-case continuation
        // counter (fork + that case's OWN draws) in `last_case_counters`
        // so the post-solve `simplifySystem` continues each branch at
        // HS's counter position, exactly like the other Cases producers.
        let fork_base = self.maude.fresh_counter_peek();
        let mut case_counters: Vec<u64> = Vec::with_capacity(n_cases);
        for (ci, store) in cases.into_iter().enumerate() {
            self.maude.reset_counter_to(fork_base);
            let mut sys = self.sys.clone();
            sys.invalidate_max_var_idx_cache();
            if fold_dbg {
                eprintln!("[rs-fold] SPLITG-CASE id={:?} case={} before={}",
                    id, ci, self.maude.fresh_counter_peek());
            }
            sys.set_eq_store(std::sync::Arc::new(simplify_picked(store)));
            let branch_counter = self.maude.fresh_counter_peek();
            if fold_dbg {
                eprintln!("[rs-fold] SPLITG-CASE-DONE id={:?} case={} after={}",
                    id, ci, branch_counter);
            }
            for (existing, status) in sys.goals_mut().iter_mut() {
                if existing == &g && !status.solved {
                    status.solved = true;
                    break;
                }
            }
            // Propagate variant subst into nodes/edges/goals for each
            // case before saving.
            let mut sub = Reduction::new(self.ctx, sys);
            sub.subst_system();
            // Haskell `solveSplit` (Goals.hs:375-386, see line 386): returns `"split"` for
            // EVERY alternative.  Disambiguation to `split_case_1`,
            // `split_case_2`, ... happens in `distinguish`
            // (ProofMethod.hs:283-340, see line 308) when multiple sibling cases share the
            // same name.  Mirror by emitting plain `"split"` here.
            out.push(("split".to_string(), sub.sys));
            case_counters.push(branch_counter);
        }
        self.changed = ChangeIndicator::Changed;
        self.last_case_counters = case_counters;
        GoalCases::Cases(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        for c in ["/usr/local/bin/maude", "maude"] {
            if std::path::Path::new(c).exists() { return Some(c.to_string()); }
        }
        None
    }

    fn ctx() -> Option<ProofContext> {
        let path = maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).ok()?;
        Some(ProofContext::new(h, Vec::new()))
    }

    #[test]
    fn reduction_starts_unchanged() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let r = Reduction::new(&ctx, System::empty());
        assert_eq!(r.changed, ChangeIndicator::Unchanged);
    }

    #[test]
    fn insert_goal_marks_changed() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let v = tamarin_term::lterm::LVar::new(
            "k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        r.insert_goal(Goal::Action(v, f));
        assert_eq!(r.changed, ChangeIndicator::Changed);
        assert_eq!(r.sys.goals.len(), 1);
    }

    #[test]
    fn solve_term_eqs_trivial_equation_no_change() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        // x =? x is trivially true.
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let t: tamarin_term::lterm::LNTerm =
            tamarin_term::term::Term::Lit(Lit::Var(v));
        let r_out = r.solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: t.clone(), rhs: t }],
        ).expect("solve");
        assert!(matches!(r_out, SolveOutcome::Linear(ChangeIndicator::Unchanged)));
    }

    #[test]
    fn solve_term_eqs_unifies_two_vars() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        // x =? y produces a single mgu.
        use tamarin_term::vterm::Lit;
        let x = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        let y = tamarin_term::lterm::LVar::new(
            "y", tamarin_term::lterm::LSort::Msg, 0);
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(x));
        let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(y));
        let r_out = r.solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }],
        ).expect("solve");
        assert!(matches!(r_out, SolveOutcome::Linear(ChangeIndicator::Changed)));
        assert_eq!(r.changed, ChangeIndicator::Changed);
    }

    // =====================================================================
    // subst_system — Haskell-equivalent invariants
    // =====================================================================
    //
    // Haskell's `Theory.Constraint.Solver.Reduction.substSystem`:
    //   substSystem = do
    //     c1 <- substNodes
    //     substEdges
    //     substLastAtom
    //     substLessAtoms
    //     ...
    //     c2 <- substGoals
    //     return (c1 <> c2)
    // pulls the eq-store substitution through every node id, edge,
    // less atom, last atom, and goal. The Rust port should preserve
    // these invariants on completion.

    #[test]
    fn subst_system_rewrites_edge_node_ids_through_eqstore() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        // Force `i_2 = j_3` into the eq-store, then add an edge whose
        // src is `i_2` and confirm that subst_system rewrites it.
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::Lit;
        let i = LVar::new("i", LSort::Node, 2);
        let j = LVar::new("j", LSort::Node, 3);
        let ti = tamarin_term::term::Term::Lit(Lit::Var(i.clone()));
        let tj = tamarin_term::term::Term::Lit(Lit::Var(j.clone()));
        // Add an edge i -> some target. (Source-only is enough — we
        // just want to verify the substitution propagates.)
        let tgt = LVar::new("t", LSort::Node, 99);
        r.sys.invalidate_max_var_idx_cache();
        r.sys.content_mut().edges.push(crate::constraint::constraints::Edge {
            src: (i.clone(), crate::rule::ConcIdx(0)),
            tgt: (tgt.clone(), crate::rule::PremIdx(0)),
        });
        // Inject the equality into the eq-store directly.
        r.solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
        ).expect("solve");
        r.subst_system();
        // After subst_system, the edge's source node id must be
        // mapped to whatever the canonical representative of i and j
        // is (the eq-store unifier picks one).
        let canonical = {
            let id_term = tamarin_term::term::Term::Lit(Lit::Var(i.clone()));
            let mapped = tamarin_term::subst::apply_vterm(&r.sys.eq_store.subst, id_term);
            if let tamarin_term::term::Term::Lit(Lit::Var(v)) = mapped { v } else { i.clone() }
        };
        assert_eq!(r.sys.edges[0].src.0, canonical,
            "edge src should be the canonical node id after subst_system");
    }

    #[test]
    fn subst_system_rewrites_less_atom_node_ids() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::Lit;
        let i = LVar::new("i", LSort::Node, 2);
        let j = LVar::new("j", LSort::Node, 3);
        let target = LVar::new("t", LSort::Node, 9);
        r.sys.invalidate_max_var_idx_cache();
        r.sys.content_mut().less_atoms.push(crate::constraint::constraints::LessAtom::new(
            i.clone(), target.clone(),
            crate::constraint::constraints::Reason::Formula));
        let ti = tamarin_term::term::Term::Lit(Lit::Var(i.clone()));
        let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
        r.solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
        ).expect("solve");
        r.subst_system();
        // The less atom's `smaller` should still resolve to the same
        // canonical id reachable from i via the eq-store.
        let canonical = {
            let id_term = tamarin_term::term::Term::Lit(Lit::Var(i.clone()));
            let mapped = tamarin_term::subst::apply_vterm(&r.sys.eq_store.subst, id_term);
            if let tamarin_term::term::Term::Lit(Lit::Var(v)) = mapped { v } else { i.clone() }
        };
        assert_eq!(r.sys.less_atoms[0].smaller, canonical);
    }

    #[test]
    fn subst_system_idempotent_on_empty_substitution() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        // No equations injected — the eq-store substitution is empty.
        let before_changed = r.changed;
        r.subst_system();
        // No-op: nothing to rewrite.
        assert_eq!(r.changed, before_changed);
        assert!(r.sys.nodes.is_empty());
        assert!(r.sys.edges.is_empty());
        assert!(r.sys.less_atoms.is_empty());
    }

    #[test]
    fn subst_system_marks_contradiction_on_shape_mismatch() {
        // Two nodes with the same canonical id but DIFFERENT rule
        // shapes (e.g. one with 0 conclusions, one with 1) cannot be
        // merged consistently — Haskell's `setNodes` reaches the same
        // conclusion via `solveRuleEqs` failing. Our port pushes
        // `gfalse` so the next contradictions check trips.
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::Lit;
        let i = LVar::new("i", LSort::Node, 2);
        let j = LVar::new("j", LSort::Node, 3);
        let info = || crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
        // First node has 0 conclusions; second has 1 — incompatible.
        r.sys.add_node(i.clone(),
            crate::rule::Rule::new(info(), vec![], vec![], vec![]));
        let dummy_fact = crate::fact::Fact::new(
            crate::fact::FactTag::Out, vec![]);
        r.sys.add_node(j.clone(),
            crate::rule::Rule::new(info(), vec![], vec![dummy_fact], vec![]));
        // Force i = j into the eq-store.
        let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
        let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
        r.solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
        ).expect("solve");
        r.subst_system();
        let bot = crate::guarded::gfalse();
        assert!(crate::guarded::stores_contains(&r.sys.formulas, &bot),
            "shape mismatch must push gfalse onto the formula list");
    }

    #[test]
    fn subst_system_merges_collided_nodes_and_equates_their_rules() {
        // When two nodes collapse to the same canonical id, Haskell's
        // `setNodes` runs `solveRuleEqs` on their facts. Our port queues
        // those into solve_fact_eqs at the tail of subst_system. Verify
        // that the merge happens and only one node remains under the
        // canonical id.
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::Lit;
        let i = LVar::new("i", LSort::Node, 2);
        let j = LVar::new("j", LSort::Node, 3);
        // Two empty rule instances, one keyed by i and one by j.
        let ru = || crate::rule::Rule {
            info: crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
                name: crate::rule::ProtoRuleName::Stand("R"),
                attributes: crate::rule::RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            premises: vec![],
            conclusions: vec![],
            actions: vec![],
            new_vars: vec![],
        };
        r.sys.add_node(i.clone(), ru());
        r.sys.add_node(j.clone(), ru());
        let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
        let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
        r.solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
        ).expect("solve");
        r.subst_system();
        assert_eq!(r.sys.nodes.len(), 1, "two nodes with the same canonical id should merge");
    }

    #[test]
    fn solve_fact_eqs_tag_mismatch_is_contradictory() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let f1 = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        let f2 = crate::fact::LNFact::new(crate::fact::FactTag::In, vec![]);
        let r_out = r.solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: f1, rhs: f2 }],
        ).expect("solve");
        assert!(matches!(r_out, SolveOutcome::Contradictory));
    }

    #[test]
    fn solve_disj_goal_empty_is_contradictory() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let d = Disj(Vec::<Guarded>::new());
        let out = r.solve_disj_goal(&d);
        assert!(matches!(out, GoalCases::Contradictory));
    }

    #[test]
    fn solve_disj_goal_singleton_is_linear() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        // Use gtrue() = Conj([]): it gets decomposed into solved_formulas
        // by insert_formula (not raw-pushed to formulas).
        let f = crate::guarded::gtrue();
        let d = Disj(vec![f.clone()]);
        r.insert_goal(Goal::Disj(d.clone()));
        let out = r.solve_disj_goal(&d);
        // Haskell `solveDisjunction` has no singleton special-case: a lone
        // alternative is named `case_1` (and `ppCases` only elides the
        // heading for the empty name), so the Rust continuation is a
        // single named linear case `case_1`, not an unnamed `Linear`.
        assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "case_1"));
        // gtrue (Conj []) decomposes to solved_formulas — see
        // insert_formula_inner for the Conj arm.
        assert!(crate::guarded::stores_contains(&r.sys.solved_formulas, &f));
        assert!(r.sys.goals.iter().any(|(g, s)| matches!(g, Goal::Disj(_)) && s.solved));
    }

    #[test]
    fn solve_disj_goal_two_branches_forks() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let f1 = crate::guarded::gtrue();   // Conj([]) → solved_formulas
        let f2 = crate::guarded::gfalse();  // Disj([]) → formulas (gfalse sentinel)
        let d = Disj(vec![f1.clone(), f2.clone()]);
        r.insert_goal(Goal::Disj(d.clone()));
        let out = r.solve_disj_goal(&d);
        match out {
            GoalCases::Cases(systems) => {
                assert_eq!(systems.len(), 2);
                assert!(crate::guarded::stores_contains(&systems[0].1.solved_formulas, &f1));
                assert!(crate::guarded::stores_contains(&systems[1].1.formulas, &f2));
                for (_, s) in &systems {
                    assert!(s.goals.iter().any(|(g, st)| matches!(g, Goal::Disj(_)) && st.solved));
                }
            }
            other => panic!("expected Cases, got {:?}", other),
        }
    }

    #[test]
    fn solve_subterm_goal_marks_solved_and_moves() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        let w = tamarin_term::lterm::LVar::new(
            "y", tamarin_term::lterm::LSort::Msg, 0);
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(v));
        let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(w));
        sys.invalidate_max_var_idx_cache();
        sys.subterm_store_mut().add(tx.clone(), ty.clone());
        sys.add_goal(Goal::Subterm((tx.clone(), ty.clone())));
        let mut r = Reduction::new(&ctx, sys);
        let out = r.solve_subterm_goal(&(tx.clone(), ty.clone()));
        // `x:msg ⊏ y:msg`: big is a bare variable, so `splitSubterm`
        // (singleStep) cannot decompose ⇒ a single `SubtermD (x,y)` leaf.
        // HS `solveSubterm` therefore emits ONE case `SubtermSplit1`,
        // moves (x,y) into solvedSubterms, and re-adds (x,y) into
        // posSubterms via the SubtermD arm's `addSubterm` (the next
        // simplify drops it again via `posSubterms \ solvedSubterms`).
        assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "SubtermSplit1"));
        assert_eq!(r.sys.subterm_store.subterms.len(), 1);
        assert_eq!(r.sys.subterm_store.solved_subterms.len(), 1);
        assert!(r.sys.goals.iter().any(|(g, s)| matches!(g, Goal::Subterm(_)) && s.solved));
    }

    #[test]
    fn solve_subterm_self_is_contradictory() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(v));
        sys.invalidate_max_var_idx_cache();
        sys.subterm_store_mut().add(tx.clone(), tx.clone());
        let mut r = Reduction::new(&ctx, sys);
        let out = r.solve_subterm_goal(&(tx.clone(), tx));
        assert!(matches!(out, GoalCases::Contradictory));
        assert!(r.sys.subterm_store.contradictory);
    }

    /// When the goal's existing node already has the matching action,
    /// `solve_action_goal` emits `GoalCases::LinearNamed(rule_case_name)`
    /// rather than bare `Linear` — mirrors HS `solveAction`'s `Just ru ->
    /// ... return ru` arm (Goals.hs) whose surrounding `showRuleCaseName
    /// <$>` (Goals.hs:218-261, see line 257) unconditionally emits the rule's case name.
    #[test]
    fn solve_action_goal_existing_node_with_action_is_linear_named() {
        let ctx = match ctx() { Some(c) => c, None => return };
        // Build a system with a node already labelled by a rule that
        // produces the action `Out(x)`.
        let mut sys = System::empty();
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let fa = crate::fact::out_fact(tx);
        let ru: crate::rule::RuleACInst = crate::rule::Rule::new(
            crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend),
            vec![],
            vec![],
            vec![fa.clone()],
        );
        sys.add_node(i.clone(), ru);
        sys.add_goal(Goal::Action(i.clone(), fa.clone()));
        let mut r = Reduction::new(&ctx, sys);
        let out = r.solve_action_goal(&i, &fa);
        // Post-Root-D: `LinearNamed(rule_case_name)`. The case name must
        // be present (showRuleCaseName ru) for the proof tree to render
        // `case <name>` correctly.  Accept any non-empty name string.
        match &out {
            GoalCases::LinearNamed(name) => assert!(
                !name.is_empty(), "rule case name must be non-empty"),
            other => panic!("expected GoalCases::LinearNamed, got {:?}", other),
        }
        assert!(r.sys.goals.iter().any(|(g, s)|
            matches!(g, Goal::Action(_, _)) && s.solved));
    }

    #[test]
    fn solve_action_goal_no_node_no_rules_is_contradictory() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let fa = crate::fact::out_fact(tx);
        let out = r.solve_action_goal(&i, &fa);
        // No rules in the context → no candidates.
        assert!(matches!(out, GoalCases::Contradictory));
    }

    #[test]
    fn solve_action_goal_no_node_with_matching_rule_unifies() {
        let ctx_no = match ctx() { Some(c) => c, None => return };
        // Build a context with one rule that has an Out(y) action.
        let v = tamarin_term::lterm::LVar::new(
            "y", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let fact_y = crate::fact::out_fact(ty);
        let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
            crate::rule::ProtoRuleEInfo::standard("Send"),
            vec![],
            vec![],
            vec![fact_y],
        );
        let open = crate::theory::OpenProtoRule::new(rule);
        let mut ctx2 = ctx_no.clone();
        ctx2.rules = vec![open];
        let mut r = Reduction::new(&ctx2, System::empty());
        // Goal: Out(x) at fresh node i.
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v2 = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
        let fa = crate::fact::out_fact(tx);
        let out = r.solve_action_goal(&i, &fa);
        // One matching rule with one matching action ⇒ LinearNamed
        // (the rule name); node added in-place to r.sys.
        assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "Send"),
            "expected LinearNamed(\"Send\"), got {:?}", out);
        assert_eq!(r.sys.nodes.len(), 1);
        assert_eq!(r.sys.nodes[0].0, i);
    }

    #[test]
    fn solve_premise_goal_no_user_rules_uses_intruder() {
        // With the intruder rules wired into ProofContext, an `In(x)`
        // premise can be discharged via `ISend` even when no user
        // rules exist. Tests that the intruder-rule fallback works.
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let fa = crate::fact::in_fact(tx);
        let p = (i, crate::rule::PremIdx(0));
        let out = r.solve_premise_goal(&p, &fa);
        // ISend supplier can satisfy the In(x) premise → LinearNamed.
        assert!(matches!(out, GoalCases::LinearNamed(_)),
            "expected LinearNamed, got {:?}", out);
    }

    #[test]
    fn solve_premise_goal_no_user_rules_unmatchable_fact_is_contradictory() {
        // Use a fact tag that no intruder rule produces (e.g. a
        // user-defined linear `Foo(x)` fact in an empty context).
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let fa = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(
                crate::fact::Multiplicity::Linear, "Foo", 1),
            vec![tx]);
        let p = (i, crate::rule::PremIdx(0));
        let out = r.solve_premise_goal(&p, &fa);
        assert!(matches!(out, GoalCases::Contradictory));
    }

    #[test]
    fn solve_premise_goal_with_matching_rule_inserts_edge() {
        let base = match ctx() { Some(c) => c, None => return };
        // Rule that produces an Out(y) conclusion.
        let v = tamarin_term::lterm::LVar::new(
            "y", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let conc_y = crate::fact::out_fact(ty);
        let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
            crate::rule::ProtoRuleEInfo::standard("Producer"),
            vec![],
            vec![conc_y],
            vec![],
        );
        let open = crate::theory::OpenProtoRule::new(rule);
        let mut ctx2 = base.clone();
        ctx2.rules = vec![open];
        let mut r = Reduction::new(&ctx2, System::empty());
        // Premise: Out(x) at node i, premise idx 0.
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 5);
        let v2 = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
        let fa = crate::fact::out_fact(tx);
        let p = (i.clone(), crate::rule::PremIdx(0));
        let out = r.solve_premise_goal(&p, &fa);
        // Single matching rule → LinearNamed("Producer"); node + edge
        // applied in-place to r.sys.
        assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "Producer"),
            "expected LinearNamed(\"Producer\"), got {:?}", out);
        assert_eq!(r.sys.nodes.len(), 1);
        assert_eq!(r.sys.edges.len(), 1);
        assert_eq!(r.sys.edges[0].tgt, p);
    }

    #[test]
    fn solve_premise_goal_kd_fact_inserts_irecv_chain() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let fa = crate::fact::kd_fact(tx);
        let p = (i, crate::rule::PremIdx(0));
        let _out = r.solve_premise_goal(&p, &fa);
        // KD branch inserts IRecv + Chain goal; the Out(mLearn) premise
        // is recursively solved inline (Haskell's solvePremise behaviour)
        // so it does NOT remain as a queued Premise goal.  The recursive
        // solve picks some producer (or Contradictory if there's none in
        // an empty test ctx); the structural invariants we check here are
        // just the IRecv node and chain goal.
        assert!(r.sys.nodes.iter().any(|(_, ru)|
            matches!(ru.info, crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv))));
        assert!(r.sys.goals.iter().any(|(g, _)| matches!(g, Goal::Chain(_, _))));
    }

    #[test]
    fn solve_chain_goal_missing_node_is_contradictory() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let j = tamarin_term::lterm::LVar::new(
            "j", tamarin_term::lterm::LSort::Node, 0);
        let c = (i, crate::rule::ConcIdx(0));
        let p = (j, crate::rule::PremIdx(0));
        let out = r.solve_chain_goal(&c, &p);
        assert!(matches!(out, GoalCases::Contradictory));
    }

    #[test]
    fn solve_chain_goal_compatible_facts_inserts_edge() {
        let ctx = match ctx() { Some(c) => c, None => return };
        // Build two nodes whose conc/prem facts are compatible.
        let mut sys = System::empty();
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let j = tamarin_term::lterm::LVar::new(
            "j", tamarin_term::lterm::LSort::Node, 0);
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        // Node i conclusion: KD(x).
        let conc_kd = crate::fact::kd_fact(tx.clone());
        let ru_i: crate::rule::RuleACInst = crate::rule::Rule::new(
            crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv),
            vec![],
            vec![conc_kd],
            vec![],
        );
        sys.add_node(i.clone(), ru_i);
        // Node j premise: KD(x).
        let prem_kd = crate::fact::kd_fact(tx);
        let ru_j: crate::rule::RuleACInst = crate::rule::Rule::new(
            crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend),
            vec![prem_kd],
            vec![],
            vec![],
        );
        sys.add_node(j.clone(), ru_j);
        let c = (i, crate::rule::ConcIdx(0));
        let p = (j, crate::rule::PremIdx(0));
        sys.add_goal(Goal::Chain(c.clone(), p.clone()));
        let mut r = Reduction::new(&ctx, sys);
        let out = r.solve_chain_goal(&c, &p);
        // Compatible facts → LinearNamed (rule-named) with edge added
        // and chain goal marked solved in-place.
        assert!(matches!(out, GoalCases::LinearNamed(_)),
            "expected LinearNamed, got {:?}", out);
        assert_eq!(r.sys.edges.len(), 1);
        assert!(r.sys.goals.iter().any(|(g, s)|
            matches!(g, Goal::Chain(_, _)) && s.solved));
    }

    #[test]
    fn insert_atom_action_creates_action_goal() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        use tamarin_parser::ast::{Atom, Fact, SortHint, Term, VarSpec};
        let mkvar = |n: &str, sort: SortHint| Term::Var(VarSpec {
            name: n.to_string(), idx: 0, sort, typ: None,
        });
        let action = Atom::Action(
            Fact {
                persistent: false,
                annotations: Vec::new(),
                name: "Setup".into(),
                args: vec![mkvar("k", SortHint::Msg)],
            },
            mkvar("i", SortHint::Node),
        );
        let ok = r.insert_atom(&action);
        assert!(ok);
        assert_eq!(r.sys.goals.len(), 1);
        assert!(matches!(&r.sys.goals[0].0, Goal::Action(_, fact)
            if fact.tag == crate::fact::FactTag::Proto(
                crate::fact::Multiplicity::Linear, "Setup", 1)));
    }

    #[test]
    fn insert_atom_less_creates_less_atom() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
        let mkvar = |n: &str| Term::Var(VarSpec {
            name: n.to_string(), idx: 0, sort: SortHint::Node, typ: None,
        });
        let less = Atom::Less(mkvar("i"), mkvar("j"));
        let ok = r.insert_atom(&less);
        assert!(ok);
        assert_eq!(r.sys.less_atoms.len(), 1);
    }

    #[test]
    fn insert_atom_last_sets_last_atom() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
        let v = Term::Var(VarSpec {
            name: "i".into(), idx: 0, sort: SortHint::Node, typ: None,
        });
        let last = Atom::Last(v);
        assert!(r.insert_atom(&last));
        assert!(r.sys.last_atom.is_some());
    }

    #[test]
    fn solve_action_with_fresh_premise_adds_fresh_supplier() {
        let base = match ctx() { Some(c) => c, None => return };
        // Setup-like rule: [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
        let v = tamarin_term::lterm::LVar::new(
            "k", tamarin_term::lterm::LSort::Fresh, 0);
        use tamarin_term::vterm::Lit;
        let tk: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let prem = crate::fact::fresh_fact(tk.clone());
        let act = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(
                crate::fact::Multiplicity::Linear, "Setup", 1),
            vec![tk.clone()]);
        let conc = crate::fact::out_fact(tk);
        let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
            crate::rule::ProtoRuleEInfo::standard("Setup"),
            vec![prem],
            vec![conc],
            vec![act],
        );
        let open = crate::theory::OpenProtoRule::new(rule);
        let mut ctx2 = base.clone();
        ctx2.rules = vec![open];
        let mut r = Reduction::new(&ctx2, System::empty());

        // Goal: Setup(x) at fresh node i.
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let v2 = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 1);
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
        let fa = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(
                crate::fact::Multiplicity::Linear, "Setup", 1),
            vec![tx]);
        let out = r.solve_action_goal(&i, &fa);
        // LinearNamed("Setup") with in-place mutation: 2 nodes (Setup
        // instance + Fresh supplier) and 1 edge in r.sys.
        assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "Setup"),
            "expected LinearNamed(\"Setup\"), got {:?}", out);
        assert_eq!(r.sys.nodes.len(), 2,
            "expected 2 nodes (Setup + Fresh supplier), got {}",
            r.sys.nodes.len());
        assert_eq!(r.sys.edges.len(), 1, "expected 1 edge");
    }

    #[test]
    fn while_changing_terminates() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let mut count = 0;
        r.while_changing(|red| {
            count += 1;
            if count < 3 {
                let v = tamarin_term::lterm::LVar::new(
                    "k", tamarin_term::lterm::LSort::Msg, count as u64);
                let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
                red.insert_goal(Goal::Action(v, f));
                ChangeIndicator::Changed
            } else {
                ChangeIndicator::Unchanged
            }
        });
        assert!(count >= 3);
    }

    // =========================================================================
    // Haskell-faithfulness invariants for case-naming.
    //
    // Mirrors Haskell's `casName` (Reduction.hs) which uses 1-INDEXED
    // `case_<n>` for generic case labels.  Off-by-one here makes
    // `distinguish` (ProofMethod.hs:283-340, see line 308) disambiguate against the
    // wrong sibling suffix and the proof skeleton drifts.
    // =========================================================================

    /// `default_case_name(i)` produces `case_<i+1>` — 1-INDEXED.
    ///
    /// Mirrors Haskell's `casName` convention; an off-by-one here regresses
    /// the `case split` cluster.  Disjunction-driven case
    /// labels (`case_1`, `case_2`, ...) must match the Haskell printer
    /// exactly or proof-skeleton diffs report spurious mismatches.
    #[test]
    fn default_case_name_is_one_indexed() {
        assert_eq!(default_case_name(0), "case_1");
        assert_eq!(default_case_name(1), "case_2");
        assert_eq!(default_case_name(9), "case_10");
        assert_eq!(default_case_name(99), "case_100",
                   "three-digit suffix renders without padding");
    }

    /// `default_case_name(i) != default_case_name(j)` for i != j —
    /// pairwise distinct.  This guards against accidentally returning
    /// "case_1" for every i (e.g. a hardcoded constant slipped in).
    #[test]
    fn default_case_name_is_injective() {
        let n = 25usize;
        let names: Vec<String> = (0..n).map(default_case_name).collect();
        let unique: std::collections::BTreeSet<&String> = names.iter().collect();
        assert_eq!(unique.len(), n,
            "default_case_name must produce {} distinct names; got {}",
            n, unique.len());
    }

    /// Build a `∀[].[Less #i #j].⊥` GGuarded value — the negated-
    /// `Less`-of-node-ids idiom HS calls `markAsSolved`+decompose on
    /// (Reduction.hs:461-486).
    fn neg_less_node_universal(i_name: &str, j_name: &str) -> Guarded {
        use crate::guarded::{GAtom, atom_to_gatom_free, Quant};
        use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
        let mkvar = |n: &str| Term::Var(VarSpec {
            name: n.to_string(), idx: 0, sort: SortHint::Node, typ: None,
        });
        let guard: GAtom = atom_to_gatom_free(&Atom::Less(mkvar(i_name), mkvar(j_name)));
        Guarded::GGuarded {
            qua: Quant::All,
            vars: Vec::new(),
            guards: vec![guard],
            body: Box::new(crate::guarded::gfalse()),
        }
    }

    /// HS-faithful `markAsSolved = when mark $ modM sSolvedFormulas
    /// $ S.insert fm` (Reduction.hs:424-491, see line 491).  Children of a Conj/Ex body
    /// recurse via `insert' False`, so a negated-atom universal that
    /// arrives transitively MUST NOT push into `solved_formulas`.
    ///
    /// The four `solved_formulas.push` sites (Less-node-id, Eq-node-id,
    /// Last, Subterm CR-rules) are gated on `mark`.
    /// This test exercises the Less-node-id arm:
    ///   - `insert_formula_inner(_, mark=false)` must leave
    ///     `solved_formulas` untouched.
    ///   - `insert_formula_inner(_, mark=true)` (the top-level
    ///     `insert_formula` entrypoint) must push the formula.
    ///     Both calls produce the same decomposition (`#i = #j ∨ #j < #i`).
    #[test]
    fn insert_formula_negated_less_mark_false_does_not_push_solved() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let g = neg_less_node_universal("i", "j");
        assert!(r.sys.solved_formulas.is_empty(),
            "precondition: solved_formulas starts empty");
        // mark=false (the Conj/Ex-body-recursion case).
        r.insert_formula_inner(g.clone(), false);
        assert!(!crate::guarded::stores_contains(&r.sys.solved_formulas, &g),
            "mark=false MUST NOT push the negated-Less universal into \
             solved_formulas — HS `markAsSolved` is `when mark $ ...` \
             (Reduction.hs:491).  Pre-fix RS pushed unconditionally, \
             bumping HS's sSolvedFormulas-count-3 to RS's count-4 on \
             Yubikey slightly_weaker_invariant.");
    }

    #[test]
    fn insert_formula_negated_less_mark_true_pushes_solved() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut r = Reduction::new(&ctx, System::empty());
        let g = neg_less_node_universal("i", "j");
        // mark=true (the top-level entrypoint).
        r.insert_formula_inner(g.clone(), true);
        assert!(crate::guarded::stores_contains(&r.sys.solved_formulas, &g),
            "mark=true (top-level `insert_formula`) MUST push the \
             negated-Less universal into solved_formulas — \
             HS `markAsSolved` fires (Reduction.hs:491).");
    }
}
