// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Proof-search driver — port of the `Theory.Proof` step loop.
//!
//! In Haskell, a proof tree (`LTreeProof`) grows by repeatedly:
//! 1. Picking a `ProofMethod` via the heuristic ranking.
//! 2. Executing it to produce zero or more child sub-systems.
//! 3. Recursing on each child.
//!
//! `candidate_methods` builds the FULL heuristic-ranked candidate list
//! (Simplify + every open goal as `SolveGoal`, plus `Induction` in the
//! initial state per `pcUseInduction`) and picks the first method whose
//! `exec_proof_method` succeeds — mirroring `rankProofMethods` /
//! `execMethods`.  The driver dispatches on `ProofContext::cut`: the
//! default runs iterative-deepening DFS with memoized re-expansion
//! (only `Sorry: depth limit` leaves are re-run across iterations),
//! optional per-child parallel expansion, oracle handling, and
//! solved-path extraction — a port of HS's `cutOnSolvedDFS`; the
//! `--stop-on-trace=seqdfs` strategy instead runs a single serial
//! unbounded-depth pass — HS's `cutOnSolvedSingleThreadDFS` (see
//! `run_proof_search`).
//!
//! Under the default `Dfs` strategy, termination is bounded by the
//! ID-DFS depth alone (`MAX_DEPTH`,
//! doubling from 4) — `cutOnSolvedDFS` (Theory/Proof.hs:854-884) has only
//! `dMax` and no step/node budget, doubling `dMax` from 4 with no
//! upper bound.  HS terminates because it deepens over a finite proof
//! tree (any TERMINATING lemma's tree is finite, so once `dMax`
//! exceeds its depth `findSolved` returns `NoSolution` and HS stops);
//! the effective bound is the actual proof depth, tens-to-low-hundreds
//! of single-path steps for any real lemma.  We mirror the unbounded
//! doubling, retaining only a far-out cap (`cap = usize::MAX / 4`)
//! as a Rust-only loop-termination guard so a genuinely
//! non-terminating proof strategy aborts rather than overflows.  No
//! realistic Tamarin proof approaches this cap, so it never flips a
//! verdict.  The per-lemma wall-clock deadline is a Rust-only
//! addition, OFF by default (opt in via `TAM_PROVE_DEADLINE_MS`); see
//! `proof_deadline`.

use std::collections::BTreeMap;

use crate::constraint::solver::context::{CutStrategy, ProofContext};
use crate::constraint::solver::goals::RankingError;
use crate::constraint::solver::proof_method::{
    exec_proof_method, is_finished, ProofMethod, Result as MethodResult,
};
use crate::constraint::system::System;

/// One node in the proof tree.
#[derive(Debug, Clone)]
pub struct ProofNode {
    pub method: ProofMethod,
    pub sys: System,
    pub children: BTreeMap<String, ProofNode>,
    pub status: NodeStatus,
    /// Whether this step carries a valid constraint-system annotation
    /// (HS `psInfo step == Just sys`).  `false` mirrors HS's
    /// `Nothing`-annotated steps produced by `checkProof`
    /// (Theory/Proof.hs:447-467, see line 467) when a stored skeleton step could not be
    /// replayed; `prettyIncrementalProof` (ProofSkeleton.hs:80-84) then
    /// appends `/* unannotated */`.  Defaults to `true` for every
    /// freshly-searched / successfully-replayed node.
    pub annotated: bool,
}

/// What's the proof-tree node currently saying?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeStatus {
    /// Not yet finished — has open children to explore.
    Open,
    /// All branches reached `Solved`.
    Solved,
    /// At least one branch reached `Contradictory(_)`.
    Contradictory,
    /// At least one branch reached `Unfinishable`.
    Unfinishable,
    /// Gave up on at least one branch (`sorry`): depth limit, deadline,
    /// `--bound` cut, or no applicable method.
    Sorry,
}

/// Map a terminal `is_finished` result to its leaf [`NodeStatus`].
pub fn node_status_of(r: &MethodResult) -> NodeStatus {
    match r {
        MethodResult::Solved => NodeStatus::Solved,
        MethodResult::Contradictory(_) => NodeStatus::Contradictory,
        MethodResult::Unfinishable => NodeStatus::Unfinishable,
    }
}

impl NodeStatus {
    /// Aggregate child statuses using HS `ProofStatus` precedence.
    pub fn combine(self, other: Self) -> Self {
        use NodeStatus::*;
        match (self, other) {
            (Solved, _) | (_, Solved) => Solved,
            (Sorry, _) | (_, Sorry) => Sorry,
            (Unfinishable, _) | (_, Unfinishable) => Unfinishable,
            (Contradictory, _) | (_, Contradictory) => Contradictory,
            (Open, Open) => Open,
        }
    }
}

/// True for a leaf parked at the ID-DFS depth limit: a `Sorry: depth
/// limit` method with `Sorry` status.  These are the frontier stubs
/// `re_expand_depth_limited` re-runs `expand` on at the next (deeper)
/// iteration — the Rust analog of Haskell's unforced `cutOnSolvedDFS`
/// thunks — so `expand` also keeps their `sys` alive for that re-run.
fn is_depth_limited(node: &ProofNode) -> bool {
    matches!(&node.method, ProofMethod::Sorry(Some(msg)) if msg == "depth limit")
        && matches!(node.status, NodeStatus::Sorry)
}

/// HS `ProofStatus` (Theory/Proof.hs:397-407) — the aggregate status of a WHOLE
/// proof tree, used to decide the lemma verdict.  Unlike the per-node
/// [`NodeStatus`], this folds over every step (HS `getProofStatus =
/// foldMap proofStepStatus`) and therefore correctly ABSORBS verbatim
/// (`/* unannotated */`) subtrees: a stale stored-proof branch kept
/// verbatim is `Undetermined`, which the Semigroup overrides with the
/// `Complete` of the freshly-proved siblings — so a part-replayed proof
/// still reports `verified`, matching HS.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofStatus {
    Undetermined,
    Complete,
    Incomplete,
    TraceFound,
    Unfinishable,
    Invalidated,
}

impl ProofStatus {
    /// HS `ProofStatus` Semigroup (Theory/Proof.hs:409-420): precedence
    /// `Invalidated > TraceFound > Incomplete > Unfinishable > Complete >
    /// Undetermined`.
    pub fn combine(self, other: ProofStatus) -> ProofStatus {
        use ProofStatus::*;
        match (self, other) {
            (Invalidated, _) | (_, Invalidated) => Invalidated,
            (TraceFound, _) | (_, TraceFound) => TraceFound,
            (Incomplete, _) | (_, Incomplete) => Incomplete,
            (Unfinishable, _) | (_, Unfinishable) => Unfinishable,
            (Complete, _) | (_, Complete) => Complete,
            (Undetermined, Undetermined) => Undetermined,
        }
    }

    pub fn from_step(method: &ProofMethod, annotated: bool) -> Self {
        if !annotated {
            return Self::Undetermined;
        }
        match method {
            ProofMethod::Finished(MethodResult::Solved) => Self::TraceFound,
            ProofMethod::Finished(MethodResult::Unfinishable) => Self::Unfinishable,
            ProofMethod::Sorry(_) => Self::Incomplete,
            ProofMethod::Invalidated => Self::Invalidated,
            _ => Self::Complete,
        }
    }
}

/// HS `proofStepStatus` (Theory/Proof.hs:427-433): the status of ONE node.
/// A node with no system annotation (`annotated == false`, HS `Nothing`)
/// is `Undetermined` REGARDLESS of its method; otherwise it is keyed on
/// the node's own method (NOT its aggregated `NodeStatus`).
fn step_status(node: &ProofNode) -> ProofStatus {
    ProofStatus::from_step(&node.method, node.annotated)
}

/// HS `getProofStatus` = `foldMap proofStepStatus` over every node in the
/// tree.  This is the source of the lemma verdict (see `run_batch`).
pub fn proof_status(node: &ProofNode) -> ProofStatus {
    let mut s = step_status(node);
    for c in node.children.values() {
        s = s.combine(proof_status(c));
    }
    s
}

/// HS `proofSystems` (Batch.hs:284-288): every solved constraint system
/// in the tree, paired with its proof path (the case names from the
/// root, outermost first).
///
/// ```text
/// proofSystems (LNode (ProofStep (Finished Solved) (Just rootSystem)) _) = [([], rootSystem)]
/// proofSystems (LNode (ProofStep _ _) children) =
///   [(l : ls, system) | (l, subProof) <- M.toList children
///                     , (ls, system) <- proofSystems subProof ]
/// ```
///
/// The first equation matches REGARDLESS of children (`_`) and does not
/// recurse into them.  `Just rootSystem` is RS `annotated == true`: a
/// `Finished(Solved)` step whose annotation was lost (HS `Nothing`,
/// printed `/* unannotated */`) falls through to the second equation and
/// is recursed into like any other node.  `M.toList` is ascending
/// `CaseName` order == `BTreeMap<String>` iteration order.
///
/// The systems only survive a `--prove` run when the process-wide
/// [`SysRetention`] was raised to at least
/// [`KeepSolved`](SysRetention::KeepSolved) beforehand; on the stored-proof
/// replay path (`replay::check_and_extend_lemma_in_session`) they are
/// always live.
///
/// The tree is taken BY VALUE: the only caller reaches here once the proof
/// body has been rendered, so the solved `System`s are moved out rather
/// than cloned.
pub fn into_solved_systems(node: ProofNode) -> Vec<(Vec<String>, System)> {
    let mut out = Vec::new();
    let mut path = Vec::new();
    collect_solved_systems_owned(node, &mut path, &mut out);
    out
}

fn collect_solved_systems_owned(
    node: ProofNode,
    path: &mut Vec<String>,
    out: &mut Vec<(Vec<String>, System)>,
) {
    if matches!(node.method, ProofMethod::Finished(MethodResult::Solved)) && node.annotated {
        out.push((path.clone(), node.sys));
        return;
    }
    for (case, child) in node.children {
        path.push(case);
        collect_solved_systems_owned(child, path, out);
        path.pop();
    }
}

// --- Cached kill-switch / debug env flags -------------------------------
// `expand`/`expand_inner` run once per proof-tree node (thousands of
// times per lemma); these env vars are constant for the process, so cache
// each behind a `OnceLock<bool>` (mirroring `trace::flag()`).
// `TAM_RS_KEEP_SYS` is `var_os`-presence, cached as the affirmative
// `keep_sys_env()`.

/// How much of a proof tree keeps its per-node constraint `System` once
/// [`expand`] has returned — a process-wide switch, since the three front
/// ends want three different answers:
///
/// * [`DropAll`](SysRetention::DropAll) — `--prove`, which never reprints
///   a per-node system in its text proof and so trades them for a low
///   peak RSS.
/// * [`KeepSolved`](SysRetention::KeepSolved) — batch trace output
///   (`--output-dot` / `--output-json`), whose HS `outputTraces`
///   (Batch.hs:252-288) reads exactly the
///   `ProofStep (Finished Solved) (Just sys)` nodes and no others.  The
///   retained systems are HS `outputTraces`' selector set, held for the
///   whole file (moved into `trace_systems`, freed after
///   `write_output_traces`), so peak RSS grows with the file's total
///   solved systems.  `extract_solved_path` (HS `extractSolved`) bounds
///   that to one per lemma ONLY on the freshly-searched `Dfs`/`SeqDfs`
///   path — a replayed stored proof or a non-DFS `--stop-on-trace` keeps
///   every solved node's system.
/// * [`KeepAll`](SysRetention::KeepAll) — the interactive web server,
///   which renders the annotated constraint system + applicable proof
///   methods at every proof path (HS keeps a `Just System` on every
///   `IncrementalProof` node).
///
/// A `Sorry: depth limit` frontier stub keeps its system under every
/// policy: the next ID-DFS iteration re-expands it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SysRetention {
    /// Drop every expanded node's `System`.
    DropAll = 0,
    /// Retain the `System` of `Finished(Solved)` nodes only.
    KeepSolved = 1,
    /// Retain every node's `System`.
    KeepAll = 2,
}

impl SysRetention {
    /// Inverse of the `#[repr(u8)]` discriminant, for [`SYS_RETENTION`].
    #[inline]
    fn from_u8(v: u8) -> SysRetention {
        match v {
            0 => SysRetention::DropAll,
            1 => SysRetention::KeepSolved,
            _ => SysRetention::KeepAll,
        }
    }
}

/// The process-wide [`SysRetention`], held as its discriminant.  Default
/// [`SysRetention::DropAll`] → CLI behaviour unchanged; the interactive
/// server (at startup) and the batch trace writers (before the first
/// lemma) raise it via [`set_sys_retention`].
static SYS_RETENTION: std::sync::atomic::AtomicU8 =
    std::sync::atomic::AtomicU8::new(SysRetention::DropAll as u8);

/// Set the process-wide `System` retention policy.  Call before any
/// `run_proof_search`.
pub fn set_sys_retention(policy: SysRetention) {
    SYS_RETENTION.store(policy as u8, std::sync::atomic::Ordering::Relaxed);
}

/// The policy in force: [`SYS_RETENTION`], raised to
/// [`SysRetention::KeepAll`] by the `TAM_RS_KEEP_SYS` env presence
/// (diagnostic).
#[inline]
fn sys_retention() -> SysRetention {
    if keep_sys_env() {
        return SysRetention::KeepAll;
    }
    SysRetention::from_u8(SYS_RETENTION.load(std::sync::atomic::Ordering::Relaxed))
}

#[inline]
fn keep_sys_env() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var_os("TAM_RS_KEEP_SYS").is_some())
}

/// Serialises the tests that write [`SYS_RETENTION`] against each other:
/// the slot is process-wide, and a policy stored mid-search changes what
/// a concurrently running proof retains.
#[cfg(test)]
pub(crate) static SYS_RETENTION_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Per-child parallel expansion is ON by default;
/// `TAM_RS_DISABLE_PARALLEL_EXPAND=1` forces serial sibling expansion
/// (debug escape hatch).  Output-neutrality depends on every worker
/// closure seeding its thread-locals from the fan-out preamble's
/// snapshots: a stolen worker thread starts with the defaults.
#[inline]
fn disable_parallel_expand() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DISABLE_PARALLEL_EXPAND")
}

/// Per-lemma wall-clock cap on `run_proof_search`. This is a Rust-only,
/// opt-in cap (`TAM_PROVE_DEADLINE_MS`) with NO Haskell counterpart — HS
/// has no `--prove-timeout`-style flag. It exists so that when the search
/// tree branches faster than CR-rules can prune (e.g. with a richer
/// signature) a corpus sweep can mark the lemma `Sorry` rather than spin
/// forever. It defaults to an effectively-infinite deadline so the default
/// behaviour is HS-faithful (no cutoff).
///
/// HS-faithful: HS has NO per-lemma wall-clock deadline — its iterative
/// deepening runs to completion.  So by DEFAULT we apply NO cutoff either
/// (a far-future deadline that never fires); under the default `Dfs`
/// strategy termination is still guaranteed by the ID-DFS depth cap
/// (`MAX_DEPTH`), while `seqdfs` has no depth cut at all (like its
/// HS counterpart — see `run_proof_search`).  A cutoff is
/// applied ONLY when the caller explicitly opts in via the
/// `TAM_PROVE_DEADLINE_MS` env var (e.g. corpus sweeps that want to bound
/// per-lemma wall time) or, for one thread only, via
/// [`ProofDeadlineGuard`].
fn proof_deadline() -> std::time::Instant {
    match deadline_cap_ms() {
        Some(ms) => std::time::Instant::now() + std::time::Duration::from_millis(ms),
        // No override → run unbounded (faithful to HS).  ~10 years is
        // effectively infinite and safe against `Instant` overflow.
        None => std::time::Instant::now() + std::time::Duration::from_secs(10 * 365 * 24 * 3600),
    }
}

thread_local! {
    /// Thread-scoped wall-clock cap for the searches this thread starts,
    /// installed by [`ProofDeadlineGuard`].  Takes precedence over the
    /// `TAM_PROVE_DEADLINE_MS` env var; `None` (the default) falls back
    /// to it.
    static DEADLINE_CAP_MS: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
}

/// The wall-clock cap in force for a search started on THIS thread: the
/// [`ProofDeadlineGuard`] override if one is installed, else the
/// `TAM_PROVE_DEADLINE_MS` env var, else `None` (unbounded).
fn deadline_cap_ms() -> Option<u64> {
    DEADLINE_CAP_MS.with(|c| c.get()).or_else(|| {
        std::env::var("TAM_PROVE_DEADLINE_MS")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
    })
}

/// RAII guard installing a wall-clock cap on the searches started by the
/// current thread, restoring the previous cap on drop.
///
/// Callers that need to bound a nested, self-contained prove (the message
/// derivation check's per-variable probes) must use this rather than
/// setting `TAM_PROVE_DEADLINE_MS`: the env var is process-global, so a
/// probe's short cap would also truncate any unrelated `run_proof_search`
/// that another thread happens to start inside the probe's window —
/// silently turning a would-be-`TraceFound` search into a no-trace one.
pub struct ProofDeadlineGuard {
    previous: Option<u64>,
}

impl ProofDeadlineGuard {
    /// Cap searches started on this thread at `ms` milliseconds.
    pub fn set_ms(ms: u64) -> Self {
        let previous = DEADLINE_CAP_MS.with(|c| c.replace(Some(ms)));
        ProofDeadlineGuard { previous }
    }
}

impl Drop for ProofDeadlineGuard {
    fn drop(&mut self) {
        DEADLINE_CAP_MS.with(|c| c.set(self.previous));
    }
}

thread_local! {
    /// Thread-local per-search deadline. Set at the start of
    /// `run_proof_search`, queried at the top of `exec_proof_method`
    /// (proof_method.rs) as a per-step entry-guard so wide case
    /// enumeration can short-circuit when the wall-clock cap is hit (the
    /// recursion-only check only fires between successive `expand` calls
    /// — a single `exec_proof_method` enumerating thousands of cases
    /// would otherwise sit unchecked).
    static DEADLINE: std::cell::Cell<Option<std::time::Instant>> =
        const { std::cell::Cell::new(None) };

    /// ID-DFS depth limit for the current iteration.  `usize::MAX` =
    /// no limit (the thread-local's initial/reset value, used outside an
    /// active search, and the fixed value for the whole of a `seqdfs`
    /// search).  Under the default `Dfs` strategy it is set per iteration
    /// in `run_proof_search`'s ID-DFS loop, which always starts at depth 4
    /// and doubles up to the cap.
    static MAX_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };

    /// Set to true by `expand` whenever a node hits `MAX_DEPTH`.  The
    /// top-level loop reads this between iterations to decide whether
    /// to retry with doubled depth.  Mirrors Haskell's `MaybeNoSolution`
    /// sentinel in `cutOnSolvedDFS` (Theory/Proof.hs:855-877).
    static DEPTH_LIMIT_HIT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };

    /// `--bound=N` proof-depth bound — HS `boundProofDepth`
    /// (Theory/Proof.hs:336-344#boundProofDepth), applied by `runAutoProver`'s
    /// `maybe id boundProver (apBound p)` (Theory/Proof.hs:730-750#runAutoProver): every
    /// node at depth `N` from the search root is replaced by a
    /// `sorry /* bound N hit */` leaf.  `usize::MAX` = no bound (HS
    /// `apBound = Nothing`, the default).  Unlike `MAX_DEPTH` this is
    /// fixed for the whole search, not an ID-DFS iteration variable, and
    /// a bound-sorry is FINAL — it never sets `DEPTH_LIMIT_HIT` and is
    /// never re-expanded, so the deepening loops terminate once the
    /// whole frontier is bound-cut.
    static PROOF_BOUND: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };

    /// Absolute proof depth represented by the root of a focused search.
    static RANKING_DEPTH_OFFSET: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// True iff the current search is past its wall-clock deadline.
pub fn deadline_reached() -> bool {
    DEADLINE.with(|d| {
        d.get()
            .map(|t| std::time::Instant::now() >= t)
            .unwrap_or(false)
    })
}

struct SearchTlsState {
    deadline: Option<std::time::Instant>,
    max_depth: usize,
    depth_limit_hit: bool,
    proof_bound: usize,
    ranking_depth_offset: usize,
}

fn replace_search_tls(state: SearchTlsState) -> SearchTlsState {
    SearchTlsState {
        deadline: DEADLINE.with(|cell| cell.replace(state.deadline)),
        max_depth: MAX_DEPTH.with(|cell| cell.replace(state.max_depth)),
        depth_limit_hit: DEPTH_LIMIT_HIT.with(|cell| cell.replace(state.depth_limit_hit)),
        proof_bound: PROOF_BOUND.with(|cell| cell.replace(state.proof_bound)),
        ranking_depth_offset: RANKING_DEPTH_OFFSET
            .with(|cell| cell.replace(state.ranking_depth_offset)),
    }
}

struct SearchTlsGuard {
    previous: Option<SearchTlsState>,
}

impl SearchTlsGuard {
    fn install(state: SearchTlsState) -> Self {
        Self {
            previous: Some(replace_search_tls(state)),
        }
    }
}

impl Drop for SearchTlsGuard {
    fn drop(&mut self) {
        replace_search_tls(self.previous.take().expect("search TLS guard dropped once"));
    }
}

/// Run an iterative-deepening search.  Heuristic: try `Simplify`
/// once, then pick the first ranked open goal each round.
///
/// `proof_bound` is `--bound=N`'s proof-depth bound (HS `apBound`,
/// applied as `boundProofDepth` — see [`PROOF_BOUND`]); pass
/// `usize::MAX` for unbounded (HS `Nothing`, the default).  It is NOT a
/// step budget: HS's `cutOnSolvedDFS` bounds the search purely by
/// the ID-DFS depth `dMax` (`MAX_DEPTH`, described below), the
/// per-lemma wall-clock timeout (`deadline`), and this proof-depth
/// bound.  See the `budget = usize::MAX` note in each strategy arm.
///
/// Returns the root proof node. The final status is the OR of children
/// (Solved if all children solved, Contradictory if any contradictory,
/// etc.) — matching Haskell's notion of "complete" proofs.
///
/// The search strategy is dispatched on `ctx.cut` (HS `apCut`):
/// `CutStrategy::SeqDfs` (HS `cutOnSolvedSingleThreadDFS`) runs a single
/// unbounded-depth serial pass; `CutStrategy::Dfs` (HS `cutOnSolvedDFS`,
/// the default) runs the iterative-deepening DFS described below.
///
/// **Iterative-deepening DFS** — port of Haskell's `cutOnSolvedDFS`
/// (Theory/Proof.hs:854-884).  Starts at `max_depth=4` and doubles up with
/// only the far-out `usize::MAX/4` loop-termination guard (no fixed
/// numeric cap).  At each iteration:
///   1. Expand the tree at the current `MAX_DEPTH`.  On the first
///      iteration this builds the tree from scratch; on subsequent
///      iterations only `depth limit` Sorry leaves are re-expanded
///      (mirroring Haskell's lazy-thunk memoization in
///      `cutOnSolvedDFS`).
///   2. If status is Solved → return immediately (matches Haskell's
///      `Solution path` short-circuit via `<>`).
///   3. If `DEPTH_LIMIT_HIT` was set and depth < cap → double and retry.
///   4. Else (no Solved found, no depth limit hit) → return.
///
/// **Memoization**: Haskell's iter-deep gets free
/// memoization because the proof tree is built lazily — each `prove sys'`
/// thunk fires once when forced, and re-forcing a thunk returns the
/// cached value.  Rust has no laziness, so without memoization each
/// iter-deep iteration rebuilds the entire tree from scratch — visiting
/// 2.3x more nodes than Haskell on NSLPK3.  We mirror Haskell by keeping
/// the tree across iterations and only re-expanding `Sorry: depth limit`
/// leaves (the analog of unforced thunks).
///
/// This makes shorter Solved paths win over longer Solved paths even
/// when the longer path is alphabetically earlier — critical for
/// NSPK3/roles `injective_agree` where Haskell renders `case c_aenc`
/// (shorter) over `case I_2` (alphabetically earlier but deeper).
pub fn run_proof_search(
    ctx: &ProofContext,
    initial: System,
    proof_bound: usize,
) -> Result<ProofNode, RankingError> {
    run_proof_search_at_depth(ctx, initial, proof_bound, 0)
}

pub fn run_proof_search_at_depth(
    ctx: &ProofContext,
    initial: System,
    proof_bound: usize,
    ranking_depth_offset: usize,
) -> Result<ProofNode, RankingError> {
    run_proof_search_at_depth_inner(ctx, initial, proof_bound, ranking_depth_offset)
}

fn run_proof_search_at_depth_inner(
    ctx: &ProofContext,
    initial: System,
    proof_bound: usize,
    ranking_depth_offset: usize,
) -> Result<ProofNode, RankingError> {
    let deadline = proof_deadline();
    let _tls = SearchTlsGuard::install(SearchTlsState {
        deadline: Some(deadline),
        max_depth: usize::MAX,
        depth_limit_hit: false,
        proof_bound,
        ranking_depth_offset,
    });
    let mut root = ProofNode {
        method: ProofMethod::Sorry(Some("initial".into())),
        sys: initial,
        children: BTreeMap::new(),
        status: NodeStatus::Open,
        annotated: true,
    };
    match ctx.cut {
        CutStrategy::SeqDfs => {
            // HS `cutOnSolvedSingleThreadDFS` (Theory/Proof.hs:795-816):
            // single-thread DFS with NO iterative deepening and NO depth
            // bound.  One unbounded-depth `expand` pass descends the leftmost
            // branch (CaseName order) to completion, short-circuiting on the
            // first solved leaf — the serial branch's `any_solved` early-break
            // (gated below on `CutStrategy::SeqDfs`) mirrors `findSolved`'s
            // `foldMap` over the children map.  `extract_solved_path` below
            // then prunes to that leaf, HS's `extractSolved path prf0`.
            // `MAX_DEPTH = usize::MAX` disables the depth cut entirely, so no
            // branch becomes a `depth limit` Sorry, `DEPTH_LIMIT_HIT` never
            // fires, and no re-expansion is needed.  Like HS (the FIXME at
            // Theory/Proof.hs:793-814) this can fail to terminate on an infinite
            // leftmost branch; the wall-clock `deadline` is the only backstop.
            MAX_DEPTH.with(|m| m.set(usize::MAX));
            DEPTH_LIMIT_HIT.with(|f| f.set(false));
            let mut budget = usize::MAX;
            expand(ctx, &mut root, &mut budget, &deadline, 0)?;
        }
        CutStrategy::Nothing => {
            // HS `CutNothing` → `id` (Theory/Proof.hs:730-750, see line 738): the full DFS proof
            // tree with NO cut and NO stop-on-solved.  Like SeqDfs this is
            // one unbounded-depth serial pass (the serial sibling loop's
            // abort policy below never fires for `Nothing`), and like HS
            // it may not terminate when a branch recurses forever; the
            // wall-clock `deadline` is the only backstop.
            MAX_DEPTH.with(|m| m.set(usize::MAX));
            DEPTH_LIMIT_HIT.with(|f| f.set(false));
            let mut budget = usize::MAX;
            expand(ctx, &mut root, &mut budget, &deadline, 0)?;
        }
        CutStrategy::AfterSorry => {
            // HS `CutAfterSorry` → `cutAfterFirstSorry` (Theory/Proof.hs:987-997).
            // HS's `M.mapAccum go` never forces a lazy subtree past the
            // abort point; the eager mirror is the serial sibling loop's
            // AfterSorry policy (below): the first Solved-or-Sorry child in
            // preorder aborts, and the remaining sibling cases are inserted
            // as bare-`sorry` leaves instead of being expanded — exactly
            // the nodes HS's `go True` rewrites to `Sorry Nothing`.
            MAX_DEPTH.with(|m| m.set(usize::MAX));
            DEPTH_LIMIT_HIT.with(|f| f.set(false));
            let mut budget = usize::MAX;
            expand(ctx, &mut root, &mut budget, &deadline, 0)?;
        }
        CutStrategy::Bfs => {
            // HS `cutOnSolvedBFS` (Theory/Proof.hs:928-955): force the tree one
            // level deeper per round and walk it with `checkLevel`'s
            // threaded state.  `checkLevel 0`'s `M.null cs` guard FORCES
            // each level-`level` node's case map (so a zero-case solve
            // renders as its own `by solve(…)` closure) without forcing
            // the child subtrees — the eager mirror expands with
            // `MAX_DEPTH = level + 1` (level-`level` nodes execute their
            // method; their children are `depth limit` stubs standing in
            // for HS's unforced thunks, and the `checkLevel` walk below
            // never descends past `remaining == 0`, so the stubs never
            // reach the output).  Deepening re-expands only the stub
            // frontier, like the Dfs arm.
            let cap: usize = usize::MAX / 4;
            let mut level: usize = 1;
            loop {
                MAX_DEPTH.with(|m| m.set(level + 1));
                DEPTH_LIMIT_HIT.with(|f| f.set(false));
                let mut budget = usize::MAX;
                if level == 1 {
                    expand(ctx, &mut root, &mut budget, &deadline, 0)?;
                } else {
                    re_expand_depth_limited(ctx, &mut root, &mut budget, &deadline, 0)?;
                }
                // HS's poor-man's logging (Theory/Proof.hs:928-955, see line 934,941) — `trace` to
                // stderr, unconditional.
                eprintln!("searching for attacks at depth: {}", level);
                let mut found = false;
                let mut incomplete = false;
                bfs_check_level(&root, level, &mut found, &mut incomplete, false);
                if found {
                    eprintln!("attack found at depth: {}", level);
                    let mut f2 = false;
                    let mut i2 = false;
                    if let Some(cut_tree) = bfs_check_level(&root, level, &mut f2, &mut i2, true) {
                        root = cut_tree;
                    }
                    break;
                }
                // CompleteProof / UnfinishableProof: nothing was cut at
                // this level — the tree is fully explored; keep it whole.
                if !incomplete {
                    break;
                }
                if std::time::Instant::now() >= deadline {
                    break;
                }
                if level >= cap {
                    break;
                }
                level += 1;
            }
        }
        CutStrategy::Dfs => {
            // HS's `cutOnSolvedDFS` (Theory/Proof.hs:855-861) doubles `dMax` from 4
            // with NO upper bound; we mirror that, keeping only a far-out cap
            // as a loop-termination guard for genuinely non-terminating
            // strategies.  No real Tamarin proof approaches this depth, so the
            // cap never flips a verdict.
            let cap: usize = usize::MAX / 4;
            let mut current_max_depth: usize = 4;
            let mut first_iter = true;
            loop {
                MAX_DEPTH.with(|m| m.set(current_max_depth));
                DEPTH_LIMIT_HIT.with(|f| f.set(false));
                // HS-faithful: `cutOnSolvedDFS` (Theory/Proof.hs:856-863) bounds the
                // search by the ID-DFS depth `dMax` (our `MAX_DEPTH`) and the
                // per-lemma wall-clock timeout ONLY — it has NO step/node
                // budget.  A finite step budget would cut off exploration of
                // *wide* (but correct) trees prematurely — e.g. csf17
                // keylessssl-modified::exists_detect_no_C_compromise, whose
                // witness is reachable but sits beneath a broad fan-out of
                // contradiction branches — turning a Solved exists-trace into
                // Sorry (the loop-breaker count is HS-faithful, so source
                // cases are wide).  So we run unbudgeted as HS does
                // (`proof_bound` cuts by DEPTH, in `expand_inner`, not by
                // step count): `MAX_DEPTH` doubles
                // unbounded (mirroring HS's `dMax`), with only the far-out
                // `cap` (`usize::MAX / 4`) as a loop-termination guard, and
                // `deadline` catching wall-clock runaway.
                let mut budget = usize::MAX;
                if first_iter {
                    expand(ctx, &mut root, &mut budget, &deadline, 0)?;
                    first_iter = false;
                } else {
                    // Re-expand only `Sorry: depth limit` leaves
                    // (Haskell-faithful memoization — the cached tree IS the
                    // proof tree, only the unforced "depth limit" thunks need
                    // (re-)expansion).
                    re_expand_depth_limited(ctx, &mut root, &mut budget, &deadline, 0)?;
                }
                if matches!(root.status, NodeStatus::Solved | NodeStatus::Contradictory) {
                    break;
                }
                if std::time::Instant::now() >= deadline {
                    break;
                }
                let hit_depth = DEPTH_LIMIT_HIT.with(|f| f.get());
                if !hit_depth {
                    // No branch hit the depth limit — going deeper won't help.
                    break;
                }
                if current_max_depth >= cap {
                    // Depth cap reached; accept whatever we have.
                    break;
                }
                current_max_depth = current_max_depth.saturating_mul(2).min(cap);
            }
        }
    }
    // HS-faithful: `cutOnSolvedDFS` / `cutOnSolvedSingleThreadDFS`
    // (Theory/Proof.hs:854-884, 795-816) call `extractSolved path prf0` once a
    // Solved leaf is found, pruning the proof tree to JUST the
    // solved-witness path.  All Contradictory siblings are removed.
    // Without this, Rust's proof_steps count includes failed branches HS
    // prunes — e.g. NSPK3 session_key_setup_possible reports 30 steps vs
    // HS 5.  The other extractors keep their trees: `CutNothing` = `id`,
    // `CutBFS` returns its level-cut tree, `CutAfterSorry` its
    // sorry-stubbed tree.
    if matches!(ctx.cut, CutStrategy::Dfs | CutStrategy::SeqDfs)
        && matches!(root.status, NodeStatus::Solved)
    {
        extract_solved_path(&mut root);
    }
    Ok(root)
}

/// HS `cutOnSolvedBFS`'s `checkLevel` (Theory/Proof.hs:943-955) over the eager
/// level-bounded tree: walk to depth `remaining` in CaseName order,
/// threading `found` (HS TraceFound) and `incomplete` (HS
/// IncompleteProof) exactly as HS's `State ProofStatus` does.  At depth 0:
/// a Solved leaf flips `found`; a node still pending (our
/// `sorry /* depth limit */` frontier mark = HS's node-with-children)
/// becomes `sorry /* bound reached */`, or
/// `sorry /* ignored (attack exists) */` once `found` is set; every other
/// leaf is untouched.  With `build` set the transformed tree is returned
/// (statuses re-rolled); a scan pass (`build = false`) returns `None`.
fn bfs_check_level(
    node: &ProofNode,
    remaining: usize,
    found: &mut bool,
    incomplete: &mut bool,
    build: bool,
) -> Option<ProofNode> {
    if remaining == 0 {
        let solved_leaf = matches!(&node.method, ProofMethod::Finished(MethodResult::Solved));
        if solved_leaf {
            *found = true;
            return build.then(|| node.clone());
        }
        let pending = !node.children.is_empty()
            || matches!(
                &node.method,
                ProofMethod::Sorry(Some(msg)) if msg == "depth limit"
            );
        if pending {
            let msg = if *found {
                "ignored (attack exists)"
            } else {
                *incomplete = true;
                "bound reached"
            };
            return build.then(|| ProofNode {
                method: ProofMethod::Sorry(Some(msg.into())),
                sys: node.sys.clone(),
                children: BTreeMap::new(),
                status: NodeStatus::Sorry,
                annotated: node.annotated,
            });
        }
        return build.then(|| node.clone());
    }
    if node.children.is_empty() {
        return build.then(|| node.clone());
    }
    let mut new_children: BTreeMap<String, ProofNode> = BTreeMap::new();
    for (name, child) in &node.children {
        let t = bfs_check_level(child, remaining - 1, found, incomplete, build);
        if build {
            new_children.insert(
                name.clone(),
                t.expect("bfs_check_level: build pass returned None"),
            );
        }
    }
    build.then(|| {
        let status = rollup_from_children(&new_children);
        ProofNode {
            method: node.method.clone(),
            sys: node.sys.clone(),
            children: new_children,
            status,
            annotated: node.annotated,
        }
    })
}

/// HS-faithful `extractSolved` (Theory/Proof.hs:879-884, the non-diff
/// `cutOnSolvedDFS` variant): walks the proof
/// tree, finds the first Solved-leaf path from root, and prunes all
/// non-path siblings.  Mutates `root` in place.
fn extract_solved_path(root: &mut ProofNode) {
    let mut path: Vec<String> = Vec::new();
    if find_solved_path(root, &mut path) {
        prune_to_path(root, &path);
    }
}

fn find_solved_path(node: &ProofNode, path: &mut Vec<String>) -> bool {
    if matches!(node.status, NodeStatus::Solved) && node.children.is_empty() {
        return true;
    }
    for (label, child) in &node.children {
        path.push(label.clone());
        if find_solved_path(child, path) {
            return true;
        }
        path.pop();
    }
    false
}

fn prune_to_path(node: &mut ProofNode, path: &[String]) {
    if path.is_empty() {
        return;
    }
    let label = &path[0];
    if let Some(mut child) = node.children.remove(label) {
        prune_to_path(&mut child, &path[1..]);
        node.children = BTreeMap::new();
        node.children.insert(label.clone(), child);
    }
}

/// Re-expand only the `Sorry: depth limit` leaves in the existing
/// proof tree, preserving previously-computed subtrees.
///
/// This is the Rust analog of Haskell's lazy-thunk memoization: when
/// `cutOnSolvedDFS` doubles `dMax` and re-walks the proof tree, only
/// the unforced thunks (those past the previous depth limit) actually
/// execute their `prove sys'` body.  Already-forced thunks return
/// cached values.
///
/// Behaviour:
/// - Solved/Contradictory/Unfinishable nodes: already resolved, skip.
/// - Sorry with `"depth limit"` reason: re-expand from scratch at this
///   depth using the (now larger) `MAX_DEPTH`.
/// - Sorry with other reasons (budget, deadline, no method): preserve.
/// - Other nodes: recurse into children, then re-roll up the status.
///
/// Early-break-on-Solved: matches `expand`'s short-circuit semantics —
/// once any sibling is Solved during re-expansion, stop traversing
/// the remaining siblings (Haskell's `foldMap`-with-Solution semigroup).
fn re_expand_depth_limited(
    ctx: &ProofContext,
    node: &mut ProofNode,
    budget: &mut usize,
    deadline: &std::time::Instant,
    depth: usize,
) -> Result<(), RankingError> {
    // Was this node stalled at the depth limit on the previous iteration?
    if is_depth_limited(node) {
        // Re-expand from scratch at this depth.  The deeper `MAX_DEPTH`
        // now lets the recursion go further before stalling again.
        node.method = ProofMethod::Sorry(None);
        node.children = BTreeMap::new();
        node.status = NodeStatus::Open;
        return expand(ctx, node, budget, deadline, depth);
    }
    // Already resolved — return cached subtree.
    if matches!(
        node.status,
        NodeStatus::Solved | NodeStatus::Contradictory | NodeStatus::Unfinishable
    ) {
        return Ok(());
    }
    // Sorry with non-depth-limit reason and no descendants: preserve.
    // (Budget exhausted, deadline, or no-method Sorrys are terminal.)
    if matches!(node.status, NodeStatus::Sorry) && node.children.is_empty() {
        return Ok(());
    }
    // Recurse into children.  Any depth-limited descendant gets
    // re-expanded in place.  Match `expand`'s early-break-on-Solved —
    // except under `Bfs`, whose level walk (like HS `checkLevel`'s
    // `traverse`) forces every sibling regardless of solved ones.
    let early_break = !matches!(ctx.cut, CutStrategy::Bfs);
    let mut found_solved = false;
    for (name, child) in node.children.iter_mut() {
        if early_break && found_solved {
            break;
        }
        if *budget == 0 {
            break;
        }
        if std::time::Instant::now() >= *deadline {
            break;
        }
        // Preserve the full proof-tree path during iterative-deepening
        // re-expansion and restore it even if solver work unwinds.
        let _path = crate::constraint::solver::trace::CasePathGuard::push(name);
        re_expand_depth_limited(ctx, child, budget, deadline, depth + 1)?;
        if matches!(child.status, NodeStatus::Solved) {
            found_solved = true;
        }
    }
    // Re-roll up the parent's status from current children — mirrors
    // `expand_inner`'s `node.status = if any_solved ...` rollup
    // (the `Semigroup ProofStatus` port below).
    if !node.children.is_empty() {
        node.status = rollup_from_children(&node.children);
    }
    Ok(())
}

/// Roll a node's children up into its status, mirroring Haskell's
/// `Semigroup ProofStatus` precedence (`Theory.Proof:409`):
/// `Solved` > `Sorry` > `Unfinishable` > `Contradictory`.  Returns
/// `Sorry` for an empty child set (the defensive fallback both call
/// sites already used); a caller that must leave `status` untouched on
/// empty children guards the call itself.
fn rollup_from_children(children: &BTreeMap<String, ProofNode>) -> NodeStatus {
    let mut any_solved = false;
    let mut any_contra = false;
    let mut any_unfin = false;
    let mut any_sorry = false;
    for child in children.values() {
        match child.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => any_unfin = true,
            NodeStatus::Sorry => any_sorry = true,
            NodeStatus::Open => {}
        }
    }
    if any_solved {
        NodeStatus::Solved
    } else if any_sorry {
        NodeStatus::Sorry
    } else if any_unfin {
        NodeStatus::Unfinishable
    } else if any_contra {
        NodeStatus::Contradictory
    } else {
        NodeStatus::Sorry
    }
}

fn expand(
    ctx: &ProofContext,
    node: &mut ProofNode,
    budget: &mut usize,
    deadline: &std::time::Instant,
    depth: usize,
) -> Result<(), RankingError> {
    expand_inner(ctx, node, budget, deadline, depth)?;
    // After expansion, `sys` is no longer read EXCEPT on
    // `Sorry: depth limit` leaves, which `re_expand_depth_limited`
    // (defined below in this file) re-runs `expand` on during the next
    // ID-DFS iteration — those need their sys — and on `Finished(Solved)`
    // leaves when batch trace output asked for them via
    // `SysRetention::KeepSolved`.  Everything else (other resolved leaves,
    // interior nodes, terminal Sorrys) can drop.  See
    // `drop_sys_after_expand`.
    // Profile: csf17::injectivity 1010-step proof tree holds ~200 MB
    // peak; this drain reduces peak RSS to ~14 MB (~ same as small
    // lemmas — most of HS's residue is the closed branches we can
    // now free).
    if drop_sys_after_expand(node, sys_retention()) {
        node.sys = crate::constraint::system::System::default();
    }
    Ok(())
}

/// The [`expand`] drop decision, as a pure predicate over the node and
/// the [`SysRetention`] policy.  `sys` survives when the node is a
/// `Sorry: depth limit` frontier stub (re-expanded next ID-DFS
/// iteration), when every node is retained, or when solved-node
/// retention is on and this node is `Finished(Solved)` — HS
/// `outputTraces`' selector (Batch.hs:285).  Keyed on `method`, not on
/// the aggregate [`NodeStatus`], which rolls up from children and would
/// retain interior nodes too.
fn drop_sys_after_expand(node: &ProofNode, retention: SysRetention) -> bool {
    if is_depth_limited(node) {
        return false;
    }
    match retention {
        SysRetention::DropAll => true,
        SysRetention::KeepSolved => {
            !matches!(node.method, ProofMethod::Finished(MethodResult::Solved))
        }
        SysRetention::KeepAll => false,
    }
}

fn expand_inner(
    ctx: &ProofContext,
    node: &mut ProofNode,
    budget: &mut usize,
    deadline: &std::time::Instant,
    depth: usize,
) -> Result<(), RankingError> {
    // `--bound=N` (HS `boundProofDepth`, Theory/Proof.hs:336-344): `go n`'s
    // `0 < n` guard fires before the node is even inspected, so ANY node at
    // depth `bound` — a would-be Solved leaf included — becomes
    // `sorry (Just $ "bound " ++ show bound ++ " hit")`.  Hence this check
    // sits before `is_finished`, and before the ID-DFS depth limit because
    // a bound-sorry is FINAL: it must not set `DEPTH_LIMIT_HIT` (it is not
    // a re-expandable "depth limit" thunk), or the deepening loop would
    // keep doubling `MAX_DEPTH` against a frontier that can never move.
    let proof_bound = PROOF_BOUND.with(|b| b.get());
    if depth >= proof_bound {
        node.method = ProofMethod::Sorry(Some(format!("bound {proof_bound} hit")));
        node.status = NodeStatus::Sorry;
        return Ok(());
    }
    // Rust-only diagnostic [STATE] emission (gated by TAM_RS_TRACE_STATE)
    // placed at every evaluated prove entry so Simplify / Induction /
    // Finished steps are recorded, not just SolveGoal dispatch
    // (proof_method.rs). Bound-cut nodes above remain wholly unevaluated,
    // matching HS's `boundProofDepth`.
    crate::constraint::solver::trace::trace_state(&node.sys);
    // ID-DFS depth limit (Haskell `cutOnSolvedDFS` Theory/Proof.hs:855-877).
    //
    // Haskell's `findSolved` checks `d >= dMax` BEFORE checking the
    // node's method type:
    //
    //   findSolved d node
    //     | d >= dMax = MaybeNoSolution
    //     | otherwise = case node of
    //         LNode (ProofStep (Finished Solved) ...) _  -> Solution path
    //         ...
    //
    // So a Solved leaf at depth d == dMax becomes MaybeNoSolution, NOT
    // Solution.  This is critical for correct alphabetical-first selection
    // during iterative deepening: if a shorter Solved (case_2 at d=8)
    // exists alongside a longer one (case_1 at d=15), Haskell needs to
    // iterate dMax up to >= 16 before EITHER returns Solution, at which
    // point alphabetical-first (case_1) wins.  Checking is_finished
    // before the depth limit would make our case_2 close at max_depth=8
    // and short-circuit before case_1 is reachable at deeper iterations.
    //
    // KAS2_eCK::eCK_key_secrecy is the lemma this ordering decides.
    let max_depth = MAX_DEPTH.with(|m| m.get());
    if depth >= max_depth {
        DEPTH_LIMIT_HIT.with(|f| f.set(true));
        node.method = ProofMethod::Sorry(Some("depth limit".into()));
        node.status = NodeStatus::Sorry;
        return Ok(());
    }
    // Already terminal.
    if let Some(r) = is_finished(ctx, &node.sys) {
        node.status = node_status_of(&r);
        node.method = ProofMethod::Finished(r);
        return Ok(());
    }
    if std::time::Instant::now() >= *deadline {
        node.method = ProofMethod::Sorry(Some("deadline reached".into()));
        node.status = NodeStatus::Sorry;
        return Ok(());
    }
    if *budget == 0 {
        node.method = ProofMethod::Sorry(Some("budget exhausted".into()));
        node.status = NodeStatus::Sorry;
        return Ok(());
    }
    *budget -= 1;
    // Mirror Haskell's `rankProofMethods` → `execMethods` flow:
    // build a priority-ordered list of candidate methods, try each
    // until one's `exec_proof_method` returns `Some(cases)`.  Haskell
    // does this via `mapMaybe execMethod`; for the automatic-search
    // path we pick the first surviving method.
    //
    // Reference: `Theory.Constraint.Solver.ProofMethod.rankProofMethods`
    // (`ProofMethod.hs:520-548`):
    //
    //   proofMethods = bool toList insertInduction (isInitialSystem sys)
    //                  ((Simplify, "") :| goals)
    //   insertInduction (simplify :| gs) = case pcUseInduction ctxt of
    //     AvoidInduction -> simplify : (Induction, "") : gs
    //     UseInduction   -> (Induction, "") : simplify : gs
    //
    // Then `execMethods` filters to those that succeed.
    // `candidate_methods_open`: the terminal check above just proved
    // `is_finished(ctx, &node.sys)` is `None`, and nothing has touched
    // `node.sys` since — skip the guarded entry's redundant re-sweep.
    let Some((method, mut cases)) = select_open_method(&node.sys, ctx, depth)? else {
        node.method = ProofMethod::Sorry(Some("no method".into()));
        node.status = NodeStatus::Sorry;
        return Ok(());
    };
    node.method = method;
    if cases.is_empty() {
        // An empty case-map after exec normally means contradictory
        // closure.  The one exception is a `Sorry` method (e.g. an
        // oracle/tactic with `quit_on_empty` that ranked no goals):
        // its node folds up as an *incomplete* proof, not a closed
        // one.  Haskell's `proofStepStatus (ProofStep (Sorry _) (Just
        // _)) = IncompleteProof` (Theory/Proof.hs), i.e. `Sorry`, NOT
        // `CompleteProof`/contradictory — otherwise an all-traces
        // lemma blocked only by the oracle would be reported verified.
        node.status = if matches!(&node.method, ProofMethod::Sorry(_)) {
            NodeStatus::Sorry
        } else {
            NodeStatus::Contradictory
        };
        return Ok(());
    }
    // Early-break-on-Solved (Haskell `foldMap` semantics):
    //
    // Haskell's Disj-monad is lazy — once any branch returns
    // `TraceFound` (Solved), the monad short-circuits and siblings
    // aren't forced.  Haskell's proof tree renders only what was
    // forced: the Solved branch and its ancestors.  Our search does
    // the same — once any child closes Solved, parent's status is
    // Solved (per rollup) and remaining siblings are wasted work.
    //
    // Critical for NSPK3::nonce_secrecy and other attack lemmas:
    // Haskell finds the trace at one specific case (e.g. `c_aenc`)
    // after the lazy Disj-monad short-circuits other paths.
    //
    // Case iteration order: `execProofMethod`'s `process` helper
    // (ProofMethod.hs:302-308) builds a `Data.Map` keyed by case name
    // via `M.fromListWith` (ProofMethod.hs:283-340, see line 307), so
    // entries are alphabetically ordered.  `proveSystemDFS` /
    // `cutOnSolvedDFS` then walk in map order (Theory/Proof.hs:855-877 —
    // `foldMap`, `M.map`).  Our `Vec` preserves creation order
    // (source-file rule order), so sort by name to match Haskell.
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    // Haskell-faithful: no per-branch budget split.  Haskell's lazy
    // Disj-monad explores each branch using as many steps as needed —
    // there is no step-count cap on individual branches.  The ID-DFS
    // depth limit (above) prevents infinite recursion; deadline catches
    // runaway Maude calls.  Each child sees the same shared `budget`
    // counter, decremented as it explores.
    //
    // Per-child parallelism (env-opt: `TAM_RS_DISABLE_PARALLEL_EXPAND=1`
    // disables; default ON).  Mirrors HS's `parTraversable nfProofMethod`
    // at `Theory/Proof.hs:854-884, see line 871` (the `nfProofMethod` helper at 871-877)
    // inside `cutOnSolvedDFS`: HS evaluates each child's
    // proof-method/info/children in parallel via the Eval monad strategy.
    // We do the equivalent by running each child's `expand` on a rayon
    // worker.  Faithful: case sort order, per-child sys cloning, rollup
    // semantics are unchanged.  Trade-off: parallel mode drops the
    // `any_solved` early-break short-circuit, so it may explore siblings
    // HS's lazy `foldMap` would prune.  This is output-neutral wasted
    // work: `run_proof_search` finishes by calling `extract_solved_path`,
    // which walks `node.children` (a key-sorted BTreeMap) and prunes to
    // the first Solved leaf in key order — re-imposing exactly HS's
    // `foldMap` + `extractSolved` first-in-map selection.  The extra
    // exploration only costs CPU; the pruned output is identical.  Gated
    // off for exists-trace lemmas (see below) so we never pay that cost
    // where the early-break matters for speed.
    // Bounded by rayon's global pool sized via `--processors=N`.
    //
    // Thread-locals propagated to workers: MAX_DEPTH and PROOF_BOUND
    // (read-only), DEPTH_LIMIT_HIT (each worker sets its local, aggregated
    // OR after the parallel pass), and the user-fun sets (snapshot
    // installed per worker — see `disable_parallel_expand`).  case_path is
    // best-effort under parallel: each worker seeds its stack from the
    // parent's snapshot at entry.
    let n_cases = cases.len();
    let serial_only = disable_parallel_expand();
    // Gate parallel mode on all-traces lemmas only.  Exists-trace
    // lemmas rely on the `any_solved` early-break (HS's lazy `foldMap`
    // short-circuit on `TraceFound`) — once a single witness branch
    // is found, sibling branches are pruned.  Parallel exploration of
    // siblings would invalidate that pruning and explore branches HS
    // would skip — observable as an 8× user-CPU blow-up on wireguard
    // exists_two_sessions when parallel was enabled unconditionally.
    // All-traces lemmas never short-circuit on Solved (Solved means a
    // counter-example was found; valid lemmas never see this), so for
    // those parallel exploration of every sibling matches HS exactly.
    let parallel = !serial_only
        && !ctx.is_exists_trace
        // Only `Dfs` (HS `cutOnSolvedDFS`, itself `parTraversable`-parallel)
        // expands siblings in parallel.  seqdfs (HS
        // `cutOnSolvedSingleThreadDFS`) is single-threaded by definition —
        // it descends the leftmost branch to completion and short-circuits
        // on the first solved leaf; parallel sibling exploration would
        // defeat that early-break, exploring (and possibly hanging on)
        // branches HS's `foldMap` prunes.  The bfs/none/sorry extractors
        // route through the serial branch's per-strategy abort policy
        // (below), which the parallel branch does not implement.
        && matches!(ctx.cut, CutStrategy::Dfs)
        && n_cases >= 2
        && depth <= 16; // bound recursion-level parallel splits; deeper
                        // splits hurt more than help under rayon's
                        // work-stealing — see HS's parLTreeDFS which
                        // is similarly shallow in practice.
    if parallel {
        use rayon::prelude::*;
        // Snapshot data needed by each worker.  MAX_DEPTH is a per-
        // search ID-DFS limit — read once here, restored at each worker.
        // PROOF_BOUND likewise: a stolen worker thread's own cell is
        // usize::MAX (or stale), and a child expanded there without the
        // re-seed would sail past the `--bound` cut.
        let mp_snapshot = MAX_DEPTH.with(|m| m.get());
        let bound_snapshot = PROOF_BOUND.with(|b| b.get());
        let ranking_offset_snapshot = RANKING_DEPTH_OFFSET.with(|d| d.get());
        // Snapshot the proof-tree case_path so each worker can seed its
        // own thread-local stack and produce coherent trace output.
        let path_snapshot = crate::constraint::solver::trace::case_path_snapshot();
        let deadline_snapshot = *deadline;
        // A rayon closure may run on this same thread. Its guards restore the
        // parent's TLS and case path; retain only the worker results that must
        // be aggregated into the parent search.
        let parent_depth_limit_hit = DEPTH_LIMIT_HIT.with(|f| f.get());
        let results: Result<Vec<(String, ProofNode, bool)>, RankingError> = cases
            .into_par_iter()
            .map(|(name, sys)| {
                // Each rayon worker has its own thread-locals.  Initialise
                // them from the parent's captured state so downstream code
                // (depth-limit check, DEPTH_LIMIT_HIT bookkeeping, trace
                // case path) sees the correct values regardless of which
                // worker thread we land on.
                let _tls = SearchTlsGuard::install(SearchTlsState {
                    deadline: Some(deadline_snapshot),
                    max_depth: mp_snapshot,
                    depth_limit_hit: false,
                    proof_bound: bound_snapshot,
                    ranking_depth_offset: ranking_offset_snapshot,
                });
                let _path = crate::constraint::solver::trace::CasePathGuard::set_child(
                    path_snapshot.clone(),
                    &name,
                );
                // Per-worker MaudeHandle: siblings must not share `ctx.maude`'s
                // `fresh_counter` -- concurrent mutation would make LVar.idx
                // allocation (and proof-tree shape) depend on worker interleaving,
                // breaking deterministic output.
                //
                // HS-faithful: HS seeds a fresh FreshT counter per child case from
                // `avoid sys` (ProofMethod.hs:283-340, see line 306).  Mirror by cloning `ctx.maude`
                // with its own `fresh_counter` per worker (bounds_max(sys) + 1).
                //
                // If a `maude_pool` is configured, also borrow a per-worker
                // Maude subprocess so workers don't serialise on the
                // single shared IPC mutex.  Without a pool we share the
                // single Maude process; the IPC mutex serialises queries,
                // which is correctness-safe (just slower).
                // HS `avoid sys` next-draw seed (0 for a frees-less system —
                // see `avoid_fresh_state`), matching `Reduction::new`.
                let avoid_next = crate::constraint::solver::reduction::avoid_fresh_state(&sys);
                // Non-blocking: with B1 lemma-level parallelism the pool may be
                // fully drained by sibling lemma tasks.  A blocking `acquire`
                // here could deadlock the nested fan-out; fall back to the shared
                // `ctx.maude` (output-identical — both branches seed via
                // `with_fresh_counter_next(avoid_next)`).
                let pool_guard = ctx.maude_pool.as_ref().and_then(|pool| pool.try_acquire());
                let worker_maude = match &pool_guard {
                    Some(pooled) => pooled.handle().with_fresh_counter_next(avoid_next),
                    None => ctx.maude.with_fresh_counter_next(avoid_next),
                };
                let worker_ctx = ctx.with_swapped_maude(worker_maude);
                let mut child = ProofNode {
                    method: ProofMethod::Sorry(None),
                    sys,
                    children: BTreeMap::new(),
                    status: NodeStatus::Open,
                    annotated: true,
                };
                // Each worker gets its own budget cell — siblings do not
                // share a single counter, but with the default usize::MAX
                // (no terminal cutoff) that's faithful: HS's lazy Disj
                // exploration also doesn't share a counter.
                let mut local_budget = *budget;
                expand(
                    &worker_ctx,
                    &mut child,
                    &mut local_budget,
                    &deadline_snapshot,
                    depth + 1,
                )?;
                // Drop the pooled Maude back to the pool only after expand
                // returns — any Maude IPC inside expand uses the pooled
                // handle via `worker_ctx.maude`.
                drop(pool_guard);
                let local_hit = DEPTH_LIMIT_HIT.with(|f| f.get());
                Ok((name, child, local_hit))
            })
            .collect();
        let results = results?;
        // Aggregate worker DEPTH_LIMIT_HIT into the parent thread —
        // run_proof_search's ID-DFS loop reads this to decide whether
        // to grow MAX_DEPTH for the next iteration.  Fold the workers'
        // hits with the parent's PRE-fan-out flag (snapshotted above) so a
        // non-hitting closure that ran on this same thread (B1) cannot lower
        // a previously-raised flag — matching the serial branch, which never
        // lowers `DEPTH_LIMIT_HIT`.
        let any_hit = results.iter().any(|(_, _, hit)| *hit);
        DEPTH_LIMIT_HIT.with(|f| f.set(parent_depth_limit_hit || any_hit));
        for (name, child, _hit) in results {
            node.children.insert(name, child);
        }
    } else {
        // Serial branch: the local `abort` flag mirrors each extractor's
        // lazy sibling cut; the final node status is rolled up from
        // `node.children` by `rollup_from_children` below.
        //
        //   Dfs / SeqDfs:  stop on the first TraceFound — HS `findSolved`'s
        //                  `foldMap`-with-`Solution` short-circuit.
        //   Bfs / Nothing: never stop — HS forces every sibling
        //                  (`checkLevel`'s `traverse` / `id`).
        //   AfterSorry:    stop on the first Solved-or-Sorry subtree, and
        //                  keep the remaining cases as bare-`sorry` LEAVES —
        //                  HS `cutAfterFirstSorry`'s `go True` rewrites every
        //                  node visited after the abort to `Sorry Nothing`
        //                  with its children dropped and its annotation
        //                  kept, which is exactly a case HS never forces.
        let mut abort = false;
        for (name, sys) in cases {
            if abort {
                match ctx.cut {
                    CutStrategy::AfterSorry => {
                        // HS `go True` (cutAfterFirstSorry, Theory/Proof.hs:993-994)
                        // still exposes a cheap `Finished _` method without
                        // forcing an open node's selected method or children:
                        // finished nodes are preserved after the abort —
                        // NSPK3 renders `by contradiction /* cyclic */`
                        // leaves amid the sorry stubs — while every
                        // still-open node becomes a bare `sorry` leaf.
                        let (method, status) = match is_finished(ctx, &sys) {
                            Some(r) => {
                                let st = node_status_of(&r);
                                (ProofMethod::Finished(r), st)
                            }
                            None => (ProofMethod::Sorry(None), NodeStatus::Sorry),
                        };
                        node.children.insert(
                            name,
                            ProofNode {
                                method,
                                sys,
                                children: BTreeMap::new(),
                                status,
                                annotated: true,
                            },
                        );
                        continue;
                    }
                    _ => break,
                }
            }
            let mut child = ProofNode {
                method: ProofMethod::Sorry(None),
                sys,
                children: BTreeMap::new(),
                status: NodeStatus::Open,
                annotated: true,
            };
            // Track proof-tree paths and restore them if recursive solver
            // work unwinds. Empty Simplify cases are transparent.
            let _path = crate::constraint::solver::trace::CasePathGuard::push(&name);
            expand(ctx, &mut child, budget, deadline, depth + 1)?;
            abort = match ctx.cut {
                CutStrategy::Dfs | CutStrategy::SeqDfs => {
                    matches!(child.status, NodeStatus::Solved)
                }
                CutStrategy::Bfs | CutStrategy::Nothing => false,
                CutStrategy::AfterSorry => {
                    matches!(child.status, NodeStatus::Solved | NodeStatus::Sorry)
                }
            };
            node.children.insert(name, child);
        }
    }
    // Rollup follows Haskell's `Semigroup ProofStatus`
    // (`Theory.Proof:409`):
    //
    //   TraceFound <> _ = TraceFound
    //   _ <> TraceFound = TraceFound
    //   IncompleteProof <> _ = IncompleteProof
    //   _ <> IncompleteProof = IncompleteProof
    //   UnfinishableProof <> _ = UnfinishableProof
    //   _ <> UnfinishableProof = UnfinishableProof
    //   CompleteProof <> _ = CompleteProof
    //   _ <> CompleteProof = CompleteProof
    //
    // `TraceFound` (a Solved leaf was found) absorbs every other
    // status — once *any* branch finds a witness, the whole proof
    // is TraceFound (witness exists).  This is what makes the
    // automatic prover correctly identify exists-trace verdicts
    // even when sibling branches remain Sorry.
    //
    // `CompleteProof` (all branches closed without finding a
    // witness) corresponds to our `Contradictory` — every path
    // exhausts to ⊥.
    // (`Contradictory` = all children closed without a Solved; the
    // empty-children fallback is `Sorry`, but the empty case-set was
    // already handled earlier as `Contradictory`.)
    node.status = rollup_from_children(&node.children);
    // Note: `Contradictory` is only reached when no child is
    // Solved/Sorry/Unfinishable — i.e. every branch closed to ⊥.
    Ok(())
}

fn select_open_method(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Option<(ProofMethod, Vec<(String, System)>)>, RankingError> {
    Ok(candidate_methods_open(sys, ctx, depth)?
        .into_iter()
        .find_map(|method| exec_proof_method(ctx, &method, sys).map(|cases| (method, cases))))
}

/// Run the goal ranker at the effective depth. `Ok(None)` is its ApplySorry
/// instruction; actual oracle/tactic failures propagate to the caller.
fn try_rank_goals(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Option<Vec<crate::constraint::solver::annotated_goals::AnnotatedGoal>>, RankingError> {
    let depth = depth.saturating_add(RANKING_DEPTH_OFFSET.with(|d| d.get()));
    crate::constraint::solver::goals::rank_goals_with(sys, Some(ctx), depth)
}

/// Insert an `Induction` candidate at the HS-mandated position when the
/// system is in its initial state and the first formula supports
/// induction.  Haskell's automatic path (`rankProofMethods`,
/// ProofMethod.hs:520-548, see line 527) gates `insertInduction` on `isInitialSystem sys`
/// only; `execMethods` then filters non-applicable methods (the
/// `ginduct` check here is our analog of `getInductionCases`).  Position:
/// index 0 for `UseInduction`, index 1 (after `Simplify`) for
/// `AvoidInduction`.  `mk` builds the element — a bare
/// `ProofMethod::Induction`, or the `(ProofMethod::Induction, String)`
/// pair the UI variant needs.
fn insert_induction_at<T>(out: &mut Vec<T>, sys: &System, ctx: &ProofContext, mk: impl Fn() -> T) {
    use crate::constraint::solver::context::UseInduction;
    if !sys.is_initial() {
        return;
    }
    let can_induct = sys
        .formulas
        .first()
        .map(|fm| crate::guarded::ginduct(fm).is_ok())
        .unwrap_or(false);
    if !can_induct {
        return;
    }
    match ctx.use_induction {
        UseInduction::UseInduction => out.insert(0, mk()),
        UseInduction::AvoidInduction => out.insert(1, mk()),
    }
}

/// Build the priority-ordered list of candidate proof methods to
/// try at this node.  Mirrors Haskell's `rankProofMethods`
/// (`ProofMethod.hs:520-548`):
///
///   proofMethods = bool toList insertInduction (isInitialSystem sys)
///                  ((Simplify, "") :| goals)
///   insertInduction (simplify :| gs) = case pcUseInduction ctxt of
///     AvoidInduction -> simplify : (Induction, "") : gs
///     UseInduction   -> (Induction, "") : simplify : gs
///
/// Then `execMethods` filters to those that succeed; the first
/// surviving method is picked.  Important: Simplify is *always*
/// in the list before goals so that when the system is reducible
/// the simplifier runs first, decomposing pending formulas into
/// goals.  Induction is only added in the initial state.
pub fn candidate_methods(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Vec<ProofMethod>, RankingError> {
    // HS `stoppingMethod` (rankProofMethods, ProofMethod.hs:749-751):
    // `(Finished <$> isFinished ctxt sys) <|> …` — a finished system's
    // method list is exactly `[Finished r]`, displacing Simplify and every
    // goal.  The web display/apply paths call here directly — e.g. an
    // accountability `⊤` VC lemma's root, whose one applicable method is
    // `contradiction` (HS redirects on it; an empty list here made RS
    // alert "prover failed").
    if let Some(r) = is_finished(ctx, sys) {
        return Ok(vec![ProofMethod::Finished(r)]);
    }
    candidate_methods_open(sys, ctx, depth)
}

/// [`candidate_methods`] minus the `stoppingMethod` guard, for callers that
/// have ALREADY run [`is_finished`] on `sys` and got `None` (`expand_inner`
/// checks the terminal case immediately before ranking): `is_finished` is
/// the full contradiction sweep, and a second sweep here doubles its cost on
/// every expanded node (measured +7% wall on CCITT_X509_3).
fn candidate_methods_open(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Vec<ProofMethod>, RankingError> {
    // Haskell-faithful: build the FULL ranked goal list, not just the
    // first one (ProofMethod.hs:520-540).  Haskell's `proofMethods`
    // includes ALL open goals as SolveGoal candidates; `execMethods`
    // then filters via `mapMaybe execMethod` and picks the first that
    // succeeds.  If the highest-ranked goal's SolveGoal returns None
    // (e.g. its dispatch_solve_goal hit Contradictory and was filtered),
    // we fall through to the next-ranked goal.
    //
    // `depth` drives round-robin heuristic scheduling (ProofMethod.hs:581-590,
    // `useHeuristic`'s `rankings !! (depth `mod` n)`).
    // The selected ranking produced no matches and quitOnEmpty is set:
    // emit ApplySorry.
    // HS: `guard (quitOnEmpty && not (null inp) && null ranked) *> Just ApplySorry`
    // (ProofMethod.hs:597-622, see line 620, inside `oracleRanking`) — stoppingMethod fires.
    // We represent this as an empty candidate list with a special Sorry.
    let goals = match try_rank_goals(sys, ctx, depth)? {
        Some(gs) => gs,
        None => {
            return Ok(vec![ProofMethod::Sorry(Some(
                "Oracle ranked no proof methods".into(),
            ))]);
        }
    };
    // Construct: [Simplify, goal_1, goal_2, ..., goal_N] (+ Induction below).
    let mut out: Vec<ProofMethod> = Vec::with_capacity(goals.len() + 2);
    out.push(ProofMethod::Simplify);
    for g in goals.into_iter() {
        out.push(ProofMethod::SolveGoal(g.goal));
    }
    // Insert Induction at the appropriate position in initial state.
    insert_induction_at(&mut out, sys, ctx, || ProofMethod::Induction);
    Ok(out)
}

/// UI-only variant of [`candidate_methods`] that also returns, for each
/// method, the explanation string HS's `rankProofMethods` attaches
/// (`ProofMethod.hs:754-769`).  `Simplify` / `Induction` / stopping
/// methods get `""`; each `SolveGoal g` gets
/// `"nr. " ++ show nr ++ sourceRule ++ usefulnessSuffix`, where
/// `sourceRule = " (from rule "++getRuleName ru++")"` for the goal's node
/// rule and the suffix comes from the `Usefulness` tag (NOT the
/// useful1/useful2 split `prettyGoals` uses).  Consumed by
/// `subProofSnippet`'s `prettyPM`, which renders it as a `// <expl>` line
/// comment after each applicable proof method.  Kept separate from
/// `candidate_methods` so the search hot path never allocates these
/// strings.
pub fn candidate_methods_with_expl(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Vec<(ProofMethod, String)>, RankingError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::annotated_goals::Usefulness;
    // HS `stoppingMethod` — see `candidate_methods`; keeps the DISPLAYED
    // numbering in lockstep with the apply path.
    if let Some(r) = is_finished(ctx, sys) {
        return Ok(vec![(ProofMethod::Finished(r), String::new())]);
    }
    // The selected ranking produced no matches with quitOnEmpty →
    // ApplySorry (expl "").
    let goals = match try_rank_goals(sys, ctx, depth)? {
        Some(gs) => gs,
        None => {
            return Ok(vec![(
                ProofMethod::Sorry(Some("Oracle ranked no proof methods".into())),
                String::new(),
            )]);
        }
    };
    let mut out: Vec<(ProofMethod, String)> = Vec::with_capacity(goals.len() + 2);
    out.push((ProofMethod::Simplify, String::new()));
    for ag in goals.into_iter() {
        // HS `sourceRule goal = case goalRule sys goal of Just ru -> …`.
        let source_rule = match &ag.goal {
            Goal::Action(i, _) | Goal::Premise((i, _), _) => sys
                .node_rule_safe(i)
                .map(|ru| format!(" (from rule {})", crate::rule::rule_name_string(ru)))
                .unwrap_or_default(),
            _ => String::new(),
        };
        let suffix = match ag.usefulness {
            Usefulness::Useful => "",
            Usefulness::LoopBreaker => " (loop breaker)",
            Usefulness::ProbablyConstructible => " (probably constructible)",
            Usefulness::CurrentlyDeducible => " (currently deducible)",
        };
        let expl = format!("nr. {}{}{}", ag.seq, source_rule, suffix);
        out.push((ProofMethod::SolveGoal(ag.goal), expl));
    }
    insert_induction_at(&mut out, sys, ctx, || {
        (ProofMethod::Induction, String::new())
    });
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;

    use tamarin_test_support::require_maude_path;

    /// This function returns `None` only when [`maude_path`] resolves nothing.
    /// That case is the documented `TAM_ALLOW_NO_MAUDE` skip.  A maude that
    /// resolves but does not start is the same misconfiguration as a dangling
    /// `MAUDE_PATH`, so this function panics for it.  A `.ok()?` here would
    /// hide that error and skip every maude-backed test in this file.
    fn ctx() -> Option<ProofContext> {
        let path = require_maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig())
            .unwrap_or_else(|e| {
                panic!(
                    "maude at {path} failed to start: {e:?} — every maude-backed \
                     test here would otherwise skip silently"
                )
            });
        Some(ProofContext::new(h, Vec::new()))
    }

    /// The per-child fan-out (`expand_children`) converts terms on rayon
    /// worker threads.  The converter answers from the signature it is
    /// handed, which the workers share with the caller, so a declared 0-arity
    /// symbol is the same application on every thread.
    #[test]
    fn a_worker_thread_converts_a_nullary_symbol_the_same_way() {
        use rayon::prelude::*;

        let thy = tamarin_parser::parse_theory(
            "theory T begin\n\
             functions: true/0\n\
             rule R: [ ] --> [ Out(true) ]\n\
             end",
            &[],
        )
        .expect("parses");
        let msig = crate::elaborate::elaborate(&thy)
            .expect("elaborates")
            .signature;
        let term = thy
            .items
            .iter()
            .find_map(|i| match i {
                tamarin_parser::ast::TheoryItem::Rule(r) => Some(r.conclusions[0].args[0].clone()),
                _ => None,
            })
            .expect("rule present");

        let on_caller = crate::elaborate::term_to_lnterm(&term, &msig).expect("converts");
        assert!(
            matches!(&on_caller, tamarin_term::term::Term::App(_, args) if args.is_empty()),
            "`true` is a 0-arity application, not a variable: {on_caller:?}"
        );
        let on_workers: Vec<_> = (0..64)
            .into_par_iter()
            .map(|_| crate::elaborate::term_to_lnterm(&term, &msig).expect("converts"))
            .collect();
        assert!(on_workers.iter().all(|t| *t == on_caller));
    }

    #[test]
    fn search_empty_system_with_a_node_solves_immediately() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        // Force out of initial state by adding a node, then no goals
        // / subterms remain.
        use crate::rule::{
            IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst, RuleAttributes,
            RuleInfo,
        };
        let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Test"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        let rule: RuleACInst = Rule::new(info, Vec::new(), Vec::new(), Vec::new());
        let mut sys = System::empty();
        // Mark non-initial via a solved formula (Haskell's
        // `isInitialSystem` uses solved_formulas emptiness, not the
        // node/edge count).
        sys.solved_formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
        sys.add_node(
            tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
            rule,
        );
        let root = run_proof_search(&ctx, sys, 10).expect("default ranking");
        assert_eq!(root.status, NodeStatus::Solved);
        // `expand_inner` consults `is_finished` before it tries `simplify`.
        // A system that is already finished therefore becomes the terminal
        // node itself.  It does not become a `Simplify` with a Solved child.
        assert_eq!(root.method, ProofMethod::Finished(MethodResult::Solved));
        assert!(root.children.is_empty());
    }

    #[test]
    fn search_empty_disj_goal_closes_contradictory() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let mut sys = System::empty();
        // Force out of initial state.
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        // An empty disjunction comes hand-in-hand with `gfalse` in the
        // formula set (insert_formula pushes both).  That's
        // also how Haskell signals contradictoryness — `openGoals`
        // filters `DisjG (Disj [])` and `FormulasFalse` fires from
        // `contradictions`.  We mirror exactly that here.
        sys.formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gfalse()));
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(Vec::new()),
        ));
        let root = run_proof_search(&ctx, sys, 5).expect("default ranking");
        assert_eq!(root.status, NodeStatus::Contradictory);
        // The root is the contradiction itself.  It is not a `SolveGoal` on
        // the empty disjunction.  `is_open_in_sys` drops `DisjG (Disj [])`, so
        // the search has no goal to pick.  It closes on `FormulasFalse` with
        // no children.
        assert_eq!(
            root.method,
            ProofMethod::Finished(MethodResult::Contradictory(Some(
                crate::constraint::solver::contradictions::Contradiction::FormulasFalse
            )))
        );
        assert!(root.children.is_empty());
    }

    #[test]
    fn search_disj_goal_with_two_branches_lazy_early_break_on_solved() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let mut sys = System::empty();
        // Force out of initial state.
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        // Add a 2-branch disjunction goal — true | false.
        // Haskell's lazy Disj-monad early-breaks once any branch
        // returns TraceFound (Solved).  The gtrue branch Solves
        // immediately, so the gfalse branch is never forced.
        // Our search mirrors this: only 1 child rendered.
        let f1 = crate::guarded::gtrue();
        let f2 = crate::guarded::gfalse();
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(vec![f1, f2]),
        ));
        let root = run_proof_search(&ctx, sys, 10).expect("default ranking");
        assert!(matches!(
            root.method,
            ProofMethod::SolveGoal(crate::constraint::constraints::Goal::Disj(_))
        ));
        // Lazy early-break: only the first-Solved branch is rendered.
        assert_eq!(root.children.len(), 1);
        assert_eq!(root.status, NodeStatus::Solved);
    }

    /// This system holds only trivially-true formulas.  `simplify` clears them
    /// with `dedupe_formulas_pass` and then
    /// `drop_trivially_true_formulas_pass`, and the child then closes as
    /// Solved.  A `simplify` that leaves the formulas in place never finishes
    /// the search, and the search returns `Sorry`.
    #[test]
    fn search_simplify_drops_trivially_true_formulas_then_solves() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let mut sys = System::empty();
        // Force out of initial state.
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        sys.formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
        sys.formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
        let root = run_proof_search(&ctx, sys, 5).expect("default ranking");
        assert_eq!(root.status, NodeStatus::Solved);
        // There is one `simplify` step, and its single child is the Solved
        // leaf.  The simplified system no longer holds the trivially-true
        // formulas.  That removal turns a system that cannot otherwise finish
        // into a Solved one.
        assert_eq!(root.method, ProofMethod::Simplify);
        assert_eq!(root.children.len(), 1);
        let (name, leaf) = root.children.iter().next().unwrap();
        assert_eq!(name, "");
        assert_eq!(leaf.method, ProofMethod::Finished(MethodResult::Solved));
        assert!(leaf.sys.formulas.is_empty());
    }

    /// `--bound=N` is HS `boundProofDepth`.  Every node at depth `N` becomes
    /// `sorry (Just "bound N hit")`.  This stub is final.  It is not a
    /// `depth limit` thunk, so `is_depth_limited` rejects it.  Otherwise the
    /// ID-DFS loop keeps doubling `MAX_DEPTH` against a frontier that can
    /// never move.
    #[test]
    fn search_runs_out_of_budget_returns_sorry() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
        let v2 = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
        let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
        // The context has no rules, so it can never solve this Action goal.
        // The search continues without end if the bound does not cut it.
        let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
        let f = crate::fact::out_fact(tx);
        sys.add_goal(crate::constraint::constraints::Goal::Action(i, f));
        // Add a non-empty piece so isInitialSystem returns false.
        sys.subterm_store_mut().add(ty.clone(), ty);
        let root = run_proof_search(&ctx, sys, 1).expect("default ranking");
        // Depth 0 is the root's own `simplify`.  Depth 1 is the cut.
        assert_eq!(root.method, ProofMethod::Simplify);
        assert_eq!(root.status, NodeStatus::Sorry);
        assert_eq!(root.children.len(), 1);
        let (name, cut) = root.children.iter().next().unwrap();
        assert_eq!(name, "");
        assert_eq!(cut.method, ProofMethod::Sorry(Some("bound 1 hit".into())));
        assert_eq!(cut.status, NodeStatus::Sorry);
        assert!(cut.children.is_empty());
        assert!(
            !is_depth_limited(cut),
            "a bound-sorry must not be re-expandable as a depth-limit thunk"
        );
    }

    #[test]
    fn proof_bound_does_not_rank_the_cut_node() {
        let mut ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        ctx.heuristic = Some(vec![
            crate::constraint::solver::goals::GoalRanking::Tactic {
                quit_on_empty: false,
                tactic: std::sync::Arc::new(crate::tactic::Tactic {
                    name: "missing".into(),
                    presort: 's',
                    prios: Vec::new(),
                    deprios: Vec::new(),
                }),
                resolution_error: Some(std::sync::Arc::from("must not be evaluated")),
            },
        ]);
        let root = run_proof_search_at_depth(&ctx, System::empty(), 0, 0)
            .expect("a bound-cut node never invokes its ranking");
        assert_eq!(root.method, ProofMethod::Sorry(Some("bound 0 hit".into())));
    }

    // --- `solved_systems` (HS `proofSystems`) + solved-sys retention ----
    //
    // Maude-free: these drive hand-built proof trees and the pure
    // `drop_sys_after_expand` predicate, so they run unconditionally.

    /// A `System` tagged with `id` recoverable by [`sys_tag`], so a walk
    /// result can be matched to the node it came from.
    fn tagged_sys(id: usize) -> System {
        let mut sys = System::empty();
        for _ in 0..id {
            sys.solved_formulas_mut()
                .push(std::sync::Arc::new(crate::guarded::gtrue()));
        }
        sys
    }

    fn sys_tag(sys: &System) -> usize {
        sys.solved_formulas.len()
    }

    fn node(
        method: ProofMethod,
        id: usize,
        children: Vec<(&str, ProofNode)>,
        annotated: bool,
    ) -> ProofNode {
        ProofNode {
            method,
            sys: tagged_sys(id),
            children: children
                .into_iter()
                .map(|(n, c)| (n.to_string(), c))
                .collect(),
            status: NodeStatus::Solved,
            annotated,
        }
    }

    fn solved(id: usize) -> ProofNode {
        node(
            ProofMethod::Finished(MethodResult::Solved),
            id,
            Vec::new(),
            true,
        )
    }

    fn walk(root: ProofNode) -> Vec<(Vec<String>, usize)> {
        into_solved_systems(root)
            .into_iter()
            .map(|(p, s)| (p, sys_tag(&s)))
            .collect()
    }

    #[test]
    fn solved_systems_root_leaf_yields_empty_path() {
        assert_eq!(walk(solved(3)), vec![(Vec::<String>::new(), 3)]);
    }

    #[test]
    fn solved_systems_walks_children_in_btreemap_order() {
        // Insertion order deliberately reversed w.r.t. the expected
        // output: `M.toList` / `BTreeMap` iterate ascending by key.
        let root = node(
            ProofMethod::Simplify,
            9,
            vec![
                (
                    "case_2",
                    node(ProofMethod::Induction, 8, vec![("z", solved(2))], true),
                ),
                (
                    "case_1",
                    node(
                        ProofMethod::Induction,
                        7,
                        vec![("b", solved(4)), ("a", solved(1))],
                        true,
                    ),
                ),
                (
                    "",
                    node(ProofMethod::Simplify, 6, vec![("k", solved(5))], true),
                ),
            ],
            true,
        );
        assert_eq!(
            walk(root),
            vec![
                (vec![String::new(), "k".to_string()], 5),
                (vec!["case_1".to_string(), "a".to_string()], 1),
                (vec!["case_1".to_string(), "b".to_string()], 4),
                (vec!["case_2".to_string(), "z".to_string()], 2),
            ]
        );
    }

    #[test]
    fn solved_systems_skips_unannotated_solved_node() {
        // HS's first equation needs `Just sys`; an unannotated
        // (`Nothing`) solved step falls through to the recursive
        // equation, so its own system is dropped but its children are
        // still walked.
        let unannotated = node(
            ProofMethod::Finished(MethodResult::Solved),
            5,
            vec![("c", solved(6))],
            false,
        );
        let root = node(ProofMethod::Simplify, 9, vec![("a", unannotated)], true);
        assert_eq!(
            walk(root),
            vec![(vec!["a".to_string(), "c".to_string()], 6)]
        );
        // A childless unannotated solved node contributes nothing.
        let bare = node(
            ProofMethod::Finished(MethodResult::Solved),
            5,
            Vec::new(),
            false,
        );
        assert!(walk(bare).is_empty());
    }

    #[test]
    fn solved_systems_does_not_recurse_into_solved_node() {
        // Batch.hs:285 matches `_` children and returns immediately: the
        // solved node's own system is the only result, its solved
        // descendants are invisible.
        let root = node(
            ProofMethod::Finished(MethodResult::Solved),
            1,
            vec![("a", solved(2)), ("b", solved(3))],
            true,
        );
        assert_eq!(walk(root), vec![(Vec::<String>::new(), 1)]);
    }

    #[test]
    fn solved_systems_other_finished_kinds_are_not_collected() {
        let root = node(
            ProofMethod::Simplify,
            9,
            vec![
                (
                    "a",
                    node(
                        ProofMethod::Finished(MethodResult::Unfinishable),
                        1,
                        Vec::new(),
                        true,
                    ),
                ),
                ("b", node(ProofMethod::Sorry(None), 2, Vec::new(), true)),
                ("c", node(ProofMethod::Invalidated, 3, Vec::new(), true)),
            ],
            true,
        );
        assert!(walk(root).is_empty());
    }

    #[test]
    fn drop_sys_after_expand_retains_only_solved_when_switch_on() {
        let solved_leaf = solved(1);
        let simplify = node(ProofMethod::Simplify, 1, Vec::new(), true);
        let contradictory = node(
            ProofMethod::Finished(MethodResult::Contradictory(None)),
            1,
            Vec::new(),
            true,
        );
        // `DropAll`: everything but a depth-limit stub is dropped.
        for n in [&solved_leaf, &simplify, &contradictory] {
            assert!(drop_sys_after_expand(n, SysRetention::DropAll));
        }
        // `KeepSolved`: the solved node keeps its system, ONLY it.
        assert!(!drop_sys_after_expand(
            &solved_leaf,
            SysRetention::KeepSolved
        ));
        assert!(drop_sys_after_expand(&simplify, SysRetention::KeepSolved));
        assert!(drop_sys_after_expand(
            &contradictory,
            SysRetention::KeepSolved
        ));
        // An unannotated solved node still counts here — `expand` never
        // produces one, and `into_solved_systems` filters it out anyway.
        let unannotated = node(
            ProofMethod::Finished(MethodResult::Solved),
            1,
            Vec::new(),
            false,
        );
        assert!(!drop_sys_after_expand(
            &unannotated,
            SysRetention::KeepSolved
        ));
        // `KeepAll` (interactive server) retains everything.
        assert!(!drop_sys_after_expand(&simplify, SysRetention::KeepAll));
    }

    #[test]
    fn drop_sys_after_expand_keeps_depth_limited_frontier() {
        let mut stub = node(
            ProofMethod::Sorry(Some("depth limit".into())),
            1,
            Vec::new(),
            true,
        );
        stub.status = NodeStatus::Sorry;
        assert!(!drop_sys_after_expand(&stub, SysRetention::DropAll));
        // A terminal (non-frontier) sorry is still dropped.
        let terminal = node(
            ProofMethod::Sorry(Some("budget exhausted".into())),
            1,
            Vec::new(),
            true,
        );
        assert!(drop_sys_after_expand(&terminal, SysRetention::DropAll));
    }

    #[test]
    fn sys_retention_switch_round_trips() {
        // `TAM_RS_KEEP_SYS` pins every reading to `KeepAll`, which is not
        // what this asserts.
        if keep_sys_env() {
            return;
        }
        // Process-global: hold the lock the other writer takes, and
        // restore the policy a concurrently running proof search expects.
        let _guard = SYS_RETENTION_TEST_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let before = sys_retention();
        for policy in [
            SysRetention::KeepAll,
            SysRetention::KeepSolved,
            SysRetention::DropAll,
        ] {
            set_sys_retention(policy);
            assert_eq!(sys_retention(), policy);
        }
        set_sys_retention(before);
    }
}
