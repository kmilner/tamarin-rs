// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Proof-search driver: the automatic prover of Theory/Proof.hs.
//!
//! Each node takes the first method of `rankProofMethods` that applies
//! (`execMethods`) and recurses on its cases. The default `Dfs` cut is
//! `cutOnSolvedDFS`: iterative deepening from depth 4, doubling without a
//! bound, re-expanding only the `depth limit` frontier between rounds, with
//! optional parallel sibling expansion. `seqdfs` is
//! `cutOnSolvedSingleThreadDFS`, one serial unbounded pass. The Rust-only
//! guards are a far-out depth cap (`usize::MAX / 4`) and an opt-in wall-clock
//! deadline (`TAM_PROVE_DEADLINE_MS`, see `ProofTimeLimit`).

use std::collections::BTreeMap;
use tamarin_term::maude_proc::OwnedPooledMaude;
use tamarin_utils::cancellation;
pub use tamarin_utils::cancellation::CancellationGuard as ProofCancellationGuard;

use crate::constraint::solver::context::{CutStrategy, ProofContext};
use crate::constraint::solver::proof_method::{
    exec_proof_method, is_finished, is_finished_or_stuck, ProofMethod, Result as MethodResult,
};
use crate::constraint::system::System;
use crate::prove::ProveError;

/// A checked step still contributes to the verdict after search releases its system.
#[derive(Debug, Clone)]
pub enum ProofAnnotation {
    Unchecked,
    Retained(Box<System>),
    Released,
}

impl ProofAnnotation {
    pub fn checked(sys: System) -> Self {
        Self::Retained(Box::new(sys))
    }

    pub fn is_checked(&self) -> bool {
        !matches!(self, Self::Unchecked)
    }

    pub fn system(&self) -> Option<&System> {
        match self {
            Self::Retained(sys) => Some(sys),
            Self::Released | Self::Unchecked => None,
        }
    }
}

/// One node in the proof tree.
#[derive(Debug, Clone)]
pub struct ProofNode {
    pub method: ProofMethod,
    pub annotation: ProofAnnotation,
    pub children: BTreeMap<String, ProofNode>,
    pub status: NodeStatus,
}

impl ProofNode {
    fn open(sys: System) -> Self {
        Self {
            method: ProofMethod::Sorry(None),
            annotation: ProofAnnotation::checked(sys),
            children: BTreeMap::new(),
            status: NodeStatus::Open,
        }
    }

    fn needs_revisit(&self) -> bool {
        self.status == NodeStatus::Sorry && (!self.children.is_empty() || is_depth_limited(self))
    }
}

/// Search outcome for a node and its descendants. See [`rollup_status`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeStatus {
    /// Not yet finished — has open children to explore.
    Open,
    /// The node or one of its descendants yields a trace.
    Solved,
    /// At least one branch reached `Contradictory(_)`.
    Contradictory,
    /// At least one branch reached `Unfinishable`.
    Unfinishable,
    /// A branch is incomplete because it hit a search limit or has no applicable method.
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

/// True for a leaf parked at the ID-DFS depth limit: a `Sorry: depth
/// limit` method with `Sorry` status.  These are the frontier stubs
/// `re_expand_depth_limited` re-runs `expand` on at the next (deeper)
/// iteration — the Rust analog of Haskell's unforced `cutOnSolvedDFS`
/// thunks — so `expand` also keeps their `sys` alive for that re-run.
fn is_depth_limited(node: &ProofNode) -> bool {
    matches!(&node.method, ProofMethod::Sorry(Some(msg)) if msg == "depth limit")
        && matches!(node.status, NodeStatus::Sorry)
}

/// HS `ProofStatus` (Theory/Proof.hs) — the aggregate status of a WHOLE
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
    /// HS `ProofStatus` Semigroup (Theory/Proof.hs): precedence
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

/// HS `proofStepStatus` (Theory/Proof.hs): the status of ONE node.
/// An unchecked node (HS `Nothing`)
/// is `Undetermined` REGARDLESS of its method; otherwise it is keyed on
/// the node's own method (NOT its aggregated `NodeStatus`).
fn step_status(node: &ProofNode) -> ProofStatus {
    ProofStatus::from_step(&node.method, node.annotation.is_checked())
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

/// HS `proofSystems` (Batch.hs): every solved constraint system
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
/// recurse into them. A
/// `Finished(Solved)` step whose annotation was lost (HS `Nothing`,
/// printed `/* unannotated */`) falls through to the second equation and
/// is recursed into like any other node.  `M.toList` is ascending
/// `CaseName` order == `BTreeMap<String>` iteration order.
///
/// The systems only survive a `--prove` run when its proof context uses at
/// least [`KeepSolved`](SysRetention::KeepSolved); on the stored-proof
/// replay path (`prove::check_and_extend_lemma_in_session`) they are
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
    if matches!(node.method, ProofMethod::Finished(MethodResult::Solved))
        && let ProofAnnotation::Retained(sys) = node.annotation
    {
        out.push((path.clone(), *sys));
        return;
    }
    for (case, child) in node.children {
        path.push(case);
        collect_solved_systems_owned(child, path, out);
        path.pop();
    }
}

/// How much of a proof tree keeps its per-node constraint `System` once
/// [`expand`] has returned. Each proof context owns the policy because the
/// three front ends want three different answers:
///
/// * [`DropAll`](SysRetention::DropAll) — `--prove`, which never reprints
///   a per-node system in its text proof and so trades them for a low
///   peak RSS.
/// * [`KeepSolved`](SysRetention::KeepSolved) — batch trace output
///   (`--output-dot` / `--output-json`), whose HS `outputTraces`
///   (Batch.hs) reads exactly the
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
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum SysRetention {
    /// Drop every expanded node's `System`.
    #[default]
    DropAll = 0,
    /// Retain the `System` of `Finished(Solved)` nodes only.
    KeepSolved = 1,
    /// Retain every node's `System`.
    KeepAll = 2,
}

/// Per-child parallel expansion is ON by default;
/// `TAM_RS_DISABLE_PARALLEL_EXPAND=1` forces serial sibling expansion
/// (debug escape hatch).  Output-neutrality depends on every worker
/// installing the caller's deadline and search limits: a stolen worker
/// thread starts with the defaults.
#[inline]
fn disable_parallel_expand() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DISABLE_PARALLEL_EXPAND")
}

/// Bound the number of enclosing forks with outstanding siblings. A single
/// worker walks its branches in order.
fn split_levels(workers: usize) -> u32 {
    if workers == 1 {
        0
    } else {
        workers.ilog2() + 2
    }
}

/// Whether the cases of a node are visited by several workers.
fn forks(ctx: &ProofContext, cases: usize) -> bool {
    cases >= 2
        && ctx.cut == CutStrategy::Dfs
        && !disable_parallel_expand()
        && rayon::current_num_threads() > 1
        // Ordinary all-traces forks inherit the same absolute deadline.
        && !(DEADLINE.with(|cell| cell.get().is_some()) && ctx.serial_under_a_deadline())
}

/// Visit cases in order on several workers, up to the first solved one.
/// A worker other than the caller looks for a pooled process of its own
/// before each case. The cases of workers without one share the caller's,
/// whose Maude calls then queue.
fn visit_forked(
    ctx: &ProofContext,
    search: &mut Search,
    children: &mut BTreeMap<String, ProofNode>,
    cases: Vec<(String, ProofNode)>,
    depth: usize,
    visit: Visit,
) -> Result<(), ProveError> {
    let mut cases = cases.into_iter();
    // Finishing a serial case can free an enclosing fork's depth budget.
    let limit = split_levels(rayon::current_num_threads()) as usize;
    while cases.len() < 2 || tamarin_utils::parallel::active_split_depth() >= limit {
        let Some((name, mut child)) = cases.next() else {
            return Ok(());
        };
        let solved = visit_child(ctx, search, &name, &mut child, depth, visit)?;
        children.insert(name, child);
        if solved {
            return Ok(());
        }
    }
    let cases = cases.collect();
    let child_search = Search {
        depth_limit_hit: false,
        ..*search
    };
    let deadline = DEADLINE.with(|cell| cell.get());
    // Snapshot the proof-tree case_path so each worker can seed its
    // own thread-local stack and produce coherent trace output.
    let path_snapshot = crate::constraint::solver::trace::case_path_snapshot();
    // A rayon closure may run on this same thread. Its guards restore the
    // parent's deadline and case path.
    check_cancelled()?;
    let ctx = ctx.clone();
    let results = {
        let pool = ctx.maude_pool.clone();
        let visit_case = move |lease: Option<OwnedPooledMaude>,
                               (name, mut child): (String, ProofNode)|
              -> Result<_, ProveError> {
            let _deadline = DeadlineGuard::install(deadline);
            let mut search = child_search;
            let _path = crate::constraint::solver::trace::CasePathGuard::set_child(
                path_snapshot.clone(),
                &name,
            );
            // HS seeds a fresh counter from the free variables of each case.
            let avoid_next = child
                .annotation
                .system()
                .map_or(0, crate::constraint::solver::reduction::avoid_fresh_state);
            let worker_ctx = ctx.for_dfs_case(lease.as_ref(), avoid_next);
            #[cfg(test)]
            super::cancellation_tests::checkpoint(
                &worker_ctx,
                super::cancellation_tests::Work::Search,
            );
            visit(&worker_ctx, &mut search, &mut child, depth + 1)?;
            Ok((name, child, search.depth_limit_hit))
        };
        let solved = |(_, child, _): &(_, ProofNode, _)| matches!(child.status, NodeStatus::Solved);
        tamarin_utils::parallel::try_map_until_with_helpers(
            cases,
            move || {
                let own = pool.as_ref().and_then(|pool| pool.try_acquire_ready());
                Some(own.map_or(
                    tamarin_utils::parallel::Helper::Shared,
                    tamarin_utils::parallel::Helper::Own,
                ))
            },
            visit_case,
            solved,
        )
    }?;
    // Iterative deepening needs another pass if the parent or any retained
    // child reached the depth limit, including children run on this thread.
    search.depth_limit_hit |= results.iter().any(|(_, _, hit)| *hit);
    for (name, child, _hit) in results {
        children.insert(name, child);
    }
    Ok(())
}

/// A relative limit captured at proof admission. Each search starts its own
/// clock, including searches of open leaves during replay.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ProofTimeLimit {
    Unlimited,
    Milliseconds(u64),
}

impl ProofTimeLimit {
    pub(crate) fn current() -> Self {
        TIME_LIMIT_OVERRIDE
            .with(|cell| cell.get())
            .unwrap_or_else(|| {
                std::env::var("TAM_PROVE_DEADLINE_MS")
                    .ok()
                    .and_then(|value| value.parse().ok())
                    .map_or(Self::Unlimited, Self::Milliseconds)
            })
    }

    fn duration(self) -> Option<std::time::Duration> {
        match self {
            Self::Unlimited => None,
            Self::Milliseconds(ms) => Some(std::time::Duration::from_millis(ms)),
        }
    }

    fn deadline(self) -> Option<std::time::Instant> {
        self.duration()
            .and_then(|duration| std::time::Instant::now().checked_add(duration))
    }

    pub(crate) fn install(self) -> ProofDeadlineGuard {
        ProofDeadlineGuard {
            previous: TIME_LIMIT_OVERRIDE.with(|cell| cell.replace(Some(self))),
            _not_send: std::marker::PhantomData,
        }
    }
}

thread_local! {
    static TIME_LIMIT_OVERRIDE: std::cell::Cell<Option<ProofTimeLimit>> = const { std::cell::Cell::new(None) };
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
    previous: Option<ProofTimeLimit>,
    _not_send: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl ProofDeadlineGuard {
    /// Cap searches started on this thread at `ms` milliseconds.
    pub fn set_ms(ms: u64) -> Self {
        ProofTimeLimit::Milliseconds(ms).install()
    }

    /// Lift both the enclosing guard and the process-wide time limit.
    pub fn unbounded() -> Self {
        ProofTimeLimit::Unlimited.install()
    }
}

impl Drop for ProofDeadlineGuard {
    fn drop(&mut self) {
        TIME_LIMIT_OVERRIDE.with(|c| c.set(self.previous));
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
}

/// The limits of one proof search, passed down its expansion.
#[derive(Clone, Copy)]
struct Search {
    /// ID-DFS depth limit of the current round (`dMax`, HS `cutOnSolvedDFS`,
    /// Theory/Proof.hs). `usize::MAX` is no limit, as for `seqdfs`.
    max_depth: usize,
    /// `--bound=N` (HS `boundProofDepth`, applied per `runAutoProver`,
    /// Theory/Proof.hs): a node at depth `N` becomes `sorry /* bound N hit
    /// */`. Unlike `max_depth` it is fixed for the whole search and a
    /// bound-sorry is final: it never sets `depth_limit_hit`.
    proof_bound: usize,
    /// Absolute proof depth of the root of a focused search, for the
    /// heuristic's round-robin rankings.
    ranking_depth_offset: usize,
    /// Set when a node is cut at `max_depth`, so the caller deepens
    /// (HS `MaybeNoSolution`).
    depth_limit_hit: bool,
}

impl Search {
    fn new(proof_bound: usize, ranking_depth_offset: usize) -> Self {
        Self {
            max_depth: usize::MAX,
            proof_bound,
            ranking_depth_offset,
            depth_limit_hit: false,
        }
    }
}

/// A search step over one node, run serially or on forked workers.
type Visit = fn(&ProofContext, &mut Search, &mut ProofNode, usize) -> Result<(), ProveError>;

pub(crate) fn check_cancelled() -> Result<(), ProveError> {
    cancellation::check().map_err(Into::into)
}

/// True iff the current search is past its wall-clock deadline.
pub fn deadline_reached() -> bool {
    DEADLINE.with(|d| {
        d.get()
            .map(|t| std::time::Instant::now() >= t)
            .unwrap_or(false)
    })
}

/// Install a search deadline on this thread, restoring the previous one on
/// drop.
struct DeadlineGuard {
    previous: Option<std::time::Instant>,
}

impl DeadlineGuard {
    fn install(deadline: Option<std::time::Instant>) -> Self {
        Self {
            previous: DEADLINE.with(|cell| cell.replace(deadline)),
        }
    }
}

impl Drop for DeadlineGuard {
    fn drop(&mut self) {
        DEADLINE.with(|cell| cell.set(self.previous));
    }
}

#[path = "saved_search.rs"]
mod saved_search;
pub(crate) use saved_search::extend_saved_proof;

/// Search from `initial` using the context's [`CutStrategy`]. The default
/// [`CutStrategy::Dfs`] retains the first solved path in case order within the
/// first depth round that finds a solution. One solved child suffices.
///
/// `proof_bound` is the maximum proof depth (`--bound=N`). Pass `usize::MAX`
/// for unbounded depth. Each search invocation gets its own deadline when a
/// time limit is configured.
pub fn run_proof_search(
    ctx: &ProofContext,
    initial: System,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    run_proof_search_at_depth(ctx, initial, proof_bound, 0)
}

pub(crate) fn run_proof_search_at_depth(
    ctx: &ProofContext,
    initial: System,
    proof_bound: usize,
    ranking_depth_offset: usize,
) -> Result<ProofNode, ProveError> {
    let _deadline = DeadlineGuard::install(ProofTimeLimit::current().deadline());
    let mut search = Search::new(proof_bound, ranking_depth_offset);
    let mut root = ProofNode {
        method: ProofMethod::Sorry(Some("initial".into())),
        annotation: ProofAnnotation::checked(initial),
        children: BTreeMap::new(),
        status: NodeStatus::Open,
    };
    match ctx.cut {
        CutStrategy::SeqDfs | CutStrategy::Nothing | CutStrategy::AfterSorry => {
            // Each takes one depth-first pass. The serial sibling loop applies
            // the cut, visiting all children for Nothing, stopping at the first
            // solved child for SeqDfs, or stubbing the suffix for AfterSorry.
            expand(ctx, &mut search, &mut root, 0)?;
        }
        CutStrategy::Bfs | CutStrategy::Dfs => {
            let mut frontier = SearchFrontier::new(ctx.cut, DEADLINE.with(|d| d.get()));
            let mut first = true;
            loop {
                search.max_depth = frontier.limit();
                search.depth_limit_hit = false;
                if first {
                    expand(ctx, &mut search, &mut root, 0)?;
                    first = false;
                } else {
                    re_expand_depth_limited(ctx, &mut search, &mut root, 0)?;
                }
                let mut path = Vec::new();
                let selected = find_solved_path(&root, &mut path).then_some(path);
                if !frontier.advance(&mut root, selected, search.depth_limit_hit) {
                    break;
                }
            }
        }
    }

    // `cutOnSolvedDFS` / `cutOnSolvedSingleThreadDFS` (Theory/Proof.hs)
    // retain only the solved-witness path. Other cut strategies retain the
    // tree produced by their own pruning policy.
    if matches!(ctx.cut, CutStrategy::Dfs | CutStrategy::SeqDfs)
        && matches!(root.status, NodeStatus::Solved)
    {
        extract_solved_path(&mut root);
    }
    Ok(root)
}

/// Whole-tree depth rounds shared by ordinary and saved-proof search.
/// The caller expands its own frontier and reports only witnesses reached in
/// this round; saved trees may contain solutions below the current limit.
struct SearchFrontier {
    cut: CutStrategy,
    depth: usize,
    deadline: Option<std::time::Instant>,
}

impl SearchFrontier {
    fn new(cut: CutStrategy, deadline: Option<std::time::Instant>) -> Self {
        let depth = match cut {
            CutStrategy::Dfs => 4,
            CutStrategy::Bfs => 1,
            _ => usize::MAX,
        };
        Self {
            cut,
            depth,
            deadline,
        }
    }

    fn limit(&self) -> usize {
        // BFS forces the cases at the selected level, leaving their children
        // as frontier stubs outside checkLevel's rendered tree.
        self.depth
            .saturating_add(usize::from(self.cut == CutStrategy::Bfs))
    }

    fn advance(
        &mut self,
        root: &mut ProofNode,
        selected: Option<Vec<String>>,
        mut incomplete: bool,
    ) -> bool {
        match self.cut {
            CutStrategy::Dfs | CutStrategy::SeqDfs => {
                if let Some(path) = selected {
                    prune_to_path(root, &path);
                    return false;
                }
            }
            CutStrategy::Bfs => {
                let depth = self.depth;
                eprintln!("searching for attacks at depth: {depth}");
                let mut found = false;
                incomplete = false;
                bfs_check_level(root, depth, &mut found, &mut incomplete, false);
                if found {
                    eprintln!("attack found at depth: {depth}");
                    *root = bfs_check_level(root, depth, &mut false, &mut false, true)
                        .expect("BFS build returns a tree");
                    return false;
                }
            }
            CutStrategy::Nothing | CutStrategy::AfterSorry => return false,
        }
        let cap = usize::MAX / 4;
        if !incomplete
            || self
                .deadline
                .is_some_and(|end| std::time::Instant::now() >= end)
            || self.depth >= cap
        {
            return false;
        }
        self.depth = if self.cut == CutStrategy::Bfs {
            self.depth + 1
        } else {
            self.depth.saturating_mul(2).min(cap)
        };
        true
    }
}

/// HS `cutOnSolvedBFS`'s `checkLevel` (Theory/Proof.hs) over the eager
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
        let solved_leaf = node.annotation.is_checked()
            && matches!(&node.method, ProofMethod::Finished(MethodResult::Solved));
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
                annotation: node.annotation.clone(),
                children: BTreeMap::new(),
                status: NodeStatus::Sorry,
            });
        }
        return build.then(|| node.clone());
    }
    // Positive-depth traversal must not descend into a stale saved subtree:
    // HS checkLevel preserves proofs whose psInfo is Nothing unchanged.
    if !node.annotation.is_checked() || node.children.is_empty() {
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
        let status = rollup_status(&new_children);
        ProofNode {
            method: node.method.clone(),
            annotation: node.annotation.clone(),
            children: new_children,
            status,
        }
    })
}

/// HS-faithful `extractSolved` (Theory/Proof.hs, the non-diff
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
///   depth using the (now larger) `max_depth`.
/// - Preserve other Sorry leaves, including expired deadlines.
/// - Other nodes: recurse into children, then re-roll up the status.
///
/// Early-break-on-Solved: matches `expand`'s short-circuit semantics —
/// once any sibling is Solved during re-expansion, stop traversing
/// the remaining siblings (Haskell's `foldMap`-with-Solution semigroup).
fn re_expand_depth_limited(
    ctx: &ProofContext,
    search: &mut Search,
    node: &mut ProofNode,
    depth: usize,
) -> Result<(), ProveError> {
    check_cancelled()?;
    // Was this node stalled at the depth limit on the previous iteration?
    if is_depth_limited(node) {
        // Re-expand from scratch at this depth.  The deeper `max_depth`
        // now lets the recursion go further before stalling again.
        node.method = ProofMethod::Sorry(None);
        node.children = BTreeMap::new();
        node.status = NodeStatus::Open;
        return expand(ctx, search, node, depth);
    }
    if !node.needs_revisit() {
        return Ok(());
    }
    // Keep deadline-limited revisits lazy so untouched siblings retain their
    // cached proof when the deadline expires between children.
    if DEADLINE.with(|d| d.get().is_none())
        && forks(ctx, node.children.len())
        && node
            .children
            .values()
            .filter(|child| child.needs_revisit())
            .nth(1)
            .is_some()
    {
        let pending: Vec<_> = node
            .children
            .extract_if(.., |_, child| child.needs_revisit())
            .collect();
        visit_forked(
            ctx,
            search,
            &mut node.children,
            pending,
            depth,
            re_expand_depth_limited,
        )?;
        node.status = rollup_status(&node.children);
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
        if deadline_reached() {
            break;
        }
        found_solved |= visit_child(ctx, search, name, child, depth, re_expand_depth_limited)?;
    }
    // Re-roll up the parent's status from current children — mirrors
    // `expand_inner`'s `node.status = if any_solved ...` rollup
    // (the `Semigroup ProofStatus` port below).
    if !node.children.is_empty() {
        node.status = rollup_status(&node.children);
    }
    Ok(())
}

/// Roll a node's children up into its status, mirroring Haskell's
/// `Semigroup ProofStatus` precedence (`Theory/Proof.hs`):
/// `Solved` > `Sorry` > `Unfinishable` > `Contradictory`.  Returns
/// `Sorry` for an empty child set (the defensive fallback used by its
/// callers); a caller that must leave `status` untouched on
/// empty children guards the call itself.
pub fn rollup_status(children: &BTreeMap<String, ProofNode>) -> NodeStatus {
    rollup_statuses(children.values().map(|child| child.status))
}

/// [`rollup_status`] over the given child statuses.
pub fn rollup_statuses(statuses: impl IntoIterator<Item = NodeStatus>) -> NodeStatus {
    let mut any_solved = false;
    let mut any_contra = false;
    let mut any_unfin = false;
    let mut any_sorry = false;
    for status in statuses {
        match status {
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
    search: &mut Search,
    node: &mut ProofNode,
    depth: usize,
) -> Result<(), ProveError> {
    expand_inner(ctx, search, node, depth)?;
    finish_expansion(node, ctx.sys_retention)
}

fn finish_expansion(node: &mut ProofNode, retention: SysRetention) -> Result<(), ProveError> {
    // Boolean terminal checks can suppress a cancelled Maude query.
    check_cancelled()?;
    // Retain systems needed by depth-limited re-expansion or the caller's
    // retention policy; release other completed systems.
    if drop_sys_after_expand(node, retention) {
        node.annotation = ProofAnnotation::Released;
    }
    Ok(())
}

/// The [`expand`] drop decision, as a pure predicate over the node and
/// the [`SysRetention`] policy.  `sys` survives when the node is a
/// `Sorry: depth limit` frontier stub (re-expanded next ID-DFS
/// iteration), when every node is retained, or when solved-node
/// retention is on and this node is `Finished(Solved)` — HS
/// `outputTraces`' selector (Batch.hs).  Keyed on `method`, not on
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

/// Visit a child on this worker and report whether it is solved. The guard
/// keeps the proof-tree path correct even if solver work unwinds.
fn visit_child(
    ctx: &ProofContext,
    search: &mut Search,
    name: &str,
    child: &mut ProofNode,
    depth: usize,
    visit: Visit,
) -> Result<bool, ProveError> {
    let _path = crate::constraint::solver::trace::CasePathGuard::push(name);
    visit(ctx, search, child, depth + 1)?;
    Ok(child.status == NodeStatus::Solved)
}

/// Force this node's method without searching any of its child systems.
fn force_method(
    ctx: &ProofContext,
    search: &mut Search,
    node: &mut ProofNode,
    depth: usize,
) -> Result<Option<Vec<(String, System)>>, ProveError> {
    check_cancelled()?;
    // `--bound=N` (HS `boundProofDepth`, Theory/Proof.hs): `go n`'s
    // `0 < n` guard fires before the node is even inspected, so ANY node at
    // depth `bound` — a would-be Solved leaf included — becomes
    // `sorry (Just $ "bound " ++ show bound ++ " hit")`.  Hence this check
    // sits before `is_finished`, and before the ID-DFS depth limit because
    // a bound-sorry is FINAL: it must not set `depth_limit_hit` (it is not
    // a re-expandable "depth limit" thunk), or the deepening loop would
    // keep doubling `max_depth` against a frontier that can never move.
    let proof_bound = search.proof_bound;
    if depth >= proof_bound {
        node.method = ProofMethod::Sorry(Some(format!("bound {proof_bound} hit")));
        node.status = NodeStatus::Sorry;
        return Ok(None);
    }
    // Rust-only diagnostic [STATE] emission (gated by TAM_RS_TRACE_STATE)
    // placed at every evaluated prove entry so Simplify / Induction /
    // Finished steps are recorded, not just SolveGoal dispatch
    // (proof_method.rs). Bound-cut nodes above remain wholly unevaluated,
    // matching HS's `boundProofDepth`.
    let sys = node
        .annotation
        .system()
        .expect("a search frontier retains its system");
    crate::constraint::solver::trace::trace_state(sys);
    // HS `findSolved` (cutOnSolvedDFS, Theory/Proof.hs) tests `d >= dMax`
    // before the node's method, so a Solved leaf at the limit is not yet a
    // solution. Deeper rounds can then still select an alphabetically
    // earlier, longer witness (KAS2_eCK::eCK_key_secrecy).
    if depth >= search.max_depth {
        search.depth_limit_hit = true;
        node.method = ProofMethod::Sorry(Some("depth limit".into()));
        node.status = NodeStatus::Sorry;
        return Ok(None);
    }
    // Already terminal.
    let finished = is_finished(ctx, sys)?;
    if let Some(r) = finished {
        node.status = node_status_of(&r);
        node.method = ProofMethod::Finished(r);
        return Ok(None);
    }
    if deadline_reached() {
        node.method = ProofMethod::Sorry(Some("deadline reached".into()));
        node.status = NodeStatus::Sorry;
        return Ok(None);
    }
    // HS `rankProofMethods` → `execMethods` (ProofMethod.hs): the first
    // ranked method that applies.
    let ranking_depth = depth.saturating_add(search.ranking_depth_offset);
    let Some((method, cases)) = select_open_method(sys, ctx, ranking_depth)? else {
        if let Some(result) = is_finished_or_stuck(ctx, sys)? {
            node.status = node_status_of(&result);
            node.method = ProofMethod::Finished(result);
        } else {
            node.method = ProofMethod::Sorry(Some(
                if deadline_reached() {
                    "deadline reached"
                } else {
                    "Cannot prove"
                }
                .into(),
            ));
            node.status = NodeStatus::Sorry;
        }
        return Ok(None);
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
        return Ok(None);
    }
    Ok(Some(cases))
}

/// Haskell's cutAfterFirstSorry inspects every sibling's method. Preserve
/// terminal methods and their reasons, and discard the children of open steps.
fn cut_sibling_after_sorry(
    ctx: &ProofContext,
    search: &mut Search,
    node: &mut ProofNode,
    depth: usize,
) -> Result<(), ProveError> {
    force_method(ctx, search, node, depth)?;
    if !matches!(
        node.method,
        ProofMethod::Finished(_) | ProofMethod::Sorry(_)
    ) {
        node.method = ProofMethod::Sorry(None);
        node.status = NodeStatus::Sorry;
    }
    node.children.clear();
    finish_expansion(node, ctx.sys_retention)
}

fn expand_inner(
    ctx: &ProofContext,
    search: &mut Search,
    node: &mut ProofNode,
    depth: usize,
) -> Result<(), ProveError> {
    let Some(mut cases) = force_method(ctx, search, node, depth)? else {
        return Ok(());
    };
    // Cases are visited in case-name order, as HS's case map is
    // (`M.fromListWith` in `execProofMethod`, ProofMethod.hs).
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    // Speculative DFS siblings run on Rayon's bounded pool. Retain the
    // sequential prefix through the first Solved child or error: a later
    // oracle failure must not override an earlier counterexample. Terminal
    // results cancel only their suffix, including blocking subprocesses.
    // `TAM_RS_DISABLE_PARALLEL_EXPAND=1` selects the serial traversal.
    if forks(ctx, cases.len()) {
        let cases = cases
            .into_iter()
            .map(|(name, sys)| (name, ProofNode::open(sys)))
            .collect();
        visit_forked(ctx, search, &mut node.children, cases, depth, expand)?;
    } else {
        // Serial branch: the local `abort` flag mirrors each extractor's
        // lazy sibling cut; the final node status is rolled up from
        // `node.children` by `rollup_status` below.
        //
        //   Dfs / SeqDfs:  stop on the first TraceFound — HS `findSolved`'s
        //                  `foldMap`-with-`Solution` short-circuit.
        //   Bfs / Nothing: never stop — HS forces every sibling
        //                  (`checkLevel`'s `traverse` / `id`).
        //   AfterSorry:    stop descending after the first Solved-or-Sorry
        //                  subtree. Force each remaining sibling's method;
        //                  retain terminal leaves and cut open steps to sorry.
        let mut abort = false;
        for (name, sys) in cases {
            if abort {
                match ctx.cut {
                    CutStrategy::AfterSorry => {
                        let mut child = ProofNode::open(sys);
                        visit_child(
                            ctx,
                            search,
                            &name,
                            &mut child,
                            depth,
                            cut_sibling_after_sorry,
                        )?;
                        node.children.insert(name, child);
                        continue;
                    }
                    _ => break,
                }
            }
            let mut child = ProofNode::open(sys);
            visit_child(ctx, search, &name, &mut child, depth, expand)?;
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
    // HS `Semigroup ProofStatus` (Theory/Proof.hs); see `rollup_status`.
    node.status = rollup_status(&node.children);
    Ok(())
}

fn select_open_method(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Option<(ProofMethod, Vec<(String, System)>)>, ProveError> {
    // The caller has just checked `is_finished`, so skip the stopping method.
    for (method, _) in rank_proof_methods(sys, ctx, depth, false)? {
        if let Some(cases) = exec_proof_method(ctx, &method, sys)? {
            return Ok(Some((method, cases)));
        }
    }
    Ok(None)
}

/// A ranked candidate method; a `SolveGoal` keeps its goal's number and
/// usefulness for the web's explanations.
type RankedMethod = (
    ProofMethod,
    Option<(u64, crate::constraint::solver::annotated_goals::Usefulness)>,
);

/// HS `rankProofMethods` (ProofMethod.hs), whose `execMethods` then picks
/// the first method that applies:
///
///   proofMethods = bool toList insertInduction (isInitialSystem sys)
///                  ((Simplify, "") :| goals)
///   insertInduction (simplify :| gs) = case pcUseInduction ctxt of
///     AvoidInduction -> simplify : (Induction, "") : gs
///     UseInduction   -> (Induction, "") : simplify : gs
///
/// A finished system's list is just its `Finished` stopping method, unless
/// `check_finished` is false because the caller has already run the full
/// [`is_finished`] sweep. An oracle ranking with `quitOnEmpty` that ranks
/// nothing yields ApplySorry. `depth` drives the heuristic's round-robin
/// rankings (`useHeuristic`).
fn rank_proof_methods(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
    check_finished: bool,
) -> Result<Vec<RankedMethod>, ProveError> {
    use crate::constraint::solver::context::UseInduction;
    if check_finished && let Some(r) = is_finished(ctx, sys)? {
        return Ok(vec![(ProofMethod::Finished(r), None)]);
    }
    let Some(goals) = crate::constraint::solver::goals::rank_goals_with(sys, ctx, depth)? else {
        return Ok(vec![(
            ProofMethod::Sorry(Some("Oracle ranked no proof methods".into())),
            None,
        )]);
    };
    let mut out = Vec::with_capacity(goals.len() + 2);
    out.push((ProofMethod::Simplify, None));
    out.extend(
        goals
            .into_iter()
            .map(|g| (ProofMethod::SolveGoal(g.goal), Some((g.seq, g.usefulness)))),
    );
    // `execMethods` drops Induction when `getInductionCases` fails, as the
    // `ginduct` check does here.
    let can_induct = sys.is_initial()
        && sys
            .formulas
            .first()
            .is_some_and(|fm| crate::guarded::ginduct(fm).is_ok());
    if can_induct {
        let at = match ctx.use_induction {
            UseInduction::UseInduction => 0,
            UseInduction::AvoidInduction => 1,
        };
        out.insert(at, (ProofMethod::Induction, None));
    }
    Ok(out)
}

/// The candidate proof methods at this node, in [`rank_proof_methods`]
/// order, each with the explanation HS's `rankProofMethods` attaches,
/// rendered by `subProofSnippet`'s `prettyPM` as a `// <expl>` comment:
/// `""` except for a `SolveGoal`, which gets
/// `"nr. " ++ show nr ++ sourceRule ++ usefulnessSuffix`. The web display
/// and apply paths call this directly; an accountability `⊤` VC lemma's
/// root, for example, has `contradiction` as its only method.
pub fn candidate_methods_with_expl(
    sys: &System,
    ctx: &ProofContext,
    depth: usize,
) -> Result<Vec<(ProofMethod, String)>, ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::annotated_goals::Usefulness;
    Ok(rank_proof_methods(sys, ctx, depth, true)?
        .into_iter()
        .map(|(method, ranked)| {
            let expl = match (&method, ranked) {
                (ProofMethod::SolveGoal(goal), Some((seq, usefulness))) => {
                    // HS `sourceRule goal = case goalRule sys goal of Just ru -> …`.
                    let source_rule = match goal {
                        Goal::Action(i, _) | Goal::Premise((i, _), _) => sys
                            .node_rule_safe(i)
                            .map(|ru| format!(" (from rule {})", crate::rule::rule_name_string(ru)))
                            .unwrap_or_default(),
                        _ => String::new(),
                    };
                    let suffix = match usefulness {
                        Usefulness::Useful => "",
                        Usefulness::LoopBreaker => " (loop breaker)",
                        Usefulness::ProbablyConstructible => " (probably constructible)",
                        Usefulness::CurrentlyDeducible => " (currently deducible)",
                    };
                    format!("nr. {seq}{source_rule}{suffix}")
                }
                _ => String::new(),
            };
            (method, expl)
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_utils::cancellation::CancellationToken;

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

    #[test]
    fn after_sorry_preserves_exhaustion_and_bound_reasons() {
        let Some(ctx) = ctx() else { return };
        let _deadline = DeadlineGuard::install(None);
        let mut search = Search::new(usize::MAX, 0);
        let mut searched = ProofNode::open(System::empty());
        expand(&ctx, &mut search, &mut searched, 0).unwrap();
        assert!(matches!(
            searched.method,
            ProofMethod::Finished(_) | ProofMethod::Sorry(Some(_))
        ));
        let mut cut = ProofNode::open(System::empty());
        cut_sibling_after_sorry(&ctx, &mut search, &mut cut, 0).unwrap();
        assert_eq!(cut.method, searched.method);
        assert_eq!(cut.status, searched.status);
        assert!(cut.children.is_empty());
        assert!(matches!(cut.annotation, ProofAnnotation::Released));

        search.proof_bound = 1;
        cut_sibling_after_sorry(&ctx, &mut search, &mut cut, 1).unwrap();
        assert!(
            matches!(cut.method, ProofMethod::Sorry(Some(ref reason)) if reason == "bound 1 hit")
        );
    }

    #[test]
    fn deadline_expiry_is_not_evidence_of_exhausted_methods() {
        let Some(ctx) = ctx() else {
            return;
        };
        let sys = System::empty();
        let _deadline = DeadlineGuard::install(None);
        assert_eq!(
            is_finished_or_stuck(&ctx, &sys).unwrap(),
            Some(MethodResult::Unfinishable)
        );
        DEADLINE.with(|deadline| deadline.set(Some(std::time::Instant::now())));
        assert_eq!(is_finished_or_stuck(&ctx, &sys).unwrap(), None);
    }

    fn search_pool(
        ctx: &ProofContext,
        size: usize,
    ) -> std::sync::Arc<tamarin_term::maude_proc::MaudePool> {
        std::sync::Arc::new(
            tamarin_term::maude_proc::MaudePool::new(
                &require_maude_path().unwrap(),
                (*ctx.maude.maude_sig()).clone(),
                size,
                Default::default(),
            )
            .unwrap(),
        )
    }

    fn branching_search() -> Option<(ProofContext, System)> {
        let mut ctx = ctx()?;
        ctx.maude_pool = Some(search_pool(&ctx, 1));
        ctx.cut = CutStrategy::Dfs;
        ctx.is_exists_trace = false;
        let mut sys = System::empty();
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(vec![
                crate::guarded::gtrue(),
                crate::guarded::gfalse(),
            ]),
        ));
        Some((ctx, sys))
    }

    #[test]
    fn queued_search_cancels_and_parallel_restart_remains_sound() {
        use super::super::cancellation_tests::{Work, WorkerGate};
        use std::sync::mpsc;
        use std::time::Duration;
        // Isolate the global Rayon pool from other tests so every worker can
        // be occupied without changing the rest of the suite's scheduler.
        const CHILD: &str = "TAM_TEST_QUEUED_SEARCH_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "constraint::solver::search::tests::queued_search_cancels_and_parallel_restart_remains_sound", "--nocapture"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build_global()
            .unwrap();
        let Some((ctx, sys)) = branching_search() else {
            return;
        };
        let baseline = run_proof_search(&ctx, sys.clone(), 10).unwrap();
        let theory = tamarin_parser::parse_theory(
            "theory T begin\nlemma a: \"T\"\nlemma b: \"T\"\nend",
            &[],
        )
        .unwrap();
        let (theory, _) = crate::closed_theory::close_theory(
            crate::elaborate::elaborate(&theory).unwrap(),
            &ctx.maude,
            None,
        )
        .unwrap();
        let session =
            crate::prove::ProverSession::build(&theory, ctx.maude.clone(), Default::default())
                .unwrap();
        let (entered_tx, entered_rx) = mpsc::channel();
        let mut releases = Vec::new();
        for _ in 0..2 {
            let (release_tx, release_rx) = mpsc::channel::<()>();
            releases.push(release_tx);
            let entered_tx = entered_tx.clone();
            rayon::spawn(move || {
                entered_tx.send(()).unwrap();
                let _ = release_rx.recv();
            });
        }
        for _ in 0..2 {
            entered_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        }
        // A cold source request queues for the same workers as proof search.
        let token = CancellationToken::default();
        let source_token = token.clone();
        let interactive = session.clone();
        let (source_done, source_result) = mpsc::channel();
        let source = std::thread::spawn(move || {
            let _guard = ProofCancellationGuard::new(Some(source_token));
            let result = interactive
                .context_for_sources(crate::constraint::system::SourceKind::RefinedSources);
            source_done.send(result.map(drop)).unwrap();
        });
        assert!(source_result
            .recv_timeout(Duration::from_millis(50))
            .is_err());
        let worker_token = token.clone();
        let batch_token = token.clone();
        let (selected, selected_rx) = mpsc::channel();
        let (finished, batch_result) = mpsc::channel();
        let batch = std::thread::spawn(move || {
            let _guard = ProofCancellationGuard::new(Some(batch_token));
            let result = session.map_lemma_proofs(
                |_| {
                    selected.send(()).unwrap();
                    Some(10)
                },
                |_, _| panic!("a retracted batch must never run"),
            );
            finished.send(result).unwrap();
        });
        for _ in 0..2 {
            selected_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        }
        let queued_sys = sys.clone();
        let (done_tx, done_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let _guard = ProofCancellationGuard::new(Some(worker_token));
            let result = run_proof_search(&ctx, queued_sys, 10);
            done_tx.send((ctx, result)).unwrap();
        });
        assert!(done_rx.recv_timeout(Duration::from_millis(100)).is_err());
        token.cancel();
        let (ctx, result) = done_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("cancellation must finish while unrelated workers remain blocked");
        assert!(matches!(result, Err(ProveError::Cancelled)));
        assert!(matches!(
            batch_result.recv_timeout(Duration::from_secs(2)),
            Ok(Err(ProveError::Cancelled))
        ));
        assert!(matches!(
            source_result.recv_timeout(Duration::from_secs(2)),
            Ok(Err(ProveError::Cancelled))
        ));
        source.join().unwrap();
        batch.join().unwrap();
        worker.join().unwrap();
        drop(releases);

        // The replacement also enters from outside Rayon. Require both workers
        // to run, cancel active work, then retry against the clean result.
        let (gate, entered) = WorkerGate::new(Work::Search, 2);
        *ctx.worker_gate.lock().unwrap() = Some(gate.clone());
        let token = CancellationToken::default();
        let worker_token = token.clone();
        let active_sys = sys.clone();
        let worker = std::thread::spawn(move || {
            let _guard = ProofCancellationGuard::new(Some(worker_token));
            let result = run_proof_search(&ctx, active_sys, 10);
            (ctx, result)
        });
        let first = entered.recv_timeout(Duration::from_secs(5)).unwrap();
        let second = entered.recv_timeout(Duration::from_secs(5)).unwrap();
        assert_ne!(first, second, "replacement must still expand in parallel");
        token.cancel();
        gate.release();
        let (ctx, result) = worker.join().unwrap();
        assert!(matches!(result, Err(ProveError::Cancelled)));
        *ctx.worker_gate.lock().unwrap() = None;
        let _guard = ProofCancellationGuard::new(Some(CancellationToken::default()));
        let retry = run_proof_search(&ctx, sys, 10).unwrap();
        assert_eq!(format!("{retry:?}"), format!("{baseline:?}"));
        assert!(rayon::broadcast(|_| cancellation::current().is_none())
            .into_iter()
            .all(|clear| clear));
    }

    #[test]
    fn oracle_and_fallible_source_searches_are_serial_under_a_deadline() {
        use crate::constraint::solver::context::FailingSourceProvider;

        let Some(mut parallel_ctx) = ctx() else {
            return;
        };
        parallel_ctx.cut = CutStrategy::Dfs;
        parallel_ctx.is_exists_trace = false;
        assert!(!parallel_ctx.serial_under_a_deadline());

        rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap()
            .install(|| {
                let _deadline = DeadlineGuard::install(Some(
                    std::time::Instant::now() + std::time::Duration::from_secs(60),
                ));
                assert!(forks(&parallel_ctx, 2));
            });

        parallel_ctx.set_source_provider(std::sync::Arc::new(FailingSourceProvider));
        assert!(parallel_ctx.serial_under_a_deadline());

        let Some(mut ctx) = ctx() else { return };
        ctx.cut = CutStrategy::Dfs;
        ctx.is_exists_trace = false;
        ctx.heuristic = Some(vec![
            crate::constraint::solver::goals::GoalRanking::Smart(false),
            crate::constraint::solver::goals::GoalRanking::Oracle {
                quit_on_empty: false,
                oracle_path: "oracle".into(),
            },
        ]);
        assert!(ctx.serial_under_a_deadline());
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
            annotation: if annotated {
                ProofAnnotation::checked(tagged_sys(id))
            } else {
                ProofAnnotation::Unchecked
            },
            children: children
                .into_iter()
                .map(|(n, c)| (n.to_string(), c))
                .collect(),
            status: NodeStatus::Solved,
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
    fn solved_systems_requires_a_retained_system() {
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
        assert_eq!(proof_status(&bare), ProofStatus::Undetermined);
        assert!(walk(bare).is_empty());

        let mut released = solved(7);
        released.annotation = ProofAnnotation::Released;
        assert_eq!(proof_status(&released), ProofStatus::TraceFound);
        assert!(walk(released).is_empty());
    }

    #[test]
    fn solved_systems_does_not_recurse_into_solved_node() {
        // Batch.hs matches `_` children and returns immediately: the
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
            ProofMethod::Sorry(Some("bound 1 hit".into())),
            1,
            Vec::new(),
            true,
        );
        assert!(drop_sys_after_expand(&terminal, SysRetention::DropAll));
    }
}
