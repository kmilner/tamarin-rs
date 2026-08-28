// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The `System` sequent — the solver's working state.
//!
//! Port of `Theory.Constraint.System.System` (from the 1939-line
//! `Theory/Constraint/System.hs`). The fields are live solver state:
//! the equation/subterm stores, source-kind/side annotations, the
//! already-grafted source list and the goal/node/edge/formula
//! collections are all read and mutated by the solver during proof search.

use std::cell::Cell;
use std::cell::RefCell;
use std::sync::Arc;

use crate::constraint::constraints::{Edge, Goal, LessAtom, NodeId};
use crate::guarded::Guarded;
use crate::rule::RuleACInst;
use crate::tools::{EquationStore, SubtermStore};
use tamarin_term::lterm::{HasFrees, LVar};

// The pure `System` serializers, mirroring the Haskell children of
// `Theory.Constraint.System`:
//
// - [`mod@dot`]   -> `Theory/Constraint/System/Dot.hs`
// - [`mod@json`]  -> `Theory/Constraint/System/JSON.hs`
// - [`mod@graph`] -> `Theory/Constraint/System/Graph/`
//
// Both the batch `--output-dot`/`--output-json` writers and the interactive
// server's graph routes render through them, which is why they live in the
// theory library rather than in either front end.
pub mod dot;
pub mod graph;
pub mod json;

// =============================================================================
// Prebuilt always-before adjacency
// =============================================================================

/// A prebuilt `alwaysBefore` adjacency map (`rawLessRel`), produced by
/// [`System::build_always_before_adj`] and queried by
/// [`System::always_before_with`]. Hoisting this build out of nested loops
/// turns the per-call O(less+edges+chains) map rebuild into a single build
/// per pass; the queries are pure BFS lookups. The relation is invariant
/// across the inner loops (the system is not mutated mid-pass), so the
/// hoisted result is identical to rebuilding the adjacency on every query.
#[derive(Debug, Clone, Default)]
pub struct PrebuiltAdj {
    adj: tamarin_utils::FastMap<NodeId, Vec<NodeId>>,
}

impl PrebuiltAdj {
    /// The inner `rawLessRel` adjacency (`from -> [to]` successor lists).
    /// Consumers that walk the relation directly (rather than through the
    /// `always_before_with` BFS) take this map so a single build
    /// feeds both query styles. It stores the same relation and preserves
    /// each node's successor order: less atoms, edges, then unsolved chains.
    pub(crate) fn map(&self) -> &tamarin_utils::FastMap<NodeId, Vec<NodeId>> {
        &self.adj
    }
}

/// Probe-index type for [`System::add_less_indexed`]: maps each stored
/// atom's `(smaller, larger)` pair (the identity key — `LessAtom`'s manual
/// `Eq`/`Ord` in constraints.rs ignore the reason) to the FIRST `less_atoms`
/// index carrying it.
///
/// The map is an *auxiliary* accelerator, not a container swap: the
/// output-bearing `less_atoms` Vec (and its insertion order) is unchanged;
/// only the dedup PROBE goes from O(n) to O(1).  Deliberately NOT a `System`
/// field — a resident index would need invalidation on every `less_atoms`
/// mutation path; instead a caller running many inserts against a
/// stable-between-inserts Vec builds one with [`System::build_less_index`]
/// and passes it by `&mut`.
pub type LessIndex =
    tamarin_utils::FastMap<(tamarin_term::lterm::LVar, tamarin_term::lterm::LVar), usize>;

// =============================================================================
// Source kind / side annotations
// =============================================================================

/// Whether a system arose from raw or refined source-traces. Mirrors
/// Haskell's `SourceKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum SourceKind {
    RawSources,
    RefinedSources,
}

/// Whether the system tracks the LHS or RHS of a diff theory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Side {
    LHS,
    RHS,
}

// =============================================================================
// Write-sealed equation-store field
// =============================================================================

/// Write-sealed newtype around the system's equation-store `Arc`.
///
/// The `eq_store` field of [`SystemContent`] stays `pub` so every READ site
/// keeps compiling unchanged — `sys.eq_store.subst` (double-deref
/// `SealedEqStore` → `Arc<EquationStore>` → `EquationStore`),
/// `Arc::ptr_eq(&a.eq_store, …)` (deref-coercion `&SealedEqStore` →
/// `&Arc<EquationStore>`), etc. — via the `Deref<Target = Arc<EquationStore>>`
/// below.
///
/// But it cannot be WRITTEN outside this module: the tuple field is private
/// and the wrapper implements **no** `Default`, `Clone`, `DerefMut`, or public
/// constructor, so a `SealedEqStore` VALUE cannot be produced anywhere except
/// `system.rs`.  That closes the residual subst-stamp hole at COMPILE time:
/// the escape-hatch `content_mut_untracked()` hands out `&mut SystemContent`
/// with the `pub eq_store` field visible, but `c.eq_store = …` has no
/// expressible right-hand side (no value to assign, no `mem::take`/`replace`
/// target, no struct-literal field), so the only reachable write path is
/// `System::set_eq_store` / `take_eq_store` / `eq_store_mut`, each of which
/// bumps `subst_stamp`.
///
/// `Debug` is implemented manually and `PartialEq` is derived; both delegate
/// to the inner `Arc`, so `SystemContent`'s derived `Debug`/`PartialEq` behave
/// exactly as they would over a bare `Arc<EquationStore>` field.  The derived
/// comparison is a content comparison (`Arc`'s `PartialEq` forwards to the
/// inner `EquationStore` value), preserving goal/case dedup equality
/// semantics.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct SealedEqStore(Arc<EquationStore>);

impl std::ops::Deref for SealedEqStore {
    type Target = Arc<EquationStore>;
    #[inline]
    fn deref(&self) -> &Arc<EquationStore> {
        &self.0
    }
}

// Delegate to the inner `Arc` so `{:?}` output (and any Debug-derived
// serialisation) is identical to that of a bare `Arc<EquationStore>` field.
impl std::fmt::Debug for SealedEqStore {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

// =============================================================================
// System
// =============================================================================

/// The value-carrying core of a [`System`]: the ten fields
/// `subst_system_once` reads/writes.  Split out of `System` so that
/// (a) `System: Deref<Target = SystemContent>` makes every field READ
/// compile unchanged (field reads auto-deref through `.`), and (b) the
/// deliberate ABSENCE of `DerefMut` turns every raw field WRITE into a
/// compile error, forcing each through one of a small, closed set of
/// stamp/cache-maintaining accessors on `System` (`content_mut`,
/// `formulas_mut`, `nodes_mut`, … / the `content_mut_untracked` escape
/// hatch).  A raw write that forgets the stamp/cache bookkeeping no
/// longer type-checks — that is the enforcement pivot for the
/// verified-identity `subst_system` skip.
// `Default` and `Clone` are IMPL'D MANUALLY (below), not derived: the
// `eq_store` field is a `SealedEqStore`, which deliberately implements neither
// `Default` nor `Clone` (that is what makes an out-of-module `SealedEqStore`
// value unproducible → the write-seal).  The manual impls rebuild the field
// through the module-private tuple constructor, so their behaviour is
// byte-identical to the derived versions (an `Arc` refcount bump / a fresh
// default `Arc`).  `Debug`/`PartialEq` are still derived (the wrapper provides
// both, delegating to the inner `Arc`).
/// The fields of HS `System` (System.hs:382-400) plus the port's own
/// `Arc` wrappers, in a different order from HS's declaration.  Only equality
/// is derived here, which is order-insensitive; HS's ordering chain is spelled
/// out by `compare_systems_up_to_new_vars`, so no order may be derived on this
/// struct.
#[derive(Debug, PartialEq)]
pub struct SystemContent {
    /// Node id → rule instance providing its conclusion.
    ///
    /// Wrapped in `Arc` for copy-on-write structural sharing: cloning a
    /// `System` (which happens at every proof branch / source-case fork)
    /// only bumps the refcount instead of deep-copying every
    /// `RuleACInst` (the biggest payload — many `LNFact`s / `LNTerm`s).
    /// Mutations go through `Arc::make_mut`, which clones the inner
    /// `Vec` only when the `Arc` is actually shared.  Reads via `Deref`
    /// are unchanged.  `Arc`'s `PartialEq` forwards to the inner `Vec`
    /// (content comparison, not pointer identity), so equality
    /// semantics — critical for goal/case dedup — are preserved.
    pub nodes: Arc<Vec<(NodeId, RuleACInst)>>,
    /// Edges from conclusions to premises.
    pub edges: Vec<Edge>,
    /// `i < j` constraints with reason tags.
    pub less_atoms: Vec<LessAtom>,
    /// Open formula obligations (lemma negations, restrictions, etc.).
    ///
    /// Each element is wrapped in `Arc` for per-element copy-on-write
    /// structural sharing: cloning a `System` (at every proof-branch /
    /// source-case fork) clones a `Vec` of refcounts instead of
    /// deep-copying every `Guarded` tree.  The `Vec` itself is owned per
    /// `System` (no whole-store `make_mut`); a formula is replaced
    /// wholesale (`*slot = Arc::new(new_f)`), so an unchanged formula
    /// keeps its shared `Arc` across a fork.  `Arc<Guarded>`'s
    /// `PartialEq` forwards to the inner `Guarded` (content comparison,
    /// not pointer identity), so dedup / `==` semantics are preserved.
    pub formulas: Vec<Arc<Guarded>>,
    /// Already-solved formulas (for memoisation).  Per-element `Arc` —
    /// see `formulas`.
    pub solved_formulas: Vec<Arc<Guarded>>,
    /// Lemmas / safety assumptions added by `insert_lemma` (mirrors
    /// Haskell's `sLemmas`). These are treated as known-true.
    /// Per-element `Arc` — see `formulas`.
    pub lemmas: Vec<Arc<Guarded>>,
    /// Last-atom constraint, e.g. `last(i)` — at most one per system.
    pub last_atom: Option<NodeId>,
    /// Equation store.
    ///
    /// `Arc`-wrapped for copy-on-write structural sharing (see `nodes`).
    /// Cloned at every proof fork; mutated through `eq_store_mut`.
    ///
    /// Write-sealed via [`SealedEqStore`]: reads deref through unchanged; the
    /// only write path is `set_eq_store`/`take_eq_store`/`eq_store_mut` (each
    /// bumps `subst_stamp`) because no `SealedEqStore` value is constructible
    /// outside this module.
    pub eq_store: SealedEqStore,
    /// Subterm store.
    ///
    /// `Arc`-wrapped for copy-on-write structural sharing (see `nodes`).
    /// Cloned at every proof fork; mutated through `subterm_store_mut`.
    pub subterm_store: Arc<SubtermStore>,
    /// Open goals paired with their current status.
    ///
    /// `Arc`-wrapped for copy-on-write structural sharing (see `nodes`).
    /// Cloned at every proof fork; mutated through `goals_mut`.
    pub goals: Arc<Vec<(Goal, GoalStatus)>>,
}

// Manual `Default` — the derived one is unavailable because `SealedEqStore`
// has no `Default` (part of the write-seal).  Rebuilds `eq_store` through the
// module-private constructor with a default `Arc<EquationStore>`; every other
// field takes its own `Default`, so the result is byte-identical to a derive.
impl Default for SystemContent {
    fn default() -> Self {
        Self {
            nodes: Arc::default(),
            edges: Vec::default(),
            less_atoms: Vec::default(),
            formulas: Vec::default(),
            solved_formulas: Vec::default(),
            lemmas: Vec::default(),
            last_atom: None,
            eq_store: SealedEqStore(Arc::default()),
            subterm_store: Arc::default(),
            goals: Arc::default(),
        }
    }
}

// Manual `Clone` — the derived one is unavailable because `SealedEqStore` has
// no `Clone` (part of the write-seal; `.clone()` on the field falls through
// `Deref` to `Arc::clone`, yielding `Arc<EquationStore>`, not another sealed
// value — so a clone can never be assigned back into an `eq_store` slot).
// Every field clones exactly as the derive would (`Arc` refcount bumps for the
// shared collections, `eq_store` rebuilt through the private constructor from
// an `Arc::clone`).  Byte-identical to a derived `Clone`.
impl Clone for SystemContent {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            less_atoms: self.less_atoms.clone(),
            formulas: self.formulas.clone(),
            solved_formulas: self.solved_formulas.clone(),
            lemmas: self.lemmas.clone(),
            last_atom: self.last_atom,
            eq_store: SealedEqStore(self.eq_store.0.clone()),
            subterm_store: self.subterm_store.clone(),
            goals: self.goals.clone(),
        }
    }
}

/// One cached generation of the implied-formula dedup canon for a single
/// formula store (`formulas` or `solved_formulas`), keyed by that store's
/// per-store stamp.  Built lazily by `insert_implied_formulas_pass` (via
/// [`System::formulas_canon_table`] / [`System::solved_formulas_canon_table`]).
///
/// Each entry is `(src, canon, hash)` for the store element at the same index:
/// * `src` is a strong `Arc` clone of the store element.  Its refcount pins the
///   allocation, so a store `Arc` whose pointer equals a `src` pointer is
///   provably the SAME immutable value (formula `Arc`s are only ever REPLACED
///   wholesale — `*slot = Arc::new(..)`, never `Arc::make_mut`/`get_mut`ed —
///   so a live pinned address can never be recycled under a different value).
///   That is the ABA-safety basis for the pointer-keyed incremental rebuild.
/// * `canon` is the dedup canonical form of `src` (the caller's canon closure).
///   When the canonicalisation is a structural no-op it is a clone of the `src`
///   `Arc` itself (refcount bump, no extra tree).
/// * `hash` is the `fx_hash_one` prefilter hash of `canon`.
///
/// The `stamp` records the store stamp the entries were built against: a probe
/// reuses this table only while the live per-store stamp still equals it (an
/// exact-value/order match, since stamps are globally unique and every store
/// mutation mints a fresh one).
#[derive(Debug)]
pub(crate) struct CanonTable {
    /// Per-store stamp the entries were built against.  Private: only the
    /// stamp-hit probe in this module reads it.
    stamp: u64,
    /// `(src, canon, hash)` for each store element, in store order.
    pub(crate) entries: Vec<(Arc<Guarded>, Arc<Guarded>, u64)>,
}

// ===== canon-cache effectiveness counters (TAM_RS_CANON_TABLE_STATS=1) =====
// Mirror the `SUBST_SKIP_STATS` / `FP_STATS` diagnostic counters: gauge whether
// the stamp/pointer reuse actually pays off (the design's stated hit-rate risk).
// Every increment is behind the once-read env gate, so a production run
// (gate off) pays nothing.
static CANON_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CANON_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CANON_INCR: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CANON_ENTRY_REUSED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CANON_ENTRY_CANONED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

#[inline]
fn canon_stats_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_CANON_TABLE_STATS")
}

/// Order-sensitive equality of two canon-entry lists on the OBSERVED components
/// (canon value + prefilter hash) — the `src` `Arc` is provenance, not part of
/// the dedup decision.  Used by the `TAM_RS_VERIFY_CANON_TABLES` oracle to
/// certify a cached generation against a fresh rebuild.
fn canon_entries_eq(
    a: &[(Arc<Guarded>, Arc<Guarded>, u64)],
    b: &[(Arc<Guarded>, Arc<Guarded>, u64)],
) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|((_, ca, ha), (_, cb, hb))| *ha == *hb && ca.as_ref() == cb.as_ref())
}

/// A constraint-solver sequent. The solver mutates this incrementally
/// during proof search.
///
/// Storage choices: the collections HS keeps in a `Data.Map`/`Data.Set` are
/// `Vec`s here (`Goal`/`Guarded`/`RuleACInst` derive no `Ord`), so they hold
/// INSERTION order and lookup is linear.  Swapping in an ordered container is
/// not a free refactor — the stored order reaches the rendered output — so a
/// site needing HS's key order materialises it at the `M.toList`/`S.toList`
/// boundary instead (see [`nodes_in_map_order`]).  `nodes`, `goals`,
/// `eq_store` and `subterm_store` are `Arc`-wrapped for copy-on-write sharing
/// across proof-branch clones, and `formulas`/`solved_formulas`/`lemmas`
/// per element (see the [`SystemContent`] field docs).
#[derive(Debug, Default)]
pub struct System {
    /// The value-carrying content fields (see [`SystemContent`]).
    ///
    /// PRIVATE — this is the enforcement pivot.  Reads reach the fields
    /// via `System: Deref<Target = SystemContent>` (so `sys.nodes` etc.
    /// still work everywhere).  Writes cannot: no code outside this
    /// module can name `system.content`, and there is no `DerefMut`, so
    /// the only reachable mutation path is a stamp/cache-maintaining
    /// accessor on `System`.
    content: SystemContent,
    pub source_kind: Option<SourceKind>,
    pub side: Option<Side>,
    /// Monotonic goal-number counter (`_sNextGoalNr`,
    /// System.hs:383-401, see line 394).  Advanced on every goal insertion (even when
    /// the goal already exists — HS's `insertGoalStatus`
    /// Reduction.hs:516-521 always `succ`s it).  Each new goal records
    /// the current value as its `GoalStatus.nr`.
    pub next_goal_nr: u64,
    /// Source-case names already grafted into this branch.  Mirrors
    /// Haskell's `filterCases` invariant in `solveAllSafeGoals`: once
    /// a precomputed case has been used to discharge a goal, it is
    /// removed from the available source list for the remainder of
    /// the search branch.  Without this, a chain-saturated case whose
    /// internal KU goals re-spawn at runtime will pick the same case
    /// again, looping until depth-limit.
    pub used_sources: Vec<String>,
    /// Provenance tracking: universals in `lemmas` that
    /// came from `[sources]`-tagged lemma bodies.  Haskell never adds
    /// these to `sLemmas` (only `[reuse]` lemmas go there via
    /// `gatherReusableLemmas`), so its runtime `insertImpliedFormulas`
    /// never fires them — they're only consulted via
    /// `refineWithSourceAsms` at precompute.  We add them to `lemmas`
    /// as a workaround for our weaker refine; tagging them here lets
    /// `insertImpliedFormulas` skip them at runtime (when
    /// `!in_precompute_mode`) while still firing them during refine's
    /// Step 1 simplify (where it's needed to drop typing-violating
    /// cases).  Matching Haskell's runtime behaviour eliminates the
    /// spurious `case case_1`/`case case_2` Disj-decomposition steps
    /// that appear in our proof trees for ~10 corpus lemmas.
    /// Per-element `Arc` — see `formulas`.
    pub sources_lemma_universals: Vec<Arc<Guarded>>,
    /// Cached max free-var idx across the system.  `None` means
    /// "invalid — lazily recompute on next `bounds_max` call".
    /// Maintained incrementally on additive mutations and
    /// invalidated on mutations that could LOWER the max.
    ///
    /// Excluded from `PartialEq`/`Clone` semantics: two systems with
    /// the same content but different cache state are still equal,
    /// and cloning copies the cached value verbatim.
    ///
    /// Wrapped in `Cell` so `bounds_max(&System)` can populate it
    /// without requiring `&mut System` at every call site.
    pub max_var_idx_cache: Cell<Option<u64>>,
    /// Cached max free-var idx across the NODES component ONLY (the
    /// `sNodes` map: node ids + their `RuleACInst` free vars).  Split
    /// out of `max_var_idx_cache` because the node walk is the dominant
    /// cost of `bounds_max` and the ~82 non-node mutation sites (which
    /// clear the full cache) leave the node component untouched — so
    /// this survives them and spares re-walking the (often large) node
    /// map.  `None` means "invalid — recompute the node component on
    /// next `bounds_max` miss".  Maintained by the node-mutation sites
    /// (invalidate on removal/substitution/rename, bump on additive
    /// push / uniform shift).  Excluded from `PartialEq`/`Clone`
    /// semantics exactly like `max_var_idx_cache`.
    pub node_max_cache: Cell<Option<u64>>,
    /// Value-version of the nine content fields `subst_system_once` reads
    /// (`nodes, edges, last_atom, less_atoms, goals, formulas,
    /// solved_formulas, lemmas, subterm_store`).  A fresh `next_stamp()` on
    /// every VALUE (or order/count) change to any of them, minted by the same
    /// cache-maintenance chokepoints the max-var-idx cache already funnels
    /// every content mutation through (see `bump_content_stamp`).  Powers the
    /// verified-identity `subst_system` skip (reduction.rs).  Excluded from
    /// `PartialEq` and from the case-dedup comparison exactly like the cache
    /// Cells.  `Cell` so read-path bump helpers need no `&mut`.
    /// Private: all access goes through the stamp/marker methods below.
    content_stamp: Cell<u64>,
    /// Value-version of `eq_store.subst`.  Fresh `next_stamp()` on every subst
    /// mutation (bumped inside `eq_store_mut`/`set_eq_store`).  Lives on
    /// `System` (not `EquationStore`) so `EquationStore`'s derived
    /// `PartialEq`/`Eq` — relied on by goal/case dedup — stays untouched.
    subst_stamp: Cell<u64>,
    /// `(content_stamp, subst_stamp)` snapshot at the end of the last
    /// zero-signal `subst_system` invocation; `None` = no verified no-op yet.
    /// While the marker still equals the live stamps, `subst_system` is a
    /// proven total no-op and the whole loop is skipped.  Cloned verbatim (a
    /// clone inherits the parent's verdict until it is itself mutated, which
    /// bumps a stamp and breaks the match).  Excluded from `PartialEq` like
    /// the cache Cells.  Private: readable/writable only through
    /// `subst_marker_matches` / `record_subst_marker` / `clear_subst_marker`.
    subst_applied_marker: Cell<Option<(u64, u64)>>,
    /// Value-version of `formulas` ALONE (finer than `content_stamp`, which
    /// tracks all nine content fields).  A fresh `next_stamp()` on every VALUE
    /// or ORDER change to `formulas`.  Powers the implied-dedup canon cache
    /// ([`formulas_canon_table`](Self::formulas_canon_table)): while it is
    /// unchanged the cached [`CanonTable`] is reused verbatim; when it bumps,
    /// the table is incrementally rebuilt (pointer-keyed entry reuse).
    ///
    /// The COMPLETE set of `formulas` write paths that mint a fresh value here:
    ///
    /// 1. `formulas_mut` — the tracked choke (also bumps `content_stamp`).
    /// 2. `formulas_mut_untracked` — the untracked choke for whole-system
    ///    rewriters (`subst_system_once`'s rewrite+dedup, `rename_precise_system`'s
    ///    re-`Arc` + sort/dedup, `sources.rs` shift/rename, the `gfalse` push).
    ///    Every untracked `formulas` write routes through this accessor: raw
    ///    `content_mut_untracked().formulas` writes are forbidden by the
    ///    `content_untracked_callers_are_enumerated` guard test (no compiler
    ///    seal is possible: `SystemContent.formulas` is a `pub` field, so the
    ///    guard test's whole-`src` scan is the enforcement).
    /// 3. `content_mut` — the coarse door (bumps this conservatively).
    /// 4. `mint_fresh_stamps` — whole-object constructors / whole-system transforms.
    ///
    /// Over-bumping only downgrades a verbatim reuse to an incremental rebuild
    /// (which then reuses every unchanged entry by pointer); under-bumping is a
    /// stale-cache bug, so every ambiguous site bumps.
    formulas_stamp: Cell<u64>,
    /// Value-version of `solved_formulas` ALONE.  See `formulas_stamp` — the
    /// same write-path enumeration applies (`solved_formulas_mut`,
    /// `solved_formulas_mut_untracked`, `content_mut`, `mint_fresh_stamps`).
    solved_formulas_stamp: Cell<u64>,
    /// Cached implied-dedup canon [`CanonTable`] for `formulas`, valid while its
    /// `stamp` field still equals `formulas_stamp`.  `RefCell` for interior
    /// mutability off the read path (built lazily during `insert_implied_formulas_pass`,
    /// which holds `&System`).  `Arc` so a stamp hit reuses the table in O(1)
    /// and so sibling clones share one generation until one of them rebuilds.
    /// Excluded from `PartialEq`/serialized keys exactly like the cache Cells;
    /// cloned into a fresh `RefCell` (never shared) so siblings' rebuilds stay
    /// independent.
    formulas_canon_cache: RefCell<Option<Arc<CanonTable>>>,
    /// Cached implied-dedup canon [`CanonTable`] for `solved_formulas`
    /// (see [`formulas_canon_cache`](Self::formulas_canon_cache)).
    solved_formulas_canon_cache: RefCell<Option<Arc<CanonTable>>>,
}

// Manual `Clone` — copies the cache value (NOT invalidates).  System
// gets cloned heavily (every prove-step grafts a child); a clone that
// invalidated the cache would defeat the optimisation.
impl Clone for System {
    fn clone(&self) -> Self {
        // Exhaustive destructure of `self` (no `..`): adding a `System` field
        // becomes a compile error here until its clone role is decided,
        // instead of being silently dropped from the clone.
        let System {
            content,
            source_kind,
            side,
            next_goal_nr,
            used_sources,
            sources_lemma_universals,
            max_var_idx_cache,
            node_max_cache,
            content_stamp,
            subst_stamp,
            subst_applied_marker,
            formulas_stamp,
            solved_formulas_stamp,
            formulas_canon_cache,
            solved_formulas_canon_cache,
        } = self;
        Self {
            content: content.clone(),
            source_kind: *source_kind,
            side: *side,
            next_goal_nr: *next_goal_nr,
            used_sources: used_sources.clone(),
            sources_lemma_universals: sources_lemma_universals.clone(),
            // The cache/stamp Cells are COPIED verbatim (NOT invalidated): a
            // clone is content-identical to its parent, so it inherits both
            // stamps AND the marker — if the parent had a verified no-op
            // verdict, the clone legitimately skips too, until the clone is
            // itself mutated (which bumps its own stamp and breaks the match).
            // Globally-unique stamps make cross-lineage aliasing impossible.
            max_var_idx_cache: Cell::new(max_var_idx_cache.get()),
            node_max_cache: Cell::new(node_max_cache.get()),
            content_stamp: Cell::new(content_stamp.get()),
            subst_stamp: Cell::new(subst_stamp.get()),
            subst_applied_marker: Cell::new(subst_applied_marker.get()),
            // Per-store stamps copied verbatim (like the content stamp): a clone
            // is formula-identical to its parent and legitimately shares its
            // stamp.  The canon caches are cloned into a FRESH `RefCell` — the
            // `Arc<CanonTable>` generation is SHARED (refcount bump) so both
            // siblings reuse it while their (identical) stamp holds, but the
            // `RefCell`s are independent, so one sibling rebuilding its table
            // does not disturb the other's cached `Arc`.
            formulas_stamp: Cell::new(formulas_stamp.get()),
            solved_formulas_stamp: Cell::new(solved_formulas_stamp.get()),
            formulas_canon_cache: RefCell::new(formulas_canon_cache.borrow().clone()),
            solved_formulas_canon_cache: RefCell::new(solved_formulas_canon_cache.borrow().clone()),
        }
    }
}

// Manual `PartialEq` — ignores the cache.  Two systems with identical
// content but different cache state (e.g. one freshly cloned, one
// after `bounds_max` populated its cache) must compare equal — see
// `proof_method.rs`'s cleanup-equality check (`let cleaned_input =
// cleanup(sys); ... if cleaned[0] == cleaned_input { return None; }`).
impl PartialEq for System {
    fn eq(&self, other: &Self) -> bool {
        // Exhaustive destructure of `self` (no `..`): adding a `System` field
        // becomes a compile error here until its equality role is decided —
        // either compare it below or bind it to `_` with a reason.
        let System {
            content,
            source_kind,
            side,
            next_goal_nr,
            used_sources,
            sources_lemma_universals,
            // DELIBERATELY excluded from equality: two systems with identical
            // content but different cache/stamp state (e.g. one freshly cloned,
            // one after `bounds_max` populated its cache) must compare equal —
            // see `proof_method.rs`'s cleanup-equality check.
            max_var_idx_cache: _,
            node_max_cache: _,
            content_stamp: _,
            subst_stamp: _,
            subst_applied_marker: _,
            // DELIBERATELY excluded from equality (like the other cache/stamp
            // Cells): the per-store stamps and canon caches are derived state,
            // so two systems with identical formula stores but different cache
            // generations must compare equal.
            formulas_stamp: _,
            solved_formulas_stamp: _,
            formulas_canon_cache: _,
            solved_formulas_canon_cache: _,
        } = self;
        *source_kind == other.source_kind
            && *side == other.side
            && *content == other.content
            && *next_goal_nr == other.next_goal_nr
            && *used_sources == other.used_sources
            && *sources_lemma_universals == other.sources_lemma_universals
    }
}

/// Read access to the [`SystemContent`] fields.  Field reads auto-deref
/// through the `.` operator, so `sys.nodes`, `sys.eq_store.subst`, … keep
/// compiling unchanged both cross-module and inside `impl System`.
///
/// There is DELIBERATELY no `DerefMut`: this is a "smart field container",
/// not a pointer.  Every write must go through a stamp/cache-maintaining
/// accessor on `System` (`content_mut`, `formulas_mut`, `nodes_mut`, … or
/// the `content_mut_untracked` escape hatch) so that forgetting the
/// stamp/cache bookkeeping is a compile error, not a silent skip
/// divergence.  See [`System::content_mut`] for the write path.
impl std::ops::Deref for System {
    type Target = SystemContent;
    #[inline]
    fn deref(&self) -> &SystemContent {
        &self.content
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct GoalStatus {
    /// Whether the goal is currently "loop-marked".
    pub looping: bool,
    /// Whether the goal is already solved (kept for replay).
    pub solved: bool,
    /// Goal creation order (`_gsNr` in HS `GoalStatus`,
    /// System.hs:369-380, see line 372).  Assigned from `System.next_goal_nr` at first
    /// insertion; on re-insertion of an existing goal HS keeps the
    /// `min` (so the original, smaller nr wins — see
    /// `combineGoalStatus`).  `goalNrRanking` (ProofMethod.hs:592-593
    /// `sortOn (fst . snd)`) orders goals by this number, NOT by Vec
    /// position.  This is the canonical tie-break within a heuristic
    /// priority class.
    pub nr: u64,
}

impl PartialOrd for GoalStatus {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// HS derives `Ord GoalStatus` over `_gsSolved`, `_gsNr`, `_gsLoopBreaker`
/// (System.hs:369-379).  The port declares `looping` first, so the order is
/// written out here instead of derived.
impl Ord for GoalStatus {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.solved
            .cmp(&other.solved)
            .then_with(|| self.nr.cmp(&other.nr))
            .then_with(|| self.looping.cmp(&other.looping))
    }
}

// =============================================================================
// HS `M.Map` / `Data.Set` iteration order
// =============================================================================

/// `sNodes` in `M.toList` / `M.elems` order, i.e. ascending `NodeId`.
///
/// THE INVARIANT, stated once for all the order helpers: `sNodes` is an
/// `M.Map NodeId RuleACInst` and `sEdges` / `sLessAtoms` are `Data.Set`s
/// (System.hs:383-385), `sFormulas` / `sSolvedFormulas` / `sLemmas` are
/// `S.Set LNGuarded` and `sGoals` is an `M.Map Goal GoalStatus`
/// (System.hs:389-392), so every HS pass that walks them — through `M.toList`,
/// `M.elems` or `S.toList` — sees them in ascending key/element order.  RS
/// stores all six as `Vec`s in INSERTION order, which carries no map/set
/// semantics: `Reduction::set_nodes` keeps first-occurrence order because that
/// is what decides which rule survives an id collision, and the display-only
/// `compress_system` pass ([`mod@graph::simplify`]) appends its
/// reconnected edges / less-atoms instead of re-inserting them in order.  A
/// port site that needs the HS order therefore has to materialise it at the
/// `M.toList` / `S.toList` boundary — through this function, through
/// [`formulas_in_set_order`], or through [`System::nodes_in_map_order`],
/// [`System::edges_in_set_order`], [`System::less_atoms_in_set_order`],
/// [`System::goals_in_map_order`].
///
/// The orders are the HS instances: `Ord NodeId` is `Ord LVar` = idx, then
/// sort, then name (LTerm.hs:546-548); `Edge`'s derived `Ord` is `src` then
/// `tgt` (Constraints.hs:79-83); `LessAtom`'s manual `Ord` is
/// `(smaller, larger)`, ignoring the reason tag (Constraints.hs:126-130);
/// `Ord Guarded` is derived (Guarded.hs:121-129); `Ord Goal` is derived
/// (Constraints.hs:159-172), mirrored by [`Goal`]'s own derive.
///
/// Takes a slice rather than a `&System` so a call site holding only
/// `&[(NodeId, RuleACInst)]` shares this one implementation.
pub fn nodes_in_map_order(nodes: &[(NodeId, RuleACInst)]) -> Vec<&(NodeId, RuleACInst)> {
    let mut ordered: Vec<&(NodeId, RuleACInst)> = nodes.iter().collect();
    ordered.sort_by_key(|a| a.0);
    ordered
}

/// One `S.Set LNGuarded` formula store in `S.toList` order — see
/// [`nodes_in_map_order`] for the map/set-order invariant these helpers
/// materialise.
///
/// Takes a slice so that `sFormulas`, `sSolvedFormulas` and `sLemmas` share
/// this one implementation.
pub(crate) fn formulas_in_set_order(formulas: &[Arc<Guarded>]) -> Vec<&Guarded> {
    let mut ordered: Vec<&Guarded> = formulas.iter().map(|f| f.as_ref()).collect();
    ordered.sort();
    ordered
}

/// [`System::node_rule_map`]'s return: a read-only `NodeId → &RuleACInst`
/// index into a system's nodes, standing in for HS's `M.lookup v sNodes`
/// (System.hs:927/931) wherever a caller resolves more than one node.
pub type NodeRuleMap<'a> = tamarin_utils::FastMap<&'a NodeId, &'a RuleACInst>;

impl System {
    pub fn empty() -> Self {
        let s = Self::default();
        // A freshly-built System has never had a verified no-op pass: mint
        // fresh, globally-unique stamps (off the reserved-0 sentinel) and
        // start with no marker, so its first `subst_system` runs a full pass.
        s.mint_fresh_stamps();
        s
    }

    // ====== verified-identity subst_system skip: stamp maintenance ======

    /// Mint a fresh `content_stamp`.  Called by every content-mutation
    /// chokepoint (the max-var-idx cache maintenance helpers below, plus
    /// `nodes_mut`/`subterm_store_mut` and the handful of raw-write gap sites
    /// the cache discipline does not cover).  A fresh unique stamp on any
    /// change breaks a stale `subst_applied_marker`, forcing the next
    /// `subst_system` to run rather than skip.  Over-bumping only loses skips;
    /// under-bumping is a soundness bug, so every ambiguous site bumps.
    #[inline]
    pub fn bump_content_stamp(&self) {
        self.content_stamp.set(tamarin_utils::next_stamp());
    }

    /// Mint a fresh `formulas_stamp` — the per-store version that the
    /// implied-dedup canon cache keys on.  Private: only the write chokes in
    /// this module call it (the `formulas_stamp` field doc enumerates them),
    /// so no outside code can substitute a hand-bump for routing through a
    /// door.  A fresh unique stamp makes the cached [`CanonTable`] a miss
    /// (incremental rebuild); over-bumping only loses a verbatim reuse,
    /// under-bumping is a stale-cache bug.
    #[inline]
    fn bump_formulas_stamp(&self) {
        self.formulas_stamp.set(tamarin_utils::next_stamp());
    }

    /// Mint a fresh `solved_formulas_stamp` (see [`bump_formulas_stamp`](Self::bump_formulas_stamp)).
    #[inline]
    fn bump_solved_formulas_stamp(&self) {
        self.solved_formulas_stamp.set(tamarin_utils::next_stamp());
    }

    /// Mint a fresh `subst_stamp` (called on every `eq_store.subst` mutation
    /// via `eq_store_mut`/`set_eq_store`).
    #[inline]
    pub fn bump_subst_stamp(&self) {
        self.subst_stamp.set(tamarin_utils::next_stamp());
    }

    /// Current `subst_stamp` — the version of this System's eq-store
    /// substitution (every subst mutation mints a fresh one).  Lets callers
    /// key derived-from-σ caches on the subst axis (e.g. `Reduction`'s
    /// `eq_vs_cache`).
    #[inline]
    pub fn subst_stamp(&self) -> u64 {
        self.subst_stamp.get()
    }

    /// True iff the verified-identity marker is set and BOTH stamps still
    /// equal the values it recorded — neither the content nor the eq-store
    /// substitution has been touched since a zero-signal `subst_system`
    /// pass observed this exact state, so re-running the pass is a proven
    /// total no-op.
    #[inline]
    pub fn subst_marker_matches(&self) -> bool {
        self.subst_applied_marker.get() == Some((self.content_stamp.get(), self.subst_stamp.get()))
    }

    /// Record the verified-identity marker at the current stamp pair.
    /// Callable only after a `subst_system` pass that raised zero change
    /// signals: the marker asserts that pass was a total no-op at exactly
    /// this `(content_stamp, subst_stamp)` state.  Any later content/subst
    /// mutation mints a fresh stamp, so the stored pair stops matching —
    /// no explicit invalidation is needed.
    #[inline]
    pub fn record_subst_marker(&self) {
        self.subst_applied_marker
            .set(Some((self.content_stamp.get(), self.subst_stamp.get())));
    }

    /// Drop the verified-identity marker.  For whole-system rewriters
    /// (precise rename) whose eq-store bump alone already breaks the match:
    /// clearing keeps the marker's meaning exact rather than relying on the
    /// stamp mismatch.
    #[inline]
    pub fn clear_subst_marker(&self) {
        self.subst_applied_marker.set(None);
    }

    /// Mint fresh values for ALL stamps (content, subst, and both per-store
    /// formula stamps) and clear the marker.  Used at whole-object
    /// construction (`System::empty`) and by the whole-system `sources.rs`
    /// freshen transforms, where a cloned marker must not survive a wholesale
    /// rewrite.  Also drops the canon caches: the freshen transforms re-`Arc`
    /// every formula, so a cached generation's pointers would never hit —
    /// dropping releases the stale pins.
    #[inline]
    pub fn mint_fresh_stamps(&self) {
        self.content_stamp.set(tamarin_utils::next_stamp());
        self.subst_stamp.set(tamarin_utils::next_stamp());
        self.subst_applied_marker.set(None);
        self.formulas_stamp.set(tamarin_utils::next_stamp());
        self.solved_formulas_stamp.set(tamarin_utils::next_stamp());
        *self.formulas_canon_cache.borrow_mut() = None;
        *self.solved_formulas_canon_cache.borrow_mut() = None;
    }

    /// Install a new equation store, bumping `subst_stamp`.  The ONLY
    /// sanctioned path for `self.eq_store = Arc::new(..)` reassignment — the
    /// `eq_store_direct_assignment_is_routed` guard test fails the build on any
    /// raw `.eq_store =` write in the solver that bypasses this.
    #[inline]
    pub fn set_eq_store(&mut self, es: Arc<EquationStore>) {
        // Module-private `SealedEqStore` constructor: the only place (with
        // `take_eq_store`/`eq_store_mut`) a sealed value is produced.
        self.content.eq_store = SealedEqStore(es);
        self.bump_subst_stamp();
    }

    /// Take the `eq_store` `Arc` out (leaving a `Default` in its place),
    /// bumping `subst_stamp`.  Sole sanctioned `mem::take(&mut …eq_store)`
    /// door for the "unwrap → rebuild → `set_eq_store`" pattern; the
    /// `eq_store_installs_route_through_set_eq_store` guard test forbids a raw
    /// `mem::take(&mut sys.eq_store)` elsewhere (the take is a subst mutation).
    #[inline]
    pub fn take_eq_store(&mut self) -> Arc<EquationStore> {
        self.bump_subst_stamp();
        // `SealedEqStore` has no `Default`, so `mem::take` is unavailable (by
        // design — that unavailability is what seals the field).  Swap in a
        // freshly-constructed default sealed store and unwrap the taken value.
        std::mem::replace(&mut self.content.eq_store, SealedEqStore(Arc::default())).0
    }

    // ====== content-write choke doors (the enforcement surface) ======

    /// The one CONSERVATIVE content-write door.  Bumps all four stamps
    /// (`content_stamp`, `subst_stamp`, and both per-store formula stamps) and
    /// invalidates BOTH max caches, then hands out `&mut SystemContent` for
    /// field-level split borrows.  Over-invalidation loses skips / cache hits,
    /// never correctness.  Prefer a precise accessor on a hot path; use this
    /// everywhere else (notably the interactive graph-render pipeline, which
    /// never runs `subst_system` afterwards so the double bump is free).
    ///
    /// `subst_system_once` and the other whole-system rewriters never use this
    /// (they use `content_mut_untracked`), so its `subst_stamp` bump never
    /// fires mid-skip-window on the hot path.
    #[inline]
    pub fn content_mut(&mut self) -> &mut SystemContent {
        self.bump_content_stamp();
        self.bump_subst_stamp();
        // Coarse door: the returned `&mut SystemContent` can rewrite `formulas`
        // / `solved_formulas`, so bump their per-store stamps conservatively
        // (over-bump — an incremental rebuild still reuses every unchanged entry
        // by pointer).
        self.bump_formulas_stamp();
        self.bump_solved_formulas_stamp();
        self.max_var_idx_cache.set(None);
        self.node_max_cache.set(None);
        &mut self.content
    }

    /// Raw `&mut SystemContent` with NO stamp bump and NO cache invalidation.
    ///
    /// ONLY for whole-system rewriters that manage the stamps AND both max
    /// caches themselves and whose perf depends on not over-invalidating (they
    /// reassign whole `Arc`s, mint fresh stamps, or track change precisely).
    /// Every other mutation MUST use `content_mut` or a precise accessor.
    ///
    /// The closed set of callers is pinned by the
    /// `content_untracked_callers_are_enumerated` guard test.  A new call site
    /// fails the build until its stamp reasoning is established.  The
    /// subst axis is sealed independently of this list: the `eq_store` field
    /// this door exposes is a `SealedEqStore`, so a raw assignment has no
    /// expressible right-hand side and every write path bumps `subst_stamp`.
    ///
    /// VISIBILITY: `pub(crate)`, not `pub` — unnameable from `tamarin-server`
    /// and any other downstream crate (only the tracked `content_mut` door is
    /// `pub`).  The conceptually-tighter `pub(in crate::constraint::solver)` is
    /// illegal here: this inherent method is declared in `impl System` inside
    /// module `crate::constraint::system`, which is a *sibling* (not an
    /// ancestor) of `solver`, and `pub(in …)` may only name an ancestor module.
    /// The guard test's whole-`src` file scan makes the enforced scope equal to
    /// the visibility scope.
    #[inline]
    pub(crate) fn content_mut_untracked(&mut self) -> &mut SystemContent {
        &mut self.content
    }

    /// Bump `content_stamp` + `formulas_stamp` and hand out
    /// `&mut Vec<Arc<Guarded>>` for the `formulas` store.  Leaves the max
    /// caches alone: the caller keeps its adjacent `bump_cache_guarded` /
    /// `invalidate_*` so the additive max-cache discipline is unchanged for
    /// these hot formula sites (routing through `content_mut` would INVALIDATE
    /// the max cache on every formula insert — a `bounds_max` regression).
    #[inline]
    pub fn formulas_mut(&mut self) -> &mut Vec<Arc<Guarded>> {
        self.bump_content_stamp();
        self.bump_formulas_stamp();
        &mut self.content.formulas
    }

    /// Bump `content_stamp` + `solved_formulas_stamp` and hand out `&mut` to
    /// `solved_formulas` (see [`formulas_mut`](Self::formulas_mut)).
    #[inline]
    pub fn solved_formulas_mut(&mut self) -> &mut Vec<Arc<Guarded>> {
        self.bump_content_stamp();
        self.bump_solved_formulas_stamp();
        &mut self.content.solved_formulas
    }

    /// Bump `formulas_stamp` ONLY (NOT `content_stamp`) and hand out
    /// `&mut Vec<Arc<Guarded>>` for `formulas`.  The untracked-door analog of
    /// [`formulas_mut`](Self::formulas_mut) for whole-system rewriters
    /// (`subst_system_once`, `rename_precise_system`, `sources.rs` shifters):
    /// they manage `content_stamp` / the max caches themselves (bumping
    /// `content_stamp` here would defeat the `subst_system` no-op skip), but the
    /// per-store formula stamp axis still needs invalidation, so this bumps it.
    /// Every untracked `formulas` write routes through here — pinned by the
    /// `content_untracked_callers_are_enumerated` guard test.
    #[inline]
    pub(crate) fn formulas_mut_untracked(&mut self) -> &mut Vec<Arc<Guarded>> {
        self.bump_formulas_stamp();
        &mut self.content.formulas
    }

    /// Bump `solved_formulas_stamp` ONLY and hand out `&mut` to `solved_formulas`
    /// (see [`formulas_mut_untracked`](Self::formulas_mut_untracked)).
    #[inline]
    pub(crate) fn solved_formulas_mut_untracked(&mut self) -> &mut Vec<Arc<Guarded>> {
        self.bump_solved_formulas_stamp();
        &mut self.content.solved_formulas
    }

    /// Bump `content_stamp` and hand out `&mut` to `lemmas`
    /// (see [`formulas_mut`](Self::formulas_mut)).
    #[inline]
    pub fn lemmas_mut(&mut self) -> &mut Vec<Arc<Guarded>> {
        self.bump_content_stamp();
        &mut self.content.lemmas
    }

    /// Set `last_atom`, bumping `content_stamp`.  The sanctioned door for the
    /// scattered `last_atom = ..` writes (except the whole-system rewriters,
    /// which use `content_mut_untracked`).  Callers keep any adjacent max-cache
    /// maintenance (`bump_cache_lvar` / `invalidate_*`).
    #[inline]
    pub fn set_last_atom(&mut self, la: Option<NodeId>) {
        self.bump_content_stamp();
        self.content.last_atom = la;
    }

    // ====== implied-dedup canon cache (stamped, ptr-keyed incremental) ======

    /// The implied-dedup [`CanonTable`] for `formulas`, reusing the cached
    /// generation while `formulas_stamp` is unchanged, else incrementally
    /// rebuilding it under the current stamp.  `canon` maps a store element to
    /// its `(canon Arc, hash)`.  The cache is keyed on the stamp ALONE — a
    /// stamp hit returns entries built by an earlier call's `canon` — so every
    /// caller must pass the same mapping (the sole caller,
    /// `insert_implied_formulas_pass`'s dedup tables, passes
    /// `ImpliedDedupTables::canon`).
    ///
    /// Lazy caller (`insert_implied_formulas_pass` forces this only when a dedup
    /// candidate exists), so a zero-candidate pass never touches the cache.
    pub(crate) fn formulas_canon_table(
        &self,
        canon: impl Fn(&Arc<Guarded>) -> (Arc<Guarded>, u64),
    ) -> Arc<CanonTable> {
        Self::canon_table_for(
            &self.content.formulas,
            self.formulas_stamp.get(),
            &self.formulas_canon_cache,
            canon,
        )
    }

    /// The implied-dedup [`CanonTable`] for `solved_formulas`
    /// (see [`formulas_canon_table`](Self::formulas_canon_table)).
    pub(crate) fn solved_formulas_canon_table(
        &self,
        canon: impl Fn(&Arc<Guarded>) -> (Arc<Guarded>, u64),
    ) -> Arc<CanonTable> {
        Self::canon_table_for(
            &self.content.solved_formulas,
            self.solved_formulas_stamp.get(),
            &self.solved_formulas_canon_cache,
            canon,
        )
    }

    /// Shared stamp-hit / incremental-rebuild logic for both canon caches.
    fn canon_table_for(
        store: &[Arc<Guarded>],
        stamp: u64,
        slot: &RefCell<Option<Arc<CanonTable>>>,
        canon: impl Fn(&Arc<Guarded>) -> (Arc<Guarded>, u64),
    ) -> Arc<CanonTable> {
        let stats = canon_stats_enabled();
        if stats {
            use std::sync::atomic::Ordering::Relaxed;
            let calls = CANON_CALLS.fetch_add(1, Relaxed) + 1;
            if calls % 20_000 == 0 {
                let hits = CANON_HITS.load(Relaxed);
                let incr = CANON_INCR.load(Relaxed);
                let reused = CANON_ENTRY_REUSED.load(Relaxed);
                let canoned = CANON_ENTRY_CANONED.load(Relaxed);
                let entries = reused + canoned;
                eprintln!(
                    "[CANON_STATS] calls={} hits={} ({:.1}%) incr={} entry_reuse={}/{} ({:.1}%)",
                    calls,
                    hits,
                    100.0 * hits as f64 / calls as f64,
                    incr,
                    reused,
                    entries,
                    if entries == 0 {
                        0.0
                    } else {
                        100.0 * reused as f64 / entries as f64
                    },
                );
            }
        }
        // Snapshot the current cached generation (an `Arc` clone) so the
        // `RefCell` borrow ends before a rebuild borrows it mutably below.
        let current = slot.borrow().clone();
        if let Some(cached) = &current {
            if cached.stamp == stamp {
                // Oracle: a stamp hit asserts the store is value/order-identical
                // to the generation that built `cached`.  Rebuild from scratch
                // and assert byte-equality — a mismatch means a `formulas`
                // change did not mint a fresh stamp (an under-bumped write path).
                if tamarin_utils::env_gate!("TAM_RS_VERIFY_CANON_TABLES") {
                    let fresh = Self::build_canon_full(store, stamp, &canon);
                    assert!(
                        canon_entries_eq(&cached.entries, &fresh.entries),
                        "TAM_RS_VERIFY_CANON_TABLES: cached canon table diverges \
                         from a fresh rebuild at a matching stamp — a formula \
                         store write did not bump its per-store stamp"
                    );
                }
                if stats {
                    CANON_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                return Arc::clone(cached);
            }
        }
        if stats {
            CANON_INCR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        // Stamp miss: incrementally rebuild, reusing each entry whose store
        // `Arc` pointer still matches the previous generation.
        let table = Arc::new(Self::build_canon_incremental(
            store,
            stamp,
            current.as_deref(),
            &canon,
        ));
        // Oracle: the pointer-keyed incremental rebuild must be byte-identical
        // to a from-scratch full recanon — a mismatch would mean a reused
        // (canon, hash) belonged to a different value (an ABA / pointer-keying
        // bug), the riskiest part of the design.
        if tamarin_utils::env_gate!("TAM_RS_VERIFY_CANON_TABLES") {
            let fresh = Self::build_canon_full(store, stamp, &canon);
            assert!(
                canon_entries_eq(&table.entries, &fresh.entries),
                "TAM_RS_VERIFY_CANON_TABLES: incremental canon rebuild diverges \
                 from a full recanon — pointer-keyed entry reuse returned a \
                 stale (canon, hash)"
            );
        }
        *slot.borrow_mut() = Some(Arc::clone(&table));
        table
    }

    /// Full (non-incremental) canon table over `store` — every element canoned
    /// afresh.  Backs the verify oracle's from-scratch rebuild.
    fn build_canon_full(
        store: &[Arc<Guarded>],
        stamp: u64,
        canon: &impl Fn(&Arc<Guarded>) -> (Arc<Guarded>, u64),
    ) -> CanonTable {
        let entries = store
            .iter()
            .map(|f| {
                let (c, h) = canon(f);
                (Arc::clone(f), c, h)
            })
            .collect();
        CanonTable { stamp, entries }
    }

    /// Incremental canon table over `store`, reusing `(canon, hash)` from `prev`
    /// for every element whose `Arc` pointer is unchanged (see [`CanonTable`]
    /// for the ABA-safety argument), recanonicalising only the pointer-misses.
    fn build_canon_incremental(
        store: &[Arc<Guarded>],
        stamp: u64,
        prev: Option<&CanonTable>,
        canon: &impl Fn(&Arc<Guarded>) -> (Arc<Guarded>, u64),
    ) -> CanonTable {
        // Pointer → previous generation's `(canon, hash)`.  `prev` stays
        // borrowed for the whole build, pinning every `prev` `src` allocation,
        // so a live `store` `Arc` sharing a pointer is provably the same
        // immutable value.
        let mut prev_by_ptr: tamarin_utils::FastMap<*const Guarded, (&Arc<Guarded>, u64)> =
            tamarin_utils::FastMap::default();
        if let Some(p) = prev {
            prev_by_ptr.reserve(p.entries.len());
            for (src, c, h) in &p.entries {
                prev_by_ptr.insert(Arc::as_ptr(src), (c, *h));
            }
        }
        let stats = canon_stats_enabled();
        let entries = store
            .iter()
            .map(|f| {
                if let Some((c, h)) = prev_by_ptr.get(&Arc::as_ptr(f)) {
                    if stats {
                        CANON_ENTRY_REUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                    return (Arc::clone(f), Arc::clone(c), *h);
                }
                if stats {
                    CANON_ENTRY_CANONED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                let (c, h) = canon(f);
                (Arc::clone(f), c, h)
            })
            .collect();
        CanonTable { stamp, entries }
    }

    /// The rule instance at node `v`, if present. Port of HS `nodeRuleSafe`
    /// (System.hs:911-913): `M.lookup v sNodes`.
    pub fn node_rule_safe(&self, v: &NodeId) -> Option<&RuleACInst> {
        self.nodes.iter().find(|(id, _)| id == v).map(|(_, r)| r)
    }

    /// Read-only `NodeId → &RuleACInst` index for `.get()` lookups,
    /// replacing a per-lookup linear `nodes.iter().find`.  `or_insert`
    /// keeps the FIRST rule for a given id, matching `find`'s /
    /// `node_rule_safe`'s first-match semantics; `nodes` is unique-keyed,
    /// so the map returns the identical rule the linear scan found.
    pub fn node_rule_map(&self) -> NodeRuleMap<'_> {
        let mut m = tamarin_utils::FastMap::default();
        for (n, r) in self.nodes.iter() {
            m.entry(n).or_insert(r);
        }
        m
    }

    /// `sNodes` in `M.toList` / `M.elems` order — see [`nodes_in_map_order`]
    /// for the map/set-order invariant these three helpers materialise.
    pub fn nodes_in_map_order(&self) -> Vec<&(NodeId, RuleACInst)> {
        nodes_in_map_order(&self.nodes)
    }

    /// `sEdges` in `S.toList` order — see [`nodes_in_map_order`].
    pub fn edges_in_set_order(&self) -> Vec<&Edge> {
        let mut ordered: Vec<&Edge> = self.edges.iter().collect();
        ordered.sort();
        ordered
    }

    /// `sLessAtoms` in `S.toList` order — see [`nodes_in_map_order`].
    pub fn less_atoms_in_set_order(&self) -> Vec<&LessAtom> {
        let mut ordered: Vec<&LessAtom> = self.less_atoms.iter().collect();
        ordered.sort();
        ordered
    }

    /// `sGoals` in `M.toList` order, i.e. ascending `Ord Goal` — see
    /// [`nodes_in_map_order`].
    pub(crate) fn goals_in_map_order(&self) -> Vec<&(Goal, GoalStatus)> {
        let mut ordered: Vec<&(Goal, GoalStatus)> = self.goals.iter().collect();
        ordered.sort_by(|a, b| a.0.cmp(&b.0));
        ordered
    }

    /// Walk the free variables of every Haskell `System` field in record order.
    /// `nodes_done` runs between `sNodes` and the remaining fields so
    /// `rename_precise_system` can retain its node-only identity fast path.
    pub(crate) fn for_each_free_with_node_boundary<S: ?Sized>(
        &self,
        state: &mut S,
        mut visit: impl FnMut(&mut S, &LVar),
        nodes_done: impl FnOnce(&mut S),
    ) {
        for (id, rule) in self.nodes_in_map_order() {
            id.for_each_free(&mut |v| visit(state, v));
            rule.for_each_free(&mut |v| visit(state, v));
        }
        nodes_done(state);
        for e in self.edges_in_set_order() {
            e.for_each_free(&mut |v| visit(state, v));
        }
        for la in self.less_atoms_in_set_order() {
            la.for_each_free(&mut |v| visit(state, v));
        }
        self.last_atom.for_each_free(&mut |v| visit(state, v));
        self.subterm_store.for_each_free(&mut |v| visit(state, v));
        self.eq_store.for_each_free(&mut |v| visit(state, v));
        for store in [&self.formulas, &self.solved_formulas, &self.lemmas] {
            for g in formulas_in_set_order(store) {
                g.for_each_free(&mut |v| visit(state, v));
            }
        }
        for entry in self.goals_in_map_order() {
            entry.for_each_free(&mut |v| visit(state, v));
        }
    }

    /// All `In`- and protocol-premise terms in the system, as
    /// `(node, premise, term-index, term)`. Port of HS `allPrems`
    /// (System.hs:894-899).
    ///
    /// ORDER: the node walk is `nodes` INSERTION order, where HS walks
    /// `M.toList sNodes` (ascending `NodeId`).  A caller whose output depends
    /// on the sequence must materialise the map order itself — see
    /// [`nodes_in_map_order`].
    pub fn all_prems(
        &self,
    ) -> Vec<(
        NodeId,
        crate::rule::PremIdx,
        usize,
        tamarin_term::lterm::LNTerm,
    )> {
        let mut out = Vec::new();
        for (i, ru) in self.nodes.iter() {
            for (j, fa) in ru.enumerate_premises() {
                if let Some(ms) = crate::fact::proto_or_in_fact_view(fa) {
                    for (k, m) in ms.into_iter().enumerate() {
                        out.push((*i, j, k, m));
                    }
                }
            }
        }
        out
    }

    /// All unsolved destruction chains, as `(NodeConc, NodePrem)`. Port of HS
    /// `unsolvedChains` (System.hs:1601-1605).
    ///
    /// ORDER: `goals` INSERTION order, where HS walks `M.toList sGoals`
    /// (ascending `Goal`).  A caller that needs the HS sequence sorts the
    /// collected pairs — see `graph::repr::compute_basic_graph_repr`.
    pub fn unsolved_chains(
        &self,
    ) -> impl Iterator<
        Item = (
            crate::constraint::constraints::NodeConc,
            crate::constraint::constraints::NodePrem,
        ),
    > + '_ {
        use crate::constraint::constraints::Goal;
        self.goals.iter().filter_map(|(g, status)| match g {
            Goal::Chain(from, to) if !status.solved => Some((*from, *to)),
            _ => None,
        })
    }

    /// All unsolved action atoms, as `(NodeId, &LNFact)`. Port of HS
    /// `unsolvedActionAtoms` (System.hs:1567-1571).  Same insertion-order
    /// caveat as [`unsolved_chains`](Self::unsolved_chains).
    pub fn unsolved_action_atoms(
        &self,
    ) -> impl Iterator<Item = (NodeId, &crate::fact::LNFact)> + '_ {
        use crate::constraint::constraints::Goal;
        self.goals.iter().filter_map(|(g, status)| match g {
            Goal::Action(i, fa) if !status.solved => Some((*i, fa)),
            _ => None,
        })
    }

    /// All unsolved premise goals, as `(NodePrem, LNFact)`. Port of HS
    /// `unsolvedPremises` (System.hs:1505-1509).  Same insertion-order caveat
    /// as [`unsolved_chains`](Self::unsolved_chains).
    pub fn unsolved_premises(
        &self,
    ) -> Vec<(
        crate::constraint::constraints::NodePrem,
        crate::fact::LNFact,
    )> {
        use crate::constraint::constraints::Goal;
        let mut out = Vec::new();
        for (g, status) in self.goals.iter() {
            if status.solved {
                continue;
            }
            if let Goal::Premise(premidx, fa) = g {
                out.push((*premidx, fa.clone()));
            }
        }
        out
    }

    /// Copy-on-write mutable access to `nodes`.  Clones the inner `Vec`
    /// only if the `Arc` is shared with another `System` (refcount > 1);
    /// otherwise hands out a `&mut` to the existing storage.  Use this
    /// for any in-place mutation of the node list.
    #[inline]
    pub fn nodes_mut(&mut self) -> &mut Vec<(NodeId, RuleACInst)> {
        // Structural content-mutation choke: any `&mut` node access bumps
        // `content_stamp` (unconditional — `subst_system_once` reassigns
        // `self.sys.nodes` directly, never via `nodes_mut`, so this never
        // over-bumps the pass's own node write; a skip stays valid).
        self.bump_content_stamp();
        Arc::make_mut(&mut self.content.nodes)
    }

    /// Copy-on-write mutable access to `goals` (see `nodes_mut`).
    #[inline]
    pub fn goals_mut(&mut self) -> &mut Vec<(Goal, GoalStatus)> {
        Arc::make_mut(&mut self.content.goals)
    }

    /// Copy-on-write mutable access to `eq_store` (see `nodes_mut`).
    #[inline]
    pub fn eq_store_mut(&mut self) -> &mut EquationStore {
        // Coarse SUBST-axis choke: bump `subst_stamp` on ANY `&mut` eq-store
        // access.  Over-reports on conj-only mutations (safe — lost skips
        // only).  `subst_system_once` never calls this on its read path (it
        // clones `eq_store.subst` once), so a fired skip is never invalidated
        // by the pass's own bookkeeping.
        self.bump_subst_stamp();
        // Reach through the sealed wrapper's private field to the inner `Arc`
        // (in-module access) for copy-on-write mutation.
        Arc::make_mut(&mut self.content.eq_store.0)
    }

    /// Copy-on-write mutable access to `subterm_store` (see `nodes_mut`).
    #[inline]
    pub fn subterm_store_mut(&mut self) -> &mut SubtermStore {
        // Structural content-mutation choke for the subterm store: EVERY
        // subterm mutation (external adds, the conjoin graft, AND
        // `subst_system_once`'s own subterm rewrite) routes through here, so
        // one unconditional bump subsumes the whole subterm enumeration.  It
        // over-bumps `subst_system_once`'s own subterm use — a free over-bump:
        // the bump lands DURING the pass, the marker captures the post-pass
        // stamp, and the next skip still fires if no EXTERNAL write intervened.
        self.bump_content_stamp();
        Arc::make_mut(&mut self.content.subterm_store)
    }

    // ====== max_var_idx_cache maintenance ======

    /// Invalidate the cached max-var-idx hint.  Call on any mutation
    /// that could LOWER the max (substitution applied to the system,
    /// eq-store simp, node removal, ...).  Cheap (single `Cell::set`).
    #[inline]
    pub fn invalidate_max_var_idx_cache(&self) {
        // CONTENT-axis choke (shared with the max-var-idx cache): every
        // value-lowering mutation of the nine fields `subst_system_once` reads
        // already funnels through this call, so bumping `content_stamp` here
        // — plus in the additive `bump_cache_*` helpers below — inherits the
        // max-var cache's proven-complete enumeration of content mutations.
        self.bump_content_stamp();
        self.max_var_idx_cache.set(None);
    }

    // ====== node_max_cache maintenance (nodes-only component) ======

    /// Invalidate the cached node-component max.  Call on any mutation
    /// of `sNodes` that could LOWER the node max (node removal / merge,
    /// substitution applied to node terms, alpha-rename).  Independent
    /// of the full-cache invalidation: the ~82 non-node sites clear only
    /// the full cache and MUST leave this one intact.
    #[inline]
    pub fn invalidate_node_max_cache(&self) {
        self.bump_content_stamp();
        self.node_max_cache.set(None);
    }

    /// Bump the node-component cache for a newly-added node id.  No-op
    /// if invalidated (mirrors `bump_cache_lvar`).
    #[inline]
    pub fn bump_node_max_lvar(&self, v: &tamarin_term::lterm::LVar) {
        if let Some(cur) = self.node_max_cache.get() {
            if v.idx > cur {
                self.node_max_cache.set(Some(v.idx));
            }
        }
    }

    /// Bump the node-component cache by walking a newly-added node's
    /// rule (mirrors `bump_cache_rule`).  No-op if invalidated.
    #[inline]
    pub fn bump_node_max_rule(&self, r: &crate::rule::RuleACInst) {
        if let Some(cur) = self.node_max_cache.get() {
            let mut m = cur;
            crate::constraint::solver::reduction::bm_rule_pub(r, &mut m);
            if m != cur {
                self.node_max_cache.set(Some(m));
            }
        }
    }

    /// Bump the node-component cache after a UNIFORM `idx += shift`
    /// applied to every node var (monotone graft/freshen).  Since every
    /// node var's idx rises by exactly `shift`, the max over them rises
    /// by exactly `shift` too — PROVIDED at least one node var exists.
    /// The caller MUST guard on non-empty nodes (an empty node map has
    /// component 0 both before and after, so bumping it would be wrong).
    /// No-op if invalidated.
    #[inline]
    pub fn bump_node_max_by_shift(&self, shift: u64) {
        if let Some(cur) = self.node_max_cache.get() {
            self.node_max_cache.set(Some(cur.saturating_add(shift)));
        }
    }

    /// Shared body of the `bump_cache_*` helpers: bump `content_stamp`, then
    /// raise the cached max-var idx to whatever `walk` leaves in its
    /// argument.  No-op on the cache if it is invalidated.
    ///
    /// CONTENT-axis choke (additive): these helpers are called on every
    /// content-growing write (add_node/edge/less/goal, insert_last, ...).
    /// The stamp bump is UNCONDITIONAL — even when the added value's idx is
    /// <= the cached max (numeric no-op), the field still grew, so the
    /// marker must invalidate.
    #[inline]
    fn bump_cache_with(&self, walk: impl FnOnce(&mut u64)) {
        self.bump_content_stamp();
        if let Some(cur) = self.max_var_idx_cache.get() {
            let mut m = cur;
            walk(&mut m);
            if m != cur {
                self.max_var_idx_cache.set(Some(m));
            }
        }
    }

    /// Bump the cache for a newly-added LVar.
    #[inline]
    pub fn bump_cache_lvar(&self, v: &tamarin_term::lterm::LVar) {
        self.bump_cache_with(|m| {
            if v.idx > *m {
                *m = v.idx;
            }
        });
    }

    /// Bump the cache by walking a term.
    #[inline]
    pub fn bump_cache_term(&self, t: &tamarin_term::lterm::LNTerm) {
        self.bump_cache_with(|m| crate::constraint::solver::reduction::bm_term_pub(t, m));
    }

    /// Bump the cache by walking a fact's terms.
    #[inline]
    pub fn bump_cache_fact(&self, fa: &crate::fact::LNFact) {
        self.bump_cache_with(|m| crate::constraint::solver::reduction::bm_fact_pub(fa, m));
    }

    /// Bump the cache by walking a rule's free vars.
    #[inline]
    pub fn bump_cache_rule(&self, r: &crate::rule::RuleACInst) {
        self.bump_cache_with(|m| crate::constraint::solver::reduction::bm_rule_pub(r, m));
    }

    /// Bump the cache by walking a guarded formula.
    #[inline]
    pub fn bump_cache_guarded(&self, f: &Guarded) {
        self.bump_cache_with(|m| {
            let n = crate::guarded::max_var_idx(f);
            if n > *m {
                *m = n;
            }
        });
    }

    /// Bump the cache by walking a goal.
    #[inline]
    pub fn bump_cache_goal(&self, g: &Goal) {
        // Bump BEFORE the cache-None early return so a goal add still moves
        // `content_stamp` when the max-var cache is currently invalidated.
        self.bump_content_stamp();
        if self.max_var_idx_cache.get().is_none() {
            return;
        }
        match g {
            Goal::Action(i, fa) => {
                self.bump_cache_lvar(i);
                self.bump_cache_fact(fa);
            }
            Goal::Premise(p, fa) => {
                self.bump_cache_lvar(&p.0);
                self.bump_cache_fact(fa);
            }
            Goal::Chain(c, p) => {
                self.bump_cache_lvar(&c.0);
                self.bump_cache_lvar(&p.0);
            }
            Goal::Subterm((s, t)) => {
                self.bump_cache_term(s);
                self.bump_cache_term(t);
            }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }

    /// Add an open goal.  An equal goal already in the store is merged into
    /// (its `looping` flag ORed, its `nr` kept) rather than duplicated — but
    /// the insertion still advances `next_goal_nr`, as HS's does.
    pub fn add_goal(&mut self, g: Goal) {
        // HS has a single goal entry point: `insertGoal goal False`
        // (Reduction.hs:523-524). `add_goal` is exactly that — defer to
        // `add_goal_with_loop_flag` with `looping = false` so both
        // entry points share one counter-advance / dedup / push path.
        self.add_goal_with_loop_flag(g, false);
    }

    /// `insertGoal` mirror with loop-breaker flag — direct port of
    /// Haskell's `insertGoal goal isLoopBreaker`. Marks the goal's
    /// `looping` field so the smart ranker can deprioritise it.
    ///
    /// Haskell uses `M.insertWith combineGoalStatus`:
    ///   combineGoalStatus (GoalStatus s1 a1 l1) (GoalStatus s2 a2 l2) =
    ///     GoalStatus (s1 || s2) (min a1 a2) (l1 || l2)
    /// — so re-inserting a goal that was previously marked `solved` keeps
    /// it solved.
    ///
    /// The key match is `==` on the goal itself.  For Disj goals that is HS's
    /// Map-key match: both sides bind quantified vars by DeBruijn index (RS's
    /// `BVar::Bound`), so a Disj re-fired across proof
    /// positions is structurally identical to the stored one and merges into
    /// it instead of accumulating a second, `solved=false` copy.
    pub fn add_goal_with_loop_flag(&mut self, g: Goal, looping: bool) {
        // HS `insertGoalStatus` (Reduction.hs:516-521) reads
        // `sNextGoalNr` then `succ`s it on EVERY call, including when
        // the goal key already exists (where `insertWith
        // combineGoalStatus` keeps the existing — smaller — nr).
        let age = self.next_goal_nr;
        self.next_goal_nr = self.next_goal_nr.wrapping_add(1);
        let slot_idx = self.goals.iter().position(|(existing, _)| *existing == g);
        if let Some(idx) = slot_idx {
            let slot = &mut self.goals_mut()[idx];
            slot.1.looping = slot.1.looping || looping;
            // combineGoalStatus keeps `min` of the two nrs; the
            // existing one is always smaller, so leave it unchanged.
            return;
        }
        let st = GoalStatus {
            looping,
            nr: age,
            ..Default::default()
        };
        self.bump_cache_goal(&g);
        self.goals_mut().push((g, st));
    }

    /// Insert a new node into the sequent. Replaces an existing entry
    /// for the same id.
    pub fn add_node(&mut self, id: NodeId, rule: RuleACInst) {
        let pos = self.nodes.iter().position(|(k, _)| k == &id);
        if let Some(i) = pos {
            // Rule-replace can LOWER the node max (old rule's max-bearing
            // var may vanish) — invalidate BOTH caches.
            self.invalidate_max_var_idx_cache();
            self.invalidate_node_max_cache();
            self.nodes_mut()[i].1 = rule;
        } else {
            // Pure additive push — bump both the full cache and the
            // node-component cache with the new node's vars.
            self.bump_cache_lvar(&id);
            self.bump_cache_rule(&rule);
            self.bump_node_max_lvar(&id);
            self.bump_node_max_rule(&rule);
            self.nodes_mut().push((id, rule));
        }
    }

    /// Add an edge if not already present.  Low-level raw insert
    /// equivalent of HS `modM sEdges (S.insert e)`.  Callers that mirror
    /// HS's `insertEdges` (Reduction.hs:278-281, which runs
    /// `solveFactEqs`) must use `Reduction::insert_edge`; callers that
    /// mirror HS's raw `modM sEdges` (e.g. `exploitPrem InFact` /
    /// `exploitPrem FreshFact`) should use this directly.
    pub fn add_edge(&mut self, e: Edge) {
        if !self.edges.contains(&e) {
            self.bump_cache_lvar(&e.src.0);
            self.bump_cache_lvar(&e.tgt.0);
            self.content.edges.push(e);
        }
    }

    /// Add a `<` atom if not already present (equality ignores reason).
    /// Self-loops (a < a) are degenerate — they produce immediate
    /// contradictions via the cyclic check.  In most cases such a
    /// self-loop arises from subst_system collapsing two distinct
    /// nodes to the same id AFTER a less-atom between them was already
    /// recorded; the resulting `a < a` is a true contradiction.  We
    /// still add it so the contradiction check catches it.
    pub fn add_less(&mut self, l: LessAtom) {
        // HS `insertLess` = `modM sLessAtoms (S.insert l)`. `Data.Set.insert`
        // REPLACES an existing equal element with the new one, and
        // `Eq`/`Ord LessAtom` ignore the reason tag (Constraints.hs:126-130),
        // so re-inserting the same `(smaller,larger)` with a DIFFERENT reason
        // OVERWRITES the stored reason (last-wins). A first-occurrence-wins
        // dedup would keep the wrong reason — e.g. a GenKey→Alice ordering
        // added first by fresh-uniqueness (`Fresh`) then by injective-fact
        // monotonicity (`InjectiveFacts`, Simplify.hs:589 in `simpInjectiveFactEqMon`) must end up
        // `InjectiveFacts`, driving the less-edge's graph colour. The reason
        // is metadata for rendering only (read solely by `Dot.hs`/graph
        // simplification); replace in place to preserve iteration order.
        // The overwrite alone bumps no `content_stamp`: `subst_system_once`
        // rewrites only `smaller`/`larger` and carries the reason through
        // (reduction.rs), so a reason-only change cannot turn a proven-no-op
        // skip into an observable one.
        if let Some(existing) = self.content.less_atoms.iter_mut().find(|x| **x == l) {
            *existing = l;
        } else {
            self.bump_cache_lvar(&l.smaller);
            self.bump_cache_lvar(&l.larger);
            self.content.less_atoms.push(l);
        }
    }

    /// Build the pair→first-index probe map over the current `less_atoms`.
    /// `entry().or_insert(i)` records the FIRST index per pair, reproducing
    /// `iter_mut().find`'s first-match choice even in the (non-occurring in
    /// practice — `add_less` is the sole dedup path) case of duplicate
    /// pairs.  `LVar` is interned, so each key clone is a pointer copy.
    pub fn build_less_index(&self) -> LessIndex {
        let mut idx: LessIndex = tamarin_utils::FastMap::default();
        for (i, la) in self.less_atoms.iter().enumerate() {
            idx.entry((la.smaller, la.larger)).or_insert(i);
        }
        idx
    }

    /// O(1) indexed twin of [`add_less`](Self::add_less) for hot insertion
    /// loops (`enforce_fresh_ordering_pass`) that probe the same `less_atoms`
    /// Vec many times per pass.  Semantically identical to `add_less`, using
    /// `idx` (built once via [`build_less_index`]) as the dedup probe instead
    /// of the linear `iter_mut().find`:
    ///   * HIT (pair already present) — overwrite the stored atom IN PLACE at
    ///     its first-match index, preserving position and last-wins reason
    ///     (identical to `add_less`'s `*existing = l`); length unchanged.
    ///   * MISS — bump the var-idx cache, push, and record the new index.
    ///
    /// Returns `true` iff a new atom was pushed (Vec length grew), so the
    /// caller can set `changed`/`red.changed` exactly as
    /// [`Reduction::insert_less`](crate::constraint::solver::reduction) does
    /// via its length compare.  Keeps `idx` coherent with the Vec; the caller
    /// must ensure no OTHER path mutates `less_atoms` between the build and
    /// the last indexed insert (within `enforce_fresh_ordering_pass` the only
    /// mutators are these calls — Maude unifiability queries are read-only).
    pub fn add_less_indexed(&mut self, l: LessAtom, idx: &mut LessIndex) -> bool {
        let key = (l.smaller, l.larger);
        if let Some(&pos) = idx.get(&key) {
            self.content.less_atoms[pos] = l;
            false
        } else {
            self.bump_cache_lvar(&l.smaller);
            self.bump_cache_lvar(&l.larger);
            let pos = self.less_atoms.len();
            self.content.less_atoms.push(l);
            idx.insert(key, pos);
            true
        }
    }

    /// Build the `alwaysBefore` adjacency map (`rawLessRel`) underpinning
    /// `alwaysBefore i j` ("True iff `i < j` in every model of the
    /// system"), mirroring Haskell's `Theory.Constraint.System.alwaysBefore`.
    /// `alwaysBefore` is transitive reachability over
    ///   `rawLessRel = sLessAtoms ++ rawEdgeRel`
    /// where
    ///   `rawEdgeRel = sEdges ++ unsolvedChains` (`System.hs`).
    /// **Unsolved chain goals contribute (c.0, p.0) to the less-relation
    /// too** — HS treats an open chain as an implicit edge for purposes
    /// of cycle detection and ordering inference. Without this, RS's
    /// `cyclic` and `has_forbidden_chain` miss contradictions HS catches
    /// (root cause of the StatVerif KU(pcs) over-saturation).
    ///
    /// Hoist this build out of loops via [`always_before_with`] so the
    /// relation is built once per pass and queried many times. The
    /// relation depends only on `&self`, never on the `i`/`j` query
    /// arguments.
    pub fn build_always_before_adj(&self) -> PrebuiltAdj {
        let mut adj: tamarin_utils::FastMap<NodeId, Vec<NodeId>> =
            tamarin_utils::FastMap::default();
        for l in &self.less_atoms {
            adj.entry(l.smaller).or_default().push(l.larger);
        }
        for e in &self.edges {
            adj.entry(e.src.0).or_default().push(e.tgt.0);
        }
        // HS-faithful `unsolvedChains` contribution to rawEdgeRel
        // (`System.hs`).
        for (c, p) in self.unsolved_chains() {
            adj.entry(c.0).or_default().push(p.0);
        }
        PrebuiltAdj { adj }
    }

    /// `alwaysBefore i j` against a prebuilt adjacency map (see
    /// [`build_always_before_adj`](Self::build_always_before_adj)). The BFS
    /// reachability over `rawLessRel` is the `alwaysBefore` query itself;
    /// hoisting the adjacency build out is a pure refactor.
    pub fn always_before_with(&self, adj: &PrebuiltAdj, i: &NodeId, j: &NodeId) -> bool {
        // DELIBERATE deviation from HS `alwaysBefore`: HS's
        // `reachableSet [i] lessRel` seeds the visited set with `i`
        // itself (Data/DAG/Simple.hs:76-79), so `alwaysBefore sys i i`
        // is `True`.  We short-circuit `i == j` to `false`.  This is
        // caller-safe: every live caller already filters equal nodes
        // before reaching here (Less/EqE simplify guards, the
        // `simpInjectiveFactEq` `i /= j` filter, contradictions.rs's
        // `id == c.0` skip), exactly as HS does, so the `i == i => true`
        // result is never observable in either codebase.
        if i == j {
            return false;
        }
        let adj = &adj.adj;
        // BFS from i until j.
        let mut frontier: std::collections::VecDeque<NodeId> = std::collections::VecDeque::new();
        let mut visited = tamarin_utils::FastSet::default();
        frontier.push_back(*i);
        visited.insert(*i);
        while let Some(n) = frontier.pop_front() {
            if let Some(nbrs) = adj.get(&n) {
                for nb in nbrs {
                    if nb == j {
                        return true;
                    }
                    if visited.insert(*nb) {
                        frontier.push_back(*nb);
                    }
                }
            }
        }
        false
    }

    /// `insertLemma`: flatten a top-level `Conj` into individual lemma
    /// entries. Mirrors the Haskell `insertLemma` recursion.
    pub fn insert_lemma(&mut self, l: Guarded) {
        match l {
            Guarded::Conj(items) => {
                for item in items.iter() {
                    self.insert_lemma(item.clone());
                }
            }
            other => {
                if !crate::guarded::stores_contains(&self.lemmas, &other) {
                    self.bump_cache_guarded(&other);
                    self.content.lemmas.push(Arc::new(other));
                }
            }
        }
    }

    pub fn insert_lemmas(&mut self, ls: Vec<Guarded>) {
        for l in ls {
            self.insert_lemma(l);
        }
    }

    /// Direct port of Haskell `isInitialSystem` (`System.hs:828-830`):
    ///   isInitialSystem sys =
    ///     null (get sSolvedFormulas sys) && not (member bot (get sFormulas sys))
    /// where `bot = gfalse()`.  Two conditions: no solved formulas yet, and no
    /// gfalse in the formula set.  This is the gate the automatic-search path
    /// (`rankProofMethods`, ProofMethod.hs:520-548, see line 527) uses to decide whether
    /// `insertInduction` runs — NOT the stricter replay-only `canApplyInduction`
    /// (ProofMethod.hs:264-270), which additionally checks node/goal emptiness
    /// and omits the gfalse check.
    pub fn is_initial(&self) -> bool {
        self.solved_formulas.is_empty()
            && !crate::guarded::stores_contains(&self.formulas, &crate::guarded::gfalse())
    }

    /// Port of Haskell's `cleanup` (`ProofMethod.hs:310-311`):
    ///
    /// Resets the system's variable indices and clears the substitution.
    pub fn cleanup(mut self) -> Self {
        crate::constraint::solver::rename_precise::rename_precise_system(&mut self);
        self.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(Vec::new());
        // The subst is inside `bounds_max`'s walk (dom + range,
        // reduction.rs `bounds_max_rest`), so clearing it can LOWER the
        // max free-var idx — while `rename_precise_system` invalidates
        // the cache only when some var was actually remapped.  After an
        // all-identity rename a pre-populated cache would survive with
        // the pre-clear max (stale-high ⇒ fresh idxs minted above HS's).
        // Invalidate so the next `bounds_max` recomputes post-clear.
        self.invalidate_max_var_idx_cache();
        self
    }
}

// =============================================================================
// HasFrees
// =============================================================================

/// `instance HasFrees GoalStatus` (System.hs:1827-1830): a goal status holds
/// no variable, so it folds to nothing and maps to itself.  The `sGoals` walk
/// reaches it through the pair instance (LTerm.hs:855-860), which is how HS's
/// `M.Map Goal GoalStatus` instance combines a key with its value
/// (LTerm.hs:905-909).
impl HasFrees for GoalStatus {
    fn for_each_free(&self, _f: &mut dyn FnMut(&LVar)) {}

    fn map_free_with(self, _f: &mut dyn FnMut(LVar) -> LVar, _monotone: bool) -> Self {
        self
    }
}

/// `instance HasFrees System` (System.hs:1832-1877).
///
/// The fold visits the thirteen fields of the Haskell record in declaration
/// order (System.hs:383-395); the last three — `sNextGoalNr`, `sSourceKind`
/// and `sDiffSystem` — hold no variable.
///
/// The map rebuilds each `Vec`-backed field in its own STORAGE order, where
/// HS re-establishes the container with `S.fromList` / `M.fromList`
/// (LTerm.hs:903, LTerm.hs:914).  The port's insertion order is what the
/// solver and the printer read back — `conjoin_system` appends to `formulas`,
/// goal numbers follow the `goals` positions — so a re-sort here would move
/// them.  A caller that wants the Haskell rebuild performs it itself, as
/// `rename_precise_system` does.
///
/// `used_sources` and `sources_lemma_universals` have no Haskell counterpart
/// and are carried over untouched, as is `side`.
///
/// The epilogue owns the derived state the rewritten fields invalidate: both
/// max-var-idx caches (the map may LOWER a maximum) and every stamp, since a
/// whole-system rewrite can inherit no verified-no-op verdict.  The equation
/// store is rebuilt through `take_eq_store` / `set_eq_store`, the sanctioned
/// write path for that field.
impl HasFrees for System {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.for_each_free_with_node_boundary(f, |f, v| f(v), |_| {});
    }

    fn map_free_with(mut self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        let nodes = Arc::unwrap_or_clone(std::mem::take(&mut self.content.nodes));
        self.content.nodes = Arc::new(
            nodes
                .into_iter()
                .map(|(id, rule)| {
                    (
                        id.map_free_with(&mut *f, monotone),
                        rule.map_free_with(&mut *f, monotone),
                    )
                })
                .collect(),
        );
        self.content.edges =
            std::mem::take(&mut self.content.edges).map_free_with(&mut *f, monotone);
        self.content.less_atoms =
            std::mem::take(&mut self.content.less_atoms).map_free_with(&mut *f, monotone);
        self.content.last_atom = self.content.last_atom.map_free_with(&mut *f, monotone);
        let subterm_store = Arc::unwrap_or_clone(std::mem::take(&mut self.content.subterm_store));
        self.content.subterm_store = Arc::new(subterm_store.map_free_with(&mut *f, monotone));
        let eq_store = Arc::unwrap_or_clone(self.take_eq_store());
        self.set_eq_store(Arc::new(eq_store.map_free_with(&mut *f, monotone)));
        self.content.formulas =
            std::mem::take(&mut self.content.formulas).map_free_with(&mut *f, monotone);
        self.content.solved_formulas =
            std::mem::take(&mut self.content.solved_formulas).map_free_with(&mut *f, monotone);
        self.content.lemmas =
            std::mem::take(&mut self.content.lemmas).map_free_with(&mut *f, monotone);
        let goals = Arc::unwrap_or_clone(std::mem::take(&mut self.content.goals));
        self.content.goals = Arc::new(goals.map_free_with(&mut *f, monotone));
        self.invalidate_node_max_cache();
        self.invalidate_max_var_idx_cache();
        self.mint_fresh_stamps();
        self
    }
}

// =============================================================================
// `formulaToSystem` — port of the `Theory.Constraint.System.formulaToSystem`
// entry point used by `Theory.Proof.proveLemma`.
// =============================================================================

/// Build the initial constraint system that has to be proven to show
/// the given lemma formula holds modulo `restrictions`.
///
/// - `AllTraces` lemmas are *negated* (we look for a counterexample).
/// - `ExistsTrace` lemmas are kept as-is.
/// - Non-safety restrictions are conjoined into the formula.
/// - Safety restrictions are inserted as known-true lemmas.
pub fn formula_to_system(
    restrictions: Vec<Guarded>,
    source_kind: SourceKind,
    trace_quantifier: crate::theory::TraceQuantifier,
    fm: &Guarded,
) -> System {
    use crate::guarded::{gconj, gnot, is_safety_formula};
    use crate::theory::TraceQuantifier;

    let mut sys = System::empty();
    sys.source_kind = Some(source_kind);
    // Partition restrictions into safety / non-safety.
    let (safety, other_restrictions): (Vec<Guarded>, Vec<Guarded>) =
        restrictions.into_iter().partition(is_safety_formula);

    // Negate AllTraces lemmas; keep ExistsTrace as-is.
    let gf1 = match trace_quantifier {
        TraceQuantifier::ExistsTrace => fm.clone(),
        TraceQuantifier::AllTraces => gnot(fm),
    };
    // Conjoin non-safety restrictions.
    let mut conj_items = vec![gf1];
    conj_items.extend(other_restrictions);
    let gf2 = gconj(conj_items);
    sys.formulas_mut().push(Arc::new(gf2));
    // Safety restrictions are added as known-true lemmas.
    sys.insert_lemmas(safety);
    sys
}

#[cfg(test)]
#[path = "system_tests.rs"]
mod tests;
