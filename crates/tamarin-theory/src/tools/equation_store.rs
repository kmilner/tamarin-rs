// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, beschmi, jdreier, PhilipLukertWork, rkunnema, felixlinker,
//   rsasse, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Maude/Types.hs,
//   lib/term/src/Term/Substitution/SubstVFresh.hs,
//   lib/term/src/Term/Unification.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Sapic/Substitution.hs,
//   lib/theory/src/Theory/Tools/EquationStore.hs,
//   lib/theory/src/Theory/Tools/RuleVariants.hs

//! Port of `Theory.Tools.EquationStore`.
//!
//! The equation store represents a (constrained) disjunction of
//! substitutions. Semantically:
//!
//! ```text
//! EqStore sigma_free
//!         [ [sigma_i1, ..., sigma_ik_i] | i ∈ 1..l ]
//! ```
//!
//! denotes
//!
//! ```text
//!     /\_i (x_i = sigma_free(x_i))
//!  /\ /\_i (sigma_i1 ∨ … ∨ sigma_ik_i)
//! ```
//!
//! where each `sigma_ij` is a *fresh-range* substitution (its
//! variables are existentially quantified).
//!
//! This Rust port exposes both the data structure / Maude-free
//! operations (empty, false-detection, adding a disjunction,
//! performing a split, listing splits) and the Maude-backed
//! operations: `add_eqs`, `apply_eq_store`, and the full `simp`
//! pipeline (`simp_with_fresh_avoiding`,
//! `simp_disjunction_with_maude`).

use std::collections::BTreeSet;

use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::subst::Subst;
use tamarin_term::subst_vfresh::SubstVFresh;

/// Rename "witness" range variables in a Maude unifier to globally
/// fresh indices. A witness is a range var that:
///  1. doesn't appear as a domain variable (otherwise it's a target
///     binding), and
///  2. doesn't appear in the original input equations (otherwise it's
///     a real system variable that Maude is reusing).
///
/// Maude introduces witnesses as `x_N` LVars when it needs auxiliary
/// variables to express a unifier. Without renaming, two separate
/// `add_eqs` calls can return witnesses with the same `x_N` name +
/// idx, causing distinct vars in the system to collapse.
///
/// **Haskell-faithful counter**: indices come from the MaudeHandle's
/// global `fresh_counter` (mirrors `MonadFresh`), NOT from
/// `avoid_max + 1`.  Using the local avoid_max means two calls with
/// the same surrounding system both rename to idxs `avoid_max + 1`,
/// `+ 2`, ... causing inter-call collisions (TESLA::authentic_reachable
/// root cause).  The global counter guarantees every freshened witness
/// gets a globally unique idx.
fn freshen_witness_range(
    raw: Vec<(LVar, LNTerm)>,
    input_vars: &std::collections::BTreeSet<LVar>,
    avoid_max: u64,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Vec<(LVar, LNTerm)> {
    use std::collections::BTreeMap;
    use tamarin_term::lterm::HasFrees;
    let trace = tamarin_utils::env_gate!("TAM_DBG_FRESHEN_WITNESS");
    let domain: BTreeSet<LVar> = raw.iter().map(|(v, _)| v.clone()).collect();
    // Witnesses = range-only vars that are neither a domain key nor an
    // input var (i.e. auxiliaries the Maude unifier introduced); these are
    // the ones that need a globally-unique idx.
    let mut witnesses: BTreeSet<LVar> = BTreeSet::new();
    for (_, t) in &raw {
        t.for_each_free(&mut |w| {
            if domain.contains(w) {
                return;
            }
            if input_vars.contains(w) {
                return;
            }
            witnesses.insert(w.clone());
        });
    }
    if witnesses.is_empty() {
        return raw;
    }
    // Push the global counter above `avoid_max` first, then draw
    // unique indices from it for each witness.
    maude.ensure_above(avoid_max);
    let mut renames: BTreeMap<LVar, LVar> = BTreeMap::new();
    for v in witnesses {
        let next = maude.fresh_idx();
        renames.insert(v.clone(), LVar { idx: next, ..v });
    }
    if trace && !renames.is_empty() {
        eprintln!("[freshen_witness] {} witness renames", renames.len());
    }
    // Apply the rename across each (var, term).  Keys get renamed too.
    raw.into_iter()
        .map(|(v, t)| {
            let new_v = renames.get(&v).cloned().unwrap_or(v);
            let new_t = t.map_free(&mut |w| renames.get(&w).cloned().unwrap_or(w));
            (new_v, new_t)
        })
        .collect()
}

// ============================================================================
// TAM_RS_DBG_IMPURE_FOLD=1 — pure-fresh-range invariant probes.
//
// HS enforces that every var in a VFresh subst's RANGE is fresh (to be
// renamed at application time): Maude unifiers go through
// `msubstToLSubstVFresh` which ERRORS on non-fresh range vars
// (Maude/Types.hs:121-130), and `composeVFresh` lifts live vars entering a
// VFresh range via `extendWithRenaming (varsRange s2) s1_0`
// (Substitution.hs:39-47).  Any RS site that stores a disjunction subst
// whose range references a LIVE system var violates this invariant; when
// `simpSingleton` later folds such a subst, `fresh_to_free_avoiding`
// renames the live var and severs its linkage to the system.
//
// These probes are zero-cost when the env var is unset.  The origin
// registry maps a subst fingerprint to the label of the site that created
// it, so an impure FOLD can be traced back to its CREATION site.
// ============================================================================

#[inline]
pub(crate) fn impure_dbg_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DBG_IMPURE_FOLD")
}

// --- Cached kill-switch / debug env flags for apply_eq_store -----------
// `apply_eq_store` is one of the hottest solver methods (per proof step,
// plus recursively from every simp pass).  These env vars are constant
// for the process, so each accessor caches its presence via `env_gate!`
// (`.is_ok()`) — the steady-state cost is an atomic load, not an env-lock
// + `String` alloc per call / per variant.  The lone exception,
// `aes_dbg_filter_substantive`, matches an exact value (`== "substantive"`)
// and so keeps its hand-rolled `OnceLock<bool>`.
#[inline]
fn aes_dbg() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_EQ_STORE")
}
/// `TAM_RS_DBG_APPLY_EQ_STORE_FILTER` selects the "substantive" filter by
/// exact value, so cache the equality test (not a bare `.is_ok()`).
#[inline]
fn aes_dbg_filter_substantive() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("TAM_RS_DBG_APPLY_EQ_STORE_FILTER")
            .map(|s| s == "substantive")
            .unwrap_or(false)
    })
}
#[inline]
fn aes_dbg_variant() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_AES_VARIANT")
}
#[inline]
fn aes_dbg_detail() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DBG_AES_DETAIL")
}
#[inline]
fn aes_dbg_raw_unifier() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_RAW_UNIFIER")
}
#[inline]
fn aes_dbg_variants() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_AES_VARIANTS")
}
#[inline]
fn aes_dbg_bad_disj() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_BAD_DISJ")
}
#[inline]
fn aes_dbg_add_disj_full() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_ADD_DISJ_FULL")
}
#[inline]
fn aes_dbg_add_disj() -> bool {
    tamarin_utils::env_gate!("TAM_DBG_ADD_DISJ")
}
/// `TAM_TRACE_SET_FALSE` debug flag (opt-IN), read on the solve-path
/// `set_false`.  Cached so the steady-state cost is an atomic load.
#[inline]
fn aes_trace_set_false() -> bool {
    tamarin_utils::env_gate!("TAM_TRACE_SET_FALSE")
}
/// `TAM_TRACE_SET_FALSE_FULL` debug flag (opt-IN), read on the solve-path
/// `set_false`.  Cached so the steady-state cost is an atomic load.
#[inline]
fn aes_trace_set_false_full() -> bool {
    tamarin_utils::env_gate!("TAM_TRACE_SET_FALSE_FULL")
}

// debug-only keyed registry; never reaches prover output;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn impure_dbg_registry() -> &'static std::sync::Mutex<std::collections::HashMap<String, String>> {
    static REG: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<String, String>>> =
        std::sync::OnceLock::new();
    REG.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

fn impure_dbg_fp(s: &SubstVFresh<Name, LVar>) -> String {
    format!("{:?}", s.to_list())
}

/// Register `s` as having been created/last-transformed at `label`.
/// First-wins: pass-through sites (e.g. perform_split) re-register the
/// same fingerprint, preserving the ORIGINAL creator's label.
pub fn dbg_register_subst_origin(label: &str, s: &SubstVFresh<Name, LVar>) {
    if !impure_dbg_enabled() {
        return;
    }
    impure_dbg_registry()
        .lock()
        .unwrap()
        .entry(impure_dbg_fp(s))
        .or_insert_with(|| label.to_string());
}

/// Chain-register: a transformation site registers its OUTPUT subst with
/// a label that includes the INPUT subst's origin, preserving provenance
/// across rewrites (applyBound, simp passes).
pub fn dbg_register_subst_transform(
    label: &str,
    input: &SubstVFresh<Name, LVar>,
    output: &SubstVFresh<Name, LVar>,
) {
    if !impure_dbg_enabled() {
        return;
    }
    let mut reg = impure_dbg_registry().lock().unwrap();
    let in_origin = reg
        .get(&impure_dbg_fp(input))
        .cloned()
        .unwrap_or_else(|| "?".to_string());
    reg.entry(impure_dbg_fp(output))
        .or_insert_with(|| format!("{}<-{}", label, in_origin));
}

pub fn dbg_subst_origin(s: &SubstVFresh<Name, LVar>) -> String {
    impure_dbg_registry()
        .lock()
        .unwrap()
        .get(&impure_dbg_fp(s))
        .cloned()
        .unwrap_or_else(|| "unknown".to_string())
}

/// Range vars of `s` that intersect `live` — nonempty means the
/// pure-fresh-range invariant is violated w.r.t. that live set.
pub fn dbg_impure_range_vars(s: &SubstVFresh<Name, LVar>, live: &BTreeSet<LVar>) -> Vec<LVar> {
    s.vars_range()
        .into_iter()
        .filter(|v| live.contains(v))
        .collect()
}

/// Index of a disjunction in the equation store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SplitId(pub i64);

impl SplitId {
    pub fn succ(self) -> Self {
        SplitId(self.0 + 1)
    }
}

/// Convenient alias for the substitution type the solver uses on the
/// "free" (currently-fixed) part of the equation store.
pub type LNSubst = Subst<Name, LVar>;

/// Convenient alias for the fresh-range substitutions stored in
/// disjunctions.
pub type LNSubstVFresh = SubstVFresh<Name, LVar>;

/// The domain/range pairs of `s` with the mapping for `v` dropped,
/// in `to_list` order. Shared head of the `simp_abstract_*` /
/// `simp_identify` passes, which each rebuild a disjunct's substs
/// after removing the abstracted domain key and appending their own
/// pass-specific mappings.
fn without_key(s: &LNSubstVFresh, v: &LVar) -> Vec<(LVar, LNTerm)> {
    s.to_list().into_iter().filter(|(x, _)| x != v).collect()
}

/// One entry in the disjunctive part of the store: a `SplitId`
/// alongside the set of substitutions making up that disjunction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqDisj {
    pub split_id: SplitId,
    pub substs: Vec<LNSubstVFresh>,
}

/// `EqStore`. Mirrors Haskell's `EqStore { _eqsSubst, _eqsConj,
/// _eqsNextSplitId }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EquationStore {
    /// "Free" substitution — currently-fixed bindings of the global
    /// variables. Composes with everything else.
    pub subst: LNSubst,
    /// Conjunction of disjunctions.
    pub conj: Vec<EqDisj>,
    pub next_split: SplitId,
}

impl Default for EquationStore {
    fn default() -> Self {
        Self::empty()
    }
}

impl EquationStore {
    pub fn empty() -> Self {
        EquationStore {
            subst: LNSubst::empty(),
            conj: Vec::new(),
            next_split: SplitId(0),
        }
    }

    /// `True` iff the store is contradictory (i.e. contains an empty
    /// disjunction).
    pub fn is_false(&self) -> bool {
        self.conj.iter().any(|d| d.substs.is_empty())
    }

    /// The conjunction representing logical false (split id `-1` and
    /// an empty disjunction).
    pub fn false_conj() -> Vec<EqDisj> {
        vec![EqDisj {
            split_id: SplitId(-1),
            substs: Vec::new(),
        }]
    }

    /// Set the store to logical false. Returns the modified store.
    pub fn set_false(mut self) -> Self {
        if aes_trace_set_false() && !self.is_false() {
            let bt = std::backtrace::Backtrace::force_capture();
            let bt_s = format!("{bt}");
            let caller = bt_s
                .lines()
                .filter(|l| {
                    l.contains("tamarin_theory")
                        || l.contains("tamarin-theory")
                        || l.contains("tamarin_term")
                })
                .filter(|l| !l.contains("set_false"))
                .nth(0)
                .unwrap_or("(no frame)")
                .trim();
            eprintln!("[set_false] caller={}", caller);
        }
        if aes_trace_set_false_full() && !self.is_false() {
            let bt = std::backtrace::Backtrace::force_capture();
            let bt_s = format!("{bt}");
            let cpath = crate::constraint::solver::trace::case_path_string();
            let frames: Vec<&str> = bt_s
                .lines()
                .filter(|l| {
                    l.contains("tamarin_theory")
                        || l.contains("tamarin-theory")
                        || l.contains("tamarin_term")
                })
                .filter(|l| !l.contains("set_false"))
                .filter(|l| !l.contains("std::"))
                .take(8)
                .map(|s| s.trim())
                .collect();
            eprintln!(
                "[set_false_full] path={} frames=[ {} ]",
                cpath,
                frames.join(" | ")
            );
        }
        self.conj = Self::false_conj();
        self
    }

    /// Add a new disjunction to the front of the conjunction. Returns
    /// the resulting store and the new split id.
    ///
    /// TAM_DBG_ADD_DISJ=1 logs each add_disj call's substs at runtime.
    pub fn add_disj(&mut self, substs: Vec<LNSubstVFresh>) -> SplitId {
        let id = self.next_split;
        // TAM_DBG_BAD_DISJ=1: print backtrace when a disj subst has two
        // distinct keys mapping to the same VTerm value (the canonical
        // KAS-divergence pattern: ~ltkA.0 and ~ltkA.1 both → ~ltkA.X).
        if aes_dbg_bad_disj() {
            for s in &substs {
                let entries: Vec<(LVar, LNTerm)> = s.to_list();
                let mut seen: std::collections::BTreeMap<String, (LVar, LVar)> =
                    std::collections::BTreeMap::new();
                let mut found_bad = false;
                for (k, v) in &entries {
                    if let tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(vv)) = v {
                        let v_str = format!("{}.{}", vv.name, vv.idx);
                        if let Some((prev_k, _)) = seen.get(&v_str) {
                            if prev_k.name == k.name && prev_k != k {
                                eprintln!(
                                    "[BAD_DISJ] FOUND collision: {}.{} and {}.{} both → {}",
                                    prev_k.name, prev_k.idx, k.name, k.idx, v_str
                                );
                                found_bad = true;
                                break;
                            }
                        }
                        seen.insert(v_str, (k.clone(), vv.clone()));
                    }
                }
                if found_bad {
                    eprintln!("[BAD_DISJ] full subst:");
                    for (k, v) in &entries {
                        eprintln!(
                            "[BAD_DISJ]   {}.{}/{:?} → {:?}",
                            k.name,
                            k.idx,
                            k.sort,
                            format!("{:?}", v).chars().take(80).collect::<String>()
                        );
                    }
                    let bt = std::backtrace::Backtrace::force_capture();
                    let bt_s = format!("{}", bt);
                    let frames: Vec<&str> = bt_s
                        .lines()
                        .filter(|l| l.contains("tamarin_") || l.contains(".rs:"))
                        .take(30)
                        .collect();
                    eprintln!("[BAD_DISJ] backtrace:\n{}", frames.join("\n"));
                }
            }
        }
        if aes_dbg_add_disj_full() {
            // Full backtrace + pre-state for every call.
            let bt = std::backtrace::Backtrace::force_capture();
            let bt_s = format!("{}", bt);
            let frames: Vec<&str> = bt_s
                .lines()
                .filter(|l| l.contains("tamarin_theory") || l.contains("add_disj"))
                .take(8)
                .collect();
            let self_id = self as *const _ as usize;
            eprintln!(
                "[add_disj-full-bt] eq_store@{:x} {}",
                self_id,
                frames.join(" | ")
            );
            eprintln!(
                "[add_disj-full-pre] eq_store@{:x} eqsSubst: {:?}",
                self_id,
                self.subst.to_list()
            );
            eprintln!(
                "[add_disj-full-pre] eq_store@{:x} {} existing disjs, next_split={:?}",
                self_id,
                self.conj.len(),
                self.next_split
            );
        }
        if aes_dbg_add_disj() {
            // TAM_DBG_ADD_DISJ=stack also prints a short backtrace of the
            // caller chain, filtered to tamarin-theory frames.
            if std::env::var("TAM_DBG_ADD_DISJ")
                .map(|s| s == "stack")
                .unwrap_or(false)
            {
                let bt = std::backtrace::Backtrace::force_capture();
                let bt_s = format!("{}", bt);
                let frames: Vec<&str> = bt_s
                    .lines()
                    .filter(|l| l.contains("tamarin_theory") || l.contains("equation_store"))
                    .take(10)
                    .collect();
                eprintln!("[add_disj-bt] {}", frames.join(" | "));
            }
            eprintln!("[add_disj] split_id={:?} {} substs", id, substs.len());
            for (i, s) in substs.iter().enumerate() {
                let pairs: Vec<String> = s
                    .to_list()
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "{}:{:?}:{}→{:?}",
                            k.name,
                            k.sort,
                            k.idx,
                            format!("{:?}", v).chars().take(80).collect::<String>()
                        )
                    })
                    .collect();
                eprintln!("[add_disj]   [{}]: {}", i, pairs.join(" ; "));
            }
        }
        // HS-faithful Set ordering of variant substs.
        // HS's `addDisj` (EquationStore.hs) does `addDisj eqStore
        // (S.fromList substs)` — substs go into a Set, sorted by Ord
        // LNSubstVFresh.  Without sorting here, RS's `Vec`-based disj
        // preserves insertion order from `maude.variants()`, putting
        // the identity-rename variant first.  HS's Set-based disj puts
        // STRUCTURED variants first (where convertpcs is reduced to
        // sign via Maude equations).  Downstream `simp_identify`
        // iterates the FIRST subst's entries — HS finds same-image
        // pairs in the structured variant, RS sees only the identity
        // variant's unreduced entries and finds none.
        let mut substs = substs;
        substs.sort();
        substs.dedup();
        self.conj.insert(
            0,
            EqDisj {
                split_id: id,
                substs,
            },
        );
        self.next_split = id.succ();
        id
    }

    /// Sorted list of split-ids by disjunction size (ascending).
    /// Mirrors Haskell's `splits`.
    pub fn splits(&self) -> Vec<SplitId> {
        let mut indexed: Vec<(SplitId, usize)> = self
            .conj
            .iter()
            .map(|d| (d.split_id, d.substs.len()))
            .collect();
        indexed.sort_by_key(|(_, sz)| *sz);
        // Mirrors Haskell's `nub`, but split-ids in `conj` are unique by
        // construction (`add_disj` assigns a fresh incrementing id and never
        // reuses one; the only other id is the lone `SplitId(-1)` false_conj),
        // so the dedup is provably a no-op and is elided.
        indexed.into_iter().map(|(id, _)| id).collect()
    }

    /// Number of cases for a given split id.
    pub fn split_size(&self, id: SplitId) -> Option<usize> {
        self.conj
            .iter()
            .find(|d| d.split_id == id)
            .map(|d| d.substs.len())
    }

    pub fn split_exists(&self, id: SplitId) -> bool {
        self.split_size(id).is_some()
    }

    /// Perform a case-split on the given disjunction, returning one
    /// fresh `EquationStore` per case.
    ///
    /// Returns `None` if no disjunction with `id` exists.
    pub fn perform_split(&self, id: SplitId) -> Option<Vec<EquationStore>> {
        let pos = self.conj.iter().position(|d| d.split_id == id)?;
        let disj = &self.conj[pos];

        // For each substitution in the chosen disjunction, build a new
        // store that drops `id` and adds a fresh single-case
        // disjunction containing just that subst.
        //
        // Mirrors Haskell `performSplit` (EquationStore.hs) with
        // the canonical-split-ordering fix (see the two-stage sort below):
        //   mkNewEqStore before after <$> orderedSubsts
        let mut sorted_substs: Vec<LNSubstVFresh> = disj.substs.clone();
        if tamarin_utils::env_gate!("TAM_DBG_PERFORM_SPLIT") {
            eprintln!(
                "[perform_split] split_id={:?}, {} substs (pre-sort):",
                id,
                sorted_substs.len()
            );
            for (i, s) in sorted_substs.iter().enumerate() {
                eprintln!("[perform_split]   raw[{}]: {:?}", i, s.to_list());
            }
            // Show full eq_store.subst too — system substitution at this point
            eprintln!("[perform_split] eq_store.subst entries:");
            for (k, v) in self.subst.to_list() {
                eprintln!("[perform_split]   {:?} → {:?}", k, v);
            }
        }
        // Canonical-split-ordering: mirror HS
        //   orderedSubsts = sortOnMemo dropNameHintsLNSubstVFresh . S.toList
        // (the chosen "Fix2" of the proof -N nondeterminism fix, which
        // retires the witness-numbering "Fix1" in favour of canonicalising
        // the SPLIT-CASE order directly).
        //
        // `sort()` is the `Data.Set LNSubstVFresh` `S.toList` raw-`Ord`
        // order.  The stable `sort_by_cached_key(drop_name_hints)` then
        // re-sorts by the α-canonical key (`drop_name_hints` =
        // `dropNameHintsLNSubstVFresh`, EquationStore.hs), which
        // renumbers each subst's fresh witness range-vars by first
        // appearance in domain-key order.  This makes `split_case_i` order
        // independent of the Maude fresh-allocation counter (Rust's witness
        // indices need not equal HS's), so case order is α-canonical and
        // does not regress to the `analysis incomplete` symptom.  HS's
        // `dropNameHintsBound` does NOT reach here: it is mapped only over
        // the throwaway `addNormSys` copy in `removeRedundantCases`
        // (Sources.hs:244-246, `map (fst . snd) ...` keeps the ORIGINAL
        // case and discards the name-hint-dropped system; gated on
        // `enableBP || enableMSet`), so it never mutates the live
        // `sEqStore` that `performSplit` later splits.
        sorted_substs.sort();
        sorted_substs.sort_by_cached_key(|s| s.drop_name_hints());
        if tamarin_utils::env_gate!("TAM_DBG_PERFORM_SPLIT") {
            eprintln!("[perform_split] sorted result:");
            for (i, s) in sorted_substs.iter().enumerate() {
                eprintln!("[perform_split]   case_{}: {:?}", i + 1, s.to_list());
            }
        }
        let mut out = Vec::with_capacity(sorted_substs.len());
        for subst in sorted_substs {
            let mut new_store = self.clone();
            new_store.conj.remove(pos);
            new_store.add_disj(vec![subst]);
            out.push(new_store);
        }
        Some(out)
    }

    /// Compute a baseline for fresh-witness allocation: max var idx
    /// across the eq-store's domain and range.
    fn fresh_baseline(&self) -> u64 {
        use tamarin_term::lterm::HasFrees;
        let mut m = 0u64;
        for v in self.subst.dom() {
            if v.idx > m {
                m = v.idx;
            }
        }
        for t in self.subst.range() {
            t.for_each_free(&mut |w| {
                if w.idx > m {
                    m = w.idx;
                }
            });
        }
        for d in &self.conj {
            for s in &d.substs {
                for v in s.dom() {
                    if v.idx > m {
                        m = v.idx;
                    }
                }
                for t in s.range() {
                    t.for_each_free(&mut |w| {
                        if w.idx > m {
                            m = w.idx;
                        }
                    });
                }
            }
        }
        m
    }

    /// Maude-backed `addEqs` with a caller-supplied freshness baseline.
    /// `extra_avoid` is the max idx seen anywhere in the surrounding
    /// system (beyond just the eq-store).  Without this, Maude
    /// witnesses get renamed using only the eq-store's max idx, which
    /// can collide with vars in nodes/edges/goals/formulas — leading
    /// to the variable conflation bug.
    pub fn add_eqs_with_avoid(
        &mut self,
        maude: &tamarin_term::maude_proc::MaudeHandle,
        eqs: &[tamarin_term::rewriting::Equal<LNTerm>],
        extra_avoid: u64,
    ) -> Result<Option<SplitId>, AddEqsError> {
        self.add_eqs_inner(maude, eqs, extra_avoid)
    }

    /// Maude-backed `addEqs` with a ZERO freshness baseline.  Equivalent to
    /// `add_eqs_with_avoid(maude, eqs, 0)`.
    ///
    /// TEST-ONLY: solver code MUST use `add_eqs_with_avoid` with the
    /// surrounding system's max var idx.  With a zero baseline, Maude
    /// witnesses are renamed using only the eq-store's own max idx, which can
    /// collide with vars in nodes/edges/goals/formulas — the variable
    /// conflation bug documented on `add_eqs_with_avoid`.  Gated behind
    /// `#[cfg(test)]` so it cannot be reintroduced on a solve path.
    ///
    /// Returns the new split id if the unification produced a non-trivial
    /// disjunction; `None` if the unifier was either single (already
    /// composed into `subst`) or empty (store becomes false).
    #[cfg(test)]
    pub fn add_eqs(
        &mut self,
        maude: &tamarin_term::maude_proc::MaudeHandle,
        eqs: &[tamarin_term::rewriting::Equal<LNTerm>],
    ) -> Result<Option<SplitId>, AddEqsError> {
        self.add_eqs_inner(maude, eqs, 0)
    }

    fn add_eqs_inner(
        &mut self,
        maude: &tamarin_term::maude_proc::MaudeHandle,
        eqs: &[tamarin_term::rewriting::Equal<LNTerm>],
        extra_avoid: u64,
    ) -> Result<Option<SplitId>, AddEqsError> {
        // Short-cut: empty input → no change.
        if eqs.is_empty() {
            return Ok(None);
        }

        // Apply the existing free substitution to the input first so the
        // unifier sees the most-refined version of each side.
        let applied: Vec<tamarin_term::rewriting::Equal<LNTerm>> = eqs
            .iter()
            .map(|e| tamarin_term::rewriting::Equal {
                lhs: tamarin_term::subst::apply_vterm(&self.subst, e.lhs.clone()),
                rhs: tamarin_term::subst::apply_vterm(&self.subst, e.rhs.clone()),
            })
            .collect();

        // Haskell-faithful factored unification (Unification.hs:107-120):
        // first run the local non-AC unifier; only AC residuals go to
        // Maude.  When `unifyLTermFactored` returns `Just (m, [])`, the
        // result is the local subst directly — NO Maude call.  This is
        // critical for foo_eligibility-style cases: the local unifier
        // orients same-sort var-var with larger-idx-as-key
        // (Unification.hs:235-243, see line 241), so stable pattern vars (small idx like
        // t.1, t.2) stay on the value side and are dropped by
        // `restrict stableVars` (Sources.hs:113-137, see line 118).
        let local_result = tamarin_term::unification::unify_lnterm_factored(applied.clone());
        let local_result = match local_result {
            Some(r) => r,
            None => {
                // Local non-AC failed → no unifier.
                *self = self.clone().set_false();
                return Ok(None);
            }
        };
        let (local_subst, ac_residuals) = local_result;

        // Fast path: no AC residuals.  Use local subst directly — this
        // mirrors Haskell's `solve _ (Just (m, [])) = (substFromMap m,
        // [emptySubstVFresh])` followed by `flattenUnif` which produces
        // a single SubstVFresh equal to the local subst.
        //
        // HS-faithful (EquationStore.hs `addEqs`):
        //     (subst, [substFresh]) | substFresh == emptySubstVFresh ->
        //         return (applyEqStoreAt "addEqs.single-unifier" hnd subst eqStore, Nothing)
        // — applyEqStoreAt is called UNCONDITIONALLY, including when subst
        // is empty.  With an empty asubst the disj loop is idempotent on
        // disj substs whose KEYS are disjoint from self.subst.dom (the
        // addRuleVariants invariant), BUT applyBound's restrict expansion
        // to include `varsRange(newsubst)` lifts system-var range
        // references in disj substs into the disj domain via
        // EXTRACT-SYSTEM-VARS-TO-DOMAIN (see apply_eq_store body).  The
        // empty-empty case must NOT be short-circuited — skipping this
        // lift is observable on the LAK06::noninjectiveagreementTAG path.
        if ac_residuals.is_empty() {
            if !local_subst.is_empty() {
                log_fresh_bindings("local", &local_subst);
                log_s_pub_bindings("local", &local_subst);
                log_vr_node_bindings("local", &local_subst);
            }
            if self.conj.is_empty() {
                if aes_dbg() {
                    let filter = aes_dbg_filter_substantive();
                    if !filter {
                        eprintln!(
                            "[rs-aes-tick] conj=0 substantive=false (short-circuit:add_eqs-no-ac)"
                        );
                    }
                }
                if !local_subst.is_empty() {
                    self.subst = local_subst.compose(&self.subst);
                }
            } else {
                self.apply_eq_store(maude, &local_subst)?;
            }
            return Ok(None);
        }

        // Maude path: log the AC unifier output (if single) — handled below.

        // Mixed case: AC residuals exist.  Send them to Maude after
        // applying local subst.  Each Maude unifier is composed with
        // the local subst at the end (mirrors `flattenUnif` =
        // `map (\`composeVFresh\` subst) substs`).
        //
        // HS-faithful (EquationStore.hs:311-313 `addEqs`): the AC unifier
        // is `unifyLNTermFactored eqs` with NO avoid — witness idxs are
        // numbered purely per-call at `avoid (M.elems bindings)`
        // (Term/Maude/Types.hs:112-113) and the resulting `SubstVFresh`
        // witnesses are α-scoped per subst, so a system-wide floor is
        // neither passed nor needed.  (The single-unifier arm below still
        // re-bases its own witnesses via `freshen_witness_range`.)
        let unifiers = maude
            .unify_at("eq_store::add_eqs", &ac_residuals)
            .map_err(|e| AddEqsError::Maude(format!("{}", e)))?;

        if unifiers.is_empty() {
            if tamarin_utils::env_gate!("TAM_DBG_NOUNIFY") {
                eprintln!("[nounify] add_eqs found 0 unifiers for:");
                for e in &applied {
                    let l = format!("{:?}", e.lhs).chars().take(150).collect::<String>();
                    let r = format!("{:?}", e.rhs).chars().take(150).collect::<String>();
                    eprintln!("[nounify]   {} = {}", l, r);
                }
            }
            // No unifiers → contradiction.
            *self = self.clone().set_false();
            return Ok(None);
        }
        // HS-faithful (EquationStore.hs `addEqs`): the compose-without-disj
        // arm fires ONLY when the unifier list is exactly
        // `[emptySubstVFresh]`:
        //     (subst, [substFresh]) | substFresh == emptySubstVFresh ->
        //         return (applyEqStoreAt "addEqs.single-unifier" hnd subst
        //                                eqStore, Nothing)
        // A SINGLE NON-EMPTY Maude unifier hits HS's THIRD arm
        // (EquationStore.hs `addEqs`):
        //     (subst, substs) -> addDisj (applyEqStoreAt ... subst eqStore)
        //                                (S.fromList substs)  -- Just sid
        // — it's stored as a SINGLETON VFresh disjunction (with split id),
        // NOT eagerly composed.  Faithful HS behaviour: (a) the fold
        // happens via `simp`'s `simpSingleton`
        // (`freshToFree` witness naming, EquationStore.hs `simpSingleton`)
        // plus a SECOND `applyEqStoreAt "foreachDisj:simpSingleton"` round
        // over the remaining disjs (EquationStore.hs `foreachDisj`) — two
        // applyBound
        // rounds with the local subst and the Maude unifier SEPARATELY,
        // not one round with their composition; (b) SplitLater callers get
        // a SplitG goal + a live singleton disj (HS Reduction.hs:616-618, see line 618
        // `solveRuleEqs SplitLater`, addEqs/performSplit at 719-725);
        // (c) addDisj bumps the next-split-id counter.
        // (Paired HS/RS traces on Scott::key_secrecy show applyBound never
        // SPLITS a disj subst on this corpus — out>1 occurs 0 times on
        // both sides — so this arm's role is naming/cadence/goal-counter
        // alignment, not disj expansion.)
        if unifiers.len() == 1 && unifiers[0].is_empty() {
            // Single unifier composes directly into the free substitution.
            // BUT first rename the witness range vars (vars Maude
            // introduced as auxiliaries that aren't in the input nor
            // in the unifier's domain) to globally fresh indices.
            // Without this, two separate unifications can produce
            // colliding witness names and spuriously equate unrelated
            // vars.
            let raw: Vec<(LVar, LNTerm)> = unifiers.into_iter().next().unwrap();
            // Collect input vars from the AC residuals (Maude's input).
            use tamarin_term::lterm::HasFrees;
            let mut input_vars: std::collections::BTreeSet<LVar> =
                std::collections::BTreeSet::new();
            for e in &ac_residuals {
                e.lhs.for_each_free(&mut |v| {
                    input_vars.insert(v.clone());
                });
                e.rhs.for_each_free(&mut |v| {
                    input_vars.insert(v.clone());
                });
            }
            let raw = freshen_witness_range(
                raw,
                &input_vars,
                self.fresh_baseline().max(extra_avoid),
                maude,
            );
            // `raw` is a Maude idempotent (solved-form) unifier: its range
            // is disjoint from its domain (freshen_witness_range only renames
            // range-only witnesses, never domain keys), so the one-at-a-time
            // `compose` accumulation collapses to a single `from_list` build.
            let maude_subst = LNSubst::from_list(raw);
            // Haskell-faithful: compose local_subst with Maude's result
            // (Unification.hs:145-146, see line 147 `flattenUnif` =
            // `map (\`composeVFresh\` subst) substs`).
            let subst = maude_subst.compose(&local_subst);
            log_fresh_bindings("maude_single", &subst);
            log_s_pub_bindings("maude_single", &subst);
            log_vr_node_bindings("maude_single", &subst);
            // Haskell-faithful: call applyEqStore so existing disj substs
            // get re-unified against the new free subst.  Without it,
            // SplitG variants whose domain intersects with `subst.dom`
            // silently get their constraints dropped on later pick
            // (e.g. `{z → verify(s,m,pkA)}` vs `{z → true}` collapse).
            // Mirrors EquationStore.hs `addEqs` (single-unifier arm).
            if self.conj.is_empty() {
                if aes_dbg() {
                    let filter = aes_dbg_filter_substantive();
                    if !filter {
                        eprintln!("[rs-aes-tick] conj=0 substantive=false (short-circuit:add_eqs-single-maude)");
                    }
                }
                // Fast path: nothing to re-unify, just compose.
                self.subst = subst.compose(&self.subst);
            } else {
                // Slow path: re-unify each disj subst.
                self.apply_eq_store(maude, &subst)?;
            }
            return Ok(None);
        }

        // Multiple unifiers — or a SINGLE NON-EMPTY unifier (HS's third
        // arm, EquationStore.hs `addEqs`; see comment above) — record as
        // a fresh-range disjunction.
        // Haskell composes each Maude unifier with the local subst
        // before storing as a disjunction (flattenUnif semantics).
        // The local subst becomes part of the free subst; the Maude
        // unifiers represent the disjunction over AC choices.
        //
        // HS-faithful (EquationStore.hs `addEqs`):
        //     let (eqStore', sid) = addDisj (applyEqStoreAt "addEqs.multi-unifier"
        //                                                   hnd subst eqStore)
        //                                   (S.fromList substs)
        // applyEqStoreAt is called unconditionally, even when local_subst
        // is empty, so existing disjs are re-narrowed via applyBound
        // against the new free subst — this matters because a later pass
        // (e.g. simp_singleton / abstraction factoring) can land bindings
        // in eqsSubst that narrow an untouched multi-subst disj to empty
        // (LAK06::noninjectiveagreementTAG's accepttag disj), which HS's
        // unconditional call captures.
        if self.conj.is_empty() {
            if aes_dbg() {
                let filter = aes_dbg_filter_substantive();
                if !filter {
                    eprintln!("[rs-aes-tick] conj=0 substantive=false (short-circuit:add_eqs-multi-maude)");
                }
            }
            if !local_subst.is_empty() {
                self.subst = local_subst.compose(&self.subst);
            }
        } else {
            // Unconditional apply_eq_store call (matches HS's
            // unconditional applyEqStoreAt).  When local_subst is empty,
            // newsubst = self.subst (unchanged) and each existing disj
            // subst gets a fresh applyBound pass — idempotent IFF disj
            // keys are disjoint from self.subst.dom (the addRuleVariants
            // invariant), but observably equivalent to HS in any case.
            self.apply_eq_store(maude, &local_subst)?;
        }
        let mut substs: Vec<LNSubstVFresh> = Vec::with_capacity(unifiers.len());
        for raw in unifiers {
            let s = LNSubstVFresh::from_list(raw);
            dbg_register_subst_origin("addEqs.disj", &s);
            substs.push(s);
        }
        if tamarin_utils::env_gate!("TAM_DBG_ADDEQS_VARIANTS") {
            eprintln!(
                "[addEqs_variants] inserted {} variants for eqs:",
                substs.len()
            );
            for (i, e) in applied.iter().enumerate() {
                eprintln!("[addEqs_variants]   eq[{}]: {:?} = {:?}", i, e.lhs, e.rhs);
            }
            eprintln!("[addEqs_variants] local_subst: {:?}", local_subst.to_list());
            for (i, s) in substs.iter().enumerate() {
                eprintln!("[addEqs_variants]   variant[{}]: {:?}", i, s.to_list());
            }
        }
        Ok(Some(self.add_disj(substs)))
    }
}

#[derive(Debug, Clone)]
pub enum AddEqsError {
    Maude(String),
}

impl std::fmt::Display for AddEqsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddEqsError::Maude(s) => write!(f, "Maude error: {}", s),
        }
    }
}
impl std::error::Error for AddEqsError {}

// =============================================================================
// Rule variants
// =============================================================================

impl EquationStore {
    /// `addRuleVariants disj store` — extends the store's conjunction
    /// with the given precomputed AC variants (a disjunction of
    /// fresh-range substitutions). Mirrors Haskell's `addRuleVariants`.
    /// Errors if the variants share variables with the free
    /// substitution's domain (Haskell `error`'s here).
    pub fn add_rule_variants(
        &mut self,
        variants: Vec<LNSubstVFresh>,
    ) -> Result<SplitId, &'static str> {
        // Domain-disjointness check: free-subst domain must not
        // overlap with any variant's domain.
        let free_dom: BTreeSet<LVar> = self.subst.dom().cloned().collect();
        for v in &variants {
            if v.dom().any(|x| free_dom.contains(x)) {
                return Err("addRuleVariants: nonempty intersection between domain \
                     of variants and free substitution");
            }
        }
        Ok(self.add_disj(variants))
    }
}

// =============================================================================
// Simplification (Maude-free pieces)
// =============================================================================

impl EquationStore {
    /// Mirrors `simp` from Haskell: a fixed-point loop running each
    /// simp1 pass until no further changes. Returns the new store.
    ///
    /// The Maude-using passes (`simp_singleton`, `simp_abstract_*`
    /// that need fresh-variable generation) are not run here — use
    /// `simp_with_fresh_avoiding` for the full pipeline. The passes
    /// this variant runs, in execution order, are:
    ///
    /// - `simp_minimize` (with a caller-supplied contradiction predicate)
    /// - `simp_remove_renamings`
    /// - `simp_empty_disj`
    /// - `simp_identify`
    /// - `simp_abstract_name`
    ///
    /// NOT solve-path faithful and effectively test-only: its only callers
    /// are the in-file tests, so it is gated behind `#[cfg(test)]`.  Unlike
    /// `simp_with_fresh_avoiding`, this variant does NOT call
    /// `sort_disj_substs` between passes, so after `simp_minimize` reorders
    /// substs in insertion order, `d.substs[0]` (probed by `simp_identify`
    /// / `simp_abstract_name`) may no longer be the `Ord`-least element that
    /// HS's `Data.Set`-based `foreachDisj` would see.  Production code must
    /// use `simp_with_fresh_avoiding`.
    #[cfg(test)]
    pub fn simp<F: Fn(&LNSubst, &LNSubstVFresh) -> bool>(mut self, is_contr: F) -> Self {
        // HS-faithful pass order (EquationStore.hs `simp1`).  This
        // variant lacks a fresh-idx allocator + Maude handle, so it skips
        // the passes that need them: simpSingleton, simpAbstractSortedVar,
        // simpAbstractFun.  Callers that need the full simp pipeline
        // should use `simp_with_fresh_avoiding`.
        loop {
            if self.is_false() {
                return self;
            }
            let mut changed = false;
            let subst_snapshot = self.subst.clone();
            changed |= self.simp_minimize(|s| is_contr(&subst_snapshot, s));
            changed |= self.simp_remove_renamings();
            changed |= self.simp_empty_disj();
            changed |= self.simp_identify();
            changed |= self.simp_abstract_name();
            if !changed {
                return self;
            }
        }
    }

    /// HS-faithful Set ordering: sort each disj's substs by Ord and
    /// dedupe (mirrors `S.fromList` invariant in HS's `Disj`).  Called
    /// after every simp pass that mutates substs so the FIRST subst
    /// (used by simp_identify/simp_abstract_fun probing) matches HS's
    /// Set-first variant.
    pub fn sort_disj_substs(&mut self) {
        for d in self.conj.iter_mut() {
            d.substs.sort();
            d.substs.dedup();
        }
    }

    /// `simpEmptyDisj`: if any disjunction is empty (and the store
    /// isn't already the canonical false-conjunction), collapse the
    /// whole store to `false`.
    pub fn simp_empty_disj(&mut self) -> bool {
        let already_false_canonical = self.conj.len() == 1
            && self.conj[0].split_id == SplitId(-1)
            && self.conj[0].substs.is_empty();
        let has_empty_disj = self.conj.iter().any(|d| d.substs.is_empty());
        if has_empty_disj && !already_false_canonical {
            self.conj = Self::false_conj();
            true
        } else {
            false
        }
    }

    /// `simpRemoveRenamings`: drop variable-renaming entries from
    /// every fresh-range substitution. Returns true if any subst was
    /// modified.
    pub fn simp_remove_renamings(&mut self) -> bool {
        let mut changed = false;
        for d in self.conj.iter_mut() {
            for s in d.substs.iter_mut() {
                // `remove_renamings` drops exactly the entries `v` for which
                // `is_renamed_var(v)` holds, so the domain count changes iff at
                // least one such entry exists.  Gate the allocation on that
                // cheap pre-check (the common case has no renamings).
                if s.dom().any(|v| s.is_renamed_var(v)) {
                    *s = s.remove_renamings();
                    changed = true;
                }
            }
        }
        changed
    }

    /// `simpMinimize`: dedupe substitutions within a disjunction; if a
    /// disjunction contains the empty subst (i.e. a tautology), reduce
    /// it to just that. Also drops substs flagged contradictory by
    /// `is_contr`.
    pub fn simp_minimize<F: Fn(&LNSubstVFresh) -> bool>(&mut self, is_contr: F) -> bool {
        let mut changed = false;
        let empty = LNSubstVFresh::empty();
        for d in self.conj.iter_mut() {
            // Fast path: if no duplicate, no empty, and no contradictory subst
            // exists, this disj is left untouched (no change, no clone).  This
            // is the common case and avoids the O(n^2) dedup-clone below.
            let mut has_dup = false;
            for (i, s) in d.substs.iter().enumerate() {
                if d.substs[..i].iter().any(|x| x == s) {
                    has_dup = true;
                    break;
                }
            }
            let needs_work = has_dup || d.substs.iter().any(|s| s == &empty || is_contr(s));
            if !needs_work {
                continue;
            }
            // Dedup in-place while preserving first occurrences.
            let mut seen: Vec<LNSubstVFresh> = Vec::new();
            for s in &d.substs {
                if !seen.iter().any(|x| x == s) {
                    seen.push(s.clone());
                }
            }
            let original_len = d.substs.len();
            // Haskell-faithful `simpMinimize` (EquationStore.hs):
            // if any subst is empty (vacuously true) OR contradictory,
            // reduce the disj.  If empty present → singleton empty
            // (next pass simpSingleton folds it into the free subst).
            // Otherwise filter out contradictory substs.
            //
            // The variant-SplitG-preservation case is handled upstream
            // in `apply_eq_store` via `renameAvoiding`, which prevents
            // the narrowing variant from collapsing to an empty subst.
            let reduce_to_empty = seen.iter().any(|s| s == &empty || is_contr(s));
            if reduce_to_empty {
                if seen.iter().any(|s| s == &empty) {
                    seen = vec![empty.clone()];
                } else {
                    seen.retain(|s| !is_contr(s));
                }
            }
            if seen.len() != original_len || seen != d.substs {
                d.substs = seen;
                changed = true;
            }
        }
        changed
    }

    /// Compose `factor` into the free substitution, re-unifying remaining
    /// disjs via `apply_eq_store` when a Maude handle is present.  On
    /// `apply_eq_store` `Err` (e.g. dom/range overlap), or when no handle
    /// is available (test-only path), fall back to a direct compose.
    /// Shared HS-faithful `foreachDisj` tail (EquationStore.hs).
    fn apply_factor_or_compose(
        &mut self,
        factor: &LNSubst,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) {
        if let Some(m) = maude {
            if self.apply_eq_store(m, factor).is_err() {
                self.subst = factor.compose(&self.subst);
            }
        } else {
            self.subst = factor.compose(&self.subst);
        }
    }

    /// Shared tail of the `simp_abstract_*`/`simp_identify` passes: register
    /// the old→new subst transforms under `label` (impure-dbg only), replace
    /// disjunction `idx` with `new_substs`, then apply `factor` via
    /// `apply_factor_or_compose`.  Preserves the HS `foreachDisj`
    /// register-then-replace-then-apply order.  Always returns `true`.
    fn replace_disj_and_apply(
        &mut self,
        idx: usize,
        new_substs: Vec<LNSubstVFresh>,
        factor: &LNSubst,
        label: &str,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> bool {
        if impure_dbg_enabled() {
            for (i, o) in self.conj[idx].substs.iter().zip(new_substs.iter()) {
                dbg_register_subst_transform(label, i, o);
            }
        }
        self.conj[idx].substs = new_substs;
        self.apply_factor_or_compose(factor, maude);
        true
    }

    /// `simpAbstractName`: if every substitution in a disjunction maps
    /// the same variable `v` to the same constant `c`, factor `{v →
    /// c}` out into the free substitution and drop those mappings.
    pub fn simp_abstract_name(&mut self) -> bool {
        self.simp_abstract_name_with_maude(None)
    }

    /// HS-faithful variant of `simp_abstract_name` that takes a Maude
    /// handle and calls `apply_eq_store` on the factored subst to
    /// re-unify remaining disjs (mirrors HS's `foreachDisj` at
    /// EquationStore.hs).
    pub fn simp_abstract_name_with_maude(
        &mut self,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> bool {
        // Walk each disjunction and look for a common (v, const)
        // mapping.
        let mut common_mapping: Option<(LVar, LNTerm, usize)> = None;
        for (idx, d) in self.conj.iter().enumerate() {
            if d.substs.is_empty() {
                continue;
            }
            let first = &d.substs[0];
            // For each (v, t) in first where t is a constant, check
            // every other subst maps v to the same t.  Borrowing scan —
            // entries are cloned only on the (rare) match.
            for (v, t) in first.iter() {
                if !is_constant_term(t) {
                    continue;
                }
                let common = d
                    .substs
                    .iter()
                    .all(|s| s.image_of(v).map(|got| got == t).unwrap_or(false));
                if common {
                    common_mapping = Some((v.clone(), t.clone(), idx));
                    break;
                }
            }
            if common_mapping.is_some() {
                break;
            }
        }
        let (v, t, idx) = match common_mapping {
            Some(p) => p,
            None => return false,
        };
        // Compose `{v → t}` into the free substitution and drop `v`
        // from every subst in disjunction `idx`.
        let factor = LNSubst::from_list(vec![(v.clone(), t)]);
        // HS-faithful order (`foreachDisj`, EquationStore.hs):
        // REPLACE the disj FIRST, THEN applyEqStore.  (For simpAbstractName
        // the factor's range is a constant; we follow the HS replace-then-
        // apply order so correctness rests on matching HS, not on any
        // independent neutrality argument.)
        let new_substs: Vec<LNSubstVFresh> = self.conj[idx]
            .substs
            .iter()
            .map(|s| {
                let kept = without_key(s, &v);
                LNSubstVFresh::from_list(kept)
            })
            .collect();
        self.replace_disj_and_apply(idx, new_substs, &factor, "simpAbstractName", maude)
    }

    /// `simpIdentify`: if every subst in a disjunction has two
    /// different variables `x` and `y` (with `x < y` and same sort)
    /// mapped to the same image, factor `{x → y}` and drop `x` from
    /// every subst.
    ///
    /// HS-faithful: also runs `applyEqStore` on the factor (per HS's
    /// `foreachDisj` wrapper in EquationStore.hs) so variants get
    /// re-unified against the new free subst. Without this, variants
    /// that would conflict with the new free subst stay around.
    pub fn simp_identify(&mut self) -> bool {
        self.simp_identify_with_maude(None)
    }

    /// Maude-using variant of `simp_identify` (HS-faithful).
    pub fn simp_identify_with_maude(
        &mut self,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> bool {
        // TAM_RS_DBG_SIMP_IDENTIFY=1: dump same-image probe results
        // per disj — used to confirm that RS variants never
        // contain same-image pairs (whereas HS's do after equation
        // reduction).
        let dbg = tamarin_utils::env_gate!("TAM_RS_DBG_SIMP_IDENTIFY");
        if dbg && self.conj.iter().any(|d| d.substs.len() >= 2) {
            for (idx, d) in self.conj.iter().enumerate() {
                if d.substs.len() < 2 {
                    continue;
                }
                let first = &d.substs[0];
                let entries = first.to_list();
                let mut pairs_found = 0u32;
                for (i, (v, t)) in entries.iter().enumerate() {
                    for (v2, t2) in entries.iter().skip(i + 1) {
                        if t == t2 && v < v2 {
                            pairs_found += 1;
                            let all_agree = d.substs.iter().skip(1).all(|s| {
                                let i1 = s.image_of(v);
                                let i2 = s.image_of(v2);
                                i1.is_some() && i1 == i2
                            });
                            if all_agree {
                                eprintln!(
                                    "[simp_id_probe] disj[{}] FIRE: ({}.{}, {}.{}) -> {:?}",
                                    idx,
                                    v.name,
                                    v.idx,
                                    v2.name,
                                    v2.idx,
                                    format!("{:?}", t).chars().take(120).collect::<String>()
                                );
                            }
                        }
                    }
                }
                if pairs_found == 0 {
                    eprintln!("[simp_id_probe] disj[{}] NO_PAIRS: no same-image pairs in first subst ({} entries, {} substs)",
                        idx, entries.len(), d.substs.len());
                    if entries.len() >= 8
                        && tamarin_utils::env_gate!("TAM_RS_DBG_SIMP_IDENTIFY_FULL")
                    {
                        for (sidx, s) in d.substs.iter().enumerate() {
                            eprintln!("[simp_id_probe]   subst[{}]:", sidx);
                            for (k, v) in s.to_list() {
                                eprintln!(
                                    "[simp_id_probe]     {}.{} -> {:?}",
                                    k.name,
                                    k.idx,
                                    format!("{:?}", v).chars().take(200).collect::<String>()
                                );
                            }
                        }
                    }
                }
            }
        }
        let mut to_apply: Option<(LVar, LVar, usize)> = None;
        for (idx, d) in self.conj.iter().enumerate() {
            if d.substs.is_empty() {
                continue;
            }
            let first = &d.substs[0];
            // Find all (v, v') pairs in `first` with same image, v < v'.
            // Borrowing scan (same entry order as `to_list`); pairs are
            // cloned only when pushed.
            let pairs: Vec<(LVar, LVar)> = {
                let entries: Vec<(&LVar, &LNTerm)> = first.iter().collect();
                let mut out = Vec::new();
                for (i, (v, t)) in entries.iter().enumerate() {
                    for (v2, t2) in entries.iter().skip(i + 1) {
                        if t == t2 && v < v2 {
                            out.push(((*v).clone(), (*v2).clone()));
                        }
                    }
                }
                out
            };
            for (v, v2) in &pairs {
                let agrees = d.substs.iter().skip(1).all(|s| {
                    let i1 = s.image_of(v);
                    let i2 = s.image_of(v2);
                    i1.is_some() && i1 == i2
                });
                if agrees {
                    to_apply = Some((v.clone(), v2.clone(), idx));
                    break;
                }
            }
            if to_apply.is_some() {
                break;
            }
        }
        let (v, v2, idx) = match to_apply {
            Some(p) => p,
            None => return false,
        };
        // Decide which to keep: the variable with the larger sort
        // (Tamarin says "GT means keep first"; we use the same rule).
        let (keep, remove) = match sort_compare(v.sort, v2.sort) {
            Some(std::cmp::Ordering::Greater) => (v2.clone(), v.clone()),
            Some(_) => (v.clone(), v2.clone()),
            None => return false, // incomparable sorts; bail
        };
        let factor = LNSubst::from_list(vec![(
            remove.clone(),
            tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(keep.clone())),
        )]);
        // HS-faithful: apply factor via apply_eq_store (re-unifies
        // variants against new free subst).  Falls back to compose if
        // no Maude handle.
        let _id_guard = crate::constraint::solver::trace::OpLabelGuard::force(&format!(
            "simpIdentify@{}",
            crate::constraint::solver::trace::current_op_label()
        ));
        // HS-faithful order (`foreachDisj`): REPLACE the disj (remove
        // `keep` from every subst) FIRST, THEN apply_eq_store the factor.
        // Same rationale as simpAbstractFun (avoids splitting shared range
        // witnesses by re-unifying the un-updated disj).
        // Remove `keep` from every subst in disjunction `idx`.
        let new_substs: Vec<LNSubstVFresh> = self.conj[idx]
            .substs
            .iter()
            .map(|s| {
                let kept = without_key(s, &keep);
                LNSubstVFresh::from_list(kept)
            })
            .collect();
        self.replace_disj_and_apply(idx, new_substs, &factor, "simpIdentify", maude)
    }

    /// `simpAbstractSortedVar`: if every substitution `si` in a
    /// disjunction maps a variable `v` to variables `xi` of the SAME
    /// sort `s` that is STRICTLY narrower than `lvarSort v`, then they
    /// all contain the common factor `{v → y}` for a fresh variable
    /// `y` of sort `s`, and we can replace `{v → xi}` by `{y → xi}` in
    /// all `si`.
    ///
    /// Haskell reference (EquationStore.hs `simpAbstractSortedVar`):
    /// ```haskell
    /// simpAbstractSortedVar (subst:others) = case commonSortedVar of
    ///     (v, s, lvs):_ -> do
    ///         fv <- freshLVar (lvarName v) s
    ///         return $ Just (Just $ substFromList [(v, varTerm fv)]
    ///                       , [S.fromList (zipWith (replaceMapping v fv) lvs (subst:others))])
    ///   where
    ///     commonSortedVar = do
    ///         (v, (viewTerm -> Lit (Var lx))) <- substToListVFresh subst
    ///         guard (sortCompare (lvarSort v) (lvarSort lx) == Just GT)
    ///         let images = map (\s -> imageOfVFresh s v) others
    ///             goodImages = [ ly | Just (viewTerm -> Lit (Var ly)) <- images
    ///                                , lvarSort lx == lvarSort ly]
    ///         guard (length images == length goodImages)
    ///         return (v, lvarSort lx, (lx:goodImages))
    /// ```
    ///
    /// This is the pass that narrows protocol rule body Msg-vars to
    /// Fresh witnesses when the variant constraints all map them to
    /// Fresh vars — load-bearing for `hasImpossibleChain` to fire on
    /// destructor extensions through TLS-style `senc(<...>, h)` payloads
    /// (otherwise the chain conc keeps Msg-var `sid` and the check
    /// can't determine root symbols).
    ///
    /// Takes a Maude handle and calls `apply_eq_store` on the factored
    /// subst to re-unify remaining disjs (mirrors HS's `foreachDisj` at
    /// EquationStore.hs).
    pub fn simp_abstract_sorted_var_with_maude<F: FnMut(u64) -> u64>(
        &mut self,
        alloc: &mut F,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> bool {
        use tamarin_term::lterm::LVar;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut to_apply: Option<(LVar, tamarin_term::lterm::LSort, Vec<LVar>, usize)> = None;
        for (idx, d) in self.conj.iter().enumerate() {
            if d.substs.is_empty() {
                continue;
            }
            let first = &d.substs[0];
            // Borrowing scan — entries are cloned only on match.
            for (v, t) in first.iter() {
                let lx = match t {
                    Term::Lit(Lit::Var(lx)) => lx.clone(),
                    _ => continue,
                };
                if !matches!(
                    sort_compare(v.sort, lx.sort),
                    Some(std::cmp::Ordering::Greater)
                ) {
                    continue;
                }
                let mut lvs: Vec<LVar> = vec![lx.clone()];
                let mut all_match = true;
                for other in d.substs.iter().skip(1) {
                    match other.image_of(v) {
                        Some(Term::Lit(Lit::Var(ly))) if ly.sort == lx.sort => {
                            lvs.push(ly.clone());
                        }
                        _ => {
                            all_match = false;
                            break;
                        }
                    }
                }
                if all_match {
                    to_apply = Some((v.clone(), lx.sort, lvs, idx));
                    break;
                }
            }
            if to_apply.is_some() {
                break;
            }
        }
        let (v, s, lvs, idx) = match to_apply {
            Some(p) => p,
            None => return false,
        };
        // Allocate a fresh witness fv with the narrower sort `s`.
        let new_idx = alloc(1);
        let fv = LVar {
            name: v.name,
            sort: s,
            idx: new_idx,
        };
        if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
            eprintln!(
                "[rs-fold] simpAbstractSortedVar v={}.{} fv={}.{}/{:?}",
                v.name, v.idx, fv.name, fv.idx, fv.sort
            );
        }
        // Compose {v → Var(fv)} into the free substitution.
        let factor = LNSubst::from_list(vec![(v.clone(), Term::Lit(Lit::Var(fv.clone())))]);
        // HS-faithful: foreachDisj (EquationStore.hs) REPLACES
        // the disj with the abstracted substs FIRST, THEN calls
        // `applyEqStore hnd msubst`.  Apply the abstraction to the disj
        // before re-unifying (matching the simpAbstractFun fix — see
        // rationale there: re-unifying the un-abstracted disj can split
        // shared range witnesses).
        // For each (subst, lv) pair, remove (v, _) and add (fv, Var(lv)).
        let new_substs: Vec<LNSubstVFresh> = self.conj[idx]
            .substs
            .iter()
            .zip(lvs.iter())
            .map(|(s, lv)| {
                let mut kept = without_key(s, &v);
                kept.push((fv.clone(), Term::Lit(Lit::Var(lv.clone()))));
                LNSubstVFresh::from_list(kept)
            })
            .collect();
        self.replace_disj_and_apply(idx, new_substs, &factor, "simpAbstractSortedVar", maude)
    }

    /// `simpAbstractFun`: if every substitution in a disjunction maps
    /// the same variable `v` to terms with the SAME outermost function
    /// symbol `o`, factor `{v → o(x1,...,xk)}` (with fresh xi vars) into
    /// the free substitution and replace `v`'s mapping in each subst
    /// with mappings `{x1 → arg[0], x2 → arg[1], ...}`.
    ///
    /// For AC operators (multiset, exp, etc.) only the FIRST TWO
    /// arguments are factored (since AC args are unordered, only the
    /// "left/right split" is meaningful): factor `{v → o(x1, x2)}` with
    /// `x2 → o(rest)` if the original had >2 args.
    ///
    /// Mirrors HS `simpAbstractFun` (EquationStore.hs).
    ///
    /// Takes a Maude handle and calls `apply_eq_store` on the factored
    /// subst to re-unify remaining disjs (mirrors HS's `foreachDisj` at
    /// EquationStore.hs).  This pass always runs, matching HS `simp1`
    /// where `b7 <- foreachDisj hnd simpAbstractFun` is an unconditional
    /// member of the simplification fixed point.
    pub fn simp_abstract_fun_with_maude<F: FnMut(u64) -> u64>(
        &mut self,
        alloc: &mut F,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> bool {
        use tamarin_term::function_symbols::FunSym;
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;

        // Find (disj_idx, v, op, argss) where v has the same outermost
        // function symbol across every subst in the disjunction.
        // argss[i] = args of subst[i]'s mapping for v.
        let mut to_apply: Option<(usize, LVar, FunSym, Vec<Vec<LNTerm>>)> = None;
        'outer: for (idx, d) in self.conj.iter().enumerate() {
            if d.substs.is_empty() {
                continue;
            }
            let first = &d.substs[0];
            // Borrowing scan — entries are cloned only on match.
            for (v, t) in first.iter() {
                let (op, args0) = match t {
                    Term::App(o, a) => (*o, a.to_vec()),
                    _ => continue,
                };
                let mut argss: Vec<Vec<LNTerm>> = vec![args0];
                let mut ok = true;
                for other in d.substs.iter().skip(1) {
                    match other.image_of(v) {
                        Some(Term::App(o2, a2)) if o2 == &op => {
                            argss.push(a2.to_vec());
                        }
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    to_apply = Some((idx, v.clone(), op, argss));
                    break 'outer;
                }
            }
        }
        let (idx, v, op, argss) = match to_apply {
            Some(p) => p,
            None => return false,
        };

        // For non-AC operators, all argss MUST have the same length
        // (since outer symbol is identical). For AC, can have varying
        // arities.
        let first_arity = argss[0].len();
        let same_arity = argss.iter().all(|a| a.len() == first_arity);

        if !op.is_ac() || same_arity {
            // Abstract ALL arguments.  Allocate `first_arity` fresh
            // Msg-sort vars.
            let mut fvars: Vec<LVar> = Vec::with_capacity(first_arity);
            for _ in 0..first_arity {
                let idx_alloc = alloc(1);
                fvars.push(LVar {
                    name: "x",
                    sort: LSort::Msg,
                    idx: idx_alloc,
                });
            }
            if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
                eprintln!(
                    "[rs-fold] simpAbstractFun v={}.{} fvars={:?}",
                    v.name,
                    v.idx,
                    fvars
                        .iter()
                        .map(|f| format!("{}.{}", f.name, f.idx))
                        .collect::<Vec<_>>()
                );
            }
            // Build factor `{v → op(x1, ..., xk)}`.
            let factor = LNSubst::from_list(vec![(
                v.clone(),
                Term::App(
                    op,
                    fvars
                        .iter()
                        .map(|fv| Term::Lit(Lit::Var(fv.clone())))
                        .collect(),
                ),
            )]);
            // Apply factor (via apply_eq_store if maude available).
            // Tag the apply_eq_store with simp_abstract_fun
            // label so HS↔RS per-label call counts match HS's
            // `foreachDisj:simpAbstractFun@<outer>` site naming.
            // `force` because we want to PREPEND a simp pass marker
            // even though an outer label exists (so the trace shows
            // both passes).
            let _abs_fun_guard = crate::constraint::solver::trace::OpLabelGuard::force(&format!(
                "simpAbstractFun@{}",
                crate::constraint::solver::trace::current_op_label()
            ));
            // HS-faithful order (`foreachDisj`, EquationStore.hs):
            // REPLACE the disjunction with the abstracted substs FIRST,
            // THEN run `applyEqStore` with the factored free subst.  Do NOT
            // run apply_eq_store before replacing the disj: re-unifying the
            // un-abstracted disj substs (still carrying `v → op(a, b)`)
            // against the new free subst `{v → op(x1, x2)}` re-allocates
            // witnesses for OTHER range terms that shared `a, b` (e.g. a
            // sibling `pcsig2 → pcs(op(a, b), ...)` entry), splitting the
            // shared `a, b` into distinct fresh vars — the resolved1 linkage
            // break (Out's `sign(a,b)` vs In's `pcs(sign(a',b'),...)`).
            // Applying the abstraction to the disj first makes `a, b`
            // cleanly bound via `{x1 → a, x2 → b}`, and the subsequent
            // apply_eq_store re-unifies the ALREADY-abstracted disj,
            // preserving the share.
            let new_substs: Vec<LNSubstVFresh> = self.conj[idx]
                .substs
                .iter()
                .zip(argss.iter())
                .map(|(s, args)| {
                    let mut kept = without_key(s, &v);
                    for (fv, a) in fvars.iter().zip(args.iter()) {
                        kept.push((fv.clone(), a.clone()));
                    }
                    LNSubstVFresh::from_list(kept)
                })
                .collect();
            self.replace_disj_and_apply(idx, new_substs, &factor, "simpAbstractFun", maude)
        } else {
            // AC operator with varying arity: factor first two args.
            let fv1_idx = alloc(1);
            let fv2_idx = alloc(1);
            let fv1 = LVar {
                name: "x",
                sort: LSort::Msg,
                idx: fv1_idx,
            };
            let fv2 = LVar {
                name: "x",
                sort: LSort::Msg,
                idx: fv2_idx,
            };
            if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
                eprintln!(
                    "[rs-fold] simpAbstractFun.AC v={}.{} fvars=[\"{}.{}\", \"{}.{}\"]",
                    v.name, v.idx, fv1.name, fv1.idx, fv2.name, fv2.idx
                );
            }
            // Factor: `{v → op(fv1, fv2)}`
            let factor = LNSubst::from_list(vec![(
                v.clone(),
                Term::App(
                    op,
                    vec![
                        Term::Lit(Lit::Var(fv1.clone())),
                        Term::Lit(Lit::Var(fv2.clone())),
                    ]
                    .into(),
                ),
            )]);
            // HS-faithful order (`foreachDisj`): replace the disj FIRST,
            // then apply_eq_store the factor.  See the non-AC branch above
            // for the rationale (resolved1 linkage break).
            // For each subst with args = [a1, a2, ...]:
            //   if length 2: add (fv1, a1), (fv2, a2)
            //   else (>2):   add (fv1, a1), (fv2, op(a2, a3, ...))
            let new_substs: Vec<LNSubstVFresh> = self.conj[idx]
                .substs
                .iter()
                .zip(argss.iter())
                .map(|(s, args)| {
                    let mut kept = without_key(s, &v);
                    // HS-faithful `abstractTwo`/`newMappings` (EquationStore.hs:
                    // 436-444): `newMappings []` ERRORS ("AC symbols must have
                    // arity >= 2"); silently bailing here would leave a
                    // malformed store (the factor `{v -> op(fv1,fv2)}` is
                    // composed into the free subst below regardless, while this
                    // subst would still bind `v`).  This branch is unreachable
                    // in practice (AC ops are always arity >= 2), so matching
                    // HS's hard error is the correct invariant.
                    let (a1, a_rest) = match args.as_slice() {
                        [] => panic!("simpAbstract: impossible, AC symbols must have arity >= 2."),
                        // `newMappings [a1,a2] = [(fv1,a1),(fv2,a2)]`
                        [a1, a2] => (a1.clone(), a2.clone()),
                        // `newMappings (a:as) = [(fv1,a),(fv2,fApp o as)]`
                        [a1, rest @ ..] => (a1.clone(), Term::App(op, rest.to_vec().into())),
                    };
                    kept.push((fv1.clone(), a1));
                    kept.push((fv2.clone(), a_rest));
                    LNSubstVFresh::from_list(kept)
                })
                .collect();
            self.replace_disj_and_apply(idx, new_substs, &factor, "simpAbstractFunAC", maude)
        }
    }

    /// Variant of `simp` that also runs `simp_singleton` — converts
    /// singleton disjunctions (one substitution as the only disjunct)
    /// into free-substitution composition via `freshToFree`.  Mirrors
    /// Haskell's `simpSingleton` (EquationStore.hs) wired into
    /// `simp1` via `foreachDisj`.
    ///
    /// Requires a fresh-idx allocator (typically wrapping
    /// `MaudeHandle::reserve_idxs`) because `freshToFree` renames range
    /// vars to distinct LVar idxs.
    ///
    /// Takes an extra `external_preserve`
    /// set — live system free vars that must NOT be treated as fresh
    /// witnesses when `simp_singleton` folds a singleton disjunction
    /// into the free subst.  Pattern_matching::Responder_secrecy was
    /// wrong-falsified by `fresh_to_free` renaming `k:Fresh#0` (a
    /// Setup_Key conclusion var) inside the variant's range.
    pub fn simp_with_fresh_avoiding<F, G>(
        mut self,
        is_contr: F,
        mut alloc: G,
        external_preserve: &BTreeSet<LVar>,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> Self
    where
        F: Fn(&LNSubst, &LNSubstVFresh) -> bool,
        G: FnMut(u64) -> u64,
    {
        let dbg_simp_disj = tamarin_utils::env_gate!("TAM_RS_DBG_SIMP_DISJ");
        if dbg_simp_disj {
            let sizes: Vec<usize> = self.conj.iter().map(|d| d.substs.len()).collect();
            if sizes.iter().any(|n| *n >= 2) {
                eprintln!("[SIMP_DISJ_IN] sizes={:?}", sizes);
            }
        }
        // HS-faithful pass order (EquationStore.hs `simp1`):
        //   1. simpMinimize
        //   2. simpRemoveRenamings
        //   3. simpEmptyDisj
        //   4. simpSingleton          (via foreachDisj)
        //   5. simpAbstractSortedVar  (via foreachDisj)
        //   6. simpIdentify           (via foreachDisj)
        //   7. simpAbstractFun        (via foreachDisj)
        //   8. simpAbstractName       (via foreachDisj)
        //
        // HS-faithful order matters: simpAbstractSortedVar can introduce
        // new mappings that simpIdentify then collapses; simpAbstractFun
        // fires before simpAbstractName so common Fun-headed images get
        // factored before common name constants.
        // Ensure substs are sorted on entry (mirrors HS's Set
        // invariant after addRuleVariants → S.fromList).
        self.sort_disj_substs();
        loop {
            if self.is_false() {
                return self;
            }
            let mut changed = false;
            let subst_snapshot = self.subst.clone();
            if self.simp_minimize(|s| is_contr(&subst_snapshot, s)) {
                changed = true;
                self.sort_disj_substs();
            }
            if self.simp_remove_renamings() {
                changed = true;
                self.sort_disj_substs();
            }
            changed |= self.simp_empty_disj();
            // ALWAYS fold singleton variant disjs into the free subst —
            // this is exactly what HS does.  HS's `simp1` runs
            // `b4 <- foreachDisj hnd simpSingleton` unconditionally on
            // every disj (EquationStore.hs `simp1`), with NO precompute guard;
            // `simpSingleton [subst0]` folds a singleton disj via
            // `freshToFree` into the free subst (EquationStore.hs `simpSingleton`).
            if self.simp_singleton_avoiding(&mut alloc, external_preserve, maude) {
                changed = true;
                self.sort_disj_substs();
            }
            if self.simp_abstract_sorted_var_with_maude(&mut alloc, maude) {
                changed = true;
                self.sort_disj_substs();
            }
            if self.simp_identify_with_maude(maude) {
                changed = true;
                self.sort_disj_substs();
            }
            if self.simp_abstract_fun_with_maude(&mut alloc, maude) {
                changed = true;
                self.sort_disj_substs();
            }
            if self.simp_abstract_name_with_maude(maude) {
                changed = true;
                self.sort_disj_substs();
            }
            if !changed {
                if dbg_simp_disj {
                    let sizes: Vec<usize> = self.conj.iter().map(|d| d.substs.len()).collect();
                    if sizes.iter().any(|n| *n >= 2) {
                        eprintln!("[SIMP_DISJ_OUT] sizes={:?}", sizes);
                    }
                }
                return self;
            }
        }
    }

    /// `simpSingleton`: if a disjunction has exactly one substitution,
    /// fold that subst into the free substitution (via `freshToFree`)
    /// and drop the disjunction.  This is what propagates picked
    /// variant subst bindings into the eq-store's free subst, which
    /// then gets pushed into rule terms by `substSystem` /
    /// `substNodes` / `normDG`.
    ///
    /// Haskell reference:
    /// ```haskell
    /// simpSingleton [subst0] = do
    ///         subst <- freshToFree subst0
    ///         return (Just (Just subst, []))
    /// simpSingleton _        = return Nothing
    /// ```
    /// Plus `foreachDisj`'s wiring that calls `applyEqStore hnd subst`
    /// on the resulting `Just subst`.  We compose into `self.subst`
    /// directly — this is sound when the new subst's domain is
    /// disjoint from `self.subst`'s range.
    ///
    /// Accepts an `external_preserve`
    /// set — typically the system's free vars — to PROTECT from
    /// renaming in `fresh_to_free`.  See `simp_with_fresh_avoiding`.
    ///
    /// If `maude` is `Some`, after composing the folded factor into the
    /// free subst, also re-unifies any REMAINING disj substs against
    /// the new free subst via `apply_eq_store`.  HS-faithful:
    /// `foreachDisj` (EquationStore.hs) does
    /// `MS.modify (applyEqStore hnd msubst)` after replacing the
    /// disj.  Without this, remaining variants stay un-refined and
    /// `perform_split` enumerates stale shapes.  Pass `None` for the
    /// test-only path that doesn't have a Maude handle.
    pub fn simp_singleton_avoiding<F: FnMut(u64) -> u64>(
        &mut self,
        alloc: &mut F,
        external_preserve: &BTreeSet<LVar>,
        maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    ) -> bool {
        // Find the first singleton disjunction (1 subst).
        let pos = self.conj.iter().position(|d| d.substs.len() == 1);
        let Some(pos) = pos else {
            return false;
        };
        let subst_vf = self.conj[pos].substs[0].clone();
        if tamarin_utils::env_gate!("TAM_DBG_APPLY_EQ") {
            let pairs: Vec<String> = subst_vf
                .to_list()
                .iter()
                .take(8)
                .map(|(k, v)| {
                    format!(
                        "{}_{} → {}",
                        k.name,
                        k.idx,
                        format!("{:?}", v).chars().take(40).collect::<String>()
                    )
                })
                .collect();
            eprintln!("[simp_singleton] folding: {:?}", pairs);
            let pre_pairs: Vec<String> = external_preserve
                .iter()
                .take(5)
                .map(|v| format!("{}_{}", v.name, v.idx))
                .collect();
            eprintln!(
                "[simp_singleton] preserve subset: {:?} (total {})",
                pre_pairs,
                external_preserve.len()
            );
        }
        // Drop the singleton disjunction.
        self.conj.remove(pos);
        if subst_vf.is_empty() {
            // HS `simpSingleton` fires for the EMPTY singleton too:
            // `freshToFree emptySubstVFresh` is empty, and `foreachDisj`
            // UNCONDITIONALLY runs `applyEqStoreAt "foreachDisj:simpSingleton"`
            // with that empty msubst after replacing the disj
            // (EquationStore.hs:823-830).  An empty asubst is NOT a no-op:
            // applyEqStore re-runs `applyBound` on every remaining disj
            // subst, re-deriving (and RENUMBERING) their fresh witnesses
            // under the current avoid set (renameAvoiding + unify +
            // restrict).  Short-circuiting here left RS's surviving disj
            // witnesses stale — JCS12 typing_assertion case_3: HS's
            // empty-fold rounds renumber ~ltkS.12/m.9 → ~ltkS.6/m.6 before
            // the next solveFactEqs, RS skipped them and rendered
            // ~ltkS.9/$C.13 where HS shows ~ltkS.6/$C.10.  Same family as
            // add_eqs' "empty-empty case must NOT be short-circuited"
            // (LAK06 lesson).  The floor / fresh_to_free steps below are
            // semantic no-ops for an empty subst, so skip straight to the
            // apply_eq_store round.
            if let Some(m) = maude {
                // Err is impossible for the empty subst (dom ∩ range = ∅);
                // the compose fallback would be a no-op anyway.
                let _ = self.apply_eq_store(m, &LNSubst::empty());
            }
            return true;
        }
        if tamarin_utils::env_gate!("TAM_DBG_FOLD_VARIANT") {
            let pairs: Vec<String> = subst_vf
                .to_list()
                .iter()
                .filter(|(k, _)| k.name.contains("ltkS") || k.name.contains("request"))
                .map(|(k, v)| {
                    format!(
                        "{}.{} → {}",
                        k.name,
                        k.idx,
                        format!("{:?}", v).chars().take(100).collect::<String>()
                    )
                })
                .collect();
            if !pairs.is_empty() {
                eprintln!("[fold_variant] BEFORE fresh_to_free: {:?}", pairs);
                let pre_ltks: Vec<String> = external_preserve
                    .iter()
                    .filter(|v| v.name.contains("ltkS") || v.name.contains("request"))
                    .map(|v| format!("{}.{}", v.name, v.idx))
                    .collect();
                eprintln!("[fold_variant]   preserve(ltkS/request): {:?}", pre_ltks);
            }
        }
        // TAM_RS_DBG_IMPURE_FOLD=1: detect folding of a disj subst whose
        // RANGE references live system vars (external_preserve).  Under
        // HS's pure-fresh-range invariant this never happens; in RS it
        // means a creation site stored an impure subst and the rename
        // below severs a live linkage.
        if impure_dbg_enabled() {
            let bad = dbg_impure_range_vars(&subst_vf, external_preserve);
            if !bad.is_empty() {
                let path = crate::constraint::solver::trace::case_path_string();
                let bad_s: Vec<String> = bad
                    .iter()
                    .map(|v| format!("{}.{}/{:?}", v.name, v.idx, v.sort))
                    .collect();
                eprintln!(
                    "[IMPURE_FOLD] origin={} path={} bad_range_vars=[{}] subst={:?}",
                    dbg_subst_origin(&subst_vf),
                    path,
                    bad_s.join(","),
                    subst_vf.to_list()
                );
            }
        }
        // HS-faithful witness-freshening floor for the already-folded free
        // subst.  `simpSingleton` folds this disj via `freshToFree`, which in
        // HS draws its fresh range-var renames from the ambient `MonadFresh`
        // counter (Substitution.hs:54-66 → importBinding → freshLVar).  That
        // counter threads monotonically through `runReduction`, so it is
        // ALWAYS above every idx it has ALREADY DRAWN — i.e. above the range
        // vars of the free `eqsSubst`, which are all prior-fold outputs
        // (`applyEqStore`'s `asubst \`compose\` eqsSubst`).  RS re-seeds a
        // per-pop counter from `avoid sys = bounds_max`, which — HS-faithfully,
        // matching `foldFrees (SubstVFresh) = foldFrees f . M.keys`
        // (SubstVFresh.hs:196-202, see line 197) — counts only DOMAIN keys, not range vars; when
        // under-advanced (the WF message-derivation probe of a let-destructor
        // rule) `alloc` could draw an idx equal to an already-folded free-subst
        // range var, fusing two witnesses and forcing the eq-store false
        // (foo_eligibility C_2 / fm24 C8 verdict flips).  Push the counter
        // above `self.subst`'s range to restore HS's monotone-counter
        // invariant.  No-op whenever the counter is already threaded above.
        //
        // Crucially we DO NOT floor above the un-folded sibling disjs in
        // `self.conj`: HS's counter is NOT above those.  Their range vars are
        // per-call-local unify witnesses (Term/Maude/Types.hs:112-113,
        // `evalFreshAvoiding (M.elems bindings)`), seeded above the *query's*
        // vars — NOT drawn from the `runReduction` MonadFresh counter — so HS's
        // counter sits far below them (RYY em source: fold draws ~x.18 while
        // SplitId(0) siblings already hold ~x.187).  HS avoids fusing the
        // fold's fresh with a conj witness not by counter-avoidance but by
        // `applyBound`'s `renameAvoiding (map snd slist) avoidSet` — which, on
        // the post-fold `applyEqStore` re-unify, renames every conj disj's
        // range away from `varsRange newsubst` (the fold's fresh vars)
        // regardless of numeric overlap (EquationStore.hs:428-435).  RS mirrors
        // that in `apply_eq_store`.  Flooring above the conj here instead makes
        // each fold ratchet the counter to the max sibling witness, and the
        // subsequent re-unify re-bases those siblings even higher — a positive
        // feedback that inflated the KU(em(_,_)) bilinear source's witness span
        // ~7x/pass (peak x.4393 vs HS x.653), diverging the `main/cases`
        // raw/refined pages (task #18).
        // TAM_RS_DBG_FOLD_DRAWS=1: trace every session-counter draw batch
        // feeding the free eqsSubst RANGE (fold draws) plus the RS-specific
        // ensure_above counter jumps.  Pair with HS's TAM_HS_DBG_FOLD_DRAWS.
        let fold_dbg = tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS");
        if let Some(m) = maude {
            use tamarin_term::lterm::HasFrees;
            let mut floor = 0u64;
            for t in self.subst.range() {
                t.for_each_free(&mut |w: &LVar| {
                    if w.idx > floor {
                        floor = w.idx;
                    }
                });
            }
            if floor > 0 {
                if fold_dbg {
                    let cur = m.fresh_counter_peek();
                    if cur < floor.saturating_add(1) {
                        eprintln!(
                            "[rs-fold] ensure_above MOVES counter {} -> {} (floor={})",
                            cur,
                            floor.saturating_add(1),
                            floor
                        );
                    }
                }
                m.ensure_above(floor);
            }
        }
        let fold_counter_before = if fold_dbg {
            maude.map(|m| m.fresh_counter_peek())
        } else {
            None
        };
        let new_subst = subst_vf.fresh_to_free_avoiding(&mut *alloc);
        if fold_dbg {
            eprintln!(
                "[rs-fold] simpSingleton in={:?} out={:?} counter_before={:?} counter_after={:?}",
                subst_vf.to_list(),
                new_subst.to_list(),
                fold_counter_before,
                maude.map(|m| m.fresh_counter_peek())
            );
        }
        if tamarin_utils::env_gate!("TAM_DBG_FOLD_VARIANT") {
            let pairs: Vec<String> = new_subst
                .to_list()
                .iter()
                .filter(|(k, _)| k.name.contains("ltkS") || k.name.contains("request"))
                .map(|(k, v)| {
                    format!(
                        "{}.{} → {}",
                        k.name,
                        k.idx,
                        format!("{:?}", v).chars().take(100).collect::<String>()
                    )
                })
                .collect();
            if !pairs.is_empty() {
                eprintln!("[fold_variant]  AFTER fresh_to_free: {:?}", pairs);
            }
        }
        // HS-faithful: foreachDisj at EquationStore.hs calls
        // `MS.modify (applyEqStore hnd msubst)` after replacing the
        // singleton disj.  applyEqStore composes msubst into eqsSubst
        // AND re-unifies remaining disj substs against the new
        // eqsSubst — so SplitG variants whose values reference the
        // newly-bound vars get refined.  Direct compose (used only as the
        // Err fallback below) leaves remaining variants stale, surfacing
        // as perform_split picking different cases than HS — so the
        // re-unifying apply_eq_store path is the faithful one.
        // apply_factor_or_compose does: compose new_subst into self.subst +
        // re-unify all remaining conj disjs when a Maude handle is present.
        // On Err (e.g. dom/range overlap), or on the no-handle test-only
        // path, fall back to direct compose (no re-unify) for malformed
        // factors.
        self.apply_factor_or_compose(&new_subst, maude);
        true
    }

    /// HS-faithful `simpDisjunction` (EquationStore.hs).  HS's
    /// `simp` runs the FULL `simp1` pipeline including `simpSingleton`
    /// (the b4 pass in EquationStore.hs `simp1`) — that pass folds a
    /// singleton-variant disj into the free subst via `freshToFree`.
    ///
    /// The test-only `simp` variant doesn't have
    /// a fresh-idx allocator and skips simpSingleton — so a singleton
    /// disj with non-renaming entries stays in the residual.  Callers
    /// that have a Maude handle (e.g. `variantsProtoRule` in
    /// RuleVariants.hs) MUST use this variant; otherwise the rule's
    /// variant-disj retains abstrTerm entries that HS bakes into the
    /// rule body via commonSubst (e.g. JKL_TS1_2004 Init_2: HS's rule
    /// shows `!Sessk(~ekI, h(<~ekI, Y, 'g'^(~lkI*~lkR)>))`; without this
    /// variant, RS's rule shows `!Sessk(~ekI, h(<~ekI, Y, z.1>))` with
    /// the abstract `z.1` still in the residual subst → diverges
    /// downstream source-case numbering).
    pub fn simp_disjunction_with_maude<F: Fn(&LNSubst, &LNSubstVFresh) -> bool>(
        substs: Vec<LNSubstVFresh>,
        is_contr: F,
        maude: &tamarin_term::maude_proc::MaudeHandle,
    ) -> (LNSubst, Option<Vec<LNSubstVFresh>>) {
        let mut store = EquationStore::empty();
        let _ = store.add_disj(substs);
        let alloc = |n: u64| maude.reserve_idxs(n);
        let store = store.simp_with_fresh_avoiding(is_contr, alloc, &BTreeSet::new(), Some(maude));
        let free = store.subst.clone();
        match store.conj.as_slice() {
            [] => (free, None),
            [d] => (free, Some(d.substs.clone())),
            _ => (
                free,
                Some(store.conj.into_iter().flat_map(|d| d.substs).collect()),
            ),
        }
    }

    /// `applyEqStore`: apply a free substitution to the store, going
    /// through Maude to renormalise each disjunction's substitutions
    /// modulo AC. Mirrors the Haskell semantics
    /// (EquationStore.hs `applyEqStore`).
    ///
    /// CRITICAL semantics: for each disjunction subst `s = {(lv_i, t_i)}`,
    /// build equations `[Equal (apply newsubst (Var lv_i)) t_i]` and
    /// AC-unify them via Maude.  Each unifier becomes a new variant
    /// (a single old variant may explode into several).  Variants
    /// whose unification fails are dropped (the disjunction shrinks).
    ///
    /// This is what propagates rule-variant constraints when the
    /// free subst is updated by a later `addEqs`. e.g. for
    /// `B_1_verify`'s variant `{z → verify(s,m,pkA)}` against a
    /// later `{z → true}`, this re-unifies as `verify(s,m,pkA) = true`
    /// → Maude narrows to `{s → sign(x1,x2), m → x1, pkA → pk(x2)}`.
    /// Without it, picking the variant later silently DROPS the
    /// verify constraint (composition `(picked ∘ {z→true})(z) = true`).
    ///
    /// Errors if `asubst`'s domain and range overlap (Haskell errors
    /// here too, since the resulting composition would be malformed).
    #[track_caller]
    pub fn apply_eq_store(
        &mut self,
        maude: &tamarin_term::maude_proc::MaudeHandle,
        asubst: &LNSubst,
    ) -> Result<(), AddEqsError> {
        let __aes_caller = std::panic::Location::caller();
        // Domain/range disjointness check.  Streaming: walk the range terms
        // in place and probe each free var against the domain map directly
        // (`image_of` = `BTreeMap::get`) — same boolean as the eager
        // dom-set ∩ range-var-set intersection, without materialising two
        // `BTreeSet`s (plus a `vars_vterm` Vec per range term) per call on
        // the common disjoint path.
        let mut dom_range_overlap = false;
        {
            use tamarin_term::lterm::HasFrees;
            for t in asubst.range() {
                t.for_each_free(&mut |v| {
                    if !dom_range_overlap && asubst.image_of(v).is_some() {
                        dom_range_overlap = true;
                    }
                });
                if dom_range_overlap {
                    break;
                }
            }
        }
        if dom_range_overlap {
            return Err(AddEqsError::Maude(
                "applyEqStore: dom and vrange not disjoint".into(),
            ));
        }

        let new_subst = asubst.compose(&self.subst);

        // TAM_RS_DBG_APPLY_EQ_STORE=1: dump every call's asubst, IN/OUT
        // disjs, per-variant applyBound input/output.  Pair with HS's
        // TAM_HS_DBG_APPLY_EQ_STORE for HS↔Rust diffing of variant flow.
        // Every call ticks (including precompute) so call counts can be
        // compared apples-to-apples against HS.
        // TAM_RS_DBG_APPLY_EQ_STORE_FILTER=substantive limits dump to
        // calls with non-empty conj (matches HS's substantive filter).
        let rs_dbg = aes_dbg();
        let rs_dbg_filter_substantive = aes_dbg_filter_substantive();
        let rs_substantive = self.conj.iter().any(|d| !d.substs.is_empty());
        // Build a HS-comparable site label: `<rust_site>@<op_label>`.
        // HS emits e.g. `addEqs.single-unifier@solveTermEqs` — the part
        // before `@` is the apply_eq_store internal call site, after `@`
        // is the originating Reduction operation.  Match RS's convention
        // so per-label diffs work.  The `current_op_label()` thread-local
        // clone + `format!` only feed the `rs_dbg`-gated traces below, so
        // skip both entirely in the common (untraced) production path.
        let aes_site = if rs_dbg {
            format!(
                "{}:{}@{}",
                __aes_caller.file(),
                __aes_caller.line(),
                crate::constraint::solver::trace::current_op_label()
            )
        } else {
            String::new()
        };
        if rs_dbg && (rs_substantive || !rs_dbg_filter_substantive) {
            eprintln!(
                "[rs-aes-tick] site={} conj={} substantive={}",
                aes_site,
                self.conj.len(),
                rs_substantive
            );
        }
        let dbg_call = rs_dbg && rs_substantive;
        if dbg_call {
            eprintln!("[rs-aes] === call site={} ===", aes_site);
            eprintln!("[rs-aes] asubst = {:?}", asubst.to_list());
            eprintln!("[rs-aes] eqsSubst = {:?}", self.subst.to_list());
            for (i, d) in self.conj.iter().enumerate() {
                if d.substs.is_empty() {
                    continue;
                }
                eprintln!(
                    "[rs-aes] IN  disj[{}] sid={:?} ({} substs)",
                    i,
                    d.split_id,
                    d.substs.len()
                );
                for (j, s) in d.substs.iter().enumerate() {
                    eprintln!("  in[{}]: {:?}", j, s.to_list());
                }
            }
        }

        // Re-unify each disj subst against the new free subst via Maude
        // (Haskell's `applyBound`).  For each `s = {(lv, t)}`, build
        // equations `[Equal (apply newsubst (Var lv)) renamed_t]` and
        // let Maude AC-unify the list; multiple unifiers split into
        // multiple variants.
        //
        // The RHS terms are FRESH-RENAMED (Haskell `renameAvoiding`,
        // EquationStore.hs `applyEqStore`, LTerm.hs) to a uniform-shifted set
        // of var idxs starting at `succ avoid_max`, where `avoid_max`
        // is the max idx across `domVFresh s ∪ varsRange newsubst`.
        // The shift `freshStart - rhs_min` may be negative (when RHS
        // vars were originally above avoid_max).  Without this rename,
        // a fresh witness in the variant subst could coincide by idx
        // with a var in newsubst, causing the unifier to incorrectly
        // identify them and collapse the variant to empty.
        use tamarin_term::rewriting::Equal;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let fresh_base = self.fresh_baseline();
        // Range vars of the composed subst.  Consumed only by membership
        // probes (`contains`) and — via `new_subst_range_max` — by the
        // per-variant `avoid_max` fold, so a hash set built with an in-place
        // walk replaces the eager BTreeSet (`vars_vterm` allocated a
        // sorted/deduped Vec per range term).  The max is hoisted here once
        // instead of re-folding the whole set per variant.
        let mut new_subst_range_vars: tamarin_utils::FastSet<LVar> = Default::default();
        let mut new_subst_range_max: u64 = 0;
        {
            use tamarin_term::lterm::HasFrees;
            for t in new_subst.range() {
                t.for_each_free(&mut |v| {
                    if v.idx > new_subst_range_max {
                        new_subst_range_max = v.idx;
                    }
                    if !new_subst_range_vars.contains(v) {
                        new_subst_range_vars.insert(v.clone());
                    }
                });
            }
        }
        let mut new_conj: Vec<EqDisj> = Vec::with_capacity(self.conj.len());
        // HS-faithful per-variant fresh-state isolation.  In HS, each
        // `applyBound` call runs `renameAvoiding (range) avoidSet` →
        // `evalFreshAvoiding (rename ...)` which seeds the supply at
        // `succ (max idx in avoidSet)` LOCALLY — bounded by the call's
        // own `avoid_max`, NOT the global session counter
        // (`avoid`/`evalFreshAvoiding` at LTerm.hs:647-653,
        // EquationStore.hs `applyEqStore`/`applyBound`).  Each variant's
        // witness allocation therefore starts from the same avoid
        // baseline, and the variants' witnesses can OVERLAP in idx
        // because each ends up in its own SubstVFresh.
        //
        // Each per-variant Maude call uses a LOCAL MaudeHandle (via
        // `with_fresh_counter_from(avoid_max)`).  The local handle shares
        // the underlying Maude process state but has its own counter that
        // starts at `succ avoid_max` PER call.  The global counter is
        // untouched by these calls, so subsequent non-applyBound
        // allocations (rule freshening, sources) keep their cross-call
        // uniqueness guarantee (TESLA Sender0a).
        //
        // The witnesses minted here all live inside SubstVFresh range
        // values (α-equivalent up to witness rename — VFresh-local), so
        // discarding the local counter on exit cannot cause downstream
        // collisions: `bounds_max` (reduction.rs, `fn bounds_max`) walks
        // only the SubstVFresh DOMAIN keys, so it won't reserve witnesses
        // — but downstream Maude calls compute their own per-call
        // `avoid_max` and use the global counter (which is the union
        // of every non-applyBound allocation we've done so far), so
        // they're guaranteed disjoint from any applyBound witness by
        // VFresh α-equivalence.
        for d in self.conj.iter() {
            let mut new_substs: Vec<LNSubstVFresh> = Vec::new();
            for s in &d.substs {
                let dbg_in = if dbg_call { Some(s.to_list()) } else { None };
                // Borrowing view of the variant's entries: every consumer
                // below either reads through the refs or clones exactly the
                // parts it keeps, so the eager `to_list` pair clone per
                // variant was pure churn.
                let bindings: Vec<(&LVar, &LNTerm)> = s.iter().collect();
                if bindings.is_empty() {
                    // Empty subst (identity) — preserves.
                    new_substs.push(s.clone());
                    if dbg_in.is_some() {
                        eprintln!("[rs-aes-applyBound] IN  : (empty)");
                        eprintln!("  OUT[0] (empty preserved)");
                    }
                    continue;
                }
                // Compute avoid_max = max idx across (domVFresh s ∪
                // varsRange newsubst); the newsubst side is the hoisted
                // per-call `new_subst_range_max`.
                let avoid_max: u64 = {
                    let mut m: u64 = new_subst_range_max;
                    for (k, _) in &bindings {
                        if k.idx > m {
                            m = k.idx;
                        }
                    }
                    m
                };
                // Find min idx across all RHS terms' vars.
                let rhs_min: Option<u64> = {
                    use tamarin_term::lterm::HasFrees;
                    let mut min: Option<u64> = None;
                    for (_, t) in &bindings {
                        t.for_each_free(&mut |v| {
                            min = Some(min.map_or(v.idx, |m| m.min(v.idx)));
                        });
                    }
                    min
                };
                // Apply uniform shift to all RHS terms.  Haskell-faithful:
                // shift = freshStart - rhs_min, where freshStart = avoid_max + 1.
                // Shift may be negative (rhs already above avoid); use i128.
                //
                // HS `applyBound` (EquationStore.hs `applyEqStore`):
                //   ran = renameAvoiding (map snd slist) avoidSet
                // where `renameAvoiding s t = evalFreshAvoiding (rename s) t`
                // (LTerm.hs:663-664) and `rename` (LTerm.hs:607-614) is a
                // SINGLE uniform monotone shift over the WHOLE range list:
                //   freshStart <- freshIdents (succ (maxVarIdx - minVarIdx))
                //   mapFrees (Monotone $ incVar (freshStart - minVarIdx))
                // seeded by `avoid avoidSet = succ (max idx in avoidSet)`.
                // So shift = (avoid_max + 1) - minVarIdx applied to EVERY
                // free var with NO exclusion — `Monotone incVar` has no
                // special case for any var.  Do NOT preserve
                // `new_subst_range_vars` (system vars): excluding them from
                // the shift causes two distinct variant cases to collapse
                // onto the same witness idx (the `~k.30` collision in
                // Responder_secrecy), because the preserved system var keeps
                // its (shared) idx while the other range vars shift away.
                // Apply HS's plain uniform shift.
                let renamed_rhs: Vec<LNTerm> = if let Some(min) = rhs_min {
                    let fresh_start: i128 = avoid_max as i128 + 1;
                    let shift: i128 = fresh_start - (min as i128);
                    if shift != 0 {
                        use tamarin_term::lterm::HasFrees;
                        bindings
                            .iter()
                            .map(|&(_, t)| {
                                t.clone().map_free(&mut |v| {
                                    let new_idx: i128 = (v.idx as i128) + shift;
                                    let new_idx_u64 = if new_idx < 0 {
                                        0
                                    } else if new_idx > u64::MAX as i128 {
                                        u64::MAX
                                    } else {
                                        new_idx as u64
                                    };
                                    LVar {
                                        name: v.name,
                                        sort: v.sort,
                                        idx: new_idx_u64,
                                    }
                                })
                            })
                            .collect()
                    } else {
                        bindings.iter().map(|&(_, t)| t.clone()).collect()
                    }
                } else {
                    bindings.iter().map(|&(_, t)| t.clone()).collect()
                };
                // Build equations.  LHS = `apply new_subst (Var lv)`,
                // RHS = renamed `t`.
                let eqs: Vec<Equal<LNTerm>> = bindings
                    .iter()
                    .zip(renamed_rhs)
                    .map(|(&(lv, _), t)| {
                        let lv_t = Term::Lit(Lit::Var(lv.clone()));
                        Equal {
                            lhs: tamarin_term::subst::apply_vterm(&new_subst, lv_t),
                            rhs: t,
                        }
                    })
                    .collect();
                // Unify with Maude — multi-unifier returns a Disj.
                let mut max_idx = fresh_base;
                {
                    use tamarin_term::lterm::HasFrees;
                    for e in &eqs {
                        e.lhs.for_each_free(&mut |v| {
                            if v.idx > max_idx {
                                max_idx = v.idx;
                            }
                        });
                        e.rhs.for_each_free(&mut |v| {
                            if v.idx > max_idx {
                                max_idx = v.idx;
                            }
                        });
                    }
                }
                // HS-faithful local Maude handle for this `applyBound`
                // invocation.  The unification, the witness lift
                // (`reserve_idxs`), and the post-unify `reduce` calls all
                // draw witness idxs from a fresh local counter seeded at
                // `succ avoid_max` (mirroring HS's `evalFreshAvoiding
                // (range) avoidSet`, LTerm.hs:647-653).  The Maude process
                // state is shared (Arc cloned), only the counter is
                // per-call — so the global counter advances ONLY for
                // non-applyBound allocations.
                //
                // HS-faithful seed: `avoid avoidSet = succ (max idx in
                // avoidSet)` where avoidSet = `domVFresh s ∪ varsRange
                // newsubst` (LTerm.hs:647-648 `avoid`; EquationStore.hs
                // `renameAvoiding (range slist) (domVFresh s ∪ varsRange newsubst)`).
                // HS does NOT include `max_idx` (the post-shift
                // equation-system vars) in the seed — the shifted RHS
                // vars are themselves all > avoid_max by construction.
                // Including `max_idx` would be non-faithful: two alpha-
                // equivalent input variants whose `rhs_min` (and hence
                // `max_idx`) differs would seed at distinct values →
                // witness `reserve_idxs` returns a different base →
                // outputs are alpha-equivalent but structurally distinct
                // → the post-loop `sort + dedup` fails to collapse them.
                let local_maude_owned = maude.with_fresh_counter_from(avoid_max);
                let aes_maude: &tamarin_term::maude_proc::MaudeHandle = &local_maude_owned;
                if let Some(input) = &dbg_in {
                    eprintln!("[rs-aes-applyBound] IN  : {:?}", input);
                }
                if aes_dbg_variant() {
                    let pairs: Vec<String> = bindings
                        .iter()
                        .map(|(k, v)| {
                            format!(
                                "{}.{} → {}",
                                k.name,
                                k.idx,
                                format!("{:?}", v).chars().take(80).collect::<String>()
                            )
                        })
                        .collect();
                    eprintln!("[aes_variant] applyBound bindings: {:?}", pairs);
                }
                // TAM_RS_DBG_AES_DETAIL=1: dump per-variant rhs_min, shift,
                // avoid_max, max_idx, counter before/after Maude.  Used to
                // diagnose witness idx divergence vs HS (split_case ordering).
                let detail_dbg = aes_dbg_detail();
                if detail_dbg {
                    eprintln!(
                        "[rs-aes-detail] avoid_max={} rhs_min={:?} max_idx={} counter_before={}",
                        avoid_max,
                        rhs_min,
                        max_idx,
                        maude.fresh_counter_peek()
                    );
                    eprintln!(
                        "[rs-aes-detail]   eqs: {:?}",
                        eqs.iter()
                            .map(|e| format!("{:?} =? {:?}", e.lhs, e.rhs))
                            .collect::<Vec<_>>()
                    );
                }
                let counter_before_maude = aes_maude.fresh_counter_peek();
                // HS `applyBound` (EquationStore.hs:406-446, see line 434): `unifiers =
                // unifyLNTerm eqs` — NO avoid.  The RHS terms were already
                // rebased above `avoidSet` by the uniform-shift rename above
                // (HS `ran = renameAvoiding (range) avoidSet`), so the reply
                // witnesses (numbered per-call at `avoid (M.elems bindings)`)
                // land above the avoid set without any injected floor.  The
                // local handle's counter is used only by the downstream
                // system-var lift (`reserve_idxs`), which mints
                // differently-named witnesses that cannot collide by
                // (name,sort,idx) with the "x"-named reply witnesses.
                let unifiers = match aes_maude.unify_at("apply_eq_store::re_unify", &eqs) {
                    Ok(u) => u,
                    Err(e) => return Err(AddEqsError::Maude(format!("{}", e))),
                };
                if detail_dbg {
                    eprintln!(
                        "[rs-aes-detail] counter_after={} delta={} #unifiers={}",
                        aes_maude.fresh_counter_peek(),
                        aes_maude
                            .fresh_counter_peek()
                            .saturating_sub(counter_before_maude),
                        unifiers.len()
                    );
                    for (i, u) in unifiers.iter().enumerate() {
                        eprintln!("[rs-aes-detail]   unifier[{}]: {:?}", i, u);
                    }
                }
                if dbg_in.is_some() {
                    eprintln!("  {} unifiers from Maude", unifiers.len());
                }
                if unifiers.is_empty() {
                    // No unifier → variant dropped.
                    continue;
                }
                // For each unifier, build the new vfresh subst.  Restrict
                // its domain to `varsRange(new_subst) ∪ dom(s)` so we
                // don't leak Maude witnesses.  `varsRange(new_subst)` is
                // already materialized once per call as
                // `new_subst_range_vars`; `dom(s)` (this variant's original
                // domain keys) is loop-invariant across the unifier loop,
                // so hoist it here as `orig_dom`.  The restrict predicate at
                // the filter below is then the two-set membership
                // `new_subst_range_vars ∪ orig_dom` — identical to
                // `restrict_set.contains`, with no per-subst set build.
                //
                // `orig_dom` also serves the system-var lift inside the
                // unifier loop: when restrict drops a (witness, system_var)
                // entry due to LARGER-idx orient, the system_var ends up
                // orphaned in OTHER entries' range values.  Without lifting
                // it, the next aes call's uniform RHS shift treats it as a
                // witness and renames it, breaking the binding to the
                // rule's premise (Client_auth Ltk vs In ltkS desync).
                let orig_dom: tamarin_utils::FastSet<LVar> =
                    bindings.iter().map(|&(k, _)| k.clone()).collect();
                for raw in unifiers {
                    // TAM_DBG_RAW_UNIFIER=1: dump Maude's raw output.
                    if aes_dbg_raw_unifier() {
                        eprintln!("[rs-raw-unifier] sid={:?} raw entries:", d.split_id);
                        for (k, t) in &raw {
                            eprintln!(
                                "[rs-raw-unifier]   {}.{}/{:?} → {:?}",
                                k.name,
                                k.idx,
                                k.sort,
                                format!("{:?}", t).chars().take(80).collect::<String>()
                            );
                        }
                    }
                    // EXTRACT-SYSTEM-VARS-TO-DOMAIN: the AC-free local
                    // unifier path (maude_proc.rs, the AC-free fast path
                    // in `unify`) doesn't
                    // introduce narrowing witnesses for cross-sort
                    // var-var unification.  E.g. for `Var(~k:Fresh) =
                    // Var(~mw:Msg)`, the local unifier returns
                    // `~mw:Msg → Var(~k:Fresh)` (Unification.hs:235-243, see line 241
                    // orientation).  After restrict drops `~mw`, the
                    // `~k` narrowing info is lost AND `~k` (a system
                    // var in new_subst's range) ends up referenced
                    // ONLY in OTHER subst entries' values — never as
                    // a domain key.
                    //
                    // Haskell's full Maude `unify` introduces a fresh
                    // narrowing witness `~w:Fresh` and produces both
                    // `~k:Fresh → ~w:Fresh` and `~mw:Msg → ~w:Fresh`.
                    // After Haskell's restrict (keys in
                    // `varsRange new_subst ∪ domVFresh s`), `~k → ~w`
                    // survives — placing the system var `~k` as a
                    // domain key with a fresh-witness value.
                    //
                    // To mirror Haskell's post-Maude shape, after the
                    // local unifier returns its raw subst, we do a
                    // post-processing pass:
                    //   1. Identify system vars S referenced in any
                    //      RANGE value of the subst that are NOT in
                    //      the domain of the subst.
                    //   2. For each such S, allocate a fresh witness
                    //      W of S's sort, replace S→W in all range
                    //      values, and ADD `S → Var(W)` to the domain.
                    //
                    // System vars S are detected as members of
                    // `new_subst_range_vars` (the vars in new_subst's
                    // range — these are by-construction the system
                    // vars introduced by prior unifications into the
                    // free subst).  Variant subst's range should refer
                    // only to fresh witnesses (Haskell's
                    // SubstVFresh invariant); any system-var reference
                    // there is a Rust-side artifact that needs to be
                    // lifted to the domain.
                    use tamarin_term::lterm::HasFrees;
                    use tamarin_term::term::Term;
                    use tamarin_term::vterm::Lit;
                    // Compute current subst's domain (after restrict).
                    // Membership-only (like `orig_dom` and `seen` below —
                    // `to_lift` carries the byte-visible order), so hash
                    // sets replace the per-unifier BTreeSet builds.
                    let current_dom: tamarin_utils::FastSet<LVar> =
                        raw.iter().map(|(k, _)| k.clone()).collect();
                    // `orig_dom` (this variant's ORIGINAL bindings.keys —
                    // the variant's system vars from its domain) is hoisted
                    // above the unifier loop; it participates in the
                    // system-var detection below.
                    // Find system vars in any range value that aren't
                    // in the current domain.  These are the ones to
                    // lift.
                    let mut to_lift: Vec<LVar> = Vec::new();
                    let mut seen: tamarin_utils::FastSet<LVar> = Default::default();
                    for (_, t) in &raw {
                        t.for_each_free(&mut |v: &LVar| {
                            let is_system =
                                new_subst_range_vars.contains(v) || orig_dom.contains(v);
                            if is_system && !current_dom.contains(v) && seen.insert(v.clone()) {
                                to_lift.push(v.clone());
                            }
                        });
                    }
                    // For each S in to_lift, allocate a fresh witness W
                    // of S's sort.  Use the local applyBound handle so
                    // these witnesses share the per-call counter and
                    // don't advance the global session counter.
                    let mut witnesses: Vec<(LVar, LVar)> = Vec::new();
                    if !to_lift.is_empty() {
                        let base = aes_maude.reserve_idxs(to_lift.len() as u64);
                        if tamarin_utils::env_gate!("TAM_RS_DBG_FOLD_DRAWS") {
                            eprintln!(
                                "[rs-fold] to_lift len={} base={} avoid_max={} vars={:?}",
                                to_lift.len(),
                                base,
                                avoid_max,
                                to_lift
                                    .iter()
                                    .map(|s| format!("{}.{}", s.name, s.idx))
                                    .collect::<Vec<_>>()
                            );
                        }
                        for (i, s) in to_lift.iter().enumerate() {
                            let w = LVar {
                                name: s.name,
                                sort: s.sort,
                                idx: base + i as u64,
                            };
                            witnesses.push((s.clone(), w));
                        }
                    }
                    let witness_map: std::collections::BTreeMap<LVar, LVar> =
                        witnesses.iter().cloned().collect();
                    let rename_term = |t: LNTerm| -> LNTerm {
                        t.map_free(&mut |v: LVar| witness_map.get(&v).cloned().unwrap_or(v))
                    };
                    // Build lifted subst: rename range values, add
                    // S → Var(W) entries to domain.
                    let mut lifted: Vec<(LVar, LNTerm)> = Vec::new();
                    for (k, t) in raw {
                        lifted.push((k, rename_term(t)));
                    }
                    for (s, w) in witnesses {
                        lifted.push((s, Term::Lit(Lit::Var(w))));
                    }
                    // HS-faithful: NO post-Maude normalisation of variant
                    // range terms.  HS's `applyEqStore` (EquationStore.hs)
                    // returns the raw Maude unifier outputs without
                    // calling `normSubstVFresh'` — that normaliser is only
                    // used during VARIANT COMPUTATION for rules
                    // (RuleVariants.hs:61-134, see line 74 `normSubstVFresh'`), NOT here.  Normalising here
                    // hides non-NF range values (e.g. `Xor(~k,~k)` that
                    // reduces to `zero`) from the post-fan-out
                    // `simpMinimize`/`substCreatesNonNormalTerms` filter,
                    // letting variant cases survive that HS drops.
                    // Observable on LAK06::noninjectiveagreementTAG —
                    // HS's per-arm simp narrows SId(1) variants to 0
                    // (eq_store false) for cases 1/3/5/6/9 of SId(0);
                    // RS's normalised variants stay NF and the simp leaves
                    // them at conj=1 [1:1], so the cases survive
                    // perform_split as bonus split_case_N branches.
                    let pairs: Vec<(LVar, LNTerm)> = lifted
                        .into_iter()
                        .filter(|(v, _)| new_subst_range_vars.contains(v) || orig_dom.contains(v))
                        .collect();
                    let out_subst = LNSubstVFresh::from_list(pairs);
                    if dbg_in.is_some() {
                        eprintln!("  OUT: {:?}", out_subst.to_list());
                    }
                    dbg_register_subst_transform("applyBound", s, &out_subst);
                    new_substs.push(out_subst);
                }
            }
            // HS-faithful (`applyEqStore`, EquationStore.hs): wrap
            // the per-variant `applyBound` results in `S.fromList`, which
            // sorts and dedups by `Set LNSubstVFresh` Ord.  Without this,
            // post-Maude variants stay in input × multi-unifier order —
            // making `perform_split` see a different sequence than HS
            // and changing `split_case_N` assignments downstream.
            //
            // STRUCTURAL-ONLY dedup (NO alpha-dedup).  HS's `S.fromList`
            // is a STRUCTURAL set: two `applyBound` outputs that are
            // alpha-equivalent up to witness rename but differ in their
            // actual fresh-var idxs are DISTINCT `Set` elements and HS
            // keeps BOTH.  This happens routinely when two different
            // input variants of the disjunction re-unify (under the
            // case-split subst) to results that are alpha-equivalent —
            // HS preserves each as its own member.  Proven on
            // CH07::noninjectiveagreement_reader: under splitEqs(0) /
            // split_case_4 the sid=4 disjunction has 6 substs in HS, two
            // of which (witness idxs ~r2.43… and ~r2.74…) are alpha-
            // equivalent but kept distinct; an alpha-canonical dedup
            // here collapses them to 5, dropping one split case and
            // adding a spurious extra splitEqs goal in that branch
            // (78 vs HS 77 steps).  HS NEVER alpha-collapses here, so we
            // must not either — the per-call avoid_max seed already aligns
            // witness allocation with HS for the cases where HS *does*
            // structurally coincide (e.g. KEA_plus_AdvKey::keaplus_
            // {initiator,responder}_key, still byte-identical without the
            // alpha-dedup).
            new_substs.sort();
            new_substs.dedup();
            if aes_dbg_variants() {
                eprintln!(
                    "[aes_variants] disj split_id={:?} before→after: {} → {} substs",
                    d.split_id,
                    d.substs.len(),
                    new_substs.len()
                );
                eprintln!("[aes_variants]   BEFORE (input variants):");
                for (i, s) in d.substs.iter().enumerate() {
                    eprintln!("[aes_variants]     in[{}]: {:?}", i, s.to_list());
                }
                eprintln!("[aes_variants]   AFTER (post-Maude variants, sorted+deduped):");
                for (i, s) in new_substs.iter().enumerate() {
                    eprintln!("[aes_variants]     out[{}]: {:?}", i, s.to_list());
                }
            }
            if dbg_call {
                eprintln!(
                    "[rs-aes] OUT disj[?] sid={:?} ({} substs)",
                    d.split_id,
                    new_substs.len()
                );
                for (j, s) in new_substs.iter().enumerate() {
                    eprintln!("  out[{}]: {:?}", j, s.to_list());
                }
            }
            // TAM_DBG_BAD_DISJ=1: detect collision in new_substs.
            if aes_dbg_bad_disj() {
                for s in &new_substs {
                    let entries: Vec<(LVar, LNTerm)> = s.to_list();
                    let mut seen: std::collections::BTreeMap<String, LVar> =
                        std::collections::BTreeMap::new();
                    for (k, v) in &entries {
                        if let tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(vv)) = v
                        {
                            let v_str = format!("{}.{}", vv.name, vv.idx);
                            if let Some(prev_k) = seen.get(&v_str) {
                                if prev_k.name == k.name && prev_k != k {
                                    eprintln!(
                                        "[BAD_DISJ_AES] sid={:?} collision: {}.{} + {}.{} → {}",
                                        d.split_id, prev_k.name, prev_k.idx, k.name, k.idx, v_str
                                    );
                                    eprintln!("[BAD_DISJ_AES] subst:");
                                    for (k2, v2) in &entries {
                                        eprintln!(
                                            "[BAD_DISJ_AES]   {}.{}/{:?} → {:?}",
                                            k2.name,
                                            k2.idx,
                                            k2.sort,
                                            format!("{:?}", v2)
                                                .chars()
                                                .take(80)
                                                .collect::<String>()
                                        );
                                    }
                                    eprintln!("[BAD_DISJ_AES] asubst={:?}", asubst.to_list());
                                    eprintln!(
                                        "[BAD_DISJ_AES] input subst (pre-aes) for this variant:"
                                    );
                                    let bt = std::backtrace::Backtrace::force_capture();
                                    let bt_s = format!("{}", bt);
                                    let frames: Vec<&str> = bt_s
                                        .lines()
                                        .filter(|l| l.contains("tamarin_") || l.contains(".rs:"))
                                        .take(20)
                                        .collect();
                                    eprintln!("[BAD_DISJ_AES] backtrace:\n{}", frames.join("\n"));
                                    break;
                                }
                            }
                            seen.insert(v_str, k.clone());
                        }
                    }
                }
            }
            new_conj.push(EqDisj {
                split_id: d.split_id,
                substs: new_substs,
            });
        }
        // No global-counter advance is needed after the per-variant loop:
        // each per-variant call uses its OWN counter (a local MaudeHandle
        // clone via `with_fresh_counter_from`), so the global counter
        // never advanced from those calls in the first place.  The
        // witnesses minted live only inside SubstVFresh range values,
        // which are α-equivalent up to witness rename — VFresh-local.
        // Any subsequent allocation that needs to avoid these witnesses
        // will see them via `bounds_max`'s walk of `eq_store.conj`
        // (reduction.rs, `fn bounds_max`), which counts domain keys; the
        // range/witness idxs don't affect cross-call uniqueness because
        // they're per-SubstVFresh.
        self.conj = new_conj;
        self.subst = new_subst;
        Ok(())
    }
}

/// True if `t` is a single constant literal (no variables, no apps).
fn is_constant_term(t: &LNTerm) -> bool {
    matches!(
        t,
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Con(_))
    )
}

/// `TAM_RS_TRACE_FRESH_BIND=1`: log every binding being composed into
/// the eq-store whose key or value is Fresh-sorted.  Used to find the
/// upstream binding that equates two distinct protocol rules' fresh
/// variables (which then causes `enforce_fresh_node_uniqueness` to
/// merge their suppliers and `enforce_edge_uniqueness` to fire
/// prem_idx_clash false-positives).
fn log_fresh_bindings(site: &str, subst: &LNSubst) {
    if !tamarin_utils::env_gate!("TAM_RS_TRACE_FRESH_BIND") {
        return;
    }
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    for (v, t) in subst.to_list() {
        // Find any Fresh-sort var on either side.
        let lhs_fresh = v.sort == LSort::Fresh;
        let mut rhs_has_fresh = false;
        if let Term::Lit(Lit::Var(rv)) = &t {
            if rv.sort == LSort::Fresh {
                rhs_has_fresh = true;
            }
        }
        if lhs_fresh || rhs_has_fresh {
            let t_str: String = format!("{:?}", t).chars().take(120).collect();
            eprintln!(
                "[FRESH_BIND] site={} {}.{}/{:?} → {}",
                site, v.name, v.idx, v.sort, t_str
            );
        }
    }
}

/// TAM_RS_TRACE_S_BIND: log every binding where lhs OR rhs mentions an
/// LVar with name="S" and sort=Pub.  Used to pinpoint the moment a
/// freshly-grafted Serv_1's $S diverges from the lemma's $S.
pub(crate) fn log_s_pub_bindings(site: &str, subst: &LNSubst) {
    if !tamarin_utils::env_gate!("TAM_RS_TRACE_S_BIND") {
        return;
    }
    use tamarin_term::lterm::{HasFrees, LSort};
    for (v, t) in subst.to_list() {
        let v_is_s = v.name == "S" && v.sort == LSort::Pub;
        let mut t_has_s = false;
        t.for_each_free(&mut |w: &tamarin_term::lterm::LVar| {
            if w.name == "S" && w.sort == LSort::Pub {
                t_has_s = true;
            }
        });
        if v_is_s || t_has_s {
            let path = crate::constraint::solver::trace::case_path_string();
            let bt = std::backtrace::Backtrace::force_capture();
            let bt_str = format!("{}", bt);
            // Trim the backtrace to the most relevant 4 frames
            // (caller's call stack into the eq_store).
            let bt_short: String = bt_str
                .lines()
                .filter(|l| l.contains("tamarin_") && !l.contains(".cargo"))
                .take(6)
                .collect::<Vec<_>>()
                .join(" | ");
            let t_str: String = format!("{:?}", t).chars().take(120).collect();
            eprintln!(
                "[S_BIND] path={} site={} {}.{}/{:?} → {}  | bt={}",
                path, site, v.name, v.idx, v.sort, t_str, bt_short
            );
        }
    }
}

/// TAM_RS_TRACE_VR_BIND: log every binding where lhs is a Node LVar with
/// name "vr" (rule-instance node ids).  Used to pinpoint when grafted
/// Serv_1 node ids get renamed to low-idx values that collide with
/// pre-existing instances.
pub(crate) fn log_vr_node_bindings(site: &str, subst: &LNSubst) {
    if !tamarin_utils::env_gate!("TAM_RS_TRACE_VR_BIND") {
        return;
    }
    use tamarin_term::lterm::LSort;
    for (v, t) in subst.to_list() {
        if v.name == "vr" && v.sort == LSort::Node {
            let path = crate::constraint::solver::trace::case_path_string();
            let bt = std::backtrace::Backtrace::force_capture();
            let bt_str = format!("{}", bt);
            let bt_short: String = bt_str
                .lines()
                .filter(|l| l.contains("tamarin_") && !l.contains(".cargo"))
                .take(6)
                .collect::<Vec<_>>()
                .join(" | ");
            let t_str: String = format!("{:?}", t).chars().take(60).collect();
            eprintln!(
                "[VR_BIND] path={} site={} vr.{} → {}  | bt={}",
                path, site, v.idx, t_str, bt_short
            );
        }
    }
}

/// Re-export sort comparison from the term layer for `simp_identify`.
fn sort_compare(
    a: tamarin_term::lterm::LSort,
    b: tamarin_term::lterm::LSort,
) -> Option<std::cmp::Ordering> {
    tamarin_term::lterm::sort_compare(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_term::subst_vfresh::SubstVFresh;

    fn fresh_subst() -> LNSubstVFresh {
        let v = LVar::new("x", LSort::Msg, 0);
        let t = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new(
            "y",
            LSort::Msg,
            0,
        )));
        SubstVFresh::from_list(vec![(v, t)])
    }

    // A distinct subst per `idx`.  `add_disj`/`add_rule_variants` dedup
    // identical substs (HS-faithful `S.fromList`, EquationStore.hs),
    // so building a multi-element disjunction from repeated `fresh_subst()`
    // collapses to a single element.  Tests that need a genuine N-element
    // disjunction use distinct substs via this helper.
    fn fresh_subst_n(idx: u64) -> LNSubstVFresh {
        let v = LVar::new("x", LSort::Msg, idx);
        let t = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new(
            "y",
            LSort::Msg,
            idx,
        )));
        SubstVFresh::from_list(vec![(v, t)])
    }

    #[test]
    fn empty_store_is_consistent() {
        let s = EquationStore::empty();
        assert!(!s.is_false());
        assert!(s.splits().is_empty());
    }

    #[test]
    fn empty_disj_makes_store_false() {
        let mut s = EquationStore::empty();
        let id = s.add_disj(vec![]);
        assert_eq!(id, SplitId(0));
        assert!(s.is_false());
    }

    #[test]
    fn add_disj_assigns_fresh_ids() {
        let mut s = EquationStore::empty();
        let id1 = s.add_disj(vec![fresh_subst()]);
        let id2 = s.add_disj(vec![fresh_subst_n(0), fresh_subst_n(1)]);
        assert_eq!(id1, SplitId(0));
        assert_eq!(id2, SplitId(1));
        assert!(!s.is_false());
        assert_eq!(s.split_size(id1), Some(1));
        assert_eq!(s.split_size(id2), Some(2));
        assert!(s.split_exists(id2));
    }

    #[test]
    fn splits_sorted_by_size() {
        let mut s = EquationStore::empty();
        let big = s.add_disj(vec![fresh_subst(), fresh_subst(), fresh_subst()]);
        let small = s.add_disj(vec![fresh_subst()]);
        let sorted = s.splits();
        assert_eq!(sorted[0], small);
        assert_eq!(sorted[1], big);
    }

    #[test]
    fn perform_split_branches() {
        let mut s = EquationStore::empty();
        let id = s.add_disj(vec![fresh_subst_n(0), fresh_subst_n(1)]);
        let branches = s.perform_split(id).unwrap();
        assert_eq!(branches.len(), 2);
        // Each branch contains a single-case disjunction.
        for b in &branches {
            assert_eq!(b.conj.len(), 1);
            assert_eq!(b.conj[0].substs.len(), 1);
        }
    }

    #[test]
    fn perform_split_unknown_id() {
        let s = EquationStore::empty();
        assert!(s.perform_split(SplitId(42)).is_none());
    }

    #[test]
    fn set_false_marks_store_false() {
        let s = EquationStore::empty().set_false();
        assert!(s.is_false());
    }

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") {
            return Some(p);
        }
        let candidates = ["/usr/local/bin/maude", "/usr/bin/maude", "maude"];
        for c in &candidates {
            if std::path::Path::new(c).exists() {
                return Some((*c).to_string());
            }
        }
        None
    }

    #[test]
    fn rule_variants_added_as_disjunction() {
        let mut store = EquationStore::empty();
        let id = store
            .add_rule_variants(vec![fresh_subst_n(0), fresh_subst_n(1)])
            .expect("add_rule_variants");
        assert_eq!(id, SplitId(0));
        assert_eq!(store.split_size(id), Some(2));
    }

    #[test]
    fn rule_variants_rejects_overlapping_domain() {
        let mut store = EquationStore::empty();
        // Pre-populate the free subst with `x`.
        let v = LVar::new("x", LSort::Msg, 0);
        let t = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new(
            "z",
            LSort::Msg,
            0,
        )));
        store.subst = LNSubst::from_list(vec![(v, t)]);
        // Variant subst also touches `x`.
        let res = store.add_rule_variants(vec![fresh_subst()]);
        assert!(res.is_err());
    }

    #[test]
    fn simp_empty_disj_makes_store_false() {
        let mut store = EquationStore::empty();
        // Add an empty disjunction.
        let _ = store.add_disj(vec![]);
        let changed = store.simp_empty_disj();
        assert!(changed);
        assert!(store.is_false());
    }

    #[test]
    fn simp_idempotent_on_consistent_store() {
        let mut store = EquationStore::empty();
        let _ = store.add_disj(vec![fresh_subst()]);
        let store = store.simp(|_, _| false);
        assert!(!store.is_false());
        assert!(!store.conj.is_empty());
    }

    #[test]
    fn simp_abstract_name_factors_common_constant() {
        // Build a disjunction where every subst maps `x → 'foo'` (pub
        // constant). simp_abstract_name should hoist that into the
        // free substitution.
        use tamarin_term::lterm::{Name, NameTag};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let v = LVar::new("x", LSort::Msg, 0);
        let foo: LNTerm = Term::Lit(Lit::Con(Name::new(NameTag::Pub, "foo".to_string())));
        let s1 = LNSubstVFresh::from_list(vec![(v.clone(), foo.clone())]);
        let s2 = LNSubstVFresh::from_list(vec![(v.clone(), foo.clone())]);
        let mut store = EquationStore::empty();
        let _ = store.add_disj(vec![s1, s2]);
        assert!(store.simp_abstract_name());
        // Free subst should now contain x → foo.
        let dom: Vec<&LVar> = store.subst.dom().collect();
        assert_eq!(dom, vec![&v]);
    }

    #[test]
    fn add_eqs_xor_produces_disjunction() {
        let path = match maude_path() {
            Some(p) => p,
            None => {
                eprintln!("skipping: no maude");
                return;
            }
        };
        let sig = tamarin_term::maude_sig::xor_maude_sig();
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
        // x XOR a =? b XOR y has multiple AC unifiers.
        use tamarin_term::function_symbols::AcSym;
        use tamarin_term::term::{f_app_ac, Term};
        use tamarin_term::vterm::Lit;
        let v = |n: &str| LVar::new(n, LSort::Msg, 0);
        let lhs: LNTerm = f_app_ac(
            AcSym::Xor,
            vec![Term::Lit(Lit::Var(v("x"))), Term::Lit(Lit::Var(v("a")))],
        );
        let rhs: LNTerm = f_app_ac(
            AcSym::Xor,
            vec![Term::Lit(Lit::Var(v("b"))), Term::Lit(Lit::Var(v("y")))],
        );
        let mut store = EquationStore::empty();
        let split = store
            .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs, rhs }])
            .expect("add_eqs xor");
        // AC unification has many unifiers, so we should get a fresh disjunction.
        assert!(split.is_some(), "expected disjunction split");
        assert!(!store.is_false());
        assert!(!store.conj.is_empty());
    }

    #[test]
    fn add_eqs_two_vars_via_maude() {
        let path = match maude_path() {
            Some(p) => p,
            None => {
                eprintln!("skipping: no maude");
                return;
            }
        };
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
        // Unify x =? y — single mgu, no disjunction, just composes into subst.
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let tx: LNTerm = Term::Lit(Lit::Var(x));
        let ty: LNTerm = Term::Lit(Lit::Var(y));
        let mut store = EquationStore::empty();
        let split = store
            .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }])
            .expect("add_eqs");
        // Single mgu → composed into subst, no new disjunction.
        assert!(split.is_none());
        assert!(!store.is_false());
        // The free substitution must now bind one variable to the other.
        assert!(
            !store.subst.is_empty(),
            "subst should be populated, got {:?}",
            store.subst
        );
    }

    // =========================================================================
    // Haskell-faithfulness invariants for `add_eqs`.
    //
    // These tests pin orientation choices in the eq-store that we missed
    // for weeks.  See `unification::haskell_invariants` for the rationale.
    // =========================================================================

    /// `add_eqs` for AC-free, same-sort var-var input must orient the
    /// resulting subst with LARGER-idx as KEY (Haskell `unifyRaw`
    /// convention, Unification.hs:235-243, see line 241).
    ///
    /// This is the most important orientation invariant for downstream
    /// `restrict stableVars`: stable pattern vars (small idx) must stay
    /// on the VALUE side so they get filtered out (they're never keys
    /// in Haskell's subst).
    ///
    /// **If this test fails, foo_eligibility-class divergences will
    /// silently appear in the corpus.**
    #[test]
    fn add_eqs_ac_free_var_var_uses_haskell_orientation() {
        let path = match maude_path() {
            Some(p) => p,
            None => {
                eprintln!("skipping: no maude");
                return;
            }
        };
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");

        // Mimic the foo_eligibility shape: stable pattern var t.1 unified
        // with rule-internal var e.10.  Both Msg, same sort.  Haskell
        // convention: e.10 (larger idx) is the key.
        let t1 = LVar::new("t", LSort::Msg, 1);
        let e10 = LVar::new("e", LSort::Msg, 10);
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let lt1: LNTerm = Term::Lit(Lit::Var(t1.clone()));
        let le10: LNTerm = Term::Lit(Lit::Var(e10.clone()));

        let mut store = EquationStore::empty();
        let split = store
            .add_eqs(
                &h,
                &[tamarin_term::rewriting::Equal {
                    lhs: lt1,
                    rhs: le10,
                }],
            )
            .expect("add_eqs");
        assert!(split.is_none(), "var-var unification produces a single mgu");
        assert!(!store.is_false());

        // Haskell-faithful: e.10 (larger idx) is the KEY.
        assert!(
            store.subst.image_of(&e10).is_some(),
            "add_eqs MUST orient same-sort var-var with larger-idx (e.10) \
                 as KEY.  If this fails, foo_eligibility::eligibility and \
                 friends will silently diverge from Haskell.  See \
                 project_rust_lvar_ord_idx_first_landed.md."
        );
        assert!(
            store.subst.image_of(&t1).is_none(),
            "smaller-idx (t.1, the stable pattern var) must NOT be a key"
        );
    }

    /// `add_eqs` for an unbinding (`x = y` where neither is in the
    /// existing subst) must NOT introduce a Maude witness ~mw.
    ///
    /// We use the local non-AC fast path for AC-free signatures, which
    /// just orients the bind directly.  If we accidentally regress to
    /// the witness-heavy Maude shape (`{x → ~mw, y → ~mw}`), the
    /// downstream `enforce_fresh_node_uniqueness_pass` will bucket
    /// nodes by witness and merge Fresh nodes that should stay
    /// distinct (the TLS_Handshake prem_idx_clash class).
    #[test]
    fn add_eqs_ac_free_var_var_does_not_introduce_witness() {
        let path = match maude_path() {
            Some(p) => p,
            None => {
                eprintln!("skipping: no maude");
                return;
            }
        };
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let tx: LNTerm = Term::Lit(Lit::Var(x.clone()));
        let ty: LNTerm = Term::Lit(Lit::Var(y.clone()));
        let mut store = EquationStore::empty();
        let _ = store
            .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }])
            .expect("add_eqs");

        // Unifying two free Msg vars must yield a simple orientation
        // between x and y (HS-faithful var-var orient gives `{y → x}`),
        // NOT a fresh `~mw`-style witness.  So flag any subst var that is
        // neither x nor y — that would be a freshly-introduced witness.
        // (Witness introduction here regressed TLS_Handshake::prem_idx_clash.)
        // x legitimately appears in the range of `{y → x}`, so the check
        // below flags any subst var other than x or y, not just non-`x`
        // values.
        use tamarin_term::lterm::HasFrees;
        let mut witness_found = false;
        for (key, term) in store.subst.to_list() {
            if key.name != "x" && key.name != "y" {
                witness_found = true;
            }
            term.for_each_free(&mut |v| {
                if v.name != "x" && v.name != "y" {
                    witness_found = true;
                }
            });
        }
        assert!(
            !witness_found,
            "AC-free var-var unification must NOT introduce ~mw \
                 witnesses.  Witness introduction here regressed \
                 TLS_Handshake::prem_idx_clash historically."
        );
    }

    /// `add_eqs` is idempotent for an already-implied equation.
    ///
    /// If the eq-store already has `x → 1`, calling `add_eqs([x = 1])`
    /// must NOT introduce new bindings or witnesses or contradictions.
    /// This is a regression guard for the eq-store's snapshot/apply
    /// chain in `add_eqs_inner` (we apply `self.subst` to inputs first).
    #[test]
    fn add_eqs_idempotent_for_already_implied_eq() {
        let path = match maude_path() {
            Some(p) => p,
            None => {
                eprintln!("skipping: no maude");
                return;
            }
        };
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 5);
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let tx: LNTerm = Term::Lit(Lit::Var(x.clone()));
        let ty: LNTerm = Term::Lit(Lit::Var(y.clone()));
        let mut store = EquationStore::empty();
        let _ = store
            .add_eqs(
                &h,
                &[tamarin_term::rewriting::Equal {
                    lhs: tx.clone(),
                    rhs: ty.clone(),
                }],
            )
            .expect("first add_eqs");
        let dom_before: Vec<LVar> = store.subst.dom().cloned().collect();

        // Repeat — should be a no-op.
        let _ = store
            .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }])
            .expect("second add_eqs");
        let dom_after: Vec<LVar> = store.subst.dom().cloned().collect();
        assert_eq!(
            dom_before, dom_after,
            "Repeated add_eqs of an already-implied equation must \
                    not change the subst domain."
        );
        assert!(
            !store.is_false(),
            "Repeating an equation must not produce a contradiction."
        );
    }

    /// `add_eqs` with an unsatisfiable input marks the store false.
    ///
    /// Constructor mismatch (pair vs pk) is unsatisfiable in non-AC.
    /// Our `add_eqs_inner` should set the store to false, not panic or
    /// silently succeed.
    #[test]
    fn add_eqs_unsatisfiable_sets_store_false() {
        let path = match maude_path() {
            Some(p) => p,
            None => {
                eprintln!("skipping: no maude");
                return;
            }
        };
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
        use tamarin_term::builtin::{msg_var, pair, pk};
        let lhs: LNTerm = pair(msg_var("a", 1), msg_var("b", 2));
        let rhs: LNTerm = pk(msg_var("c", 3));
        let mut store = EquationStore::empty();
        let _ = store.add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs, rhs }]);
        assert!(
            store.is_false(),
            "constructor mismatch must set store to false"
        );
    }
}
