// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Fact` from `lib/theory/src/Theory/Model/Fact.hs`.
//!
//! Multiset-rewriting facts. This port covers the data type plus the
//! tagging / construction / query API. The Maude-backed `unifyLNFactEqs`
//! and `unifiableLNFacts` entry points live in `rule.rs` and call the
//! live Maude unification bridge (`maude.unify_at`).

use std::collections::BTreeSet;
use std::sync::Arc;

use tamarin_term::lterm::{HasFrees, LNTerm, LVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Multiplicity {
    Persistent,
    Linear,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactTag {
    /// A protocol fact: `ProtoFact(multiplicity, name, arity)`.
    /// Interned `&'static str` (see `tamarin_term::intern`): pointer-copy
    /// clone, no alloc/atomic, shared.
    Proto(Multiplicity, &'static str, usize),
    Fresh,
    Out,
    In,
    Ku,
    Kd,
    Ded,
    /// Internal: only for converting terms to facts during analysis.
    Term,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactAnnotation {
    SolveFirst,
    SolveLast,
    NoSources,
}

/// Variable fingerprint bit (cached-bloom skip).
///
/// SINGLE SHARED hashing site: both [`fact_fingerprints`] and the per-pass
/// `dom_bloom` fold in `subst_system_once` call this — never introduce a
/// second, ad-hoc var-hashing site (a divergent hash silently breaks the
/// `bloom ⊇ frees` superset invariant the skip's soundness rests on).
///
/// `LVar`'s derived `Hash` is content-based (`&str` contents + sort + idx),
/// so two independently-constructed content-equal vars hash equal (one from
/// `subst.dom()`, one from a fact's `for_each_free`); `FxBuildHasher` is
/// zero-seed deterministic, so the bit is stable process-wide. The hash is a
/// FILTER only — it never reaches observable output, so byte-determinism is
/// preserved. Do NOT "optimise" `LVar::Hash` to hash the interned name
/// *pointer*: the superset invariant depends on content-based hashing.
#[inline]
pub fn var_bit(v: &LVar) -> u64 {
    1u64 << (tamarin_utils::fx_hash_one(v) & 63)
}

/// Both cached fingerprints over a term slice in a SINGLE `for_each_free`
/// walk: the superset variable bloom (`.0`) and the EXACT maximum free-`LVar`
/// index (`.1`).  `O(number of free-var occurrences)`.
///
/// - Bloom (`.0`): a 1 in every bit position any free `LVar` hashes to, so
///   `bloom ⊇ frees` by construction.
/// - Max idx (`.1`): the largest `v.idx` over the same free leaves, folded
///   directly (NOT derived from the bloom), so it is EXACT — a no-free slice
///   yields `0`.  The fold mirrors, bit-for-bit, `bm_term`'s max fold over
///   the same `Var` leaves (reduction.rs).  This function is the sole
///   computation site of the `max_var` cache that `bm_fact` reads for the
///   `bounds_max` fresh-index seed.
#[inline]
pub fn fact_fingerprints<T: HasFrees>(terms: &[T]) -> (u64, u64) {
    let mut b = 0u64;
    let mut max = 0u64;
    for t in terms {
        t.for_each_free(&mut |v| {
            b |= var_bit(v);
            if v.idx > max {
                max = v.idx;
            }
        });
    }
    (b, max)
}

/// A multiset-rewriting fact carrying a tag, optional annotations, and
/// term arguments.
#[derive(Debug, Clone)]
pub struct Fact<T> {
    pub tag: FactTag,
    pub annotations: BTreeSet<FactAnnotation>,
    pub terms: Arc<[T]>,
    /// Cached variable fingerprint over `terms`.  `u64::MAX` =
    /// "unknown, always descend" — the never-wrong-skip default (a fact that
    /// reaches the skip with `MAX` simply descends: `MAX & dom != 0` while
    /// `dom` is non-empty).  NOT read by the manual `Eq`/`Ord` impls, so it is
    /// invisible to equality, ordering, and dedup.  NEVER copy this across a
    /// frees-changing rebuild — recompute or `MAX`.
    ///
    /// MODULE-PRIVATE (not `pub(crate)`): a stale-copy like `bloom: fa.bloom`
    /// in a frees-changing rebuild is the classic soundness bug (a bloom that
    /// no longer covers the rebuilt terms' frees breaks the `bloom ⊇ frees`
    /// skip invariant).  Keeping the field private to this module makes such a
    /// copy UNEXPRESSIBLE anywhere else — every out-of-module `Fact` must be
    /// built through a constructor (`new`/`fresh`/`fresh_annotated`/`map`) that
    /// sets the bloom correctly (computed, or the safe `MAX`), and any
    /// post-construction `.terms` edit must call `recompute_bloom()`.
    bloom: u64,
    /// Cached EXACT maximum free-`LVar` index over `terms`, or `u64::MAX` =
    /// "unknown, walk the terms".  Computed in the SAME `for_each_free` walk
    /// as `bloom` (see [`fact_fingerprints`]); a no-free fact caches `0`
    /// (folding `0` is the same no-op the per-term walk performs).
    ///
    /// UNLIKE `bloom`, this value is used as an EXACT max, never an
    /// over-approximation: `bounds_max` (reduction.rs) seeds fresh-variable
    /// drawing from it, so a value larger than the true max would draw a
    /// different fresh index and CHANGE observable output.  Every producer
    /// therefore stores the exact max or the `u64::MAX` sentinel — never a
    /// looser bound.  Consumed by `bm_fact` (reduction.rs) via
    /// [`Fact::max_var_cached`].
    ///
    /// Same MODULE-PRIVATE + never-stale-copy discipline as `bloom`: set only
    /// by the constructors and recomputed alongside `bloom` on every
    /// frees-changing rebuild.
    max_var: u64,
}

// Equality and ordering compare `tag` and `terms` only.  `annotations` is
// excluded because HS `Eq`/`Ord LNFact` treat it as metadata; `bloom` is
// excluded because it is an out-of-band skip fingerprint of the terms' frees
// (a superset of them, or the `u64::MAX` sentinel), not part of a fact's
// value — HS `LNFact` carries no such field.  Each impl destructures without
// `..` so a new `Fact` field forces an inclusion decision in every sibling
// impl at once.
impl<T: PartialEq> PartialEq for Fact<T> {
    fn eq(&self, other: &Self) -> bool {
        let Fact {
            tag,
            terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = self;
        let Fact {
            tag: other_tag,
            terms: other_terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = other;
        tag == other_tag && terms == other_terms
    }
}
impl<T: Eq> Eq for Fact<T> {}
impl<T: PartialOrd> PartialOrd for Fact<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let Fact {
            tag,
            terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = self;
        let Fact {
            tag: other_tag,
            terms: other_terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = other;
        match tag.partial_cmp(other_tag) {
            Some(std::cmp::Ordering::Equal) => terms.partial_cmp(other_terms),
            ord => ord,
        }
    }
}
impl<T: Ord> Ord for Fact<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let Fact {
            tag,
            terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = self;
        let Fact {
            tag: other_tag,
            terms: other_terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = other;
        tag.cmp(other_tag).then(terms.cmp(other_terms))
    }
}

impl<T> Fact<T> {
    /// Generic constructor: stores `bloom = u64::MAX` (no `HasFrees` bound, so
    /// the fingerprint cannot be computed here).  For LNFact producers whose
    /// output reaches `subst_system_once`, prefer [`Fact::fresh`] so the
    /// fast-path fires (a `MAX` bloom is SOUND but never skips).
    pub fn new(tag: FactTag, terms: Vec<T>) -> Self {
        Fact {
            tag,
            annotations: BTreeSet::new(),
            terms: terms.into(),
            bloom: u64::MAX,
            max_var: u64::MAX,
        }
    }
    pub fn with_annotations(mut self, ann: BTreeSet<FactAnnotation>) -> Self {
        self.annotations = ann;
        self
    }
    pub fn annotate(mut self, a: FactAnnotation) -> Self {
        self.annotations.insert(a);
        self
    }
    pub fn arity(&self) -> usize {
        self.terms.len()
    }
    /// Cached variable fingerprint.  `u64::MAX` means "not
    /// computed — always descend".
    #[inline]
    pub fn bloom(&self) -> u64 {
        self.bloom
    }
    /// Cached EXACT maximum free-var index, or `None` when unknown (the
    /// `u64::MAX` sentinel).  `bm_fact` (reduction.rs) folds `Some(m)`
    /// straight into the running max and falls back to a per-term walk on
    /// `None`.
    #[inline]
    pub fn max_var_cached(&self) -> Option<u64> {
        if self.max_var == u64::MAX {
            None
        } else {
            Some(self.max_var)
        }
    }
    /// Generic map: stores both fingerprints as `u64::MAX` (result type `U`
    /// carries no `HasFrees` bound).  A `MAX` bloom is a safe perf-miss and a
    /// `MAX` max_var falls back to the walk; if a hot LNFact producer routes
    /// through `map`, recompute via [`Fact::recompute_bloom`].
    pub fn map<U, F: FnMut(T) -> U>(self, f: F) -> Fact<U>
    where
        T: Clone,
    {
        Fact {
            tag: self.tag,
            annotations: self.annotations,
            terms: self.terms.iter().cloned().map(f).collect(),
            bloom: u64::MAX,
            max_var: u64::MAX,
        }
    }
    /// Borrowing map — the HS `Functor Fact` instance (Theory/Model/Fact.hs:176-177) for
    /// producers holding a `&Fact`.  Clones `tag`/`annotations` and stores both
    /// fingerprints as `u64::MAX`, exactly like [`Fact::new`]/[`Fact::map`]; the
    /// same recompute guidance applies if a hot LNFact producer routes here.
    pub fn map_ref<U>(&self, f: impl FnMut(&T) -> U) -> Fact<U> {
        Fact {
            tag: self.tag,
            annotations: self.annotations.clone(),
            terms: self.terms.iter().map(f).collect(),
            bloom: u64::MAX,
            max_var: u64::MAX,
        }
    }
    /// Fallible borrowing map — the HS `Traversable Fact` instance
    /// (Theory/Model/Fact.hs:182-184) specialised to `Result`; short-circuits on the first
    /// `Err`.  Same `tag`/`annotations` clone and `u64::MAX` fingerprints as
    /// [`Fact::map_ref`].
    pub fn try_map_ref<U, E>(&self, f: impl FnMut(&T) -> Result<U, E>) -> Result<Fact<U>, E> {
        let terms: Result<Vec<U>, E> = self.terms.iter().map(f).collect();
        Ok(Fact {
            tag: self.tag,
            annotations: self.annotations.clone(),
            terms: terms?.into(),
            bloom: u64::MAX,
            max_var: u64::MAX,
        })
    }
}

impl<T: HasFrees> Fact<T> {
    /// Bloom-COMPUTING constructor: use for every LNFact
    /// producer whose output reaches `subst_system_once`, so the whole-fact
    /// skip fast-path can fire.  The cached fingerprint is paid ONCE here and
    /// reused on every unchanged pass the fact survives (P1 amortization).
    pub fn fresh(tag: FactTag, terms: Vec<T>) -> Self {
        let (bloom, max_var) = fact_fingerprints(&terms);
        Fact {
            tag,
            annotations: BTreeSet::new(),
            terms: terms.into(),
            bloom,
            max_var,
        }
    }
    /// Bloom-computing constructor with annotations.
    pub fn fresh_annotated(
        tag: FactTag,
        annotations: BTreeSet<FactAnnotation>,
        terms: Vec<T>,
    ) -> Self {
        let (bloom, max_var) = fact_fingerprints(&terms);
        Fact {
            tag,
            annotations,
            terms: terms.into(),
            bloom,
            max_var,
        }
    }
    /// Recompute both cached fingerprints (`bloom` and `max_var`) from the
    /// CURRENT terms.  Call after any external `.terms` mutation (never leave a
    /// stale fingerprint).
    pub fn recompute_bloom(&mut self) {
        let (bloom, max_var) = fact_fingerprints(&self.terms);
        self.bloom = bloom;
        self.max_var = max_var;
    }
}

// =============================================================================
// HasFrees instance — visit/map over the fact's term arguments.
// =============================================================================

impl<T: HasFrees + Clone> HasFrees for Fact<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for t in self.terms.iter() {
            t.for_each_free(f);
        }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        // Freshen / rule-rename producer: this renames vars, so
        // the rebuilt fact's frees ≠ the source frees.  RECOMPUTE both
        // fingerprints from the renamed terms — NEVER copy `self`'s (would
        // fingerprint the old var names → possible wrong skip / stale max).
        let terms: Vec<T> = self
            .terms
            .iter()
            .map(|t| t.clone().map_free_with(f, monotone))
            .collect();
        let (bloom, max_var) = fact_fingerprints(&terms);
        Fact {
            tag: self.tag,
            annotations: self.annotations,
            terms: terms.into(),
            bloom,
            max_var,
        }
    }
}

// =============================================================================
// Tag queries
// =============================================================================

pub fn fact_tag_name(t: &FactTag) -> String {
    match t {
        FactTag::Proto(_, n, _) => n.to_string(),
        FactTag::Fresh => "Fr".into(),
        FactTag::Out => "Out".into(),
        FactTag::In => "In".into(),
        FactTag::Ku => "KU".into(),
        FactTag::Kd => "KD".into(),
        FactTag::Ded => "Ded".into(),
        FactTag::Term => "Term".into(),
    }
}

/// `showFactTag` (Theory/Model/Fact.hs:547-554): `factTagName` prefixed with `!` for
/// persistent facts.
pub fn show_fact_tag(t: &FactTag) -> String {
    let prefix = if fact_tag_multiplicity(t) == Multiplicity::Persistent {
        "!"
    } else {
        ""
    };
    format!("{}{}", prefix, fact_tag_name(t))
}

pub fn fact_tag_arity(t: &FactTag) -> usize {
    match t {
        FactTag::Proto(_, _, n) => *n,
        // Every built-in tag carries exactly one term.
        FactTag::Fresh
        | FactTag::Out
        | FactTag::In
        | FactTag::Ku
        | FactTag::Kd
        | FactTag::Ded
        | FactTag::Term => 1,
    }
}

pub fn fact_tag_multiplicity(t: &FactTag) -> Multiplicity {
    // Mirror Haskell's `factTagMultiplicity` (Theory/Model/Fact.hs:383-388):
    //
    //   factTagMultiplicity tag = case tag of
    //       ProtoFact multi _ _ -> multi
    //       KUFact              -> Persistent
    //       KDFact              -> Persistent
    //       _                   -> Linear
    //
    // KU/KD are Persistent because adversary knowledge is inherently
    // reusable.
    match t {
        FactTag::Proto(m, _, _) => *m,
        FactTag::Ku | FactTag::Kd => Multiplicity::Persistent,
        _ => Multiplicity::Linear,
    }
}

// =============================================================================
// Predicates on Fact<T>
// =============================================================================

impl<T> Fact<T> {
    pub fn is_linear(&self) -> bool {
        fact_tag_multiplicity(&self.tag) == Multiplicity::Linear
    }
    pub fn is_persistent(&self) -> bool {
        fact_tag_multiplicity(&self.tag) == Multiplicity::Persistent
    }
    // Used by the graph's protocol-edge classification
    // (`constraint::system::json`).
    pub fn is_proto(&self) -> bool {
        matches!(self.tag, FactTag::Proto(_, _, _))
    }
    pub fn is_k_fact(&self) -> bool {
        matches!(self.tag, FactTag::Ku | FactTag::Kd)
    }
    pub fn is_ku(&self) -> bool {
        self.tag == FactTag::Ku
    }
    pub fn is_kd(&self) -> bool {
        self.tag == FactTag::Kd
    }
    /// Mirrors Haskell `Theory.Model.Fact.isNoSourcesFact`
    /// (Theory/Model/Fact.hs:434-436): returns true iff this fact has the
    /// `NoSources` annotation (set via `[no_sources]` on a fact).
    /// Used by `safeGoal` to exclude premise solving during
    /// saturate-time `solveAllSafeGoals`.
    pub fn is_no_sources(&self) -> bool {
        self.annotations.contains(&FactAnnotation::NoSources)
    }
}

/// Mirrors Haskell `Theory.Model.Fact.isKDXorFact` (Theory/Model/Fact.hs:262-265):
/// returns true iff this is a KD-tagged fact whose single term is
/// `xor`-headed.  Used by `safeGoal` and `isKDPrem` to exclude
/// Xor-KD goals from saturate-time solving — Xor-KD goals are
/// re-inserted directly by `insertAction` (Sources.hs:158-159).
pub fn is_kd_xor_fact(fa: &LNFact) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    if fa.tag != FactTag::Kd || fa.terms.len() != 1 {
        return false;
    }
    matches!(&fa.terms[0], Term::App(FunSym::Ac(AcSym::Xor), _))
}

/// The single term of a KU-fact — the shape shared by the `isTrivialKUFact`
/// family below (Theory/Model/Fact.hs:242-255).
fn ku_fact_term(fa: &LNFact) -> Option<&LNTerm> {
    match &fa.terms[..] {
        [t] if fa.tag == FactTag::Ku => Some(t),
        _ => None,
    }
}

/// Mirrors Haskell `isTrivialKUFact` (Theory/Model/Fact.hs:242-245): a KU-fact whose single
/// term is a plain message variable.
pub fn is_trivial_ku_fact(fa: &LNFact) -> bool {
    ku_fact_term(fa).is_some_and(tamarin_term::lterm::is_msg_var)
}

/// Mirrors Haskell `isNearlyTrivialKUFact` (Theory/Model/Fact.hs:247-250): a KU-fact whose
/// single term applies `sym` to message variables only.
pub fn is_nearly_trivial_ku_fact(
    sym: &tamarin_term::function_symbols::FunSym,
    fa: &LNFact,
) -> bool {
    ku_fact_term(fa).is_some_and(|t| tamarin_term::lterm::is_trivial_fun_sym_term(t, sym))
}

// =============================================================================
// Construction helpers (NFact / LNFact specialised)
// =============================================================================

pub type LNFact = Fact<LNTerm>;

/// HS `instance Apply s t => Apply s (Fact t)` (Theory/Model/Fact.hs:196-197,
/// `apply subst = fmap (apply subst)`): a free substitution applied to every
/// term of a fact, tag and annotations kept.
pub(crate) fn apply_subst_fact(
    sigma: &tamarin_term::subst::Subst<tamarin_term::lterm::Name, LVar>,
    f: &LNFact,
) -> LNFact {
    let terms: Vec<LNTerm> = f
        .terms
        .iter()
        .map(|t| tamarin_term::subst::apply_vterm(sigma, t.clone()))
        .collect();
    Fact::fresh_annotated(f.tag, f.annotations.clone(), terms)
}

// LNFact producers: route through the bloom-COMPUTING
// `Fact::fresh` so the dominant node/action-fact skip fires.
pub fn fresh_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Fresh, vec![t])
}
pub fn out_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Out, vec![t])
}
pub fn in_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::In, vec![t])
}
pub fn ku_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Ku, vec![t])
}
pub fn kd_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Kd, vec![t])
}

/// `kLogFact` from Haskell's `Theory/Model/Fact.hs:301-303`:
///   `kLogFact = protoFact Linear "K" . return`
///
/// ISend's action — the trace event "the intruder knows m".  A
/// regular ProtoFact tagged with name "K", not `FactTag::Ded`.
/// User formulas writing `K(t) @ j` parse into atoms with the
/// same tag (per the parser's fall-through for unknown fact
/// names), so action goals like `K(t) @ j` match ISend instances.
pub fn k_log_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Proto(Multiplicity::Linear, "K", 1), vec![t])
}

pub fn proto_fact(mult: Multiplicity, name: &str, terms: Vec<LNTerm>) -> LNFact {
    Fact::fresh(
        FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()),
        terms,
    )
}

/// View a protocol or `In` fact's terms. Port of HS `protoOrInFactView`
/// (Theory/Model/Fact.hs:358-364): a `ProtoFact` yields its terms; an `In` fact (arity 1)
/// yields its single term; anything else is `None`. A malformed `In` fact
/// (arity ≠ 1) panics, mirroring HS `errMalformed`.
pub fn proto_or_in_fact_view(fa: &LNFact) -> Option<Vec<LNTerm>> {
    match &fa.tag {
        FactTag::Proto(..) => Some(fa.terms.to_vec()),
        FactTag::In => match &fa.terms[..] {
            [m] => Some(vec![m.clone()]),
            _ => panic!("proto_or_in_fact_view: malformed In fact"),
        },
        _ => None,
    }
}

/// View a protocol or `Out` fact's terms. Port of HS `protoOrOutFactView`
/// (Theory/Model/Fact.hs:366-372).
pub fn proto_or_out_fact_view(fa: &LNFact) -> Option<Vec<LNTerm>> {
    match &fa.tag {
        FactTag::Proto(..) => Some(fa.terms.to_vec()),
        FactTag::Out => match &fa.terms[..] {
            [m] => Some(vec![m.clone()]),
            _ => panic!("proto_or_out_fact_view: malformed Out fact"),
        },
        _ => None,
    }
}

/// Mirrors Haskell `freesToFresh = map (freshFact . lvarToLnterm)`
/// (Theory/Model/Fact.hs:327-329): one `Fr`-premise per variable, with nat-sorted variables
/// reinterpreted as fresh ones (see [`lvar_to_lnterm`]).
///
/// Intentionally retained: faithful mirror of HS `freesToFresh`
/// (Theory/Model/Fact.hs:327-329); no production caller yet (exercised only by the unit test
/// below).
pub fn frees_to_fresh(vs: &[LVar]) -> Vec<LNFact> {
    vs.iter().map(|v| fresh_fact(lvar_to_lnterm(v))).collect()
}

/// Mirrors Haskell `lvarToLnterm` (Theory/Model/Fact.hs:331-333): a variable as a term, with
/// `LSortNat` variables re-sorted to `LSortFresh` (so they can be bound by an
/// `Fr`-premise); every other sort is kept as is.
pub fn lvar_to_lnterm(v: &LVar) -> LNTerm {
    use tamarin_term::lterm::LSort;
    let v = if v.sort == LSort::Nat {
        LVar {
            name: v.name,
            sort: LSort::Fresh,
            idx: v.idx,
        }
    } else {
        *v
    };
    tamarin_term::vterm::var_term(v)
}

#[cfg(test)]
#[path = "fact_tests.rs"]
mod tests;
