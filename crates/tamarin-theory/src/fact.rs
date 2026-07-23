// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, rkunnema, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Model/Fact.hs

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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// Borrowing map — the HS `Functor Fact` instance (Fact.hs:171-172) for
    /// producers holding a `&Fact`.  Clones `tag`/`annotations` and stores both
    /// fingerprints as `u64::MAX`, exactly like [`Fact::new`]/[`Fact::map`]; the
    /// same recompute guidance applies if a hot LNFact producer routes here.
    pub fn map_ref<U>(&self, f: impl FnMut(&T) -> U) -> Fact<U> {
        Fact {
            tag: self.tag.clone(),
            annotations: self.annotations.clone(),
            terms: self.terms.iter().map(f).collect(),
            bloom: u64::MAX,
            max_var: u64::MAX,
        }
    }
    /// Fallible borrowing map — the HS `Traversable Fact` instance
    /// (Fact.hs:177-179) specialised to `Result`; short-circuits on the first
    /// `Err`.  Same `tag`/`annotations` clone and `u64::MAX` fingerprints as
    /// [`Fact::map_ref`].
    pub fn try_map_ref<U, E>(&self, f: impl FnMut(&T) -> Result<U, E>) -> Result<Fact<U>, E> {
        let terms: Result<Vec<U>, E> = self.terms.iter().map(f).collect();
        Ok(Fact {
            tag: self.tag.clone(),
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

/// `showFactTag` (Fact.hs:516-523): `factTagName` prefixed with `!` for
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
    // Mirror Haskell's `factTagMultiplicity` (Fact.hs:353-358):
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
    // Intentionally retained: faithful HS port; no caller yet.
    pub fn is_proto(&self) -> bool {
        matches!(self.tag, FactTag::Proto(_, _, _))
    }
    // Intentionally retained: faithful HS port; no caller yet.
    pub fn is_in_fact(&self) -> bool {
        self.tag == FactTag::In
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
    /// (Fact.hs:405-406): returns true iff this fact has the
    /// `NoSources` annotation (set via `[no_sources]` on a fact).
    /// Used by `safeGoal` to exclude premise solving during
    /// saturate-time `solveAllSafeGoals`.
    pub fn is_no_sources(&self) -> bool {
        self.annotations.contains(&FactAnnotation::NoSources)
    }
}

/// Mirrors Haskell `Theory.Model.Fact.isKDXorFact` (Fact.hs:241-243):
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

// =============================================================================
// Construction helpers (NFact / LNFact specialised)
// =============================================================================

pub type LNFact = Fact<LNTerm>;

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
// Intentionally retained: faithful HS port; no caller yet.
pub fn ded_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Ded, vec![t])
}

/// `kLogFact` from Haskell's `Theory.Model.Fact:280`:
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
pub fn term_fact(t: LNTerm) -> LNFact {
    Fact::fresh(FactTag::Term, vec![t])
}

pub fn proto_fact(mult: Multiplicity, name: &str, terms: Vec<LNTerm>) -> LNFact {
    Fact::fresh(
        FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()),
        terms,
    )
}

/// View a protocol or `In` fact's terms. Port of HS `protoOrInFactView`
/// (Fact.hs:331-336): a `ProtoFact` yields its terms; an `In` fact (arity 1)
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
/// (Fact.hs:339-344).
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

pub fn proto_fact_ann(
    mult: Multiplicity,
    name: &str,
    annotations: BTreeSet<FactAnnotation>,
    terms: Vec<LNTerm>,
) -> LNFact {
    Fact::fresh_annotated(
        FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()),
        annotations,
        terms,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::builtin::msg_var;

    #[test]
    fn proto_fact_arity() {
        let f = proto_fact(
            Multiplicity::Linear,
            "P",
            vec![msg_var("x", 0), msg_var("y", 0)],
        );
        assert_eq!(f.arity(), 2);
        assert_eq!(fact_tag_arity(&f.tag), 2);
    }

    #[test]
    fn equality_ignores_annotations() {
        let a = fresh_fact(msg_var("x", 0)).annotate(FactAnnotation::SolveFirst);
        let b = fresh_fact(msg_var("x", 0));
        assert_eq!(a, b);
    }

    #[test]
    fn linear_vs_persistent() {
        let lin = proto_fact(Multiplicity::Linear, "P", vec![]);
        let per = proto_fact(Multiplicity::Persistent, "Q", vec![]);
        assert!(lin.is_linear());
        assert!(per.is_persistent());
    }

    #[test]
    fn k_fact_categorisation() {
        assert!(ku_fact(msg_var("x", 0)).is_ku());
        assert!(kd_fact(msg_var("x", 0)).is_kd());
    }

    // =========================================================================
    // Haskell-faithfulness invariants.
    //
    // Fact.hs:128:  `data Multiplicity = Persistent | Linear`
    // Fact.hs:132:  `data FactTag = ProtoFact ... | FreshFact | OutFact |
    //                              InFact | KUFact | KDFact | DedFact |
    //                              TermFact`
    //
    // FactTag Ord matters because BTreeSet<LNFact> is used in injective-fact
    // analysis and rule-conclusion sets.  If the tag order drifts, the
    // "Proto facts come first" iteration property breaks, which downstream
    // injective-fact code assumes.
    // =========================================================================

    /// Multiplicity: `Persistent < Linear` from Fact.hs:128-129.
    #[test]
    fn multiplicity_ord_matches_haskell_declaration() {
        assert!(
            Multiplicity::Persistent < Multiplicity::Linear,
            "Persistent must sort before Linear (Fact.hs:128)"
        );
    }

    /// `FactTag` Ord — `Proto < Fresh < Out < In < Ku < Kd < Ded < Term`.
    ///
    /// Critical: Proto facts MUST sort before all built-in tags so that
    /// BTreeSet<LNFact> iteration puts protocol facts first.  Multiple
    /// downstream code paths (simpInjectiveFactEqMon, partial_atom_valuation
    /// nonUnifiableNodes) iterate fact sets and depend on Proto-first order
    /// for deterministic case ranking.
    #[test]
    fn fact_tag_ord_proto_sorts_before_builtins() {
        let proto = FactTag::Proto(Multiplicity::Linear, "Foo", 0);
        let fresh = FactTag::Fresh;
        assert!(
            proto < fresh,
            "Proto must sort before Fresh (Haskell decl order Fact.hs:132)"
        );
        assert!(fresh < FactTag::Out);
        assert!(FactTag::Out < FactTag::In);
        assert!(FactTag::In < FactTag::Ku);
        assert!(FactTag::Ku < FactTag::Kd);
        assert!(FactTag::Kd < FactTag::Ded);
        assert!(FactTag::Ded < FactTag::Term);
    }

    /// `Proto` facts compare by `(multiplicity, name, arity)` triple.
    /// Specifically: Linear and Persistent same-named facts compare via
    /// Multiplicity first, then name, then arity.  If we drift, lemmas
    /// using both `!P(x)` (persistent) and `P(x)` (linear) versions get
    /// inconsistently bucketed.
    #[test]
    fn proto_fact_tag_compare_by_multiplicity_then_name_then_arity() {
        let lp = FactTag::Proto(Multiplicity::Linear, "P", 1);
        let pp = FactTag::Proto(Multiplicity::Persistent, "P", 1);
        // Persistent < Linear (per Haskell Multiplicity Ord).
        assert!(pp < lp);

        // Same multiplicity, different name → name breaks tie.
        let la = FactTag::Proto(Multiplicity::Linear, "A", 1);
        assert!(la < lp);

        // Same multiplicity+name, different arity → arity breaks tie.
        let lp2 = FactTag::Proto(Multiplicity::Linear, "P", 2);
        assert!(lp < lp2);
    }

    /// `ku` and `kd` predicates are mutually exclusive.
    /// Used in `enforce_kd_fact_uniqueness` to skip KU facts.
    #[test]
    fn ku_and_kd_are_mutually_exclusive() {
        let ku = ku_fact(msg_var("x", 0));
        let kd = kd_fact(msg_var("x", 0));
        assert!(ku.is_ku() && !ku.is_kd());
        assert!(kd.is_kd() && !kd.is_ku());
    }

    // =========================================================================
    // Cached-bloom fingerprint skip: soundness invariants.
    // =========================================================================

    use tamarin_term::builtin::{fresh_var, msg_var as mv, pair, pub_var};
    use tamarin_term::lterm::{LNTerm, LSort, LVar};
    use tamarin_term::subst::{apply_vterm_changed, Subst};

    /// Tiny deterministic PRNG (no external quickcheck dep) for the property
    /// tests below.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn range(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Build a pseudo-random `LNTerm` of bounded depth over a small var pool.
    fn rand_term(r: &mut Lcg, depth: u32) -> LNTerm {
        if depth == 0 || r.range(3) == 0 {
            let i = r.range(6);
            match r.range(3) {
                0 => mv(&format!("x{i}"), r.range(4)),
                1 => fresh_var(&format!("n{i}"), r.range(4)),
                _ => pub_var(&format!("p{i}"), r.range(4)),
            }
        } else {
            pair(rand_term(r, depth - 1), rand_term(r, depth - 1))
        }
    }

    fn rand_fact(r: &mut Lcg) -> LNFact {
        let arity = 1 + r.range(4) as usize;
        let terms: Vec<LNTerm> = (0..arity).map(|_| rand_term(r, 3)).collect();
        let tag = match r.range(4) {
            0 => FactTag::Out,
            1 => FactTag::Ku,
            2 => FactTag::Proto(Multiplicity::Linear, "P", arity),
            _ => FactTag::Proto(Multiplicity::Persistent, "Q", arity),
        };
        Fact::fresh(tag, terms)
    }

    /// Superset property: every var visited by `for_each_free` has its bit
    /// set in `fact.bloom()` (`bloom ⊇ frees`), and structurally-equal facts
    /// get equal blooms (deterministic function of content).
    #[test]
    fn bloom_is_superset_of_frees_and_content_deterministic() {
        let mut r = Lcg(0x1234_5678);
        for _ in 0..2000 {
            let fa = rand_fact(&mut r);
            let b = fa.bloom();
            fa.for_each_free(&mut |v| {
                assert_ne!(
                    b & var_bit(v),
                    0,
                    "bloom missing a bit for free var {v:?} — superset invariant broken"
                );
            });
            // Recomputing from the same terms is identical (content-deterministic).
            let b2 = fact_fingerprints(&fa.terms).0;
            assert_eq!(b, b2);
            // A structurally-equal rebuild gets an equal bloom.
            let fa2 = Fact::fresh(fa.tag.clone(), fa.terms.to_vec());
            assert_eq!(fa.bloom(), fa2.bloom());
        }
    }

    /// Skip-equivalence property: `bloom(fact) & dom_bloom == 0` implies
    /// the subst changes NO term of the fact (the skip never fires on a fact
    /// the subst actually rewrites).
    #[test]
    fn bloom_miss_implies_no_change() {
        let mut r = Lcg(0xDEAD_BEEF);
        let mut fired = 0u64;
        for _ in 0..4000 {
            let fa = rand_fact(&mut r);
            // Random subst: map a handful of vars to random terms (dropping
            // trivial bindings via `from_list`, as the real eq-store does).
            let ndom = 1 + r.range(4);
            let pairs: Vec<(LVar, LNTerm)> = (0..ndom)
                .map(|_| {
                    let i = r.range(6);
                    let v = LVar::new(format!("x{i}"), LSort::Msg, r.range(4));
                    (v, rand_term(&mut r, 2))
                })
                .collect();
            let subst: Subst<_, _> = Subst::from_list(pairs);
            if subst.is_empty() {
                continue;
            }
            let dom_bloom = subst.dom().fold(0u64, |b, v| b | var_bit(v));
            if fa.bloom() & dom_bloom == 0 {
                fired += 1;
                for t in fa.terms.iter() {
                    assert!(
                        apply_vterm_changed(&subst, t).is_none(),
                        "skip fired but subst changed a term — UNSOUND: fact={fa:?}"
                    );
                }
            }
        }
        assert!(
            fired > 0,
            "test never exercised a real skip — weaken the generator"
        );
    }

    /// Trait regression: two facts equal-but-for-fingerprints compare `==`
    /// and `Ord`-equal.  Pins that the manual `Eq`/`Ord` stay blind to BOTH
    /// out-of-band caches (`bloom` and `max_var`; no `Hash` derive added).
    #[test]
    fn fingerprints_are_invisible_to_eq_and_ord() {
        let mut a = Fact::fresh(FactTag::Out, vec![mv("x", 0)]);
        let mut b = a.clone();
        a.bloom = 0; // deliberately divergent fingerprints
        b.bloom = u64::MAX;
        a.max_var = 0;
        b.max_var = u64::MAX;
        assert_eq!(a, b, "Eq must ignore the bloom/max_var fields");
        assert_eq!(
            a.cmp(&b),
            std::cmp::Ordering::Equal,
            "Ord must ignore the bloom/max_var fields"
        );
        assert!(a.partial_cmp(&b) == Some(std::cmp::Ordering::Equal));
    }

    /// `var_bit` determinism: two INDEPENDENTLY-constructed content-equal
    /// `LVar`s hash to the same bit (guards against a future ptr-hash
    /// "optimisation" of `LVar::Hash` that would break the superset invariant).
    #[test]
    fn var_bit_is_content_deterministic() {
        let a = LVar::new(String::from("foo"), LSort::Msg, 7);
        let b = LVar::new(format!("f{}{}", "o", "o"), LSort::Msg, 7);
        assert_eq!(a, b);
        assert_eq!(
            var_bit(&a),
            var_bit(&b),
            "content-equal LVars must yield the same bloom bit"
        );
        assert_eq!(
            tamarin_utils::fx_hash_one(&a),
            tamarin_utils::fx_hash_one(&b)
        );
    }

    // =========================================================================
    // Per-fact cached max-var-idx: soundness invariants (the `bm_fact`
    // fast-path in reduction.rs).
    // =========================================================================

    /// Manual `bm_term`-style max-idx fold, replicated here so the property
    /// test below is independent of reduction.rs's (private) walker.
    fn term_max_idx(t: &LNTerm, max: &mut u64) {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => {
                if v.idx > *max {
                    *max = v.idx;
                }
            }
            Term::Lit(Lit::Con(_)) => {}
            Term::App(_, args) => {
                for a in args.iter() {
                    term_max_idx(a, max);
                }
            }
        }
    }

    /// A fact with no free vars caches `0` (folding it is the same no-op the
    /// per-term walk performs on a no-free fact).
    #[test]
    fn max_var_no_free_caches_zero() {
        let fa = proto_fact(Multiplicity::Linear, "P", vec![]);
        assert_eq!(fa.max_var_cached(), Some(0));
    }

    /// A fact whose largest free-var index is `k` caches exactly `k` (never an
    /// over-approximation — `bounds_max` reads this as an exact max).
    #[test]
    fn max_var_caches_the_exact_largest_index() {
        let fa = Fact::fresh(FactTag::Out, vec![mv("x", 7)]);
        assert_eq!(fa.max_var_cached(), Some(7));
        // Multiple vars: the maximum wins, order-independently.
        let fa2 = proto_fact(
            Multiplicity::Linear,
            "P",
            vec![mv("a", 3), fresh_var("n", 9), pub_var("p", 5)],
        );
        assert_eq!(fa2.max_var_cached(), Some(9));
    }

    /// The no-`HasFrees` constructors store the `u64::MAX` sentinel, so
    /// `max_var_cached()` is `None` — `bm_fact` falls back to the per-term walk.
    #[test]
    fn max_var_new_and_map_are_sentinel() {
        let new_fa: LNFact = Fact::new(FactTag::Out, vec![mv("x", 7)]);
        assert_eq!(new_fa.max_var_cached(), None);
        // `map` drops the cache to the sentinel even from a computed source.
        let mapped: LNFact = Fact::fresh(FactTag::Out, vec![mv("x", 7)]).map(|t| t);
        assert_eq!(mapped.max_var_cached(), None);
    }

    /// `recompute_bloom` refreshes BOTH fingerprints from the current terms.
    #[test]
    fn recompute_bloom_refreshes_both_fingerprints() {
        let mut fa = Fact::fresh(FactTag::Out, vec![mv("x", 2)]);
        assert_eq!(fa.max_var_cached(), Some(2));
        fa.terms = vec![mv("y", 11), mv("z", 4)].into();
        fa.recompute_bloom();
        assert_eq!(fa.max_var_cached(), Some(11));
        assert_eq!(fa.bloom(), fact_fingerprints(&fa.terms).0);
    }

    /// A `map_free_with` rebuild recomputes the max over the RENAMED terms
    /// (never copies the stale source max).
    #[test]
    fn map_free_with_recomputes_the_max() {
        let fa = Fact::fresh(FactTag::Out, vec![mv("x", 3)]);
        let shifted = fa.map_free_with(
            &mut |mut v| {
                v.idx += 10;
                v
            },
            false,
        );
        assert_eq!(shifted.max_var_cached(), Some(13));
    }

    /// Parity property: the cached max equals a fresh `bm_term`-style fold over
    /// the same terms, bit-for-bit — the invariant the `bm_fact` fast-path
    /// rests on (a cached max that drifts from the walk would change every
    /// `bounds_max` fresh-index seed).
    #[test]
    fn max_var_equals_the_manual_walk() {
        let mut r = Lcg(0x0BAD_F00D);
        for _ in 0..2000 {
            let fa = rand_fact(&mut r);
            let mut walked = 0u64;
            for t in fa.terms.iter() {
                term_max_idx(t, &mut walked);
            }
            assert_eq!(
                fa.max_var_cached(),
                Some(walked),
                "cached max must equal the per-term walk — fact={fa:?}"
            );
        }
    }
}
