// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Model.Fact` from `lib/theory/src/Theory/Model/Fact.hs`.
//!
//! Multiset-rewriting facts. This port covers the data type plus the
//! tagging / construction / query API. The Maude-backed `unifyLNFactEqs`
//! and `unifiableLNFacts` entry points live in `rule.rs` and call the
//! live Maude unification bridge (`maude.unify`).

use std::collections::BTreeSet;
use std::sync::Arc;

use tamarin_term::apply::{Apply, LeafSubst};
use tamarin_term::lterm::{BVar, HasFrees, LNTerm, LVar, Name};
use tamarin_term::macro_expand::LNMacro;
use tamarin_term::subst::Subst;
pub use tamarin_term::tags::FactAnnotation;
use tamarin_term::term::show_term;
use tamarin_term::vterm::VTerm;

use tamarin_utils::cow::cow_map_vec;

use crate::apply::SystemSubst;
use crate::pretty_hpj::{fsep, nest_short_doc, punctuate, Doc};

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

/// A variable's fingerprint bit.  Fact blooms and the substitution-domain
/// bloom must both use it: the bloom skip is sound only while a fact's bloom
/// covers the bits of its free variables.  `LVar`'s hash is content-based and
/// unseeded, so the bit is stable.
#[inline]
pub fn var_bit(v: &LVar) -> u64 {
    1u64 << (tamarin_utils::fx_hash_one(v) & 63)
}

/// Both fact caches over `terms` from one walk: the bloom of the free
/// variables' [`var_bit`]s (`.0`) and the exact maximum free-variable index
/// (`.1`, `0` when there is none), which `bm_fact` (reduction.rs) seeds fresh
/// indices from.
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
    terms: Arc<[T]>,
    /// Cached bloom of the terms' free variables, or `u64::MAX` for unknown.
    bloom: u64,
    /// Cached exact maximum free-variable index of the terms (`0` with none),
    /// or `u64::MAX` for unknown.  It must be exact, not a bound: fresh
    /// variables are drawn above it.  Set together with `bloom`.
    max_var: u64,
}

// Equality, ordering and hashing read only `tag` and `terms`, through
// `cmp_key`: HS ignores annotations in `Eq`/`Ord LNFact` (Theory/Model/Fact.hs)
// and the caches are not part of the value.  `Hash` must read what
// `PartialEq` reads, since the implied-formula dedup compares hashes first.
impl<T> Fact<T> {
    /// The fields the comparison impls read, in comparison order.  Destructured
    /// without `..` so a new `Fact` field forces an inclusion decision here.
    fn cmp_key(&self) -> (&FactTag, &Arc<[T]>) {
        let Fact {
            tag,
            terms,
            annotations: _,
            bloom: _,
            max_var: _,
        } = self;
        (tag, terms)
    }
}

impl<T: PartialEq> PartialEq for Fact<T> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp_key() == other.cmp_key()
    }
}
impl<T: Eq> Eq for Fact<T> {}
impl<T: PartialOrd> PartialOrd for Fact<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.cmp_key().partial_cmp(&other.cmp_key())
    }
}
impl<T: Ord> Ord for Fact<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cmp_key().cmp(&other.cmp_key())
    }
}
impl<T: std::hash::Hash> std::hash::Hash for Fact<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.cmp_key().hash(state);
    }
}

impl<T> Fact<T> {
    /// A fact with unknown caches, which the bloom skip never skips; prefer
    /// [`Fact::fresh`] where the terms have free variables.
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
    /// The fact over other terms, tag and annotations kept; both caches
    /// become unknown.
    pub fn with_terms(&self, terms: Arc<[T]>) -> Fact<T> {
        Fact {
            tag: self.tag,
            annotations: self.annotations.clone(),
            terms,
            bloom: u64::MAX,
            max_var: u64::MAX,
        }
    }
    pub fn annotate(mut self, a: FactAnnotation) -> Self {
        self.annotations.insert(a);
        self
    }
    pub fn terms(&self) -> &[T] {
        &self.terms
    }
    pub fn arity(&self) -> usize {
        self.terms.len()
    }
    /// The cached bloom; `u64::MAX` when unknown.
    #[inline]
    pub fn bloom(&self) -> u64 {
        self.bloom
    }
    /// The cached maximum free-variable index, `None` when unknown.
    #[inline]
    pub fn max_var_cached(&self) -> Option<u64> {
        if self.max_var == u64::MAX {
            None
        } else {
            Some(self.max_var)
        }
    }
    /// Map the terms; both caches become unknown.
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
    /// HS `Functor Fact` (Theory/Model/Fact.hs) over a borrowed fact; both
    /// caches become unknown.
    pub fn map_ref<U>(&self, f: impl FnMut(&T) -> U) -> Fact<U> {
        Fact {
            tag: self.tag,
            annotations: self.annotations.clone(),
            terms: self.terms.iter().map(f).collect(),
            bloom: u64::MAX,
            max_var: u64::MAX,
        }
    }
    /// HS `Traversable Fact` (Theory/Model/Fact.hs) at `Result`; both caches
    /// become unknown.
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
    /// Constructor that computes both caches, so the bloom skip can fire on
    /// the fact.
    pub fn fresh(tag: FactTag, terms: Vec<T>) -> Self {
        Self::fresh_annotated(tag, BTreeSet::new(), terms)
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
        // Renaming changes the free variables, so recompute both caches.
        let terms: Vec<T> = self
            .terms
            .iter()
            .map(|t| t.clone().map_free_with(f, monotone))
            .collect();
        Self::fresh_annotated(self.tag, self.annotations, terms)
    }
}

/// A free substitution the fact and rule [`Apply`] instances accept: its
/// leaves, plus whether a fact may be returned unchanged without walking its
/// terms.  Only the whole-system pass ([`SystemSubst`]) has such a fast path.
pub trait FactSubst: LeafSubst<Const = Name, Var = LVar> {
    fn skips_fact(&self, _fa: &LNFact) -> bool {
        false
    }
}

impl FactSubst for Subst<Name, LVar> {}

impl FactSubst for SystemSubst<'_> {
    fn skips_fact(&self, fa: &LNFact) -> bool {
        SystemSubst::skips_fact(self, fa)
    }
}

/// HS `Apply s t => Apply s (Fact t)` (Theory/Model/Fact.hs): the
/// substitution reaches the fact's terms.  A rewritten fact goes through the
/// computing constructor, which derives both cached fingerprints from the
/// rewritten terms: their free variables differ from this fact's, so this
/// fact's fingerprints do not describe them.
impl<S: FactSubst> Apply<S> for LNFact {
    fn apply_changed(&self, subst: &S) -> Option<Self> {
        if subst.skips_fact(self) {
            return None;
        }
        let terms = cow_map_vec(&self.terms[..], |t| t.apply_changed(subst))?;
        Some(Fact::fresh_annotated(
            self.tag,
            self.annotations.clone(),
            terms,
        ))
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

/// `showFactTag` (Theory/Model/Fact.hs): `factTagName` prefixed with `!` for
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
    // Mirror Haskell's `factTagMultiplicity` (Theory/Model/Fact.hs):
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
    /// (Theory/Model/Fact.hs): returns true iff this fact has the
    /// `NoSources` annotation (set via `[no_sources]` on a fact).
    /// Used by `safeGoal` to exclude premise solving during
    /// saturate-time `solveAllSafeGoals`.
    pub fn is_no_sources(&self) -> bool {
        self.annotations.contains(&FactAnnotation::NoSources)
    }
}

/// HS `isProtoFact` (Theory/Model/Fact.hs): a fact tagged
/// `ProtoFact`, i.e. one of the theory's own facts rather than a special
/// tag.
pub fn is_proto_fact<T>(f: &Fact<T>) -> bool {
    matches!(f.tag, FactTag::Proto(..))
}

/// HS `isKLogFact` (Theory/Model/Fact.hs): the protocol fact named
/// `K`, which the intruder rule `isend` emits as an action
/// ([`k_log_fact`]).  Its tag is a `ProtoFact`, so [`is_proto_fact`] holds of
/// it too.
pub fn is_k_log_fact<T>(f: &Fact<T>) -> bool {
    is_proto_fact(f) && fact_tag_name(&f.tag) == "K"
}

/// Mirrors Haskell `Theory.Model.Fact.isKDXorFact` (Theory/Model/Fact.hs):
/// returns true iff this is a KD-tagged fact whose single term is
/// `xor`-headed.  Used by `safeGoal` and `isKDPrem` to exclude
/// Xor-KD goals from saturate-time solving — Xor-KD goals are
/// re-inserted directly by `insertAction` (Sources.hs).
pub fn is_kd_xor_fact(fa: &LNFact) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    if fa.tag != FactTag::Kd || fa.terms.len() != 1 {
        return false;
    }
    matches!(&fa.terms[0], Term::App(FunSym::Ac(AcSym::Xor), _))
}

/// The single term of a KU-fact — the shape shared by the `isTrivialKUFact`
/// family below (Theory/Model/Fact.hs).
fn ku_fact_term(fa: &LNFact) -> Option<&LNTerm> {
    match &fa.terms[..] {
        [t] if fa.tag == FactTag::Ku => Some(t),
        _ => None,
    }
}

/// Mirrors Haskell `isTrivialKUFact` (Theory/Model/Fact.hs): a KU-fact whose single
/// term is a plain message variable.
pub fn is_trivial_ku_fact(fa: &LNFact) -> bool {
    ku_fact_term(fa).is_some_and(tamarin_term::lterm::is_msg_var)
}

/// Mirrors Haskell `isNearlyTrivialKUFact` (Theory/Model/Fact.hs): a KU-fact whose
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

/// HS `applyMacroInFact` (Theory/Model/Fact.hs): the theory's macros
/// applied to every term of a fact, tag and annotations kept.
pub fn apply_macro_in_fact(macros: &[LNMacro], f: &LNFact) -> LNFact {
    let terms: Vec<LNTerm> = f
        .terms
        .iter()
        .map(|t| tamarin_term::macro_expand::apply_macros(macros, t.clone()))
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

/// `kLogFact` from Haskell's `Theory/Model/Fact.hs`:
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

/// HS `newVariables` (Theory/Model/Fact.hs): the variables of `concs`
/// not free in `prems`, as `varTerm`s in `S.toList` (sorted `LVar`) order.
/// Call sites compose the second argument as HS does: the rule elaboration
/// and `apply_macro_in_rule` pass `cs ++ as`
/// (Theory/Text/Parser/Rule.hs, Theory/Model/Rule.hs); the
/// intruder-variant and SAPIC rule builders pass the conclusions alone
/// (Theory/Text/Parser/Rule.hs, Sapic/Facts.hs).
pub fn new_variables(prems: &[LNFact], concs: &[LNFact]) -> Vec<LNTerm> {
    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        f.for_each_free(&mut |v| {
            prem_vars.insert(*v);
        });
    }
    let mut conc_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in concs {
        f.for_each_free(&mut |v| {
            conc_vars.insert(*v);
        });
    }
    conc_vars
        .difference(&prem_vars)
        .map(|v| tamarin_term::vterm::var_term(*v))
        .collect()
}

/// View a protocol or `In` fact's terms. Port of HS `protoOrInFactView`
/// (Theory/Model/Fact.hs): a `ProtoFact` yields its terms; an `In` fact (arity 1)
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
/// (Theory/Model/Fact.hs).
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

/// The variable HS `lvarToLnterm` (Theory/Model/Fact.hs) builds its term
/// from: an `LSortNat` variable re-sorted to `LSortFresh` (so an
/// `Fr`-premise can bind it), any other variable as is.
pub fn nat_to_fresh_var(v: LVar) -> LVar {
    if v.sort == tamarin_term::lterm::LSort::Nat {
        LVar {
            sort: tamarin_term::lterm::LSort::Fresh,
            ..v
        }
    } else {
        v
    }
}

/// HS `lvarToLnterm` (Theory/Model/Fact.hs).
pub fn lvar_to_lnterm(v: &LVar) -> LNTerm {
    tamarin_term::vterm::var_term(nat_to_fresh_var(*v))
}

// =============================================================================
// Pretty printing
// =============================================================================

/// HS `showFactAnnotation` (Theory/Model/Fact.hs).
pub(crate) fn show_fact_annotation(a: FactAnnotation) -> &'static str {
    match a {
        FactAnnotation::SolveFirst => "+",
        FactAnnotation::SolveLast => "-",
        FactAnnotation::NoSources => "no_precomp",
    }
}

/// HS's DERIVED `Show FactTag` (Theory/Model/Fact.hs) — the
/// constructor spelling [`pretty_fact`] puts after `MALFORMED-`
/// (Theory/Model/Fact.hs), which is a different string from
/// [`show_fact_tag`].  For `ProtoFact m n a` this is
/// `ProtoFact <show m> <show n> <a>`, the name through the `Show String`
/// instance ([`tamarin_parser::parser::show_lit_string`]).  Also the string
/// the `isFactName` tactic compares an action goal's tag against.
pub(crate) fn show_fact_tag_derived(t: &FactTag) -> String {
    match t {
        FactTag::Proto(m, n, arity) => {
            let mult = match m {
                Multiplicity::Persistent => "Persistent",
                Multiplicity::Linear => "Linear",
            };
            format!(
                "ProtoFact {mult} {} {arity}",
                tamarin_parser::parser::show_lit_string(n)
            )
        }
        FactTag::Fresh => "FreshFact".to_string(),
        FactTag::Out => "OutFact".to_string(),
        FactTag::In => "InFact".to_string(),
        FactTag::Ku => "KUFact".to_string(),
        FactTag::Kd => "KDFact".to_string(),
        FactTag::Ded => "DedFact".to_string(),
        FactTag::Term => "TermFact".to_string(),
    }
}

/// HS's DERIVED `Show FactAnnotation` (Theory/Model/Fact.hs) — the
/// constructor spelling, which is a different string from the concrete
/// syntax [`show_fact_annotation`] writes.
fn show_fact_annotation_derived(a: FactAnnotation) -> &'static str {
    match a {
        FactAnnotation::SolveFirst => "SolveFirst",
        FactAnnotation::SolveLast => "SolveLast",
        FactAnnotation::NoSources => "NoSources",
    }
}

/// HS's DERIVED `Show (Fact t)` (Theory/Model/Fact.hs) at
/// `t = VTerm Name (BVar LVar)`, the fact type a formula's `Action` atom
/// carries.  Record syntax, each field at precedence 0: the tag through
/// [`show_fact_tag_derived`], the annotation set as `fromList ` before the
/// derived list `show` of its elements in `Ord` order (`Show (Set a)`,
/// containers `Data.Set.Internal`), and the terms through
/// [`tamarin_term::term::show_term`].  Both lists separate their elements
/// with a bare comma, as Haskell's `showList__` does.
pub fn show_bl_fact(fa: &Fact<VTerm<Name, BVar<LVar>>>) -> String {
    let ann: Vec<&str> = fa
        .annotations
        .iter()
        .map(|a| show_fact_annotation_derived(*a))
        .collect();
    let terms: Vec<String> = fa.terms.iter().map(show_term).collect();
    format!(
        "Fact {{factTag = {}, factAnnotations = fromList [{}], factTerms = [{}]}}",
        show_fact_tag_derived(&fa.tag),
        ann.join(","),
        terms.join(","),
    )
}

/// HS `ppFact n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $
/// map ppTerm t` (Theory/Model/Fact.hs), with `nestShort' lead finish =
/// nestShort (length lead + 1) (text lead) (text finish)` and `nestShort n
/// lead finish body = sep [lead $$ nest n body, finish]`
/// (Text/PrettyPrint/Class.hs).
fn pp_fact<T>(pp_term: &dyn Fn(&T) -> Doc, n: &str, ts: &[T]) -> Doc {
    let args: Vec<Doc> = ts.iter().map(pp_term).collect();
    nest_short_doc(&format!("{n}("), ")", fsep(punctuate(Doc::char(','), args)))
}

/// HS `ppAnn ann` (Theory/Model/Fact.hs): the empty set prints as
/// `emptyDoc`, any other as `brackets . fsep . punctuate comma` over
/// `S.toList`.  `S.toList` yields `FactAnnotation`'s `Ord` order, which is
/// the order a `BTreeSet` iterates in.
fn pp_ann(ann: &BTreeSet<FactAnnotation>) -> Doc {
    if ann.is_empty() {
        return Doc::Empty;
    }
    let items: Vec<Doc> = ann
        .iter()
        .map(|a| Doc::text(show_fact_annotation(*a)))
        .collect();
    // HS `brackets p = char '[' <> p <> char ']'`
    // (Text/PrettyPrint/Class.hs).
    Doc::char('[')
        .beside(fsep(punctuate(Doc::char(','), items)))
        .beside(Doc::char(']'))
}

/// HS `prettyFact ppTerm (Fact tag an ts)` (Theory/Model/Fact.hs):
/// the tag, the arguments in parentheses and the annotation suffix.  A tag
/// whose arity disagrees with the argument count prints its head as
/// `MALFORMED-` followed by HS's derived `show tag`
/// (Theory/Model/Fact.hs).
pub fn pretty_fact<T>(pp_term: &dyn Fn(&T) -> Doc, fa: &Fact<T>) -> Doc {
    let head = if fact_tag_arity(&fa.tag) == fa.terms.len() {
        show_fact_tag(&fa.tag)
    } else {
        format!("MALFORMED-{}", show_fact_tag_derived(&fa.tag))
    };
    pp_fact(pp_term, &head, &fa.terms).beside(pp_ann(&fa.annotations))
}

/// HS `prettyLNFact = prettyFact prettyNTerm` (Theory/Model/Fact.hs).
pub fn pretty_lnfact(fa: &LNFact) -> Doc {
    pretty_fact(&|t: &LNTerm| tamarin_term::pretty::pretty_nterm(t), fa)
}

#[cfg(test)]
#[path = "fact_tests.rs"]
mod tests;
