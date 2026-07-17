// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Benedikt Schmidt, Jannik Dreier, Ralf Sasse, Philip Lukert,
//   "Nynko" (github), Charlie Jacomme, Felix Linker, "Tom" (github BTom-GH),
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Unification.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs

//! Port of `Term.LTerm` data types from `lib/term/src/Term/LTerm.hs`:
//! sorts, names, logical variables, simple predicates and convertors,
//! the `BVar`/`BLVar`/`BLTerm` bound-variable wrappers, the `HasFrees`
//! trait with `frees`/`occurs`/`bounds_var_idx`/`avoid`/`rename`, and
//! `nat_to_fresh_vars`.
//!
//! The `MonotoneFunction` split (AC-preserving vs. arbitrary updates) is
//! ported as a `monotone: bool` flag rather than an enum: see
//! `HasFrees::map_free` (`Arbitrary`) and `map_free_monotone` (`Monotone`).
//!
//! Pretty-printing (`Show LVar` / `Display LNTerm`) is ported in `pretty.rs`.
//!
//! (`varOccurences`, `eqModuloFreshnessNoAC`, `someInst`/`renamePrecise`,
//! and `freshToFreeAvoiding` are ported elsewhere — see `subsumption.rs`,
//! `sources.rs`, `constraint::solver::rename_precise`, and `subst_vfresh.rs`.)

use std::cmp::Ordering;

use crate::function_symbols::{AcSym, FunSym, Privacy};
use crate::term::{Term, TermView};
use tamarin_utils::cow::cow_map_vec;
use crate::vterm::{const_term, var_term, Lit, VTerm};

// =============================================================================
// Sorts
// =============================================================================

/// Sorts for logical variables. Subsort relation:
/// `LSortFresh < LSortMsg`, `LSortPub < LSortMsg`, `LSortNat < LSortMsg`.
/// `LSortNode` is incomparable to the others.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LSort {
    Pub,
    Fresh,
    Msg,
    Node,
    Nat,
}

/// Partial-order comparison on sorts. Returns `None` for incomparable sorts.
pub fn sort_compare(a: LSort, b: LSort) -> Option<Ordering> {
    use LSort::*;
    if a == b { return Some(Ordering::Equal); }
    match (a, b) {
        (Node, _) | (_, Node) => None,
        (Msg, _) => Some(Ordering::Greater),
        (_, Msg) => Some(Ordering::Less),
        _ => None, // Pub/Fresh/Nat are pairwise incomparable
    }
}

/// Annotation prefix for variables of this sort: `~` fresh, `$` pub,
/// `#` node, `%` nat, empty for msg.
pub fn sort_prefix(s: LSort) -> &'static str {
    match s {
        LSort::Msg => "",
        LSort::Fresh => "~",
        LSort::Pub => "$",
        LSort::Node => "#",
        LSort::Nat => "%",
    }
}

pub fn sort_suffix(s: LSort) -> &'static str {
    match s {
        LSort::Msg => "msg",
        LSort::Fresh => "fresh",
        LSort::Pub => "pub",
        LSort::Node => "node",
        LSort::Nat => "nat",
    }
}

// =============================================================================
// Names
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NameId(pub &'static str);

impl NameId {
    pub fn new(s: impl Into<String>) -> Self { NameId(crate::intern::intern_str(&s.into())) }
    pub fn as_str(&self) -> &str { self.0 }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NameTag {
    Fresh,
    Pub,
    Node,
    Nat,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub tag: NameTag,
    pub id: NameId,
}

impl Name {
    pub fn new(tag: NameTag, id: impl Into<String>) -> Self {
        Name { tag, id: NameId::new(id) }
    }
}

/// `NTerm<V>` — terms with `Name` constants and arbitrary variable type.
pub type NTerm<V> = VTerm<Name, V>;

pub fn fresh_term<V>(s: impl Into<String>) -> NTerm<V> {
    const_term(Name::new(NameTag::Fresh, s))
}
pub fn pub_term<V>(s: impl Into<String>) -> NTerm<V> {
    const_term(Name::new(NameTag::Pub, s))
}

pub fn sort_of_name(n: &Name) -> LSort {
    match n.tag {
        NameTag::Fresh => LSort::Fresh,
        NameTag::Pub => LSort::Pub,
        NameTag::Node => LSort::Node,
        NameTag::Nat => LSort::Nat,
    }
}

// =============================================================================
// LVar — logical variable
// =============================================================================

/// Logical variable. Two `LVar`s are equal only if all three of name, sort,
/// and index match.
///
/// **Ord semantics**: idx FIRST, then sort, then name — mirrors Haskell's
/// `instance Ord LVar` in `lib/term/src/Term/LTerm.hs:521-523`:
///
/// ```haskell
/// instance Ord LVar where
///     compare (LVar x1 x2 x3) (LVar y1 y2 y3) =
///         compare x3 y3 <> compare x2 y2 <> compare x1 y1
/// ```
///
/// where `x1=name, x2=sort, x3=idx` (comment: *"An ord instance that prefers
/// the 'lvarIdx' over the 'lvarName'."*).  This matters because Haskell's
/// `unifyRaw` (Unification.hs:241) orients same-sort var-var bindings such
/// that the larger-Ord (=larger-idx) becomes the KEY:
///
/// ```haskell
/// (sl, sr) | sl == sr -> if vl < vr then elim vr l else elim vl r
/// ```
///
/// Combined with `refineSource`'s post-saturate
/// `restrict stableVars sSubst` (Sources.hs:118-124), this ensures stable
/// pattern vars (small idx like t.1, t.2) are NEVER keys, so all
/// stable-keyed bindings drop and pattern vars stay unbound for runtime
/// `applySource` to bind cleanly.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LVar {
    /// Interned `&'static str` (see [`crate::intern`]): clone is a pointer
    /// copy — no alloc, no atomic refcount — and equal names share one copy.
    pub name: &'static str,
    pub sort: LSort,
    pub idx: u64,
}

impl Ord for LVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Haskell-faithful: idx <> sort <> name (idx FIRST).  Destructure
        // without `..` so a new field forces an ordering decision here, keeping
        // the manual Ord in step with the derived Eq/Hash (which auto-include
        // every field).
        let LVar { name, sort, idx } = self;
        let LVar { name: other_name, sort: other_sort, idx: other_idx } = other;
        idx.cmp(other_idx)
            .then_with(|| sort.cmp(other_sort))
            .then_with(|| name.cmp(other_name))
    }
}

impl PartialOrd for LVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl LVar {
    pub fn new(name: impl AsRef<str>, sort: LSort, idx: u64) -> Self {
        LVar { name: crate::intern::intern_str(name.as_ref()), sort, idx }
    }
}

/// Alias for `LVar` when used as a derivation-graph node id.
pub type NodeId = LVar;

/// `LTerm<C>` — term whose variables are `LVar`s and constants are of type
/// `C`.
pub type LTerm<C> = VTerm<C, LVar>;
/// `LNTerm` — `LTerm<Name>`.
pub type LNTerm = LTerm<Name>;

/// `freshLVar`: pull a fresh per-name index from the supplied state.
pub fn fresh_lvar(
    state: &mut tamarin_utils::fresh::PreciseFreshState,
    name: &str,
    sort: LSort,
) -> LVar {
    LVar { name: crate::intern::intern_str(name), sort, idx: state.fresh_ident(name) }
}

// =============================================================================
// Predicates on LNTerm
// =============================================================================

// Intentionally retained: faithful HS port of `sortOfLit` (LTerm.hs); no caller yet.
#[allow(dead_code)]
pub(crate) fn sort_of_lit(l: &Lit<Name, LVar>) -> LSort {
    match l {
        Lit::Con(n) => sort_of_name(n),
        Lit::Var(v) => v.sort,
    }
}

/// Most precise sort of an `LNTerm`.
pub fn sort_of_lnterm(t: &LNTerm) -> LSort {
    sort_of_lterm(t, sort_of_name)
}

/// Generic sort-of-LTerm given a sort function for constants.
pub fn sort_of_lterm<C, F: Fn(&C) -> LSort>(t: &LTerm<C>, sort_of_const: F) -> LSort {
    match t {
        Term::Lit(Lit::Con(c)) => sort_of_const(c),
        Term::Lit(Lit::Var(v)) => v.sort,
        Term::App(FunSym::Ac(AcSym::NatPlus), _) => LSort::Nat,
        Term::App(FunSym::NoEq(s), args)
            if args.is_empty() && s.name == crate::function_symbols::NAT_ONE_SYM_STRING =>
        {
            LSort::Nat
        }
        _ => LSort::Msg,
    }
}

/// `t` is a single variable with the given sort.
fn is_var_of_sort(t: &LNTerm, want: LSort) -> bool {
    matches!(t.view(), TermView::Lit(Lit::Var(v)) if v.sort == want)
}

pub fn is_msg_var(t: &LNTerm) -> bool { is_var_of_sort(t, LSort::Msg) }
pub fn is_pub_var(t: &LNTerm) -> bool { is_var_of_sort(t, LSort::Pub) }
pub fn is_nat_var(t: &LNTerm) -> bool { is_var_of_sort(t, LSort::Nat) }
pub fn is_fresh_var(t: &LNTerm) -> bool { is_var_of_sort(t, LSort::Fresh) }

pub fn is_pub_const(t: &LNTerm) -> bool {
    matches!(t.view(), TermView::Lit(Lit::Con(n)) if sort_of_name(n) == LSort::Pub)
}

/// If `t` is a single variable, return it.
pub fn get_var(t: &LNTerm) -> Option<&LVar> {
    if let TermView::Lit(Lit::Var(v)) = t.view() { Some(v) } else { None }
}

/// `containsPrivate t`: any private NoEq symbol anywhere in `t`?
pub fn contains_private<A>(t: &Term<A>) -> bool {
    match t {
        Term::Lit(_) => false,
        Term::App(FunSym::NoEq(s), args) => {
            s.privacy == Privacy::Private || args.iter().any(contains_private)
        }
        Term::App(_, args) => args.iter().any(contains_private),
    }
}

/// `flattenedACTerms sym t`: flattened `+`-children list (no nested same
/// AC operator).
pub fn flattened_ac_terms<A>(sym: AcSym, t: &Term<A>) -> Vec<&Term<A>> {
    let mut out = Vec::new();
    fn go<'b, A>(sym: AcSym, t: &'b Term<A>, out: &mut Vec<&'b Term<A>>) {
        if let Term::App(FunSym::Ac(s), args) = t {
            if *s == sym {
                for a in args.iter() {
                    go(sym, a, out);
                }
                return;
            }
        }
        out.push(t);
    }
    go(sym, t, &mut out);
    out
}

/// `freshToConst t`: replace every fresh-sort variable with a fresh-tagged
/// constant carrying its name and index.
///
/// Intentionally retained: faithful HS port of `freshToConst` (LTerm.hs); no
/// production caller yet (exercised only by the unit test below).
#[allow(dead_code)]
pub(crate) fn fresh_to_const(t: LNTerm) -> LNTerm {
    match t {
        Term::Lit(Lit::Var(ref v)) if v.sort == LSort::Fresh => variable_to_const(v),
        Term::Lit(_) => t,
        Term::App(f, args) => {
            let mapped: Vec<LNTerm> = args.iter().cloned().map(fresh_to_const).collect();
            Term::App(f, mapped.into())
        }
    }
}

/// `variableToConst v`: build a constant whose name encodes `v`'s sort,
/// index, and name. Panics if `v.sort` is `LSort::Msg`, mirroring the
/// Haskell `error "Invalid sort Msg"`.
pub fn variable_to_const(v: &LVar) -> LNTerm {
    let tag = match v.sort {
        LSort::Fresh => NameTag::Fresh,
        LSort::Pub => NameTag::Pub,
        LSort::Node => NameTag::Node,
        LSort::Nat => NameTag::Nat,
        LSort::Msg => panic!("variable_to_const: invalid sort Msg"),
    };
    // Mirror Haskell `show vsort` (derived `Show LSort`), which yields
    // "LSortPub"/"LSortFresh"/"LSortNode"/"LSortNat" — NOT the bare Rust
    // Debug names ("Pub"/"Fresh"/...). See LTerm.hs:411-413 / 161-166.
    let sort_show = match v.sort {
        LSort::Pub => "LSortPub",
        LSort::Fresh => "LSortFresh",
        LSort::Msg => "LSortMsg",
        LSort::Node => "LSortNode",
        LSort::Nat => "LSortNat",
    };
    let id = format!("constVar_{}_{}_{}", sort_show, v.idx, v.name);
    const_term(Name::new(tag, id))
}

// =============================================================================
// BVar — bound or free variable (for binders / formulas)
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BVar<V> {
    Bound(u64),
    Free(V),
}

impl<V> BVar<V> {
    pub fn is_bound(&self) -> bool { matches!(self, BVar::Bound(_)) }
    pub fn is_free(&self) -> bool { matches!(self, BVar::Free(_)) }
    /// HS `fromFree` (LTerm.hs): unwrap a free variable, panicking on `Bound`.
    pub fn into_free(self) -> V {
        match self {
            BVar::Free(v) => v,
            BVar::Bound(i) => panic!("into_free: bound variable {}", i),
        }
    }
}

pub(crate) type BLVar = BVar<LVar>;
/// `BLTerm` — `NTerm<BLVar>`.
pub(crate) type BLTerm = NTerm<BLVar>;

// Intentionally retained: faithful HS ports of `freeLNTerm`/`freeTerm`
// (LTerm.hs). Currently unwired — the macro path that consumes them lives in
// `macro_expand.rs` (reimplemented on the parser AST).
#[allow(dead_code)]
pub(crate) fn free_lnterm(v: LVar) -> BLVar { BVar::Free(v) }

/// Convert an `LNTerm` to a term over `BVar<LVar>` — every variable becomes
/// `Free`.
#[allow(dead_code)]
pub(crate) fn free_term(t: LNTerm) -> BLTerm {
    match t {
        Term::Lit(Lit::Var(v)) => crate::term::lit(Lit::Var(BVar::Free(v))),
        Term::Lit(Lit::Con(c)) => crate::term::lit(Lit::Con(c)),
        Term::App(f, args) => Term::App(f, args.iter().cloned().map(free_term).collect::<Vec<_>>().into()),
    }
}

// =============================================================================
// HasFrees — collect / map over free LVars
// =============================================================================

/// A type that contains free `LVar`s. The Haskell typeclass takes a
/// `MonotoneFunction` (LTerm.hs:550) distinguishing AC-position-preserving
/// updates (`Monotone`, used by `rename`/`renameIgnoring`/`renameAvoiding*`
/// index shifts) from arbitrary ones (`Arbitrary`, used by `someInst`,
/// `applyVTerm` substitution, `fmap`). The two differ only at AC sub-terms:
/// `Arbitrary` re-sorts the AC argument list (`fApp` -> `fAppAC`), while
/// `Monotone` preserves the relative argument order (`unsafefApp`) because a
/// monotone shift cannot change the AC-normal form ordering (LTerm.hs:733-735).
pub trait HasFrees {
    /// Visit every free `LVar` exactly once in deterministic order.
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar));

    /// Map every free `LVar` through `f`, threading the `monotone` flag down
    /// to AC sub-terms.  When `monotone == false` (the `Arbitrary` case) AC
    /// argument lists are re-sorted via the smart constructors; when
    /// `monotone == true` (the `Monotone` case) AC argument order is
    /// preserved (`unsafe_f_app`).  Implementations rebuild themselves with
    /// the renamed variables.
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self;

    /// `Arbitrary` map (HS default): re-AC-normalises sub-terms.  Use for
    /// `someInst`, substitution application, and any non-order-preserving
    /// remap.
    fn map_free(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self
    where
        Self: Sized,
    {
        self.map_free_with(f, false)
    }

    /// `Monotone` map: preserves AC argument order.  Use ONLY where HS uses
    /// `rename`/`renameIgnoring`/`renameAvoiding*`/`someRuleACInst*` — i.e.
    /// pure index shifts whose monotonicity guarantees the AC-normal form
    /// does not change (LTerm.hs:545-550).
    fn map_free_monotone(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self
    where
        Self: Sized,
    {
        self.map_free_with(f, true)
    }
}

/// `freesList`: every free `LVar`, in traversal order (with duplicates).
pub fn frees_list<T: HasFrees>(t: &T) -> Vec<LVar> {
    let mut out = Vec::new();
    t.for_each_free(&mut |v| out.push(v.clone()));
    out
}

/// `frees`: deduplicated, sorted free `LVar`s.
pub fn frees<T: HasFrees>(t: &T) -> Vec<LVar> {
    let mut out = frees_list(t);
    out.sort();
    out.dedup();
    out
}

/// `occurs v t`: whether `v` is among `t`'s free variables.
pub fn occurs<T: HasFrees>(v: &LVar, t: &T) -> bool {
    let mut found = false;
    t.for_each_free(&mut |w| if w == v { found = true; });
    found
}

/// `boundsVarIdx t`: smallest and largest free variable indices in `t`.
pub fn bounds_var_idx<T: HasFrees>(t: &T) -> Option<(u64, u64)> {
    let mut min = u64::MAX;
    let mut max = 0u64;
    let mut any = false;
    t.for_each_free(&mut |v| {
        any = true;
        if v.idx < min { min = v.idx; }
        if v.idx > max { max = v.idx; }
    });
    if any { Some((min, max)) } else { None }
}

/// `avoid t`: a `FastFreshState` that won't generate any indices already
/// used by free variables in `t`.
pub fn avoid<T: HasFrees>(t: &T) -> tamarin_utils::fresh::FastFreshState {
    let mut s = tamarin_utils::fresh::FastFreshState::nothing_used();
    if let Some((_, max)) = bounds_var_idx(t) {
        // Reserve [0, max+1) so the next fresh starts at max+1.
        s.fresh_idents(max + 1);
    }
    s
}

// -- HasFrees impls -----------------------------------------------------------

impl HasFrees for LVar {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) { f(self); }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, _monotone: bool) -> Self { f(self) }
}

impl<C: Clone, V: HasFreesV> HasFrees for Lit<C, V> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        if let Lit::Var(v) = self { v.for_each_free_v(f); }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, _monotone: bool) -> Self {
        match self {
            Lit::Var(v) => Lit::Var(v.map_free_v(f)),
            l @ Lit::Con(_) => l,
        }
    }
}

/// Specialisation of `HasFrees` for the inner variable of a `Lit` — needed
/// because `Lit<C, V>` can wrap `LVar` directly *or* `BVar<LVar>`.
pub trait HasFreesV {
    fn for_each_free_v(&self, f: &mut dyn FnMut(&LVar));
    fn map_free_v(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self;
}

impl HasFreesV for LVar {
    fn for_each_free_v(&self, f: &mut dyn FnMut(&LVar)) { f(self); }
    fn map_free_v(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self { f(self) }
}

// Intentionally retained: faithful HS port of the `HasFrees (BVar v)` instance,
// so `Lit<C, BVar<LVar>>` is a `HasFrees` leaf. Not yet reached through the
// trait (formula terms over `BVar<LVar>` are traversed by pattern matching).
impl HasFreesV for BVar<LVar> {
    fn for_each_free_v(&self, f: &mut dyn FnMut(&LVar)) {
        if let BVar::Free(v) = self { f(v); }
    }
    fn map_free_v(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self {
        match self {
            BVar::Free(v) => BVar::Free(f(v)),
            b @ BVar::Bound(_) => b,
        }
    }
}

impl<L: Clone + Ord + HasFrees> HasFrees for Term<L>
where
    L: HasFreesLit,
{
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        match self {
            Term::Lit(l) => l.for_each_free(f),
            Term::App(_, args) => {
                for a in args.iter() { a.for_each_free(f); }
            }
        }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        // Copy-on-write: when `f` is identity on every free leaf of a subtree,
        // that subtree is unchanged, so reuse it (the owned `self`) instead of
        // cloning all args and re-running `f_app`/`unsafe_f_app`.  Mirrors
        // `subst::apply_vterm_map_changed`.  Byte-identical: a subtree with no
        // remapped leaf is already in `f_app`-normal form (the monotone path
        // never re-sorts; the non-monotone path's `f_app` re-sort of unchanged,
        // already-normal args yields the same term — the same invariant
        // `apply_vterm_map_changed` relies on).
        match map_free_term_cow(&self, f, monotone) {
            Some(t) => t,
            None => self,
        }
    }
}

/// Copy-on-write core of `Term::map_free_with`: `None` when no free leaf in `t`
/// is remapped by `f` (so the caller can reuse the input), else the rebuilt
/// term.  Single-pass: the rebuild `Vec` is allocated lazily on the first
/// changed child, and unchanged children reuse their `Arc` by clone.  Mirrors
/// `Term::App`'s `mapFrees`: monotone keeps arg order (`unsafe_f_app`),
/// non-monotone re-sorts AC/C (`f_app`).
fn map_free_term_cow<L>(t: &Term<L>, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Option<Term<L>>
where
    L: Clone + Ord + HasFrees + HasFreesLit,
{
    match t {
        Term::Lit(l) => {
            let nl = l.clone().map_free_with(f, monotone);
            if &nl != l { Some(Term::Lit(nl)) } else { None }
        }
        Term::App(fsym, args) => {
            cow_map_vec(&args[..], |a| map_free_term_cow(a, &mut *f, monotone)).map(|mapped| {
                if monotone {
                    crate::term::unsafe_f_app(fsym.clone(), mapped)
                } else {
                    crate::term::f_app(fsym.clone(), mapped)
                }
            })
        }
    }
}

/// Marker trait so the generic `HasFrees for Term<L>` impl can resolve.
/// `Lit<C, V>` and `LVar` qualify; arbitrary `L` does not.
pub trait HasFreesLit {}
impl<C: Clone, V: HasFreesV> HasFreesLit for Lit<C, V> {}
impl HasFreesLit for LVar {}

impl<T: HasFrees> HasFrees for Vec<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for t in self { t.for_each_free(f); }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        self.into_iter().map(|t| t.map_free_with(f, monotone)).collect()
    }
}

impl<A: HasFrees, B: HasFrees> HasFrees for (A, B) {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.0.for_each_free(f);
        self.1.for_each_free(f);
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        (self.0.map_free_with(f, monotone), self.1.map_free_with(f, monotone))
    }
}

impl<T: HasFrees> HasFrees for Option<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        if let Some(t) = self { t.for_each_free(f); }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        self.map(|t| t.map_free_with(f, monotone))
    }
}

// =============================================================================
// Renaming helpers
// =============================================================================

/// `rename t`: replace every free variable with a fresh one (preserving
/// sort and name hint).
pub fn rename<T: HasFrees>(t: T, fresh: &mut tamarin_utils::fresh::FastFreshState) -> T {
    let bounds = bounds_var_idx(&t);
    match bounds {
        None => t,
        Some((min, max)) => {
            let span = max - min + 1;
            let fresh_start = fresh.fresh_idents(span);
            let shift = fresh_start as i128 - min as i128;
            // HS `rename` (LTerm.hs:607-614) uses `mapFrees (Monotone ...)`: the
            // index shift is monotone, so AC arg order is preserved.
            t.map_free_monotone(&mut |LVar { name, sort, idx }| LVar {
                name,
                sort,
                idx: ((idx as i128) + shift) as u64,
            })
        }
    }
}

// Intentionally retained: faithful HS port of `natToFreshVars` (LTerm.hs).
// Currently unwired — the nat→fresh logic on the parser AST in `deriv_check.rs`
// supersedes this term-level version (exercised only by the unit test below).
#[allow(dead_code)]
pub(crate) fn nat_to_fresh_vars(t: LNTerm) -> LNTerm {
    match t {
        Term::Lit(Lit::Var(LVar { name, sort: LSort::Nat, idx })) => {
            var_term(LVar { name, sort: LSort::Fresh, idx })
        }
        Term::Lit(_) => t,
        Term::App(f, args) => {
            let mapped: Vec<LNTerm> = args.iter().cloned().map(nat_to_fresh_vars).collect();
            Term::App(f, mapped.into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::pair_sym;
    use crate::term::f_app_no_eq;

    #[test]
    fn sort_partial_order() {
        assert_eq!(sort_compare(LSort::Fresh, LSort::Msg), Some(Ordering::Less));
        assert_eq!(sort_compare(LSort::Msg, LSort::Pub), Some(Ordering::Greater));
        assert_eq!(sort_compare(LSort::Fresh, LSort::Fresh), Some(Ordering::Equal));
        // Fresh and Pub are incomparable.
        assert_eq!(sort_compare(LSort::Fresh, LSort::Pub), None);
        // Node is incomparable to everything else.
        assert_eq!(sort_compare(LSort::Node, LSort::Msg), None);
    }

    #[test]
    fn sort_prefixes() {
        assert_eq!(sort_prefix(LSort::Fresh), "~");
        assert_eq!(sort_prefix(LSort::Pub), "$");
        assert_eq!(sort_prefix(LSort::Msg), "");
        assert_eq!(sort_suffix(LSort::Nat), "nat");
    }

    #[test]
    fn name_sort_mapping() {
        assert_eq!(sort_of_name(&Name::new(NameTag::Fresh, "k")), LSort::Fresh);
        assert_eq!(sort_of_name(&Name::new(NameTag::Pub, "p")), LSort::Pub);
        assert_eq!(sort_of_name(&Name::new(NameTag::Node, "n")), LSort::Node);
        assert_eq!(sort_of_name(&Name::new(NameTag::Nat, "n")), LSort::Nat);
    }

    #[test]
    fn lvar_predicates() {
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = var_term(v.clone());
        assert!(is_msg_var(&t));
        assert!(!is_pub_var(&t));
        assert_eq!(get_var(&t), Some(&v));
    }

    #[test]
    fn pub_const_check() {
        let p: LNTerm = pub_term("alice");
        assert!(is_pub_const(&p));
        let f: LNTerm = fresh_term("k");
        assert!(!is_pub_const(&f));
    }

    #[test]
    fn flattened_ac_extracts_terms() {
        use crate::function_symbols::AcSym;
        use crate::term::f_app_ac;
        let inner: LNTerm = f_app_ac(AcSym::Mult, vec![pub_term("a"), pub_term("b")]);
        let outer: LNTerm = f_app_ac(AcSym::Mult, vec![inner, pub_term("c")]);
        let flat = flattened_ac_terms(AcSym::Mult, &outer);
        assert_eq!(flat.len(), 3);
    }

    #[test]
    fn fresh_to_const_replaces_only_fresh_vars() {
        let v_fresh: LNTerm = var_term(LVar::new("k", LSort::Fresh, 0));
        let v_pub: LNTerm = var_term(LVar::new("p", LSort::Pub, 0));
        let t: LNTerm = f_app_no_eq(pair_sym(), vec![v_fresh.clone(), v_pub.clone()]);
        let r = fresh_to_const(t);
        if let Term::App(_, ts) = &r {
            // First arg should now be a Con.
            assert!(matches!(ts[0], Term::Lit(Lit::Con(_))));
            // Second arg (pub variable) should still be a Var.
            assert!(matches!(ts[1], Term::Lit(Lit::Var(_))));
        } else {
            panic!();
        }
    }

    #[test]
    fn nat_to_fresh_vars_swaps_sort() {
        let t: LNTerm = var_term(LVar::new("n", LSort::Nat, 3));
        let r = nat_to_fresh_vars(t);
        assert_eq!(get_var(&r).unwrap().sort, LSort::Fresh);
    }

    #[test]
    fn contains_private_detects_private_symbol() {
        // diff is private.
        let t: LNTerm = f_app_no_eq(
            crate::function_symbols::diff_sym(),
            vec![pub_term("a"), pub_term("b")],
        );
        assert!(contains_private(&t));
        let t: LNTerm = f_app_no_eq(pair_sym(), vec![pub_term("a"), pub_term("b")]);
        assert!(!contains_private(&t));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for enum declaration order.
    //
    // For every Haskell `data X = A | B | C deriving (Ord, ...)`, the
    // induced `Ord` is the declaration order.  If our Rust enum reorders
    // variants, BTreeMap/BTreeSet iteration over X-keyed maps silently
    // sorts differently — and proof state inspection by downstream code
    // (goal-ranking, case dedup, source-case ordering) diverges.
    //
    // **Pin every Ord-bearing enum's declaration order to its Haskell
    // counterpart by checked file:line below.**
    // =========================================================================

    /// LTerm.hs:161-166:
    ///     data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode | LSortNat
    ///                deriving( Eq, Ord, ... )
    #[test]
    fn lsort_ord_matches_haskell_declaration() {
        // Pub < Fresh < Msg < Node < Nat
        assert!(LSort::Pub   < LSort::Fresh);
        assert!(LSort::Fresh < LSort::Msg);
        assert!(LSort::Msg   < LSort::Node);
        assert!(LSort::Node  < LSort::Nat);
        // Transitive.
        assert!(LSort::Pub < LSort::Nat);
    }

    /// LTerm.hs:215: `data NameTag = FreshName | PubName | NodeName | NatName`
    #[test]
    fn name_tag_ord_matches_haskell_declaration() {
        // Fresh < Pub < Node < Nat
        assert!(NameTag::Fresh < NameTag::Pub);
        assert!(NameTag::Pub   < NameTag::Node);
        assert!(NameTag::Node  < NameTag::Nat);
    }

    /// Haskell `sortCompare` (LTerm.hs:177-187) is a PARTIAL ORDER, NOT
    /// the same as `Ord LSort`.  Specifically:
    ///   - Msg is greater than every other comparable sort
    ///   - Node is incomparable to ALL other sorts (returns Nothing)
    ///   - Pub, Fresh, Nat are pairwise incomparable
    ///
    /// **Do not confuse with `Ord LSort`.** `Ord LSort` is the derived
    /// total order from declaration order, used as BTreeMap/Set key.
    /// `sortCompare` is the order-sorted lattice used during unification
    /// for sort narrowing.  Mixing them up breaks unify_raw cross-sort
    /// handling.
    #[test]
    fn sort_compare_is_partial_not_total() {
        // Comparable: Msg dominates.
        assert_eq!(sort_compare(LSort::Msg, LSort::Pub),   Some(Ordering::Greater));
        assert_eq!(sort_compare(LSort::Msg, LSort::Fresh), Some(Ordering::Greater));
        assert_eq!(sort_compare(LSort::Msg, LSort::Nat),   Some(Ordering::Greater));
        // Pub, Fresh, Nat are pairwise incomparable.
        assert_eq!(sort_compare(LSort::Pub,   LSort::Fresh), None);
        assert_eq!(sort_compare(LSort::Pub,   LSort::Nat),   None);
        assert_eq!(sort_compare(LSort::Fresh, LSort::Nat),   None);
        // Node is incomparable to all.
        assert_eq!(sort_compare(LSort::Node, LSort::Msg),   None);
        assert_eq!(sort_compare(LSort::Node, LSort::Pub),   None);
        assert_eq!(sort_compare(LSort::Node, LSort::Fresh), None);
        assert_eq!(sort_compare(LSort::Node, LSort::Nat),   None);
        // BUT `Ord LSort` total order differs!  Pub < Fresh < Msg < Node
        // in Ord, even though Pub vs Fresh is incomparable in sortCompare.
        assert!(LSort::Pub < LSort::Fresh,
                "Ord LSort is total — Pub < Fresh by declaration order. \
                 (sort_compare returns None for this pair; the two \
                 contracts are deliberately different.)");
    }

    /// LTerm.hs `sortPrefix`: sort prefixes for variable rendering.  These
    /// show up in the proof skeleton as `~k` / `$A` / `#i` / `%n` and a parse
    /// regression in the renderer would break corpus diffing.
    #[test]
    fn sort_prefixes_match_haskell() {
        assert_eq!(sort_prefix(LSort::Fresh), "~");
        assert_eq!(sort_prefix(LSort::Pub),   "$");
        assert_eq!(sort_prefix(LSort::Node),  "#");
        assert_eq!(sort_prefix(LSort::Nat),   "%");
        assert_eq!(sort_prefix(LSort::Msg),   "");
    }

    /// LTerm.hs sort suffix strings used in maude bridge interchange.
    #[test]
    fn sort_suffixes_match_haskell() {
        assert_eq!(sort_suffix(LSort::Msg),   "msg");
        assert_eq!(sort_suffix(LSort::Fresh), "fresh");
        assert_eq!(sort_suffix(LSort::Pub),   "pub");
        assert_eq!(sort_suffix(LSort::Node),  "node");
        assert_eq!(sort_suffix(LSort::Nat),   "nat");
    }
}
