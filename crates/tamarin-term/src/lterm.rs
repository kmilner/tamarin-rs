// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.LTerm` data types from `lib/term/src/Term/LTerm.hs`:
//! sorts, names, logical variables, simple predicates and convertors,
//! the `BVar` bound-variable wrapper, and the `HasFrees` trait with
//! `frees`/`bounds_var_idx`/`avoid`/`rename`.
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
use crate::vterm::{const_term, Lit, VTerm};
use tamarin_utils::cow::cow_map_vec;
use tamarin_utils::fresh::MonadFresh;

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
    if a == b {
        return Some(Ordering::Equal);
    }
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

/// HS `newtype NameId = NameId { getNameId :: String }` with a derived `Ord`
/// (LTerm.hs:215-216).
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NameId(pub &'static str);

impl NameId {
    pub fn new(s: impl Into<String>) -> Self {
        NameId(crate::intern::intern_str(&s.into()))
    }
    pub fn as_str(&self) -> &str {
        self.0
    }
}

/// Variant order mirrors the Haskell constructor order
/// (`data NameTag = FreshName | PubName | NodeName | NatName | AbbrevName`,
/// LTerm.hs:219), which the derived `Ord` on both sides reads off.
///
/// `Abbrev` is the tag `Web.Utils.shorten` (`src/Web/Utils.hs:71-88`) puts on
/// the short constant it substitutes for a long term; it never occurs in a
/// parsed or solved term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NameTag {
    Fresh,
    Pub,
    Node,
    Nat,
    Abbrev,
}

/// HS `data Name = Name {nTag :: NameTag, nId :: NameId}` with a derived `Ord`
/// (LTerm.hs:223-224): the tag decides first, then the identifier.  This order
/// reaches printed output through `Term`'s `Ord`, which sorts AC arguments.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub tag: NameTag,
    pub id: NameId,
}

impl Name {
    pub fn new(tag: NameTag, id: impl Into<String>) -> Self {
        Name {
            tag,
            id: NameId::new(id),
        }
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
        // LTerm.hs:266.
        NameTag::Abbrev => LSort::Msg,
    }
}

// =============================================================================
// LVar — logical variable
// =============================================================================

/// Logical variable. Two `LVar`s are equal only if all three of name, sort,
/// and index match.
///
/// **Ord semantics**: idx FIRST, then sort, then name — mirrors Haskell's
/// `instance Ord LVar` in `lib/term/src/Term/LTerm.hs:546-548`:
///
/// ```haskell
/// instance Ord LVar where
///     compare (LVar x1 x2 x3) (LVar y1 y2 y3) =
///         compare x3 y3 <> compare x2 y2 <> compare x1 y1
/// ```
///
/// where `x1=name, x2=sort, x3=idx` (comment: *"An ord instance that prefers
/// the 'lvarIdx' over the 'lvarName'."*).  This matters because Haskell's
/// `unifyRaw` (Unification.hs:275-276) orients same-sort var-var bindings such
/// that the larger-Ord (=larger-idx) becomes the KEY:
///
/// ```haskell
/// (sl, sr) | sl == sr -> if vl < vr then elim vr l else elim vl r
/// ```
///
/// Combined with `refineSource`'s post-saturate
/// `restrict stableVars sSubst` (Sources.hs:119-126, see line 123), this ensures stable
/// pattern vars (small idx like t.1, t.2) are NEVER keys, so all
/// stable-keyed bindings drop and pattern vars stay unbound for runtime
/// `applySource` to bind cleanly.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
        let LVar {
            name: other_name,
            sort: other_sort,
            idx: other_idx,
        } = other;
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
        LVar {
            name: crate::intern::intern_str(name.as_ref()),
            sort,
            idx,
        }
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
    LVar {
        name: crate::intern::intern_str(name),
        sort,
        idx: state.fresh_ident(name),
    }
}

// =============================================================================
// Predicates on LNTerm
// =============================================================================

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

pub fn is_msg_var(t: &LNTerm) -> bool {
    is_var_of_sort(t, LSort::Msg)
}
pub fn is_pub_var(t: &LNTerm) -> bool {
    is_var_of_sort(t, LSort::Pub)
}
pub fn is_fresh_var(t: &LNTerm) -> bool {
    is_var_of_sort(t, LSort::Fresh)
}

pub fn is_pub_const(t: &LNTerm) -> bool {
    matches!(t.view(), TermView::Lit(Lit::Con(n)) if sort_of_name(n) == LSort::Pub)
}

/// If `t` is a single variable, return it.
pub fn get_var(t: &LNTerm) -> Option<&LVar> {
    if let TermView::Lit(Lit::Var(v)) = t.view() {
        Some(v)
    } else {
        None
    }
}

/// `containsPrivate t`: any private NoEq symbol anywhere in `t`?
pub fn contains_private<A>(t: &Term<A>) -> bool {
    t.any_fun_sym(|f| matches!(f, FunSym::NoEq(s) if s.privacy == Privacy::Private))
}

/// `containsOnlyNoEq t`: does `t` contain only NoEq function symbols (i.e.
/// no AC and no C symbol)?  A literal trivially qualifies.
pub fn contains_only_no_eq<A>(t: &Term<A>) -> bool {
    t.all_fun_syms(|f| matches!(f, FunSym::NoEq(_)))
}

/// `containsNoPrivateExcept funs t`: does `t` contain no private function
/// symbol other than those in `funs`?  The membership test is on the whole
/// `FunSym`, so a symbol differing in arity/constructability/NDC state from
/// its `funs` entry is not exempted.
pub fn contains_no_private_except<A>(funs: &[FunSym], t: &Term<A>) -> bool {
    t.all_fun_syms(|f| {
        !matches!(f, FunSym::NoEq(s) if s.privacy == Privacy::Private) || funs.contains(f)
    })
}

/// `isTrivialFunSymTerm t sym`: is `t` an application of `sym` whose
/// arguments are all message variables?
pub fn is_trivial_fun_sym_term(t: &LNTerm, sym: &FunSym) -> bool {
    match t {
        Term::App(f, args) => f == sym && args.iter().all(is_msg_var),
        Term::Lit(_) => false,
    }
}

/// `isTrivialACFunSymTerm t`: is `t` an application of any AC function
/// symbol whose arguments are all message variables?
pub fn is_trivial_ac_fun_sym_term(t: &LNTerm) -> bool {
    match t {
        Term::App(FunSym::Ac(_), args) => args.iter().all(is_msg_var),
        _ => false,
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

/// HS `ltermNodeId` (LTerm.hs:464-465): the node-id variable of a term that is
/// one — a variable leaf of sort `LSortNode` — and `None` otherwise.
///
/// The sort guard is load-bearing for the solver: answering `Some` for another
/// sort fires `insertFormula`'s `Eq`/`Less` → disjunction CR-rules on a
/// `¬(a = b)` formula over message variables, which HS instead keeps in
/// `sFormulas` (the `WrongEquality` lemma of
/// examples/regression/trace/MinValueEq.spthy).
pub fn lterm_node_id<C>(t: &crate::term::Term<crate::vterm::Lit<C, LVar>>) -> Option<LVar> {
    match t {
        crate::term::Term::Lit(crate::vterm::Lit::Var(v)) if v.sort == LSort::Node => Some(*v),
        _ => None,
    }
}

// =============================================================================
// BVar — bound or free variable (for binders / formulas)
// =============================================================================

/// HS `data BVar v = Bound Integer | Free v` derives `Ord` in that variant
/// order (LTerm.hs:476-478), which orders the terms inside a formula.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BVar<V> {
    Bound(u64),
    Free(V),
}

/// HS `bltermNodeId` (LTerm.hs:526-528): the node-id variable of a term that
/// is one — a `Free` leaf of sort `LSortNode` — and `None` otherwise.
pub fn blterm_node_id<C>(t: &crate::term::Term<crate::vterm::Lit<C, BVar<LVar>>>) -> Option<LVar> {
    match t {
        crate::term::Term::Lit(crate::vterm::Lit::Var(BVar::Free(v))) if v.sort == LSort::Node => {
            Some(*v)
        }
        _ => None,
    }
}

impl<V> BVar<V> {
    pub fn is_bound(&self) -> bool {
        matches!(self, BVar::Bound(_))
    }
    pub fn is_free(&self) -> bool {
        matches!(self, BVar::Free(_))
    }
    /// HS `fromFree` (LTerm.hs): unwrap a free variable, panicking on `Bound`.
    pub fn into_free(self) -> V {
        match self {
            BVar::Free(v) => v,
            BVar::Bound(i) => panic!("into_free: bound variable {}", i),
        }
    }
}

// =============================================================================
// HasFrees — collect / map over free LVars
// =============================================================================

/// A type that contains free `LVar`s. The Haskell typeclass takes a
/// `MonotoneFunction` (LTerm.hs:574-575) distinguishing AC-position-preserving
/// updates (`Monotone`, used by `rename`/`renameIgnoring`/`renameAvoiding*`
/// index shifts) from arbitrary ones (`Arbitrary`, used by `someInst`,
/// `applyVTerm` substitution, `fmap`). The two differ only at AC sub-terms:
/// `Arbitrary` re-sorts the AC argument list (`fApp` -> `fAppAC`), while
/// `Monotone` preserves the relative argument order (`unsafefApp`) because a
/// monotone shift cannot change the AC-normal form ordering
/// (`instance HasFrees (Term l)`'s `mapFrees`, LTerm.hs:788-791).
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
    /// does not change (LTerm.hs:569-575).
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
    t.for_each_free(&mut |v| out.push(*v));
    out
}

/// `getAny . foldFrees (Any . (v ==))` (Simplification.hs:96): whether `v` is
/// one of the free `LVar`s of `t`, compared on name, sort and index.
pub fn occurs_free<T: HasFrees + ?Sized>(v: &LVar, t: &T) -> bool {
    let mut found = false;
    t.for_each_free(&mut |w| found |= w == v);
    found
}

/// `frees`: deduplicated, sorted free `LVar`s.
pub fn frees<T: HasFrees>(t: &T) -> Vec<LVar> {
    let mut out = frees_list(t);
    out.sort();
    out.dedup();
    out
}

/// `boundsVarIdx t`: smallest and largest free variable indices in `t`.
pub fn bounds_var_idx<T: HasFrees>(t: &T) -> Option<(u64, u64)> {
    let mut min = u64::MAX;
    let mut max = 0u64;
    let mut any = false;
    t.for_each_free(&mut |v| {
        any = true;
        if v.idx < min {
            min = v.idx;
        }
        if v.idx > max {
            max = v.idx;
        }
    });
    if any {
        Some((min, max))
    } else {
        None
    }
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
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        f(self);
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, _monotone: bool) -> Self {
        f(self)
    }
}

impl<C: Clone, V: HasFreesV> HasFrees for Lit<C, V> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        if let Lit::Var(v) = self {
            v.for_each_free_v(f);
        }
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
    fn for_each_free_v(&self, f: &mut dyn FnMut(&LVar)) {
        f(self);
    }
    fn map_free_v(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self {
        f(self)
    }
}

// HS `instance HasFrees v => HasFrees (BVar v)` (LTerm.hs:766-776): a `Bound`
// index carries no variable, so both directions pass it through.  This makes
// `Lit<C, BVar<LVar>>` a `HasFrees` leaf, which is how the guarded formula's
// terms over `BVar<LVar>` reach the trait.
impl HasFreesV for BVar<LVar> {
    fn for_each_free_v(&self, f: &mut dyn FnMut(&LVar)) {
        if let BVar::Free(v) = self {
            f(v);
        }
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
                for a in args.iter() {
                    a.for_each_free(f);
                }
            }
        }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        // Copy-on-write: when `f` is identity on every free leaf of a subtree,
        // that subtree is unchanged, so reuse it (the owned `self`) instead of
        // cloning all args and re-running `f_app`/`unsafe_f_app`.  Mirrors the
        // `Apply` instance for `VTerm`.  Byte-identical: a subtree with no
        // remapped leaf is already in `f_app`-normal form (the monotone path
        // never re-sorts; the non-monotone path's `f_app` re-sort of unchanged,
        // already-normal args yields the same term — the same invariant that
        // instance relies on).
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
fn map_free_term_cow<L>(
    t: &Term<L>,
    f: &mut dyn FnMut(LVar) -> LVar,
    monotone: bool,
) -> Option<Term<L>>
where
    L: Clone + Ord + HasFrees + HasFreesLit,
{
    match t {
        Term::Lit(l) => {
            let nl = l.clone().map_free_with(f, monotone);
            if &nl != l {
                Some(Term::Lit(nl))
            } else {
                None
            }
        }
        Term::App(fsym, args) => {
            cow_map_vec(&args[..], |a| map_free_term_cow(a, &mut *f, monotone)).map(|mapped| {
                if monotone {
                    crate::term::unsafe_f_app(*fsym, mapped)
                } else {
                    crate::term::f_app(*fsym, mapped)
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
        for t in self {
            t.for_each_free(f);
        }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        self.into_iter()
            .map(|t| t.map_free_with(f, monotone))
            .collect()
    }
}

impl<A: HasFrees, B: HasFrees> HasFrees for (A, B) {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.0.for_each_free(f);
        self.1.for_each_free(f);
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        (
            self.0.map_free_with(f, monotone),
            self.1.map_free_with(f, monotone),
        )
    }
}

impl<T: HasFrees> HasFrees for Option<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        if let Some(t) = self {
            t.for_each_free(f);
        }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        self.map(|t| t.map_free_with(f, monotone))
    }
}

/// Free-variable traversal through a shared pointer, for the `HasFrees`
/// containers whose elements the port stores behind an `Arc`.  The map takes
/// the payload out when this handle is its sole owner and clones it when it
/// is not.
impl<T: HasFrees + Clone> HasFrees for std::sync::Arc<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        (**self).for_each_free(f);
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        let inner = std::sync::Arc::try_unwrap(self).unwrap_or_else(|shared| (*shared).clone());
        std::sync::Arc::new(inner.map_free_with(f, monotone))
    }
}

// =============================================================================
// Renaming helpers
// =============================================================================

/// `rename t`: replace every free variable with a fresh one (preserving
/// sort and name hint).
///
/// The empty-exemption case of [`rename_ignoring`]: HS states the two
/// separately (`rename`, LTerm.hs:638-645) with bodies that differ only in the
/// `elem … vars` test, which an empty list always answers `False`.
#[inline]
pub fn rename<T: HasFrees, M: MonadFresh>(t: T, fresh: &mut M) -> T {
    rename_ignoring(&[], t, fresh)
}

/// `renameIgnoring vars t`: like [`rename`], but the variables in `vars` keep
/// their index.  The shift is applied to every other free variable, so — as
/// for `rename` — the result is not guaranteed to be equal for terms that are
/// equal modulo variable indices.
#[inline]
pub fn rename_ignoring<T: HasFrees, M: MonadFresh>(vars: &[LVar], t: T, fresh: &mut M) -> T {
    match bounds_var_idx(&t) {
        None => t,
        Some((min, max)) => {
            let span = max - min + 1;
            let fresh_start = fresh.fresh_idents(span);
            let shift = fresh_start as i128 - min as i128;
            // HS `renameIgnoring` (LTerm.hs:650-657) uses `mapFrees (Monotone
            // ...)` here even though the `vars` exemption makes the map
            // non-monotone in general; transcribing HS verbatim (rather than
            // "fixing" it to an `Arbitrary` map) is what preserves AC arg
            // order — and byte parity — with the Haskell prover.
            t.map_free_monotone(&mut |v| {
                if vars.contains(&v) {
                    v
                } else {
                    LVar {
                        name: v.name,
                        sort: v.sort,
                        idx: ((v.idx as i128) + shift) as u64,
                    }
                }
            })
        }
    }
}

/// `renameAvoidingIgnoring s t vars`: replace all free variables in `s`
/// except those in `vars` by fresh variables avoiding the variables in
/// `avoid_in`.
pub fn rename_avoiding_ignoring<S: HasFrees, T: HasFrees>(s: S, avoid_in: &T, vars: &[LVar]) -> S {
    let mut fresh = avoid(avoid_in);
    rename_ignoring(vars, s, &mut fresh)
}

/// `renameAvoiding s avoid_in` (LTerm.hs:696): replace all free variables in
/// `s` by fresh variables avoiding the variables in `avoid_in`.
pub fn rename_avoiding<S: HasFrees, T: HasFrees>(s: S, avoid_in: &T) -> S {
    let mut fresh = avoid(avoid_in);
    rename(s, &mut fresh)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::pair_sym;
    use crate::term::f_app_no_eq;
    use crate::vterm::var_term;

    /// `Name`'s derived `Ord` compares the tag before the identifier, and
    /// `NameId`'s compares its one string, as HS's declarations do.
    #[test]
    fn name_ord_compares_the_tag_before_the_id() {
        let fresh_z = Name::new(NameTag::Fresh, "z");
        let pub_a = Name::new(NameTag::Pub, "a");
        assert!(fresh_z < pub_a, "the tag decides before the identifier");
        assert!(Name::new(NameTag::Pub, "a") < Name::new(NameTag::Pub, "b"));
        assert!(NameId::new("a") < NameId::new("b"));
    }

    /// `Bound` before `Free`, the variant order of HS's `BVar v`.
    #[test]
    fn bvar_ord_puts_bound_before_free() {
        let bound: BVar<LVar> = BVar::Bound(9);
        let free = BVar::Free(LVar::new("x", LSort::Msg, 0));
        assert!(bound < free);
        assert!(BVar::<LVar>::Bound(0) < BVar::Bound(1));
    }

    #[test]
    fn name_sort_mapping() {
        assert_eq!(sort_of_name(&Name::new(NameTag::Fresh, "k")), LSort::Fresh);
        assert_eq!(sort_of_name(&Name::new(NameTag::Pub, "p")), LSort::Pub);
        assert_eq!(sort_of_name(&Name::new(NameTag::Node, "n")), LSort::Node);
        assert_eq!(sort_of_name(&Name::new(NameTag::Nat, "n")), LSort::Nat);
        // The web abbreviation tag has no sort of its own.  It falls back to
        // Msg (LTerm.hs:266).  It is the one tag whose sort does not carry
        // the name of the tag.
        assert_eq!(sort_of_name(&Name::new(NameTag::Abbrev, "a")), LSort::Msg);
    }

    #[test]
    fn arc_walks_and_maps_the_payload() {
        use std::sync::Arc;
        let v = LVar::new("x", LSort::Msg, 3);
        let shared: Arc<LNTerm> = Arc::new(var_term(v));
        assert_eq!(frees_list(&shared), vec![v]);
        // A second handle forces the payload to be cloned before it is
        // mapped, and leaves the original handle's term alone.
        let other = Arc::clone(&shared);
        let mapped = other.map_free(&mut |w| LVar::new(w.name, w.sort, w.idx + 1));
        assert_eq!(*mapped, var_term(LVar::new("x", LSort::Msg, 4)));
        assert_eq!(*shared, var_term(v));
    }

    #[test]
    fn lvar_predicates() {
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = var_term(v);
        assert!(is_msg_var(&t));
        assert!(!is_pub_var(&t));
        assert_eq!(get_var(&t), Some(&v));
    }

    /// The `LSortNode` guard is the MinValueEq `WrongEquality` invariant: a
    /// message variable is not a node id, so a negated equality over two of
    /// them stays a formula instead of splitting into an ordering
    /// disjunction.
    #[test]
    fn lterm_node_id_rejects_a_message_sorted_variable() {
        let i = LVar::new("i", LSort::Node, 0);
        let n: LNTerm = var_term(i);
        assert_eq!(lterm_node_id(&n), Some(i));
        let m: LNTerm = var_term(LVar::new("a", LSort::Msg, 0));
        assert_eq!(lterm_node_id(&m), None);
    }

    #[test]
    fn lterm_node_id_rejects_an_application() {
        let n: LNTerm = var_term(LVar::new("i", LSort::Node, 0));
        let t: LNTerm = f_app_no_eq(pair_sym(), vec![n.clone(), n]);
        assert_eq!(lterm_node_id(&t), None);
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
        let a: LNTerm = pub_term("a");
        let b: LNTerm = pub_term("b");
        let c: LNTerm = pub_term("c");
        let inner: LNTerm = f_app_ac(AcSym::Mult, vec![a.clone(), b.clone()]);
        let outer: LNTerm = f_app_ac(AcSym::Mult, vec![inner, c.clone()]);
        // The children come back in their AC-sorted order, and not merely as
        // three children.  Callers index this list by position.
        assert_eq!(flattened_ac_terms(AcSym::Mult, &outer), vec![&a, &b, &c]);
        // A different AC operator does not flatten the term.  The complete
        // term comes back as the single child.
        assert_eq!(flattened_ac_terms(AcSym::Xor, &outer), vec![&outer]);
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

    /// LTerm.hs:165-170:
    ///     data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode | LSortNat
    ///                deriving( Eq, Ord, ... )
    #[test]
    fn lsort_ord_matches_haskell_declaration() {
        // Pub < Fresh < Msg < Node < Nat
        assert!(LSort::Pub < LSort::Fresh);
        assert!(LSort::Fresh < LSort::Msg);
        assert!(LSort::Msg < LSort::Node);
        assert!(LSort::Node < LSort::Nat);
        // Transitive.
        assert!(LSort::Pub < LSort::Nat);
    }

    /// LTerm.hs:219:
    ///     data NameTag = FreshName | PubName | NodeName | NatName | AbbrevName
    #[test]
    fn name_tag_ord_matches_haskell_declaration() {
        assert!(NameTag::Fresh < NameTag::Pub);
        assert!(NameTag::Pub < NameTag::Node);
        assert!(NameTag::Node < NameTag::Nat);
        assert!(NameTag::Nat < NameTag::Abbrev);
    }

    /// Haskell `sortCompare` (LTerm.hs:181-191) is a PARTIAL ORDER, NOT
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
        // Reflexive.
        assert_eq!(
            sort_compare(LSort::Fresh, LSort::Fresh),
            Some(Ordering::Equal)
        );
        // Comparable: Msg dominates, in both directions.
        assert_eq!(sort_compare(LSort::Fresh, LSort::Msg), Some(Ordering::Less));
        assert_eq!(
            sort_compare(LSort::Msg, LSort::Pub),
            Some(Ordering::Greater)
        );
        assert_eq!(
            sort_compare(LSort::Msg, LSort::Fresh),
            Some(Ordering::Greater)
        );
        assert_eq!(
            sort_compare(LSort::Msg, LSort::Nat),
            Some(Ordering::Greater)
        );
        // Pub, Fresh, Nat are pairwise incomparable.
        assert_eq!(sort_compare(LSort::Pub, LSort::Fresh), None);
        assert_eq!(sort_compare(LSort::Pub, LSort::Nat), None);
        assert_eq!(sort_compare(LSort::Fresh, LSort::Nat), None);
        // Node is incomparable to all.
        assert_eq!(sort_compare(LSort::Node, LSort::Msg), None);
        assert_eq!(sort_compare(LSort::Node, LSort::Pub), None);
        assert_eq!(sort_compare(LSort::Node, LSort::Fresh), None);
        assert_eq!(sort_compare(LSort::Node, LSort::Nat), None);
        // BUT `Ord LSort` total order differs!  Pub < Fresh < Msg < Node
        // in Ord, even though Pub vs Fresh is incomparable in sortCompare.
        assert!(
            LSort::Pub < LSort::Fresh,
            "Ord LSort is total — Pub < Fresh by declaration order. \
                 (sort_compare returns None for this pair; the two \
                 contracts are deliberately different.)"
        );
    }

    /// LTerm.hs `sortPrefix`: sort prefixes for variable rendering.  These
    /// show up in the proof skeleton as `~k` / `$A` / `#i` / `%n` and a parse
    /// regression in the renderer would break corpus diffing.
    #[test]
    fn sort_prefixes_match_haskell() {
        assert_eq!(sort_prefix(LSort::Fresh), "~");
        assert_eq!(sort_prefix(LSort::Pub), "$");
        assert_eq!(sort_prefix(LSort::Node), "#");
        assert_eq!(sort_prefix(LSort::Nat), "%");
        assert_eq!(sort_prefix(LSort::Msg), "");
    }

    /// LTerm.hs sort suffix strings used in maude bridge interchange.
    #[test]
    fn sort_suffixes_match_haskell() {
        assert_eq!(sort_suffix(LSort::Msg), "msg");
        assert_eq!(sort_suffix(LSort::Fresh), "fresh");
        assert_eq!(sort_suffix(LSort::Pub), "pub");
        assert_eq!(sort_suffix(LSort::Node), "node");
        assert_eq!(sort_suffix(LSort::Nat), "nat");
    }
}
