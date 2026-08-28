// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Atom` from `lib/theory/src/Theory/Model/Atom.hs`.
//!
//! Atoms of trace formulas. A `ProtoAtom<S, T>` is parameterised over a
//! syntactic-sugar wrapper `S` and a term type `T`. Stripping the sugar
//! (`Atom<T>` ≡ `ProtoAtom<Unit, T>`) yields the form used after parsing.
//! The sugar's own `Functor`/`Foldable` instances are [`MapSugar`] and
//! [`SugarTerms`].

use std::fmt;

use tamarin_term::lterm::{HasFrees, LVar, Name};
use tamarin_term::pretty::pretty_nterm;
use tamarin_term::term::{show_term, ShowLit, Term};
use tamarin_term::vterm::{Lit, VTerm};

use crate::fact::{pretty_fact, Fact};
use crate::pretty_hpj::{self as hpj, Doc};

/// Marker type with no fields — Haskell's `Unit2 t = Unit2`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Unit2;

/// Syntactic sugar wrapper used during parsing.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntacticSugar<T> {
    Pred(Fact<T>),
}

/// HS `data ProtoAtom s t` (Atom.hs:78-84), whose derived `Ord` ranks the
/// variants in this declaration order and, within one variant, compares the
/// fields left to right.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProtoAtom<S, T> {
    Action(T, Fact<T>),
    EqE(T, T),
    Subterm(T, T),
    Less(T, T),
    Last(T),
    Syntactic(S),
}

/// `Atom<T>` ≡ `ProtoAtom<Unit2, T>` — the post-parsing form.
pub type Atom<T> = ProtoAtom<Unit2, T>;
pub type SyntacticAtom<T> = ProtoAtom<SyntacticSugar<T>, T>;

/// Strip syntactic sugar, replacing it with `Unit2` (HS `toAtom`,
/// Atom.hs:200-206).
pub fn to_atom<S, T>(a: ProtoAtom<S, T>) -> Atom<T> {
    match a {
        ProtoAtom::Action(t, fa) => ProtoAtom::Action(t, fa),
        ProtoAtom::EqE(l, r) => ProtoAtom::EqE(l, r),
        ProtoAtom::Subterm(l, r) => ProtoAtom::Subterm(l, r),
        ProtoAtom::Less(l, r) => ProtoAtom::Less(l, r),
        ProtoAtom::Last(t) => ProtoAtom::Last(t),
        ProtoAtom::Syntactic(_) => ProtoAtom::Syntactic(Unit2),
    }
}

/// The `Functor` instance of a sugar type: both `SyntacticSugar` and `Unit2`
/// derive one (Atom.hs:87-94), and `Functor (ProtoAtom s)` descends into it at
/// `Syntactic` (Atom.hs:127).  The term type changes under the map, so the
/// mapped sugar is a type of its own.
pub trait MapSugar<T, U> {
    /// The sugar over the mapped term type.
    type Mapped;
    /// Rebuild the sugar with every term it holds mapped, left to right.
    fn map_sugar(&self, f: &mut dyn FnMut(&T) -> U) -> Self::Mapped;
}

impl<T, U> MapSugar<T, U> for Unit2 {
    type Mapped = Unit2;
    fn map_sugar(&self, _f: &mut dyn FnMut(&T) -> U) -> Unit2 {
        Unit2
    }
}

impl<T, U> MapSugar<T, U> for SyntacticSugar<T> {
    type Mapped = SyntacticSugar<U>;
    fn map_sugar(&self, f: &mut dyn FnMut(&T) -> U) -> SyntacticSugar<U> {
        let SyntacticSugar::Pred(fa) = self;
        SyntacticSugar::Pred(fa.map_ref(f))
    }
}

/// The `Foldable` instance of a sugar type, which both `SyntacticSugar` and
/// `Unit2` derive (Atom.hs:87-94) and which `Foldable (ProtoAtom s)` descends
/// into at `Syntactic` (Atom.hs:136).  The `Functor` half is [`MapSugar`].
pub trait SugarTerms<T>: Sized {
    /// Visit every term held by the sugar, left to right.
    fn for_each_term<'a>(&'a self, f: &mut dyn FnMut(&'a T));
}

impl<T> SugarTerms<T> for Unit2 {
    fn for_each_term<'a>(&'a self, _f: &mut dyn FnMut(&'a T)) {}
}

impl<T> SugarTerms<T> for SyntacticSugar<T> {
    fn for_each_term<'a>(&'a self, f: &mut dyn FnMut(&'a T)) {
        let SyntacticSugar::Pred(fa) = self;
        fa.terms.iter().for_each(f);
    }
}

/// HS `Functor (ProtoAtom s)` (Atom.hs:121-127), borrowing its input.
/// `Action` maps its time point before the fact's terms, the binary atoms map
/// left before right, and `Syntactic` maps the sugar — the order a mapping
/// function that mints fresh names or counts occurrences sees.
pub fn map_atom<S: MapSugar<T, U>, T, U>(
    a: &ProtoAtom<S, T>,
    f: &mut dyn FnMut(&T) -> U,
) -> ProtoAtom<S::Mapped, U> {
    match a {
        ProtoAtom::Action(t, fa) => {
            let t_mapped = f(t);
            ProtoAtom::Action(t_mapped, fa.map_ref(&mut *f))
        }
        ProtoAtom::EqE(l, r) => ProtoAtom::EqE(f(l), f(r)),
        ProtoAtom::Subterm(l, r) => ProtoAtom::Subterm(f(l), f(r)),
        ProtoAtom::Less(l, r) => ProtoAtom::Less(f(l), f(r)),
        ProtoAtom::Last(t) => ProtoAtom::Last(f(t)),
        ProtoAtom::Syntactic(s) => ProtoAtom::Syntactic(s.map_sugar(f)),
    }
}

/// The term ladder HS's two atom traversals share: `Action` gives the time
/// point before the fact's terms, each binary atom gives its left operand
/// before its right, and `Last` gives its single term.  `syntactic` is the one
/// arm the two differ in.
fn fold_atom_ladder<'a, S, T>(
    a: &'a ProtoAtom<S, T>,
    f: &mut dyn FnMut(&'a T),
    syntactic: &mut dyn FnMut(&'a S, &mut dyn FnMut(&'a T)),
) {
    match a {
        ProtoAtom::Action(t, fa) => {
            f(t);
            for x in fa.terms.iter() {
                f(x);
            }
        }
        ProtoAtom::EqE(l, r) | ProtoAtom::Subterm(l, r) | ProtoAtom::Less(l, r) => {
            f(l);
            f(r);
        }
        ProtoAtom::Last(t) => f(t),
        ProtoAtom::Syntactic(s) => syntactic(s, f),
    }
}

/// HS `Foldable (ProtoAtom s)` (Atom.hs:129-136): the ladder with the sugar's
/// own `Foldable` (Atom.hs:87-94) run at `Syntactic` — the order a folding
/// function with a counter sees.
pub fn fold_atom<'a, S: SugarTerms<T>, T>(a: &'a ProtoAtom<S, T>, f: &mut dyn FnMut(&'a T)) {
    fold_atom_ladder(a, f, &mut |s, g| s.for_each_term(g));
}

/// HS `atomTerms` (Theory/Tools/Wellformedness.hs:908-915): the ladder with a
/// `Syntactic` atom giving no terms, appending to `out`.
pub fn collect_atom_terms<'a, S, T>(a: &'a ProtoAtom<S, T>, out: &mut Vec<&'a T>) {
    fold_atom_ladder(a, &mut |t| out.push(t), &mut |_, _| {});
}

/// HS `instance HasFrees t => HasFrees (Atom t)` (Atom.hs:156-161): both
/// directions run through the `Traversable`/`Foldable` instances, so they
/// reach every term of the atom in [`fold_atom`]'s order and rebuild the atom
/// around the mapped terms.  `foldFreesOcc` contributes nothing.
impl<T: HasFrees + Clone> HasFrees for Atom<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        fold_atom(self, &mut |t| t.for_each_free(f));
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        map_atom(&self, &mut |t| t.clone().map_free_with(f, monotone))
    }
}

// -- Predicates ---------------------------------------------------------------
//
// The predicates of Haskell's `Theory.Model.Atom` used by the Rust port.

impl<T> Atom<T> {
    pub fn is_action(&self) -> bool {
        matches!(self, ProtoAtom::Action(_, _))
    }
    pub fn is_eq(&self) -> bool {
        matches!(self, ProtoAtom::EqE(_, _))
    }
    pub fn is_subterm(&self) -> bool {
        matches!(self, ProtoAtom::Subterm(_, _))
    }
    pub fn is_less(&self) -> bool {
        matches!(self, ProtoAtom::Less(_, _))
    }
    pub fn is_last(&self) -> bool {
        matches!(self, ProtoAtom::Last(_))
    }
}

// -- Pretty-printing ----------------------------------------------------------

/// HS `prettyProtoAtom ppS ppT` (Atom.hs:212-224).  `ppT` prints the `Action`
/// fact's terms and both operands of `EqE` and `Subterm`; the `Action` time
/// point, both `Less` operands and the `Last` operand print with `show`
/// (Atom.hs:217,223,224), which on a term is
/// [`tamarin_term::term::show_term`].
pub fn pretty_proto_atom<S, A: ShowLit>(
    pp_s: &dyn Fn(&S) -> Doc,
    pp_t: &dyn Fn(&Term<A>) -> Doc,
    a: &ProtoAtom<S, Term<A>>,
) -> Doc {
    match a {
        ProtoAtom::Action(v, fa) => pretty_fact(pp_t, fa)
            .beside_sp(hpj::operator_("@"))
            .beside_sp(Doc::text(show_term(v))),
        ProtoAtom::Syntactic(s) => pp_s(s),
        ProtoAtom::EqE(l, r) => hpj::sep(vec![pp_t(l).beside_sp(hpj::operator_("=")), pp_t(r)]),
        ProtoAtom::Subterm(l, r) => {
            hpj::sep(vec![pp_t(l).beside_sp(hpj::operator_("\u{228F}")), pp_t(r)])
        }
        ProtoAtom::Less(u, v) => Doc::text(show_term(u))
            .beside_sp(hpj::operator_("<"))
            .beside_sp(Doc::text(show_term(v))),
        ProtoAtom::Last(i) => hpj::operator_("last").beside(hpj::parens(Doc::text(show_term(i)))),
    }
}

/// HS `prettyAtom = prettyProtoAtom (const emptyDoc)` (Atom.hs:226-229): the
/// `Unit2` sugar of a post-parsing atom carries nothing to print.
pub(crate) fn pretty_atom<A: ShowLit>(pp_t: &dyn Fn(&Term<A>) -> Doc, a: &Atom<Term<A>>) -> Doc {
    pretty_proto_atom(&|_: &Unit2| Doc::empty(), pp_t, a)
}

/// HS `prettyNAtom = prettyAtom prettyNTerm` (Atom.hs:232-233) over
/// `NAtom v = Atom (VTerm Name v)` (Atom.hs:107).
pub fn pretty_natom<V>(a: &Atom<VTerm<Name, V>>) -> Doc
where
    V: fmt::Display,
    Lit<Name, V>: ShowLit,
{
    pretty_atom(&|t: &VTerm<Name, V>| pretty_nterm(t), a)
}

/// HS `prettySyntacticNAtom = prettyProtoAtom prettyPred prettyNTerm`, whose
/// `prettyPred (Pred fa) = prettyNFact fa` (Atom.hs:236-239) is
/// `prettyFact prettyNTerm` (Theory/Model/Fact.hs:577-578) on the sugar's
/// fact.
pub fn pretty_syntactic_natom<V>(a: &SyntacticAtom<VTerm<Name, V>>) -> Doc
where
    V: fmt::Display,
    Lit<Name, V>: ShowLit,
{
    let pp_t = |t: &VTerm<Name, V>| pretty_nterm(t);
    pretty_proto_atom(&|SyntacticSugar::Pred(fa)| pretty_fact(&pp_t, fa), &pp_t, a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{fresh_fact, FactTag};
    use tamarin_term::builtin::msg_var;
    use tamarin_term::function_symbols::pair_sym;
    use tamarin_term::lterm::{LNTerm, LSort, LVar};
    use tamarin_term::term::{f_app_no_eq, lit};

    fn x() -> LNTerm {
        msg_var("x", 0)
    }
    fn y() -> LNTerm {
        msg_var("y", 0)
    }
    fn tp(name: &str) -> LNTerm {
        lit(Lit::Var(LVar::new(name, LSort::Node, 0)))
    }

    /// Every predicate used by production code matches exactly its own
    /// variant. The syntactic-sugar variant matches none of them.
    #[test]
    fn atom_predicates() {
        let atoms: Vec<Atom<LNTerm>> = vec![
            ProtoAtom::Action(x(), fresh_fact(y())),
            ProtoAtom::EqE(x(), y()),
            ProtoAtom::Subterm(x(), y()),
            ProtoAtom::Less(x(), y()),
            ProtoAtom::Last(x()),
            ProtoAtom::Syntactic(Unit2),
        ];
        for (i, a) in atoms.iter().enumerate() {
            let row = [
                a.is_action(),
                a.is_eq(),
                a.is_subterm(),
                a.is_less(),
                a.is_last(),
            ];
            for (j, hit) in row.iter().enumerate() {
                assert_eq!(*hit, i == j, "predicate {j} on {a:?}");
            }
        }
    }

    /// `fmap` on an `Action` maps the time point before the fact's terms
    /// (Atom.hs:122), which is the order a mapping function with a counter or
    /// a fresh-name supply sees.  The map also changes the term type, and the
    /// sugar's with it.
    #[test]
    fn map_atom_visits_the_action_timepoint_before_the_facts_terms() {
        let a: SyntacticAtom<LNTerm> =
            ProtoAtom::Action(x(), Fact::new(FactTag::Term, vec![y(), x()]));
        let mut visited = 0usize;
        let mapped = map_atom(&a, &mut |_| {
            visited += 1;
            visited
        });
        let want: ProtoAtom<SyntacticSugar<usize>, usize> =
            ProtoAtom::Action(1, Fact::new(FactTag::Term, vec![2, 3]));
        assert_eq!(mapped, want);

        let sugared: SyntacticAtom<LNTerm> =
            ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(FactTag::Term, vec![x()])));
        let want: ProtoAtom<SyntacticSugar<usize>, usize> =
            ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(FactTag::Term, vec![4])));
        assert_eq!(
            map_atom(&sugared, &mut |_| {
                visited += 1;
                visited
            }),
            want
        );
    }

    /// `fold_atom` visits the `Action` time point before the fact's terms
    /// (Atom.hs:129-130) and each binary atom's left operand before its
    /// right, and the `Unit2` sugar contributes nothing (Atom.hs:92-94).
    #[test]
    fn fold_atom_visits_the_terms_in_the_haskell_order() {
        let seen = |a: &Atom<LNTerm>| {
            let mut out = Vec::new();
            fold_atom(a, &mut |t| out.push(show_term(t)));
            out
        };
        let action: Atom<LNTerm> =
            ProtoAtom::Action(tp("i"), Fact::new(FactTag::Term, vec![y(), x()]));
        assert_eq!(seen(&action), vec!["#i", "y", "x"]);
        assert_eq!(seen(&ProtoAtom::EqE(y(), x())), vec!["y", "x"]);
        assert_eq!(seen(&ProtoAtom::Syntactic(Unit2)), Vec::<String>::new());
    }

    /// The derived `Ord` ranks the variants in HS's declaration order
    /// (Atom.hs:78-84): Action, EqE, Subterm, Less, Last, Syntactic.
    #[test]
    fn proto_atom_ord_follows_the_haskell_declaration_order() {
        let ascending: Vec<Atom<LNTerm>> = vec![
            ProtoAtom::Action(x(), fresh_fact(y())),
            ProtoAtom::EqE(x(), y()),
            ProtoAtom::Subterm(x(), y()),
            ProtoAtom::Less(x(), y()),
            ProtoAtom::Last(x()),
            ProtoAtom::Syntactic(Unit2),
        ];
        for (i, a) in ascending.iter().enumerate() {
            for (j, b) in ascending.iter().enumerate() {
                assert_eq!(a.cmp(b), i.cmp(&j), "{a:?} vs {b:?}");
            }
        }
    }

    /// HS `Action t (Fact t)` (Atom.hs:78) puts the time point first, so the
    /// derived `Ord` decides on it before it reaches the fact.  Here the two
    /// halves disagree: the smaller time point carries the larger fact.
    #[test]
    fn proto_atom_action_orders_the_timepoint_before_the_fact() {
        let early: Atom<LNTerm> = ProtoAtom::Action(tp("i"), fresh_fact(y()));
        let late: Atom<LNTerm> = ProtoAtom::Action(tp("j"), fresh_fact(x()));
        assert!(tp("i") < tp("j"));
        assert!(fresh_fact(y()) > fresh_fact(x()));
        assert!(early < late);
    }

    /// `to_atom` replaces the sugar payload with the field-less `Unit2`.  It
    /// carries every other variant across unchanged.  This includes the
    /// constructor of the variant.  A check that uses `matches!` on one
    /// variant cannot see that constructor.
    #[test]
    fn to_atom_strips_sugar() {
        let s: SyntacticAtom<LNTerm> =
            ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::fresh(FactTag::Term, vec![x()])));
        assert_eq!(to_atom(s), ProtoAtom::Syntactic(Unit2));

        let cases: Vec<(SyntacticAtom<LNTerm>, Atom<LNTerm>)> = vec![
            (
                ProtoAtom::Action(x(), fresh_fact(y())),
                ProtoAtom::Action(x(), fresh_fact(y())),
            ),
            (ProtoAtom::EqE(x(), y()), ProtoAtom::EqE(x(), y())),
            (ProtoAtom::Subterm(x(), y()), ProtoAtom::Subterm(x(), y())),
            (ProtoAtom::Less(x(), y()), ProtoAtom::Less(x(), y())),
            (ProtoAtom::Last(x()), ProtoAtom::Last(x())),
        ];
        for (input, expected) in cases {
            assert_eq!(to_atom(input), expected);
        }
    }

    /// Every arm of `prettyProtoAtom` other than `Syntactic`
    /// (Atom.hs:216-224) carries its own operator: `Action` joins the fact,
    /// `@` and the time point with `<->`, `EqE` and `Subterm` are `sep`s,
    /// `Less` is two `<->`s and `Last` wraps its operand in plain
    /// parentheses.  Only the two `sep` arms add a break point of their own.
    #[test]
    fn pretty_natom_prints_each_arm() {
        let cases: Vec<(Atom<LNTerm>, &str)> = vec![
            (ProtoAtom::Action(tp("i"), fresh_fact(y())), "Fr( y ) @ #i"),
            (ProtoAtom::EqE(x(), y()), "x = y"),
            (ProtoAtom::Subterm(x(), y()), "x \u{228F} y"),
            (ProtoAtom::Less(tp("i"), tp("j")), "#i < #j"),
            (ProtoAtom::Last(tp("i")), "last(#i)"),
        ];
        for (a, want) in cases {
            assert_eq!(pretty_natom(&a).render(), want, "{a:?}");
        }
    }

    /// `prettySyntacticNAtom` prints a `Pred` atom as its fact
    /// (Atom.hs:236-239) and leaves the other arms to `prettyProtoAtom`.
    #[test]
    fn pretty_syntactic_natom_prints_the_pred_fact() {
        let a: SyntacticAtom<LNTerm> = ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(
            FactTag::Proto(crate::fact::Multiplicity::Linear, "Eq", 2),
            vec![x(), y()],
        )));
        assert_eq!(pretty_syntactic_natom(&a).render(), "Eq( x, y )");
        let plain: SyntacticAtom<LNTerm> = ProtoAtom::EqE(x(), y());
        assert_eq!(pretty_syntactic_natom(&plain).render(), "x = y");
    }

    /// The time point positions take HS `show` (Atom.hs:217,223,224), not the
    /// `ppT` the fact and the `EqE`/`Subterm` operands take.  The two spell a
    /// `Lit` alike, so the difference shows only on an applied term: `show`
    /// keeps the prefix form where `prettyTerm` would write `<x, y>`.
    #[test]
    fn pretty_natom_shows_the_time_point() {
        let applied = f_app_no_eq(pair_sym(), vec![x(), y()]);
        let a: Atom<LNTerm> = ProtoAtom::Last(applied.clone());
        assert_eq!(pretty_natom(&a).render(), "last(pair(x,y))");
        let eq: Atom<LNTerm> = ProtoAtom::EqE(applied, y());
        assert_eq!(pretty_natom(&eq).render(), "<x, y> = y");
    }

    /// `show LVar` writes the index alone when the name is empty
    /// (LTerm.hs:554), which is the variable spelling `prettyNTerm` reaches
    /// through `Show (Lit c v)` (VTerm.hs:98-100).
    #[test]
    fn lvar_with_no_name_shows_its_index() {
        let anon: LNTerm = lit(Lit::Var(LVar::new("", LSort::Fresh, 7)));
        let a: Atom<LNTerm> = ProtoAtom::EqE(anon, y());
        assert_eq!(pretty_natom(&a).render(), "~7 = y");
    }
}
