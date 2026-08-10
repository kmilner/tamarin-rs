// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Formula` from
//! `lib/theory/src/Theory/Model/Formula.hs` — data type, basic builders, and
//! the quantifier-introduction helpers (`quantify`, `exists`, `forAll`,
//! `existFormula`, `forAllFormula`).
//!
//! The Haskell version uses a locally-nameless representation: bound
//! variables are `BVar::Bound(de_bruijn_idx)`, free variables are `Free(v)`.
//!
//! The pure transforms (`nnf`, `pullquants`, `prenex`, `pnf`,
//! `simplifyFormula`) are not ported on THIS type. Formula.hs's
//! `shiftFreeIndices`/`simplifyFormula` (plus Generation.hs's
//! `pullQuantifiers`/`mergeQuantifiers`, and a second `quantify`) ARE ported in
//! `tamarin-accountability/src/formula.rs`, over a parallel locally-nameless
//! type (`Fm`) whose leaves are `guarded_types` parser-AST atoms rather than
//! this module's real-term `ProtoAtom`s — check there before porting a
//! transform here. (The guarded-formula simplifier `simplifyGuarded` is a
//! DIFFERENT HS function, ported as `simplify_guarded_with` in guarded.rs.)
//! (Pretty-printing of the parser-AST formula representation lives in
//! `pretty_formula.rs`; this `ProtoFormula` has no pretty-printer.)

use crate::atom::{ProtoAtom, Unit2};
use tamarin_term::lterm::{BVar, HasFrees, LSort, LVar, Name};
use tamarin_term::term::Term;
use tamarin_term::vterm::{Lit, VTerm};

/// Logical connectives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Connective {
    And,
    Or,
    Imp,
    Iff,
}

/// Quantifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    All,
    Ex,
}

/// First-order formula in locally-nameless representation.
///
/// - `S`: syntactic-sugar type (use `()` for the post-parsing form)
/// - `H`: name/sort hint stored at each binder
/// - `C`: constant type for terms
/// - `V`: free-variable type for terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtoFormula<S, H, C, V> {
    Atom(ProtoAtom<S, VTerm<C, BVar<V>>>),
    /// `true`/`false`.
    Tf(bool),
    Not(Box<ProtoFormula<S, H, C, V>>),
    Conn(
        Connective,
        Box<ProtoFormula<S, H, C, V>>,
        Box<ProtoFormula<S, H, C, V>>,
    ),
    Qua(Quantifier, H, Box<ProtoFormula<S, H, C, V>>),
}

/// `Formula` after parsing: no syntactic sugar.
pub type Formula<H, C, V> = ProtoFormula<Unit2, H, C, V>;
pub type LFormula<C> = Formula<(String, tamarin_term::lterm::LSort), C, LVar>;
pub type LNFormula = LFormula<Name>;

impl<S, H, C, V> ProtoFormula<S, H, C, V> {
    pub fn ltrue() -> Self {
        ProtoFormula::Tf(true)
    }
    pub fn lfalse() -> Self {
        ProtoFormula::Tf(false)
    }

    pub fn not(self) -> Self {
        ProtoFormula::Not(Box::new(self))
    }

    pub fn and(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::And, Box::new(self), Box::new(other))
    }
    pub fn or(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Or, Box::new(self), Box::new(other))
    }
    pub fn implies(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Imp, Box::new(self), Box::new(other))
    }
    pub fn iff(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Iff, Box::new(self), Box::new(other))
    }

    pub fn for_all(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::All, hint, Box::new(body))
    }
    pub fn exists(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::Ex, hint, Box::new(body))
    }
}

// =============================================================================
// Quantifier introduction (Formula.hs:347-360) + the whole-formula closures
// `existFormula` / `forAllFormula` (Formula.hs:528-538)
//
// Intentionally retained: faithful, unit-tested mirror of the HS quantifier
// machinery at those two anchors (`quantify`/`forAll`/`exists` and
// `existFormula`/`forAllFormula`); no caller yet — `close_rule` builds its
// `Deduction` lemma as theory text.  Each item below names its own HS
// counterpart.
// =============================================================================

/// The term type of an [`LNFormula`] atom: variables are `BVar`s, so a term
/// mentions both the enclosing binders' De Bruijn indices and free `LVar`s.
type BLNTerm = VTerm<Name, BVar<LVar>>;

/// HS `frees` on an `LNFormula`, i.e. its `HasFrees` instance
/// (Formula.hs:321-326): `foldFrees f = foldMap (foldFrees f)`, where the
/// `Foldable (ProtoFormula ...)` instance (Formula.hs:197-199) descends into the
/// atoms' terms and the `Foldable BVar` instance yields only `Free` variables —
/// so bound De Bruijn indices contribute nothing and binder hints are ignored.
/// Deduplicated and sorted, like [`tamarin_term::lterm::frees`].
pub fn formula_frees(fm: &LNFormula) -> Vec<LVar> {
    let mut out = Vec::new();
    for_each_free_var(fm, &mut |v| out.push(*v));
    out.sort();
    out.dedup();
    out
}

fn for_each_free_var(fm: &LNFormula, f: &mut dyn FnMut(&LVar)) {
    match fm {
        ProtoFormula::Atom(a) => for_each_atom_term(a, &mut |t| t.for_each_free(&mut *f)),
        ProtoFormula::Tf(_) => {}
        ProtoFormula::Not(p) => for_each_free_var(p, f),
        ProtoFormula::Conn(_, p, q) => {
            for_each_free_var(p, f);
            for_each_free_var(q, f);
        }
        ProtoFormula::Qua(_, _, p) => for_each_free_var(p, f),
    }
}

/// The `Foldable (ProtoAtom s)` traversal order (Atom.hs:129-136): `Action`
/// visits its time-point term before the fact's terms; the binary atoms visit
/// left then right; `Syntactic` holds no term of the folded type.
fn for_each_atom_term<T>(a: &ProtoAtom<Unit2, T>, f: &mut dyn FnMut(&T)) {
    match a {
        ProtoAtom::Action(t, fa) => {
            f(t);
            for t2 in fa.terms.iter() {
                f(t2);
            }
        }
        ProtoAtom::EqE(l, r) | ProtoAtom::Subterm(l, r) | ProtoAtom::Less(l, r) => {
            f(l);
            f(r);
        }
        ProtoAtom::Last(t) => f(t),
        ProtoAtom::Syntactic(_) => {}
    }
}

/// The `Functor (ProtoAtom s)` instance (Atom.hs:121-127), borrowing its input.
fn map_atom_terms<T, U>(
    a: &ProtoAtom<Unit2, T>,
    f: &mut dyn FnMut(&T) -> U,
) -> ProtoAtom<Unit2, U> {
    match a {
        ProtoAtom::Action(t, fa) => {
            let t_new = f(t);
            let fa_new = fa.map_ref(&mut *f);
            ProtoAtom::Action(t_new, fa_new)
        }
        ProtoAtom::EqE(l, r) => ProtoAtom::EqE(f(l), f(r)),
        ProtoAtom::Subterm(l, r) => ProtoAtom::Subterm(f(l), f(r)),
        ProtoAtom::Less(l, r) => ProtoAtom::Less(f(l), f(r)),
        ProtoAtom::Last(t) => ProtoAtom::Last(f(t)),
        ProtoAtom::Syntactic(_) => ProtoAtom::Syntactic(Unit2),
    }
}

/// The inner substitution of HS `quantify`, `mapLits (fmap (>>= subst i))`
/// applied to one atom term (Formula.hs:349-352):
/// replace the free occurrences of `x` by the De Bruijn index `i`, leaving
/// every other literal — including already-bound indices — untouched.
/// Applications are rebuilt with `f_app`, which re-normalises AC argument
/// order (`Bound` sorts before `Free`, so the order can change), exactly as
/// HS `mapLits` does.
fn subst_free_var(t: &BLNTerm, x: &LVar, i: u64) -> BLNTerm {
    match t {
        Term::Lit(Lit::Var(BVar::Free(v))) if v == x => {
            tamarin_term::vterm::var_term(BVar::Bound(i))
        }
        Term::Lit(_) => t.clone(),
        Term::App(sym, args) => {
            tamarin_term::term::f_app(*sym, args.iter().map(|a| subst_free_var(a, x, i)).collect())
        }
    }
}

/// HS `quantify x` (Formula.hs:347-352): turn the free variable `x` into a
/// bound one, using the De Bruijn index of the binder that is about to be put
/// in front of the formula.  The index counts the binders between the atom and
/// that new binder, threaded by HS `mapAtoms` (Formula.hs:266-270) over
/// `foldFormulaScope` (Formula.hs:158-173), whose `Qua` case recurses with
/// `succ i` (Formula.hs:173).
pub fn quantify(x: &LVar, fm: LNFormula) -> LNFormula {
    quantify_at(x, fm, 0)
}

fn quantify_at(x: &LVar, fm: LNFormula, i: u64) -> LNFormula {
    match fm {
        ProtoFormula::Atom(a) => {
            let mapped = map_atom_terms(&a, &mut |t| subst_free_var(t, x, i));
            ProtoFormula::Atom(mapped)
        }
        ProtoFormula::Tf(b) => ProtoFormula::Tf(b),
        ProtoFormula::Not(p) => ProtoFormula::Not(Box::new(quantify_at(x, *p, i))),
        ProtoFormula::Conn(c, p, q) => ProtoFormula::Conn(
            c,
            Box::new(quantify_at(x, *p, i)),
            Box::new(quantify_at(x, *q, i)),
        ),
        ProtoFormula::Qua(q, h, p) => ProtoFormula::Qua(q, h, Box::new(quantify_at(x, *p, i + 1))),
    }
}

/// HS `exists hint x` (Formula.hs:359-360): `Qua Ex hint . quantify x`.
pub fn exists_var(hint: (String, LSort), x: &LVar, fm: LNFormula) -> LNFormula {
    ProtoFormula::exists(hint, quantify(x, fm))
}

/// HS `forAll hint x` (Formula.hs:355-356): `Qua All hint . quantify x`.
pub fn for_all_var(hint: (String, LSort), x: &LVar, fm: LNFormula) -> LNFormula {
    ProtoFormula::for_all(hint, quantify(x, fm))
}

/// HS `existFormula` (Formula.hs:532-534): exists-quantify every free variable
/// of the formula, each under its own name/sort hint.  `frees` is sorted, and
/// the fold is a `foldl`, so the SMALLEST free variable ends up innermost.
pub fn exist_formula(fm: LNFormula) -> LNFormula {
    let vars = formula_frees(&fm);
    vars.into_iter().fold(fm, |acc, v| {
        exists_var((v.name.to_string(), v.sort), &v, acc)
    })
}

/// HS `forAllFormula` (Formula.hs:536-538): as [`exist_formula`], with
/// universal quantifiers.
pub fn for_all_formula(fm: LNFormula) -> LNFormula {
    let vars = formula_frees(&fm);
    vars.into_iter().fold(fm, |acc, v| {
        for_all_var((v.name.to_string(), v.sort), &v, acc)
    })
}

// NOTE: Haskell `mapAtoms` (Formula.hs:266-270) is
// `foldFormulaScope (\i a -> Ato $ f i a) ...`, i.e. its callback receives
// the De Bruijn binder-depth `i` (threaded via `go (succ i)` at each `Qua`,
// Formula.hs:173). The scope-aware machinery in the Rust port lives
// elsewhere (depth-threaded rewrites in `guarded_types.rs`, macro
// application in `macro_expand.rs::apply_macros_formula`), so no
// depth-blind `mapAtoms` mirror is provided here.

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    fn lftrue() -> LNFormula {
        ProtoFormula::ltrue()
    }
    fn lffalse() -> LNFormula {
        ProtoFormula::lfalse()
    }

    #[test]
    fn build_a_simple_formula() {
        // ∀ x:msg. true ∧ ¬false
        let body: LNFormula = lftrue().and(lffalse().not());
        let f: LNFormula = ProtoFormula::for_all(("x".into(), LSort::Msg), body);
        if let ProtoFormula::Qua(q, _, _) = f {
            assert_eq!(q, Quantifier::All);
        } else {
            panic!();
        }
    }

    #[test]
    fn implies_constructs_imp() {
        let f: LNFormula = lftrue().implies(lffalse());
        assert!(matches!(f, ProtoFormula::Conn(Connective::Imp, _, _)));
    }

    /// `existFormula` quantifies every free variable, and `quantify` turns its
    /// free occurrences into the new binder's De Bruijn index.
    #[test]
    fn exist_formula_binds_each_free_var() {
        use tamarin_term::vterm::var_term;

        let x = LVar::new("x", LSort::Msg, 0);
        let atom = ProtoAtom::EqE(var_term(BVar::Free(x)), var_term(BVar::Free(x)));
        let fm: LNFormula = ProtoFormula::Atom(atom);

        let ProtoFormula::Qua(q, hint, body) = exist_formula(fm) else {
            panic!("expected an existential quantifier around the atom");
        };
        assert_eq!(q, Quantifier::Ex);
        assert_eq!(hint, ("x".to_string(), LSort::Msg));
        let bound = ProtoAtom::EqE(var_term(BVar::Bound(0)), var_term(BVar::Bound(0)));
        assert_eq!(*body, ProtoFormula::Atom(bound));
    }

    /// The binder depth counts the quantifiers between the atom and the new
    /// binder (HS `foldFormulaScope`'s `go (succ i)`).
    #[test]
    fn quantify_uses_the_enclosing_binder_depth() {
        use tamarin_term::vterm::var_term;

        let x = LVar::new("x", LSort::Msg, 0);
        let atom = ProtoAtom::Last(var_term(BVar::Free(x)));
        // ∀ y. last(x) — one binder between the atom and the new one.
        let hint = ("y".to_string(), LSort::Node);
        let inner: LNFormula = ProtoFormula::for_all(hint, ProtoFormula::Atom(atom));
        let ProtoFormula::Qua(_, _, body) = quantify(&x, inner) else {
            panic!("expected the inner quantifier to survive quantify");
        };
        let bound = ProtoAtom::Last(var_term(BVar::Bound(1)));
        assert_eq!(*body, ProtoFormula::Atom(bound));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for Connective and Quantifier order.
    //
    // Theory/Model/Formula.hs:106-108: `data Connective = And | Or | Imp | Iff`
    // Theory/Model/Formula.hs:110-112: `data Quantifier = All | Ex`
    //
    // These orders matter for any BTreeMap<Connective,_> iteration and for
    // Haskell-faithful structural comparison / round-tripping of formulas.
    // =========================================================================

    /// `Connective` Ord — `And < Or < Imp < Iff` from Theory/Model/Formula.hs:107.
    #[test]
    fn connective_ord_matches_haskell_declaration() {
        assert!(Connective::And < Connective::Or);
        assert!(Connective::Or < Connective::Imp);
        assert!(Connective::Imp < Connective::Iff);
    }

    /// `Quantifier` Ord — `All < Ex` from Theory/Model/Formula.hs:111.
    ///
    /// The All<Ex order is required for Haskell-faithful structural /
    /// BTreeMap comparisons and round-tripping of formulas, matching the
    /// `data Quantifier = All | Ex` declaration order. (The guarded-formula
    /// simplifier does not iterate quantifiers in this order; it
    /// pattern-matches structurally — see `simplify_guarded_with`.)
    #[test]
    fn quantifier_ord_matches_haskell_declaration() {
        assert!(
            Quantifier::All < Quantifier::Ex,
            "All MUST sort before Ex (Theory/Model/Formula.hs:111)"
        );
    }
}
