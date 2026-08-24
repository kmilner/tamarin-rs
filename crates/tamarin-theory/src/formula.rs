// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Formula` from
//! `lib/theory/src/Theory/Model/Formula.hs`: the formula data type with its
//! `LNFormula`/`SyntacticLNFormula` instances, the basic builders, the
//! sugar traversal ([`SugarTerms`]), free variables ([`formula_frees`]), the
//! quantifier-introduction helpers (`quantify`, `exists`, `forAll`,
//! `existFormula`, `forAllFormula`), the sugar-stripping [`to_lnformula`],
//! the closing of the parser AST into a [`SyntacticLNFormula`]
//! ([`from_parser`], which HS does inside its formula parser,
//! `Theory/Text/Parser/Formula.hs`) and the opening of a bound term against
//! a binder scope (`open_bound_term`, the substitution step of HS
//! `openFormula`, used by the printer).
//!
//! The representation is locally nameless: bound variables are
//! `BVar::Bound(de_bruijn_idx)`, free variables are `Free(v)`.
//!
//! The pure transforms (`nnf`, `pullquants`, `prenex`, `pnf`,
//! `simplifyFormula`) are not ported on this type. Formula.hs's
//! `shiftFreeIndices`/`simplifyFormula` (plus Generation.hs's
//! `pullQuantifiers`/`mergeQuantifiers`, and a second `quantify`) are ported
//! in `tamarin-accountability/src/formula.rs`, over a parallel
//! locally-nameless type (`Fm`) whose leaves are `guarded_types` parser-AST
//! atoms rather than this module's real-term `ProtoAtom`s. (The
//! guarded-formula simplifier `simplifyGuarded` is a different HS function,
//! ported as `simplify_guarded_with` in guarded.rs.)

use crate::atom::{to_atom, ProtoAtom, SyntacticAtom, SyntacticSugar, Unit2};
use crate::elaborate::{fact_to_lnfact, term_to_lnterm, ElabError};
use crate::fact::Fact;
use crate::predicate::smaller_fact;
use tamarin_parser::ast as p;
use tamarin_term::lterm::{BVar, HasFrees, LNTerm, LSort, LVar, Name};
use tamarin_term::term::map_lits;
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
pub type LFormula<C> = Formula<(String, LSort), C, LVar>;
pub type LNFormula = LFormula<Name>;

/// The term type of an [`LNFormula`] atom: variables are `BVar`s, so a term
/// mentions both the enclosing binders' De Bruijn indices and free `LVar`s.
pub type BLNTerm = VTerm<Name, BVar<LVar>>;

/// [`LNFormula`] with its sugar type left open: `Unit2` gives `LNFormula`,
/// `SyntacticSugar` gives [`SyntacticLNFormula`].
pub type LNProtoFormula<S> = ProtoFormula<S, (String, LSort), Name, LVar>;

/// HS `SyntacticLNFormula` (Theory/Model/Formula.hs:263): an [`LNFormula`]
/// whose atoms may carry the parser's `Pred` sugar, with the sugar's fact
/// over the same `BVar` terms as the plain atoms (Atom.hs:78-87).
pub type SyntacticLNFormula = LNProtoFormula<SyntacticSugar<BLNTerm>>;

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
// Sugar traversal (Atom.hs:87-94), free variables (Theory/Model/Formula.hs:321-333),
// quantifier introduction (Theory/Model/Formula.hs:347-360), the whole-formula
// closures `existFormula` / `forAllFormula` (Theory/Model/Formula.hs:532-538)
// and `toLNFormula` (Theory/Model/Formula.hs:369-373).
// =============================================================================

/// The `Foldable` and `Functor` instances of a sugar type, which both
/// `SyntacticSugar` and `Unit2` derive (Atom.hs:87-94) and which
/// `ProtoAtom`'s own instances descend into at `Syntactic` (Atom.hs:121-136).
/// The map keeps the term type, as every caller in this module does.
pub trait SugarTerms<T>: Sized {
    /// Visit every term held by the sugar, left to right.
    fn for_each_term(&self, f: &mut dyn FnMut(&T));
    /// Rebuild the sugar with every held term mapped.
    fn map_terms(&self, f: &mut dyn FnMut(&T) -> T) -> Self;
}

impl<T> SugarTerms<T> for Unit2 {
    fn for_each_term(&self, _f: &mut dyn FnMut(&T)) {}
    fn map_terms(&self, _f: &mut dyn FnMut(&T) -> T) -> Self {
        Unit2
    }
}

impl<T> SugarTerms<T> for SyntacticSugar<T> {
    fn for_each_term(&self, f: &mut dyn FnMut(&T)) {
        let SyntacticSugar::Pred(fa) = self;
        fa.terms.iter().for_each(f);
    }
    fn map_terms(&self, f: &mut dyn FnMut(&T) -> T) -> Self {
        let SyntacticSugar::Pred(fa) = self;
        SyntacticSugar::Pred(fa.map_ref(f))
    }
}

/// HS `frees` on an `LNFormula` or `SyntacticLNFormula`, i.e. their `HasFrees`
/// instances (Theory/Model/Formula.hs:321-333): `foldFrees f = foldMap (foldFrees f)`,
/// where the `Foldable (ProtoFormula ...)` instance (Theory/Model/Formula.hs:197-199)
/// descends into the atoms' terms, sugar included, and the `Foldable BVar`
/// instance yields only `Free` variables — so bound De Bruijn indices
/// contribute nothing and binder hints are ignored. Deduplicated and sorted,
/// like [`tamarin_term::lterm::frees`].
pub fn formula_frees<S: SugarTerms<BLNTerm>>(fm: &LNProtoFormula<S>) -> Vec<LVar> {
    let mut out = Vec::new();
    for_each_free_var(fm, &mut |v| out.push(*v));
    out.sort();
    out.dedup();
    out
}

fn for_each_free_var<S: SugarTerms<BLNTerm>>(fm: &LNProtoFormula<S>, f: &mut dyn FnMut(&LVar)) {
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
/// left then right; `Syntactic` visits the sugar's terms.
fn for_each_atom_term<S: SugarTerms<T>, T>(a: &ProtoAtom<S, T>, f: &mut dyn FnMut(&T)) {
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
        ProtoAtom::Syntactic(s) => s.for_each_term(f),
    }
}

/// The `Functor (ProtoAtom s)` instance (Atom.hs:121-127) with the term type
/// unchanged, borrowing its input.
fn map_atom_terms<S: SugarTerms<T>, T>(
    a: &ProtoAtom<S, T>,
    f: &mut dyn FnMut(&T) -> T,
) -> ProtoAtom<S, T> {
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
        ProtoAtom::Syntactic(s) => ProtoAtom::Syntactic(s.map_terms(f)),
    }
}

/// HS `quantify x` (Theory/Model/Formula.hs:347-352): turn the free variable `x` into a
/// bound one, using the De Bruijn index of the binder that is about to be put
/// in front of the formula.  The index counts the binders between the atom and
/// that new binder, threaded by HS `mapAtoms` (Theory/Model/Formula.hs:266-270) over
/// `foldFormulaScope` (Theory/Model/Formula.hs:158-173), whose `Qua` case recurses with
/// `succ i` (Theory/Model/Formula.hs:173).
pub fn quantify<S: SugarTerms<BLNTerm>>(x: &LVar, fm: LNProtoFormula<S>) -> LNProtoFormula<S> {
    quantify_at(x, fm, 0)
}

fn quantify_at<S: SugarTerms<BLNTerm>>(
    x: &LVar,
    fm: LNProtoFormula<S>,
    i: u64,
) -> LNProtoFormula<S> {
    match fm {
        ProtoFormula::Atom(a) => {
            // `mapLits (fmap (>>= subst i))` (Theory/Model/Formula.hs:349-352): the
            // free occurrences of `x` become the index `i`; constants and
            // already-bound indices are untouched, and the `f_app` rebuild
            // inside `map_lits` re-sorts AC arguments (`Bound` sorts before
            // `Free`).
            let mapped = map_atom_terms(&a, &mut |t| {
                map_lits(t, &mut |l| match l {
                    Lit::Var(BVar::Free(v)) if v == x => Lit::Var(BVar::Bound(i)),
                    other => other.clone(),
                })
            });
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

/// HS `exists hint x` (Theory/Model/Formula.hs:359-360): `Qua Ex hint . quantify x`.
pub fn exists_var<S: SugarTerms<BLNTerm>>(
    hint: (String, LSort),
    x: &LVar,
    fm: LNProtoFormula<S>,
) -> LNProtoFormula<S> {
    ProtoFormula::exists(hint, quantify(x, fm))
}

/// HS `forAll hint x` (Theory/Model/Formula.hs:355-356): `Qua All hint . quantify x`.
pub fn for_all_var<S: SugarTerms<BLNTerm>>(
    hint: (String, LSort),
    x: &LVar,
    fm: LNProtoFormula<S>,
) -> LNProtoFormula<S> {
    ProtoFormula::for_all(hint, quantify(x, fm))
}

/// HS `existFormula` (Theory/Model/Formula.hs:532-534): exists-quantify every free variable
/// of the formula, each under its own name/sort hint.  `frees` is sorted, and
/// the fold is a `foldl`, so the SMALLEST free variable ends up innermost.
pub fn exist_formula(fm: LNFormula) -> LNFormula {
    let vars = formula_frees(&fm);
    vars.into_iter().fold(fm, |acc, v| {
        exists_var((v.name.to_string(), v.sort), &v, acc)
    })
}

/// HS `forAllFormula` (Theory/Model/Formula.hs:536-538): as [`exist_formula`], with
/// universal quantifiers.
pub fn for_all_formula(fm: LNFormula) -> LNFormula {
    let vars = formula_frees(&fm);
    vars.into_iter().fold(fm, |acc, v| {
        for_all_var((v.name.to_string(), v.sort), &v, acc)
    })
}

/// HS `toLNFormula` (Theory/Model/Formula.hs:369-373): strip the sugar with
/// `toAtom` (Atom.hs:200-206); `None` if any atom carries sugar.
pub fn to_lnformula(fm: &SyntacticLNFormula) -> Option<LNFormula> {
    match fm {
        ProtoFormula::Atom(ProtoAtom::Syntactic(_)) => None,
        ProtoFormula::Atom(a) => Some(ProtoFormula::Atom(to_atom(a.clone()))),
        ProtoFormula::Tf(b) => Some(ProtoFormula::Tf(*b)),
        ProtoFormula::Not(p) => Some(ProtoFormula::Not(Box::new(to_lnformula(p)?))),
        ProtoFormula::Conn(c, p, q) => Some(ProtoFormula::Conn(
            *c,
            Box::new(to_lnformula(p)?),
            Box::new(to_lnformula(q)?),
        )),
        ProtoFormula::Qua(q, h, p) => {
            Some(ProtoFormula::Qua(*q, h.clone(), Box::new(to_lnformula(p)?)))
        }
    }
}

// =============================================================================
// Closing the parser AST (Theory/Text/Parser/Formula.hs:44-77) and opening a
// bound term for display (Theory/Model/Formula.hs:274-291, :481-484).
// =============================================================================

/// Build a [`SyntacticLNFormula`] from the parser's formula AST the way HS's
/// formula parser builds one while parsing
/// (Theory/Text/Parser/Formula.hs:44-77): every atom is lifted with all of
/// its variables free (`blatom`'s `fmap (fmapTerm (fmap Free))`,
/// Theory/Text/Parser/Formula.hs:44-45), and a quantifier closes its binders
/// with `foldr (hinted q) f vs` (Theory/Text/Parser/Formula.hs:73-77) over
/// `forAll`/`exists` (Theory/Model/Formula.hs:355-360), so the last binder
/// of the list is the innermost one.
///
/// Variable sorts come from the parser, which stamps them by syntactic
/// position as HS's `msgvar`/`nodevar` do (Token.hs:440-448), and reach the
/// `LVar` through `elaborate::sort_of`.  A
/// binder closes exactly the occurrences equal to its `LVar` in name, sort
/// and index (HS `quantify`'s `v == x`, Theory/Model/Formula.hs:350-352), so
/// `Ex ~k. Made(k)` leaves the message-sorted `k` free.  Terms go through
/// [`term_to_lnterm`], which reads the thread-local user-function bundle and
/// turns a bare nullary symbol into its application before any binder is
/// considered (HS `nullaryApp`, Theory/Text/Parser/Term.hs:158-163).  A
/// `(<)` atom becomes the `Smaller` predicate (`smallerp`,
/// Theory/Text/Parser/Formula.hs:30-38); a SAPIC `=t` pattern term, which
/// `term_to_lnterm` rejects, is an [`ElabError`].
pub fn from_parser(f: &p::Formula) -> Result<SyntacticLNFormula, ElabError> {
    match f {
        p::Formula::True => Ok(ProtoFormula::Tf(true)),
        p::Formula::False => Ok(ProtoFormula::Tf(false)),
        p::Formula::Atom(a) => Ok(ProtoFormula::Atom(atom_from_parser(a)?)),
        p::Formula::Not(q) => Ok(from_parser(q)?.not()),
        p::Formula::And(l, r) => Ok(from_parser(l)?.and(from_parser(r)?)),
        p::Formula::Or(l, r) => Ok(from_parser(l)?.or(from_parser(r)?)),
        p::Formula::Implies(l, r) => Ok(from_parser(l)?.implies(from_parser(r)?)),
        p::Formula::Iff(l, r) => Ok(from_parser(l)?.iff(from_parser(r)?)),
        p::Formula::Forall(vs, body) => Ok(close_binders(for_all_var, vs, from_parser(body)?)),
        p::Formula::Exists(vs, body) => Ok(close_binders(exists_var, vs, from_parser(body)?)),
    }
}

/// HS `foldr (hinted q) f vs` (Theory/Text/Parser/Formula.hs:73-77): close
/// the binders from the last to the first, each with the hint that `hinted`
/// (Theory/Model/Formula.hs:364-365) reads off the binder's `LVar`
/// (Theory/Model/Formula.hs:227-228).
fn close_binders(
    q: fn((String, LSort), &LVar, SyntacticLNFormula) -> SyntacticLNFormula,
    vs: &[p::VarSpec],
    body: SyntacticLNFormula,
) -> SyntacticLNFormula {
    vs.iter().rev().fold(body, |acc, v| {
        let x = LVar::new(&v.name, v.sort, v.idx);
        q((x.name.to_string(), x.sort), &x, acc)
    })
}

/// The atom alternatives of HS `blatom` (Theory/Text/Parser/Formula.hs:45-57).
fn atom_from_parser(a: &p::Atom) -> Result<SyntacticAtom<BLNTerm>, ElabError> {
    Ok(match a {
        p::Atom::Eq(l, r) => ProtoAtom::EqE(free_term(l)?, free_term(r)?),
        p::Atom::Subterm(l, r) => ProtoAtom::Subterm(free_term(l)?, free_term(r)?),
        p::Atom::Less(l, r) => ProtoAtom::Less(free_term(l)?, free_term(r)?),
        p::Atom::Action(fa, t) => ProtoAtom::Action(free_term(t)?, free_fact(fa)?),
        p::Atom::Last(t) => ProtoAtom::Last(free_term(t)?),
        p::Atom::Pred(fa) => ProtoAtom::Syntactic(SyntacticSugar::Pred(free_fact(fa)?)),
        p::Atom::LessMset(l, r) => ProtoAtom::Syntactic(SyntacticSugar::Pred(smaller_fact(
            free_term(l)?,
            free_term(r)?,
        ))),
    })
}

/// `fmapTerm (fmap Free)` (Theory/Text/Parser/Formula.hs:45): every variable
/// of the term as a free `BVar`.  The literal order is unchanged, so the
/// `f_app` rebuild inside [`map_lits`] keeps the AC argument order.
fn lift_free(t: &LNTerm) -> BLNTerm {
    map_lits(t, &mut |l| match l {
        Lit::Con(c) => Lit::Con(*c),
        Lit::Var(v) => Lit::Var(BVar::Free(*v)),
    })
}

fn free_term(t: &p::Term) -> Result<BLNTerm, ElabError> {
    term_to_lnterm(t)
        .map(|t| lift_free(&t))
        .ok_or_else(|| ElabError {
            message: "could not elaborate term in formula".to_string(),
        })
}

fn free_fact(fa: &p::Fact) -> Result<Fact<BLNTerm>, ElabError> {
    Ok(fact_to_lnfact(fa)?.map_ref(lift_free))
}

/// Replace every bound index of `t` by the binder it refers to, given the
/// enclosing binders innermost-last in `scope`: `Bound(0)` is the innermost
/// binder, `Bound(i)` the one `i` binders further out.  This is HS
/// `openFormula`'s `mapLits (subst x i)` (Theory/Model/Formula.hs:274-291)
/// applied once per enclosing binder, followed by `extractFree`
/// (Theory/Model/Formula.hs:481-484), whose error message is kept for an
/// index past the scope.  The rebuild through [`map_lits`] re-sorts AC
/// arguments under the opened `LVar`s, as HS's `fApp` does.
pub(crate) fn open_bound_term(t: &BLNTerm, scope: &[LVar]) -> LNTerm {
    map_lits(t, &mut |l| match l {
        Lit::Con(c) => Lit::Con(*c),
        Lit::Var(BVar::Free(v)) => Lit::Var(*v),
        Lit::Var(BVar::Bound(i)) => match scope.iter().rev().nth(*i as usize) {
            Some(v) => Lit::Var(*v),
            None => panic!("prettyFormula: illegal bound variable '{i}'"),
        },
    })
}

// NOTE: Haskell `mapAtoms` (Theory/Model/Formula.hs:266-270) is
// `foldFormulaScope (\i a -> Ato $ f i a) ...`, i.e. its callback receives
// the De Bruijn binder-depth `i` (threaded via `go (succ i)` at each `Qua`,
// Theory/Model/Formula.hs:173). The scope-aware machinery in the Rust port lives
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

    /// Each builder tags the node with its own connective or quantifier.  The
    /// four `Conn` builders are the same in every other way, and so are the
    /// two `Qua` builders.  So the shape alone does not show a copy-paste
    /// mistake between them.
    #[test]
    fn builders_tag_their_own_connective_and_quantifier() {
        let hint = || ("x".to_string(), LSort::Msg);
        let cases: [(LNFormula, Connective); 4] = [
            (lftrue().and(lffalse()), Connective::And),
            (lftrue().or(lffalse()), Connective::Or),
            (lftrue().implies(lffalse()), Connective::Imp),
            (lftrue().iff(lffalse()), Connective::Iff),
        ];
        for (f, want) in cases {
            match f {
                ProtoFormula::Conn(c, l, r) => {
                    assert_eq!(c, want);
                    assert_eq!(
                        (*l, *r),
                        (lftrue(), lffalse()),
                        "operand order for {want:?}"
                    );
                }
                other => panic!("expected Conn({want:?}), got {other:?}"),
            }
        }
        assert!(matches!(lftrue().not(), ProtoFormula::Not(b) if *b == lftrue()));
        let all: LNFormula = ProtoFormula::for_all(hint(), lftrue());
        assert!(matches!(all, ProtoFormula::Qua(Quantifier::All, h, _) if h == hint()));
        let ex: LNFormula = ProtoFormula::exists(hint(), lftrue());
        assert!(matches!(ex, ProtoFormula::Qua(Quantifier::Ex, h, _) if h == hint()));
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

    fn x_var() -> LVar {
        LVar::new("x", LSort::Msg, 0)
    }

    /// `Pred(F(x))` as a sugared atom over `BVar` terms.
    fn pred_atom(arg: BVar<LVar>) -> SyntacticAtom<BLNTerm> {
        use crate::fact::{Fact, FactTag};
        use tamarin_term::vterm::var_term;

        ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(
            FactTag::Term,
            vec![var_term(arg)],
        )))
    }

    /// `frees` descends into the sugar's fact (the `Foldable SyntacticSugar`
    /// instance), so a variable that occurs only inside a `Pred` is free.
    #[test]
    fn formula_frees_includes_pred_terms() {
        let fm: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Free(x_var())));
        assert_eq!(formula_frees(&fm), vec![x_var()]);
        let closed: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Bound(0)));
        assert_eq!(formula_frees(&closed), Vec::<LVar>::new());
    }

    /// `quantify` maps through the sugar (the `Functor SyntacticSugar`
    /// instance), so `exists` closes a variable that occurs inside a `Pred`.
    #[test]
    fn quantify_closes_pred_terms() {
        let hint = ("x".to_string(), LSort::Msg);
        let fm: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Free(x_var())));
        let want: SyntacticLNFormula =
            ProtoFormula::exists(hint.clone(), ProtoFormula::Atom(pred_atom(BVar::Bound(0))));
        assert_eq!(exists_var(hint, &x_var(), fm), want);
    }

    /// `toLNFormula` is `Nothing` while any atom still carries sugar, however
    /// deep it sits.
    #[test]
    fn to_lnformula_rejects_sugar() {
        let pred: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Free(x_var())));
        let fm: SyntacticLNFormula = ProtoFormula::for_all(
            ("x".to_string(), LSort::Msg),
            ProtoFormula::ltrue().and(pred.not()),
        );
        assert_eq!(to_lnformula(&fm), None);
    }

    /// `All #x. (x < y) ==> not(last(x))` over any sugar type: no atom uses
    /// the sugar, so the same construction types as both formula forms.
    fn plain_formula<S>() -> LNProtoFormula<S> {
        use tamarin_term::vterm::var_term;

        let less = ProtoAtom::Less(var_term(BVar::Bound(0)), var_term(BVar::Free(x_var())));
        let last = ProtoAtom::Last(var_term(BVar::Bound(0)));
        ProtoFormula::for_all(
            ("x".to_string(), LSort::Node),
            ProtoFormula::Atom(less).implies(ProtoFormula::Atom(last).not()),
        )
    }

    /// Plain atoms cross `toLNFormula` unchanged, only their sugar type
    /// becomes `Unit2`; every formula constructor above them is kept.
    #[test]
    fn to_lnformula_strips_unit2_atoms() {
        let fm: SyntacticLNFormula = plain_formula();
        let want: LNFormula = plain_formula();
        assert_eq!(to_lnformula(&fm), Some(want));
    }

    // =========================================================================
    // from_parser / open_bound_term
    // =========================================================================

    use crate::fact::{FactTag, Multiplicity};
    use tamarin_parser::parser::{parse_formula_str, parse_theory};
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::intern::intern_str;
    use tamarin_term::term::{f_app_ac, f_app_no_eq, Term};
    use tamarin_term::vterm::var_term;

    fn parsed(src: &str) -> SyntacticLNFormula {
        from_parser(&parse_formula_str(src).unwrap()).unwrap()
    }

    fn free(name: &str, sort: LSort, idx: u64) -> BLNTerm {
        var_term(BVar::Free(LVar::new(name, sort, idx)))
    }

    fn bound(i: u64) -> BLNTerm {
        var_term(BVar::Bound(i))
    }

    fn proto_fact<T>(name: &str, args: Vec<T>) -> Fact<T> {
        Fact::new(
            FactTag::Proto(Multiplicity::Linear, intern_str(name), args.len()),
            args,
        )
    }

    fn pred(name: &str, args: Vec<BLNTerm>) -> SyntacticLNFormula {
        ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(proto_fact(
            name, args,
        ))))
    }

    fn hint(name: &str, sort: LSort) -> (String, LSort) {
        (name.to_string(), sort)
    }

    fn parser_var(name: &str, sort: LSort) -> p::Term {
        p::Term::Var(p::VarSpec {
            name: name.to_string(),
            idx: 0,
            sort,
            typ: None,
        })
    }

    /// `foldr (hinted q) f vs` puts the last binder innermost, so the
    /// innermost binder is `Bound(0)` at the atom and the `@` operand stays a
    /// free `Node` variable.
    #[test]
    fn from_parser_nests_binders_innermost_zero() {
        let want = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::exists(
                hint("y", LSort::Msg),
                ProtoFormula::Atom(ProtoAtom::Action(
                    free("i", LSort::Node, 0),
                    proto_fact("P", vec![bound(1), bound(0)]),
                )),
            ),
        );
        assert_eq!(parsed("All x. Ex y. P(x, y) @ #i"), want);
    }

    /// The `@` operand is `Node` whatever its hint, so it is closed by the
    /// `#k` binder, while the `k` inside the fact is `Msg` and closed by the
    /// message binder of the same name.
    #[test]
    fn from_parser_resolves_sort_by_position() {
        let pair = f_app_no_eq(
            tamarin_term::function_symbols::pair_sym(),
            vec![bound(1), bound(2)],
        );
        let want = ProtoFormula::exists(
            hint("k", LSort::Msg),
            ProtoFormula::exists(
                hint("m", LSort::Msg),
                ProtoFormula::exists(
                    hint("k", LSort::Node),
                    ProtoFormula::Atom(ProtoAtom::Action(bound(0), proto_fact("G", vec![pair]))),
                ),
            ),
        );
        assert_eq!(parsed("Ex k m #k. G(<m, k>) @ k"), want);
    }

    /// `#k = l` is HS's node equality: the bare `l` is a `nodevar`, so the
    /// `#l` binder closes it, while a message-term equality `k = l` keeps
    /// the bare `l` as `Msg` (probe `S0_bare_name_under_node_binder.spthy`).
    #[test]
    fn from_parser_node_equality_binds_bare_right_operand() {
        let want = ProtoFormula::for_all(
            hint("k", LSort::Node),
            ProtoFormula::for_all(
                hint("l", LSort::Node),
                ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
            ),
        );
        assert_eq!(parsed("All #k #l. #k = l"), want);
        assert_eq!(parsed("All #k #l. k:node = l"), want);
        let msg = ProtoFormula::for_all(
            hint("l", LSort::Node),
            ProtoFormula::Atom(ProtoAtom::EqE(
                free("k", LSort::Msg, 0),
                free("l", LSort::Msg, 0),
            )),
        );
        assert_eq!(parsed("All #l. k = l"), msg);
    }

    /// Closing compares the whole `LVar`: a `~k` binder does not capture the
    /// message-sorted `k` of the body.
    #[test]
    fn from_parser_leaves_other_sorted_name_free() {
        let want = ProtoFormula::exists(
            hint("k", LSort::Fresh),
            pred("Made", vec![free("k", LSort::Msg, 0)]),
        );
        assert_eq!(parsed("Ex ~k. Made(k)"), want);
    }

    /// The inner binder closes the occurrence first, so the outer binder of
    /// the same name finds nothing left to close.
    #[test]
    fn from_parser_inner_binder_shadows() {
        let want = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::for_all(hint("x", LSort::Msg), pred("P", vec![bound(0)])),
        );
        assert_eq!(parsed("All x. All x. P(x)"), want);
    }

    /// A bare identifier that names a nullary user symbol is that symbol's
    /// application (HS `nullaryApp`), so a binder of the same name closes
    /// nothing.
    #[test]
    fn from_parser_keeps_nullary_symbol_constant() {
        let thy = parse_theory("theory T begin\nfunctions: zero/0\nend", &[]).unwrap();
        let _guard = crate::elaborate::set_user_funs_for_theory(&thy);

        let ProtoFormula::Qua(Quantifier::All, h, body) = parsed("All zero. P(zero)") else {
            panic!("expected a universal quantifier");
        };
        assert_eq!(h, hint("zero", LSort::Msg));
        let ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(fa))) = *body else {
            panic!("expected a predicate atom");
        };
        match &fa.terms[..] {
            [Term::App(FunSym::NoEq(sym), args)] => {
                assert_eq!(sym.name, b"zero");
                assert!(args.is_empty());
            }
            other => panic!("expected the nullary application, got {other:?}"),
        }
    }

    /// `t (<) t` is the `Smaller` predicate (HS `smallerp`).
    #[test]
    fn from_parser_less_mset_is_smaller_pred() {
        let f = p::Formula::Atom(p::Atom::LessMset(
            parser_var("x", LSort::Msg),
            parser_var("y", LSort::Msg),
        ));
        let want = ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(smaller_fact(
            free("x", LSort::Msg, 0),
            free("y", LSort::Msg, 0),
        ))));
        assert_eq!(from_parser(&f).unwrap(), want);
    }

    /// A SAPIC `=t` pattern has no `LNTerm` form.
    #[test]
    fn from_parser_rejects_pat_match() {
        let pat = p::Term::PatMatch(Box::new(parser_var("x", LSort::Msg)));
        let in_term = p::Formula::Atom(p::Atom::Eq(pat.clone(), parser_var("y", LSort::Msg)));
        let err = from_parser(&in_term).unwrap_err();
        assert_eq!(err.message, "could not elaborate term in formula");
        let in_fact = p::Formula::Atom(p::Atom::Pred(p::Fact {
            persistent: false,
            name: "F".to_string(),
            args: vec![pat],
            annotations: Vec::new(),
        }));
        assert!(from_parser(&in_fact).is_err());
    }

    /// Opening against the binders that `quantify` closed gives the original
    /// term back, AC argument order included.
    #[test]
    fn open_bound_term_round_trips_quantify() {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let z = LVar::new("z", LSort::Msg, 0);
        let original: LNTerm = f_app_ac(AcSym::Mult, vec![var_term(x), var_term(y), var_term(z)]);
        let lifted = lift_free(&original);
        let fm: LNFormula = ProtoFormula::Atom(ProtoAtom::Last(lifted));
        // Outer binder `y`, inner binder `x`: `x` is `Bound(0)`, `y` `Bound(1)`.
        let closed = for_all_var(
            (y.name.to_string(), y.sort),
            &y,
            for_all_var((x.name.to_string(), x.sort), &x, fm),
        );
        let ProtoFormula::Qua(_, _, inner) = closed else {
            panic!("expected the outer quantifier");
        };
        let ProtoFormula::Qua(_, _, body) = *inner else {
            panic!("expected the inner quantifier");
        };
        let ProtoFormula::Atom(ProtoAtom::Last(term)) = *body else {
            panic!("expected the atom");
        };
        assert_eq!(
            term,
            f_app_ac(
                AcSym::Mult,
                vec![bound(0), bound(1), lift_free(&var_term(z))]
            )
        );
        assert_eq!(open_bound_term(&term, &[y, x]), original);
    }

    /// An index past the scope is HS `extractFree`'s error.
    #[test]
    #[should_panic(expected = "prettyFormula: illegal bound variable '1'")]
    fn open_bound_term_panics_past_scope() {
        let x = LVar::new("x", LSort::Msg, 0);
        open_bound_term(&bound(1), &[x]);
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
