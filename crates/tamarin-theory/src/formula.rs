// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Formula` from
//! `lib/theory/src/Theory/Model/Formula.hs`: the formula data type with its
//! `LNFormula`/`SyntacticLNFormula` instances, the basic builders, free
//! variables ([`formula_frees`]), the quantifier-introduction helpers (`quantify`, `exists`, `forAll`), the
//! De Bruijn lift [`shift_free_indices`], the sugar-stripping
//! [`to_lnformula`], the closing of the parser AST into a
//! [`SyntacticLNFormula`]
//! ([`from_parser`], which HS does inside its formula parser,
//! `Theory/Text/Parser/Formula.hs`), the opening of a bound term against a
//! binder scope ([`open_bound_term`], the substitution step of HS
//! `openFormula`, used by the printer) and the opening of a whole quantifier
//! prefix ([`open_formula`], [`open_formula_prefix`]).
//!
//! The representation is locally nameless: bound variables are
//! `BVar::Bound(de_bruijn_idx)`, free variables are `Free(v)`.
//!
//! The pure transforms `nnf`, `pullquants`, `prenex` and `pnf` are not
//! ported on this type. `simplifyFormula`, together with Generation.hs's
//! `pullQuantifiers`/`mergeQuantifiers` that call it, is ported in
//! `tamarin-accountability/src/generation.rs` beside its only caller. (The
//! guarded-formula simplifier `simplifyGuarded` is a different HS function,
//! ported as `simplify_guarded_with` in guarded.rs.)

use crate::atom::{
    collect_atom_terms, fold_atom, map_atom, to_atom, MapSugar, ProtoAtom, SugarTerms,
    SyntacticAtom, SyntacticSugar, Unit2,
};
use crate::elaborate::{
    fact_to_lnfact, fact_to_sapic_fact, term_to_lnterm, term_to_sapic_term, varspec_to_lvar,
    varspec_to_sapic, ElabError,
};
use crate::fact::Fact;
use crate::predicate::smaller_fact;
use crate::sapic::{default_sapic_node_type, SapicFormula, SapicLNFact, SapicLVar, SapicTerm};
use tamarin_parser::ast as p;
use tamarin_term::lterm::{fresh_lvar, BVar, LNTerm, LSort, LVar, Name};
use tamarin_term::macro_expand::{apply_macros, ln_macros_to_bn_macros, LNMacro};
use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::subst::{apply_bvar, apply_bvterm, Subst};
use tamarin_term::term::{map_lits, Term};
use tamarin_term::vterm::{var_term, Lit, VTerm};
use tamarin_utils::fresh::PreciseFreshState;

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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
pub type LNFormula = Formula<(String, LSort), Name, LVar>;

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

/// HS `SyntacticNFormula v` (Theory/Model/Formula.hs:264): a
/// [`SyntacticLNFormula`] over a free-variable type of the caller's choice.
pub type SyntacticNFormula<V> =
    ProtoFormula<SyntacticSugar<VTerm<Name, BVar<V>>>, (String, LSort), Name, V>;

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
// quantifier introduction (Theory/Model/Formula.hs:347-360) and `toLNFormula`
// (Theory/Model/Formula.hs:369-373).
// =============================================================================

/// HS `frees` on a formula: its `HasFrees` instance
/// (Theory/Model/Formula.hs:321-333) at `V = LVar`, and HS `freesSapicTerm`
/// (Theory/Sapic/Term.hs:131-132) at a variable type `HasFrees` does not
/// cover.  The `Foldable (ProtoFormula ...)` instance
/// (Theory/Model/Formula.hs:197-199) descends into the atoms' terms, sugar
/// included, and the `Foldable BVar` instance yields only `Free` variables —
/// so bound De Bruijn indices contribute nothing and binder hints are
/// ignored. Deduplicated and sorted, like [`tamarin_term::lterm::frees`].
pub fn formula_frees<S, C, V>(fm: &ProtoFormula<S, (String, LSort), C, V>) -> Vec<V>
where
    S: SugarTerms<VTerm<C, BVar<V>>>,
    V: Ord + Clone,
{
    let mut out = formula_frees_list(fm);
    out.sort();
    out.dedup();
    out
}

/// HS `freesList` (Term/LTerm.hs:605-608) at the same instances
/// [`formula_frees`] uses: the free variables in the order the `Foldable`
/// traversal yields them, duplicates kept. HS `frees = sortednub . freesList`
/// (Term/LTerm.hs:610-614) is [`formula_frees`]; callers that number
/// variables by first occurrence need this list instead.
pub fn formula_frees_list<S, C, V>(fm: &ProtoFormula<S, (String, LSort), C, V>) -> Vec<V>
where
    S: SugarTerms<VTerm<C, BVar<V>>>,
    V: Clone,
{
    let mut out = Vec::new();
    for_each_free_var(fm, &mut |v| out.push(v.clone()));
    out
}

fn for_each_free_var<S, C, V>(fm: &ProtoFormula<S, (String, LSort), C, V>, f: &mut dyn FnMut(&V))
where
    S: SugarTerms<VTerm<C, BVar<V>>>,
{
    for_each_formula_term(fm, &mut |t| for_each_free_term_var(t, &mut *f));
}

/// The free variables of one term in literal order — HS `freesSapicTerm =
/// foldMap $ foldMap (: [])` (Theory/Sapic/Term.hs:131-132), whose inner
/// `foldMap` is the `Foldable BVar` instance and so skips a bound index.
fn for_each_free_term_var<C, V>(t: &VTerm<C, BVar<V>>, f: &mut dyn FnMut(&V)) {
    match t {
        Term::Lit(Lit::Var(BVar::Free(v))) => f(v),
        Term::Lit(_) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                for_each_free_term_var(a, f);
            }
        }
    }
}

/// Every term of every atom, in the order the `Foldable (ProtoFormula syn s c)`
/// instance folds them (Theory/Model/Formula.hs:197-199).
pub(crate) fn for_each_formula_term<S, C, V>(
    fm: &ProtoFormula<S, (String, LSort), C, V>,
    f: &mut dyn FnMut(&VTerm<C, BVar<V>>),
) where
    S: SugarTerms<VTerm<C, BVar<V>>>,
{
    for_each_formula_atom(fm, &mut |a| fold_atom(a, f));
}

/// Visit every atom in formula order.  This is the shared structural walk for
/// read-only atom folds; each caller decides which payloads of an atom count.
pub fn for_each_formula_atom<'a, S, H, C, V>(
    fm: &'a ProtoFormula<S, H, C, V>,
    f: &mut impl FnMut(&'a ProtoAtom<S, VTerm<C, BVar<V>>>),
) {
    match fm {
        ProtoFormula::Atom(a) => f(a),
        ProtoFormula::Tf(_) => {}
        ProtoFormula::Not(p) => for_each_formula_atom(p, f),
        ProtoFormula::Conn(_, p, q) => {
            for_each_formula_atom(p, f);
            for_each_formula_atom(q, f);
        }
        ProtoFormula::Qua(_, _, p) => for_each_formula_atom(p, f),
    }
}

/// HS `formulaFacts` (Theory/Tools/Wellformedness.hs:893-906): the fact of
/// every `Action` atom, in `foldFormula` order.  A `Syntactic` atom carries a
/// fact too, and it is deliberately skipped — HS's comment at
/// Theory/Tools/Wellformedness.hs:902 reads "the 'facts' in a predicate atom
/// are not real facts".
pub fn formula_facts<S, H, C, V>(fm: &ProtoFormula<S, H, C, V>) -> Vec<&Fact<VTerm<C, BVar<V>>>> {
    let mut out = Vec::new();
    for_each_formula_atom(fm, &mut |a| {
        if let ProtoAtom::Action(_, fa) = a {
            out.push(fa);
        }
    });
    out
}

/// HS `formulaTerms` (Theory/Tools/Wellformedness.hs:918-920): the terms of
/// every atom, in `foldFormula` order.  Its atom step is `atomTerms`
/// (Theory/Tools/Wellformedness.hs:908-915), which yields NOTHING for a
/// `Syntactic` atom, so this is a different traversal from the `Foldable`
/// instance [`for_each_formula_term`] runs.
pub(crate) fn formula_terms<S, H, C, V>(fm: &ProtoFormula<S, H, C, V>) -> Vec<&VTerm<C, BVar<V>>> {
    let mut out = Vec::new();
    for_each_formula_atom(fm, &mut |a| collect_atom_terms(a, &mut out));
    out
}

/// HS `traverseFormulaAtom` (Theory/Model/Formula.hs:212-219#traverseFormulaAtom):
/// rebuild the formula with every atom replaced by the WHOLE FORMULA the
/// callback returns, under an effect — `Result` here, the `Either FactTag`
/// HS's predicate expansion runs in.  It is built on `foldFormula`
/// (Theory/Model/Formula.hs:140-156#foldFormula), which threads no De Bruijn
/// depth, so the callback sees the atom alone; [`map_atoms`] runs on
/// `foldFormulaScope` and hands each atom its depth.  Atoms are visited left
/// to right, and the binder hints are carried across.
pub fn traverse_formula_atom<S, S2, H, C, C2, V, V2, E>(
    fm: &ProtoFormula<S, H, C, V>,
    f: &mut dyn FnMut(&ProtoAtom<S, VTerm<C, BVar<V>>>) -> Result<ProtoFormula<S2, H, C2, V2>, E>,
) -> Result<ProtoFormula<S2, H, C2, V2>, E>
where
    H: Clone,
{
    match fm {
        ProtoFormula::Atom(a) => f(a),
        ProtoFormula::Tf(b) => Ok(ProtoFormula::Tf(*b)),
        ProtoFormula::Not(p) => Ok(ProtoFormula::Not(Box::new(traverse_formula_atom(p, f)?))),
        ProtoFormula::Conn(c, p, q) => {
            let l = traverse_formula_atom(p, &mut *f)?;
            let r = traverse_formula_atom(q, f)?;
            Ok(ProtoFormula::Conn(*c, Box::new(l), Box::new(r)))
        }
        ProtoFormula::Qua(q, h, p) => Ok(ProtoFormula::Qua(
            *q,
            h.clone(),
            Box::new(traverse_formula_atom(p, f)?),
        )),
    }
}

/// HS `mapAtoms` (Theory/Model/Formula.hs:267-270): rebuild the formula with
/// every atom replaced by `f`'s result.  `f` also receives the atom's De
/// Bruijn depth — the number of binders between the formula's root and the
/// atom — which `foldFormulaScope` threads by recursing with `succ i` at each
/// `Qua` (Theory/Model/Formula.hs:160-173).  The atom map may change the
/// sugar, constant and variable types; the binder hints are carried across.
pub fn map_atoms<S, S2, H, C, C2, V, V2>(
    fm: ProtoFormula<S, H, C, V>,
    f: &mut dyn FnMut(u64, &ProtoAtom<S, VTerm<C, BVar<V>>>) -> ProtoAtom<S2, VTerm<C2, BVar<V2>>>,
) -> ProtoFormula<S2, H, C2, V2> {
    map_atoms_at(fm, f, 0)
}

fn map_atoms_at<S, S2, H, C, C2, V, V2>(
    fm: ProtoFormula<S, H, C, V>,
    f: &mut dyn FnMut(u64, &ProtoAtom<S, VTerm<C, BVar<V>>>) -> ProtoAtom<S2, VTerm<C2, BVar<V2>>>,
    i: u64,
) -> ProtoFormula<S2, H, C2, V2> {
    match fm {
        ProtoFormula::Atom(a) => ProtoFormula::Atom(f(i, &a)),
        ProtoFormula::Tf(b) => ProtoFormula::Tf(b),
        ProtoFormula::Not(p) => ProtoFormula::Not(Box::new(map_atoms_at(*p, f, i))),
        ProtoFormula::Conn(c, p, q) => {
            let l = map_atoms_at(*p, &mut *f, i);
            let r = map_atoms_at(*q, &mut *f, i);
            ProtoFormula::Conn(c, Box::new(l), Box::new(r))
        }
        ProtoFormula::Qua(q, h, p) => ProtoFormula::Qua(q, h, Box::new(map_atoms_at(*p, f, i + 1))),
    }
}

/// [`map_atoms`] over [`map_atom`]: rebuild the formula with `f` applied to
/// every term of every atom, at the atom's De Bruijn depth.  This is the shape
/// HS writes as `mapAtoms (\i a -> fmap (g i) a)`
/// (Theory/Model/Formula.hs:267-270 over the `Functor (ProtoAtom s)` instance,
/// Atom.hs:121-127) in each of the formula rewrites below.
fn map_formula_terms<S, H, C, V>(
    fm: ProtoFormula<S, H, C, V>,
    f: &mut dyn FnMut(u64, &VTerm<C, BVar<V>>) -> VTerm<C, BVar<V>>,
) -> ProtoFormula<S, H, C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
{
    map_atoms(fm, &mut |i, a| map_atom(a, &mut |t| f(i, t)))
}

/// HS `quantify x` (Theory/Model/Formula.hs:347-352): turn the free variable `x` into a
/// bound one, using the De Bruijn index of the binder that is about to be put
/// in front of the formula.
pub fn quantify<S, C, V>(
    x: &V,
    fm: ProtoFormula<S, (String, LSort), C, V>,
) -> ProtoFormula<S, (String, LSort), C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
    C: Ord + Clone,
    V: Ord + Clone,
{
    // `mapLits (fmap (>>= subst i))` (Theory/Model/Formula.hs:349-352): the
    // free occurrences of `x` become the index `i`; constants and already-bound
    // indices are untouched, and the `f_app` rebuild inside `map_lits` re-sorts
    // AC arguments (`Bound` sorts before `Free`).
    map_formula_terms(fm, &mut |i, t| {
        map_lits(t, &mut |l| match l {
            Lit::Var(BVar::Free(v)) if v == x => Lit::Var(BVar::Bound(i)),
            other => other.clone(),
        })
    })
}

/// HS `applyMacroInFormula` (Theory/Model/Formula.hs:314-316): the theory's
/// macros applied to every term of every atom, through the `BVar`-tagged
/// macros [`ln_macros_to_bn_macros`](tamarin_term::macro_expand::ln_macros_to_bn_macros)
/// builds.  An empty macro list leaves the formula as it stands, which is HS's
/// own first equation (:315).
pub fn apply_macro_in_formula(macros: &[LNMacro], fm: LNFormula) -> LNFormula {
    if macros.is_empty() {
        return fm;
    }
    let bn = ln_macros_to_bn_macros(macros);
    map_formula_terms(fm, &mut |_, t| apply_macros(&bn, t.clone()))
}

/// HS `exists hint x` (Theory/Model/Formula.hs:359-360): `Qua Ex hint . quantify x`.
pub fn exists_var<S, C, V>(
    hint: (String, LSort),
    x: &V,
    fm: ProtoFormula<S, (String, LSort), C, V>,
) -> ProtoFormula<S, (String, LSort), C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
    C: Ord + Clone,
    V: Ord + Clone,
{
    ProtoFormula::exists(hint, quantify(x, fm))
}

/// HS `forAll hint x` (Theory/Model/Formula.hs:355-356): `Qua All hint . quantify x`.
pub fn for_all_var<S, C, V>(
    hint: (String, LSort),
    x: &V,
    fm: ProtoFormula<S, (String, LSort), C, V>,
) -> ProtoFormula<S, (String, LSort), C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
    C: Ord + Clone,
    V: Ord + Clone,
{
    ProtoFormula::for_all(hint, quantify(x, fm))
}

/// HS's overlapping `Apply (Subst c v) (VTerm c (BVar v))`
/// (Term/Substitution/SubstVFree.hs:297-302) under `mapAtoms (const $ apply
/// subst)`, the `Apply s (ProtoFormula syn h c v)` instance
/// (Theory/Model/Formula.hs:338-340): rewrite the free occurrences of the
/// substitution's domain in every atom.  A binder is a `Bound` index and is
/// outside the domain, so it cannot capture a variable of the image.
pub fn apply_subst<S, C, V>(
    s: &Subst<C, V>,
    fm: ProtoFormula<S, (String, LSort), C, V>,
) -> ProtoFormula<S, (String, LSort), C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
    C: Ord + Clone,
    V: Ord + Clone,
{
    map_formula_terms(fm, &mut |_, t| apply_bvterm(s, t))
}

/// The same `Apply s (ProtoFormula syn h c v)` instance
/// (Theory/Model/Formula.hs:338-340) at a substitution that does not map the
/// formula's own variable type: the atoms' terms take the overlappable `Apply
/// s (Term (Lit c v))` (Term/Substitution/SubstVFree.hs:290-291), which
/// rewrites each literal and rebuilds through `fApp`, and each free variable
/// takes `rename` through [`apply_bvar`].  A `SapicLVar` renamed this way
/// keeps its type tag (Theory/Sapic/Term.hs:115-117).
pub fn apply_rename<S, C, V>(
    fm: ProtoFormula<S, (String, LSort), C, V>,
    rename: &mut dyn FnMut(&V) -> V,
) -> ProtoFormula<S, (String, LSort), C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
    C: Ord + Clone,
    V: Ord + Clone,
{
    map_formula_terms(fm, &mut |_, t| {
        map_lits(t, &mut |l| match l {
            Lit::Con(c) => Lit::Con(c.clone()),
            Lit::Var(v) => Lit::Var(apply_bvar(v, &mut *rename)),
        })
    })
}

/// HS `shiftFreeIndices n` (Theory/Model/Formula.hs:458-465): raise by `n`
/// every bound index that refers past this formula's own binders, which is
/// what moving a sub-formula under one more binder needs.  `map_atoms` hands
/// each atom its De Bruijn depth `i`, so an index below `i` belongs to a
/// binder inside the formula and stays.
pub fn shift_free_indices<S, H, C, V>(
    n: u64,
    fm: ProtoFormula<S, H, C, V>,
) -> ProtoFormula<S, H, C, V>
where
    S: MapSugar<VTerm<C, BVar<V>>, VTerm<C, BVar<V>>, Mapped = S>,
    C: Ord + Clone,
    V: Ord + Clone,
{
    map_formula_terms(fm, &mut |i, t| {
        map_lits(t, &mut |l| match l {
            Lit::Var(BVar::Bound(j)) if *j >= i => Lit::Var(BVar::Bound(j + n)),
            other => other.clone(),
        })
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

/// The two variable parsers HS's formula grammar is parameterised over,
/// `standardFormula varp nodep` (Theory/Text/Parser/Formula.hs:108-109),
/// bundled with the term and fact converters that read a literal the same
/// way `varp` does.  HS instantiates the grammar at `msgvar`/`nodevar` for
/// the theory's own formulas (Theory/Text/Parser/Formula.hs:112-114) and at
/// `sapicvar`/`sapicnodevar` for a SAPIC condition
/// (Theory/Text/Parser/Sapic.hs:253-254); [`MsgVars`] and [`SapicVars`] are
/// those two instantiations.
pub trait FormulaVars {
    /// The free-variable type of the formula the walk builds.
    type Var: Ord + Clone;

    /// `varp`: a quantifier binder, and the variable inside every term the
    /// walk converts.
    fn var(v: &p::VarSpec) -> Self::Var;

    /// `nodep`: the variable `nodevarTerm` reads in a timepoint position
    /// (Theory/Text/Parser/Formula.hs:59).
    fn node_var(v: &p::VarSpec) -> Self::Var;

    /// HS `hint` (Theory/Model/Formula.hs:134-135): the name and sort a
    /// binder records for display.
    fn hint(v: &Self::Var) -> (String, LSort);

    /// The term converter, `None` on a term with no internal form.
    fn term(t: &p::Term, sig: &MaudeSig) -> Option<VTerm<Name, Self::Var>>;

    /// The fact converter, over the same terms.
    fn fact(f: &p::Fact, sig: &MaudeSig) -> Result<Fact<VTerm<Name, Self::Var>>, ElabError>;
}

/// HS's `msgvar`/`nodevar` instantiation (Theory/Text/Parser/Formula.hs:112-114).
/// Both parsers give an `LVar`, and the RS parser has already stamped the
/// sort each of them would read (Token.hs:440-448), so [`FormulaVars::var`]
/// and [`FormulaVars::node_var`] are the same reading of a `VarSpec`.
pub struct MsgVars;

impl FormulaVars for MsgVars {
    type Var = LVar;

    fn var(v: &p::VarSpec) -> LVar {
        varspec_to_lvar(v)
    }

    fn node_var(v: &p::VarSpec) -> LVar {
        varspec_to_lvar(v)
    }

    fn hint(v: &LVar) -> (String, LSort) {
        (v.name.to_string(), v.sort)
    }

    fn term(t: &p::Term, sig: &MaudeSig) -> Option<LNTerm> {
        term_to_lnterm(t, sig)
    }

    fn fact(f: &p::Fact, sig: &MaudeSig) -> Result<Fact<LNTerm>, ElabError> {
        fact_to_lnfact(f, sig)
    }
}

/// HS's `sapicvar`/`sapicnodevar` instantiation
/// (Theory/Text/Parser/Sapic.hs:253-254).  `sapicvar` reads the written
/// `name:type` annotation (Token.hs:506-510) and `sapicnodevar` stamps
/// `defaultSapicNodeType` on a timepoint (Token.hs:522-525,
/// Theory/Sapic/Term.hs:99-100).  A binder is `sapicvar`'s reading for every
/// spelling: `many1 (try varp <|> nodep)`
/// (Theory/Text/Parser/Formula.hs:75) reaches `sapicnodevar` only where
/// `sapicvar` fails, and `lvarNoSuffix` accepts every sort's sigil
/// (Token.hs:502-503).
pub struct SapicVars;

impl FormulaVars for SapicVars {
    type Var = SapicLVar;

    fn var(v: &p::VarSpec) -> SapicLVar {
        varspec_to_sapic(v)
    }

    fn node_var(v: &p::VarSpec) -> SapicLVar {
        SapicLVar::new(varspec_to_lvar(v), default_sapic_node_type())
    }

    fn hint(v: &SapicLVar) -> (String, LSort) {
        (v.var.name.to_string(), v.var.sort)
    }

    fn term(t: &p::Term, sig: &MaudeSig) -> Option<SapicTerm> {
        term_to_sapic_term(t, sig)
    }

    fn fact(f: &p::Fact, sig: &MaudeSig) -> Result<SapicLNFact, ElabError> {
        fact_to_sapic_fact(f, sig)
    }
}

/// Build a [`SyntacticLNFormula`] from the parser's formula AST the way HS's
/// formula parser builds one while parsing
/// (Theory/Text/Parser/Formula.hs:44-77) — [`from_parser_with`] at
/// [`MsgVars`].
///
/// Variable sorts come from the parser, which stamps them by syntactic
/// position as HS's `msgvar`/`nodevar` do (Token.hs:440-448).  A binder
/// closes exactly the occurrences equal to its `LVar` in name, sort and
/// index (HS `quantify`'s `v == x`, Theory/Model/Formula.hs:350-352), so
/// `Ex ~k. Made(k)` leaves the message-sorted `k` free.  A bare 0-arity
/// symbol is already an application when it arrives, so no binder of that
/// name closes it (HS `nullaryApp`, Theory/Text/Parser/Term.hs:158-163).  A
/// `(<)` atom becomes the `Smaller` predicate (`smallerp`,
/// Theory/Text/Parser/Formula.hs:30-38); a SAPIC `=t` pattern term, which
/// `term_to_lnterm` rejects, is an [`ElabError`].
pub fn from_parser(f: &p::Formula, sig: &MaudeSig) -> Result<SyntacticLNFormula, ElabError> {
    from_parser_with::<MsgVars>(f, sig)
}

/// [`from_parser_with`] at [`SapicVars`]: HS `standardFormula sapicvar
/// sapicnodevar` (Theory/Text/Parser/Sapic.hs:253-254), the formula a
/// `Cond` combinator and an embedded `_restrict` carry.
///
/// A binder closes exactly the occurrences equal to its whole `SapicLVar`,
/// type tag included (HS `quantify`'s `v == x`,
/// Theory/Model/Formula.hs:350-352). Current `sapicvar` defaults a node-sorted
/// binder to type `node`, matching `sapicnodevar` at its occurrences.
pub fn sapic_from_parser(f: &p::Formula, sig: &MaudeSig) -> Result<SapicFormula, ElabError> {
    from_parser_with::<SapicVars>(f, sig)
}

/// The closing walk of HS's formula grammar
/// (Theory/Text/Parser/Formula.hs:44-77): every atom is lifted with all of
/// its variables free (`blatom`'s `fmap (fmapTerm (fmap Free))`,
/// Theory/Text/Parser/Formula.hs:44-45), and a quantifier closes its binders
/// with `foldr (hinted q) f vs` (Theory/Text/Parser/Formula.hs:73-77) over
/// `forAll`/`exists` (Theory/Model/Formula.hs:355-360), so the last binder
/// of the list is the innermost one.
pub fn from_parser_with<F: FormulaVars>(
    f: &p::Formula,
    sig: &MaudeSig,
) -> Result<SyntacticNFormula<F::Var>, ElabError> {
    match f {
        p::Formula::True => Ok(ProtoFormula::Tf(true)),
        p::Formula::False => Ok(ProtoFormula::Tf(false)),
        p::Formula::Atom(a) => Ok(ProtoFormula::Atom(atom_from_parser::<F>(a, sig)?)),
        p::Formula::Not(q) => Ok(from_parser_with::<F>(q, sig)?.not()),
        p::Formula::And(l, r) => {
            Ok(from_parser_with::<F>(l, sig)?.and(from_parser_with::<F>(r, sig)?))
        }
        p::Formula::Or(l, r) => {
            Ok(from_parser_with::<F>(l, sig)?.or(from_parser_with::<F>(r, sig)?))
        }
        p::Formula::Implies(l, r) => {
            Ok(from_parser_with::<F>(l, sig)?.implies(from_parser_with::<F>(r, sig)?))
        }
        p::Formula::Iff(l, r) => {
            Ok(from_parser_with::<F>(l, sig)?.iff(from_parser_with::<F>(r, sig)?))
        }
        p::Formula::Forall(vs, body) => Ok(close_binders::<F>(
            for_all_var,
            vs,
            from_parser_with::<F>(body, sig)?,
        )),
        p::Formula::Exists(vs, body) => Ok(close_binders::<F>(
            exists_var,
            vs,
            from_parser_with::<F>(body, sig)?,
        )),
    }
}

/// HS `foldr (hinted q) f vs` (Theory/Text/Parser/Formula.hs:73-77): close
/// the binders from the last to the first, each with the hint that `hinted`
/// (Theory/Model/Formula.hs:364-365) reads off the binder's variable
/// (Theory/Model/Formula.hs:227-228 at an `LVar`, Theory/Sapic/Term.hs:111-112
/// at a `SapicLVar`).
fn close_binders<F: FormulaVars>(
    q: fn((String, LSort), &F::Var, SyntacticNFormula<F::Var>) -> SyntacticNFormula<F::Var>,
    vs: &[p::VarSpec],
    body: SyntacticNFormula<F::Var>,
) -> SyntacticNFormula<F::Var> {
    vs.iter().rev().fold(body, |acc, v| {
        let x = F::var(v);
        q(F::hint(&x), &x, acc)
    })
}

/// The atom alternatives of HS `blatom` (Theory/Text/Parser/Formula.hs:45-57).
fn atom_from_parser<F: FormulaVars>(
    a: &p::Atom,
    sig: &MaudeSig,
) -> Result<SyntacticAtom<VTerm<Name, BVar<F::Var>>>, ElabError> {
    Ok(match a {
        p::Atom::Eq(l, r) => ProtoAtom::EqE(free_term::<F>(l, sig)?, free_term::<F>(r, sig)?),
        p::Atom::Subterm(l, r) => {
            ProtoAtom::Subterm(free_term::<F>(l, sig)?, free_term::<F>(r, sig)?)
        }
        p::Atom::Less(l, r) => ProtoAtom::Less(node_term::<F>(l, sig)?, node_term::<F>(r, sig)?),
        p::Atom::Action(fa, t) => {
            ProtoAtom::Action(node_term::<F>(t, sig)?, free_fact::<F>(fa, sig)?)
        }
        p::Atom::Last(t) => ProtoAtom::Last(node_term::<F>(t, sig)?),
        p::Atom::Pred(fa) => ProtoAtom::Syntactic(SyntacticSugar::Pred(free_fact::<F>(fa, sig)?)),
        p::Atom::LessMset(l, r) => ProtoAtom::Syntactic(SyntacticSugar::Pred(smaller_fact(
            free_term::<F>(l, sig)?,
            free_term::<F>(r, sig)?,
        ))),
    })
}

/// `fmapTerm (fmap Free)` (Theory/Text/Parser/Formula.hs:45): every variable
/// of the term as a free `BVar`.  The literal order is unchanged, so the
/// `f_app` rebuild inside [`map_lits`] keeps the AC argument order.
pub fn lift_free<C: Ord + Clone, V: Ord + Clone>(t: &VTerm<C, V>) -> VTerm<C, BVar<V>> {
    map_lits(t, &mut |l| match l {
        Lit::Con(c) => Lit::Con(c.clone()),
        Lit::Var(v) => Lit::Var(BVar::Free(v.clone())),
    })
}

fn free_term<F: FormulaVars>(
    t: &p::Term,
    sig: &MaudeSig,
) -> Result<VTerm<Name, BVar<F::Var>>, ElabError> {
    F::term(t, sig)
        .map(|t| lift_free(&t))
        .ok_or_else(|| ElabError {
            message: "could not elaborate term in formula".to_string(),
        })
}

/// HS `nodevarTerm = lit . Var <$> nodep` (Theory/Text/Parser/Formula.hs:59):
/// the three positions `blatom` reads with it — `last`'s argument (:46), an
/// action's timepoint (:47) and both operands of `<` (:49) — take a bare
/// variable through `nodep`.  The RS parser also accepts a non-variable term
/// there (parser.rs's `<` arm), which converts like any other term.
fn node_term<F: FormulaVars>(
    t: &p::Term,
    sig: &MaudeSig,
) -> Result<VTerm<Name, BVar<F::Var>>, ElabError> {
    match t {
        p::Term::Var(v) => Ok(var_term(BVar::Free(F::node_var(v)))),
        _ => free_term::<F>(t, sig),
    }
}

fn free_fact<F: FormulaVars>(
    fa: &p::Fact,
    sig: &MaudeSig,
) -> Result<Fact<VTerm<Name, BVar<F::Var>>>, ElabError> {
    Ok(F::fact(fa, sig)?.map_ref(lift_free))
}

/// Replace every bound index of `t` by the binder it refers to, given the
/// enclosing binders innermost-last in `scope`: `Bound(0)` is the innermost
/// binder, `Bound(i)` the one `i` binders further out.  This is HS
/// `openFormula`'s `mapLits (subst x i)` (Theory/Model/Formula.hs:274-291)
/// applied once per enclosing binder, followed by `extractFree`
/// (Theory/Model/Formula.hs:481-484), whose error message is kept for an
/// index past the scope.  The rebuild through [`map_lits`] re-sorts AC
/// arguments under the opened `LVar`s, as HS's `fApp` does.
pub fn open_bound_term(t: &BLNTerm, scope: &[LVar]) -> LNTerm {
    map_lits(t, &mut |l| match l {
        Lit::Con(c) => Lit::Con(*c),
        Lit::Var(BVar::Free(v)) => Lit::Var(*v),
        Lit::Var(BVar::Bound(i)) => match scope.iter().rev().nth(*i as usize) {
            Some(v) => Lit::Var(*v),
            None => panic!("prettyFormula: illegal bound variable '{i}'"),
        },
    })
}

// =============================================================================
// Opening a quantifier prefix (Theory/Model/Formula.hs:272-309) against the
// precise fresh supply HS seeds with `avoidPrecise` (LTerm.hs:706-715).
// =============================================================================

/// HS `avoidPrecise = avoidPreciseVars . frees` (LTerm.hs:706-709, :714-715)
/// on a locally-nameless formula: the free variables seed the per-name
/// counters, so a binder whose name a free variable uses is drawn with a
/// larger index.
pub(crate) fn avoid_precise_lnformula<S: SugarTerms<BLNTerm>>(
    f: &LNProtoFormula<S>,
) -> PreciseFreshState {
    PreciseFreshState::avoid_precise(
        formula_frees(f)
            .into_iter()
            .map(|v| (v.name.to_string(), v.idx)),
    )
}

/// HS `openFormula` (Theory/Model/Formula.hs:272-286): when `f` is `Q v. f'`,
/// the quantifier, a fresh `LVar` for the binder and the body with that
/// variable put in the binder's place; `None` when `f` is not a quantifier.
///
/// HS returns the fresh draw as an unrun action, so a caller that rejects the
/// quantifier takes nothing from the supply
/// (Theory/Model/Formula.hs:305-307); here the caller decides before calling.
pub fn open_formula<S, C>(
    f: &ProtoFormula<S, (String, LSort), C, LVar>,
    fresh: &mut PreciseFreshState,
) -> Option<(Quantifier, LVar, ProtoFormula<S, (String, LSort), C, LVar>)>
where
    S: MapSugar<VTerm<C, BVar<LVar>>, VTerm<C, BVar<LVar>>, Mapped = S> + Clone,
    C: Ord + Clone,
{
    match f {
        ProtoFormula::Qua(qua, hint, body) => {
            let (x, opened) = open_binder(hint, body, fresh);
            Some((*qua, x, opened))
        }
        _ => None,
    }
}

/// The action HS `openFormula` returns (Theory/Model/Formula.hs:279-284):
/// `freshLVar` on the binder's name and sort ([`fresh_lvar`],
/// LTerm.hs:300-302), then `mapAtoms (\i a -> fmap (mapLits (subst x i)) a)`
/// over the body.  `i` is the atom's depth below the opened binder, and
/// `subst` rewrites exactly the index `i`, so an index that belongs to an
/// enclosing binder stays bound.
fn open_binder<S, C>(
    hint: &(String, LSort),
    body: &ProtoFormula<S, (String, LSort), C, LVar>,
    fresh: &mut PreciseFreshState,
) -> (LVar, ProtoFormula<S, (String, LSort), C, LVar>)
where
    S: MapSugar<VTerm<C, BVar<LVar>>, VTerm<C, BVar<LVar>>, Mapped = S> + Clone,
    C: Ord + Clone,
{
    let (name, sort) = hint;
    let x = fresh_lvar(fresh, name, *sort);
    let opened = map_atoms(body.clone(), &mut |i, a| {
        map_atom(a, &mut |t| {
            map_lits(t, &mut |l| match l {
                Lit::Var(BVar::Bound(j)) if *j == i => Lit::Var(BVar::Free(x)),
                other => other.clone(),
            })
        })
    });
    (x, opened)
}

/// HS `openFormulaPrefix` (Theory/Model/Formula.hs:293-309): open the
/// outermost binder and every directly nested binder of the same quantifier,
/// each with its own fresh `LVar`, and return them outermost first with the
/// quantifier and the body beneath them.  A binder of the other quantifier
/// ends the prefix and draws nothing.  HS's `error` for a formula that does
/// not start with a quantifier is kept.
pub fn open_formula_prefix<S, C>(
    f: &ProtoFormula<S, (String, LSort), C, LVar>,
    fresh: &mut PreciseFreshState,
) -> (
    Vec<LVar>,
    Quantifier,
    ProtoFormula<S, (String, LSort), C, LVar>,
)
where
    S: MapSugar<VTerm<C, BVar<LVar>>, VTerm<C, BVar<LVar>>, Mapped = S> + Clone,
    C: Ord + Clone,
{
    let Some((qua, x, mut body)) = open_formula(f, fresh) else {
        panic!("openFormulaPrefix: no outermost quantifier")
    };
    let mut xs = vec![x];
    loop {
        let next = match &body {
            ProtoFormula::Qua(qua2, hint, inner) if *qua2 == qua => {
                Some(open_binder(hint, inner, fresh))
            }
            _ => None,
        };
        match next {
            Some((x2, opened)) => {
                xs.push(x2);
                body = opened;
            }
            None => return (xs, qua, body),
        }
    }
}

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

    /// `exists_var` closes the variable, and `quantify` turns its free
    /// occurrences into the new binder's De Bruijn index.
    #[test]
    fn exists_var_binds_the_free_var() {
        use tamarin_term::vterm::var_term;

        let x = LVar::new("x", LSort::Msg, 0);
        let atom = ProtoAtom::EqE(var_term(BVar::Free(x)), var_term(BVar::Free(x)));
        let fm: LNFormula = ProtoFormula::Atom(atom);

        let ProtoFormula::Qua(q, hint, body) = exists_var(("x".to_string(), LSort::Msg), &x, fm)
        else {
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

    /// `shiftFreeIndices n` raises exactly the indices that dangle past the
    /// formula's own binders: at an atom under one binder, `Bound(0)` is that
    /// binder's and stays, while `Bound(1)` points outside and moves.
    #[test]
    fn shift_free_indices_lifts_only_the_indices_above_the_scope() {
        use tamarin_term::vterm::var_term;

        let atom = |i: u64, j: u64| -> LNFormula {
            ProtoFormula::Atom(ProtoAtom::Less(
                var_term(BVar::Bound(i)),
                var_term(BVar::Bound(j)),
            ))
        };
        let hint = ("y".to_string(), LSort::Node);
        let fm: LNFormula = ProtoFormula::for_all(hint.clone(), atom(0, 1)).and(atom(0, 1));
        let ProtoFormula::Conn(_, under, outside) = shift_free_indices(2, fm) else {
            panic!("expected the conjunction to survive the shift");
        };
        assert_eq!(
            *under,
            ProtoFormula::for_all(hint, atom(0, 3)),
            "under the binder only the dangling index moves"
        );
        assert_eq!(*outside, atom(2, 3), "outside it both move");
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
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_term::term::{f_app_ac, f_app_no_eq, Term};
    use tamarin_term::vterm::var_term;

    fn parsed(src: &str) -> SyntacticLNFormula {
        parsed_with(src, &pair_maude_sig())
    }

    /// [`parsed`] against a theory's own signature, for the sources whose
    /// meaning depends on a declaration.
    fn parsed_with(src: &str, msig: &tamarin_term::maude_sig::MaudeSig) -> SyntacticLNFormula {
        from_parser(&parse_formula_str(src, msig).unwrap(), msig).unwrap()
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
        let elab = crate::elaborate::elaborate(&thy).unwrap();

        let ProtoFormula::Qua(Quantifier::All, h, body) =
            parsed_with("All zero. P(zero)", &elab.signature)
        else {
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
        assert_eq!(from_parser(&f, &pair_maude_sig()).unwrap(), want);
    }

    /// A SAPIC `=t` pattern has no `LNTerm` form.
    #[test]
    fn from_parser_rejects_pat_match() {
        let pat = p::Term::PatMatch(Box::new(parser_var("x", LSort::Msg)));
        let in_term = p::Formula::Atom(p::Atom::Eq(pat.clone(), parser_var("y", LSort::Msg)));
        let err = from_parser(&in_term, &pair_maude_sig()).unwrap_err();
        assert_eq!(err.message, "could not elaborate term in formula");
        let in_fact = p::Formula::Atom(p::Atom::Pred(p::Fact {
            persistent: false,
            name: "F".to_string(),
            args: vec![pat],
            annotations: Vec::new(),
        }));
        assert!(from_parser(&in_fact, &pair_maude_sig()).is_err());
    }

    // =========================================================================
    // sapic_from_parser
    // =========================================================================

    fn sapic_parsed(src: &str) -> SapicFormula {
        let msig = pair_maude_sig();
        let parsed = tamarin_parser::parse_theory(
            &format!("theory T begin process: if {src} then 0 end"),
            &[],
        )
        .unwrap();
        let condition = parsed
            .items
            .iter()
            .find_map(|item| match item {
                p::TheoryItem::TopLevelProcess(p::Process::Comb {
                    comb: p::ProcessComb::Cond(condition),
                    ..
                }) => Some(condition),
                _ => None,
            })
            .unwrap();
        let formula = match condition {
            p::Condition::Formula(formula) => formula.clone(),
            p::Condition::Eq(left, right) => {
                p::Formula::Atom(p::Atom::Eq(left.clone(), right.clone()))
            }
        };
        sapic_from_parser(&formula, &msig).unwrap()
    }

    fn sapic_free(name: &str, sort: LSort, typ: Option<&str>) -> VTerm<Name, BVar<SapicLVar>> {
        var_term(BVar::Free(SapicLVar::new(
            LVar::new(name, sort, 0),
            typ.map(str::to_string),
        )))
    }

    fn sapic_bound(i: u64) -> VTerm<Name, BVar<SapicLVar>> {
        var_term(BVar::Bound(i))
    }

    fn sapic_pred(name: &str, args: Vec<VTerm<Name, BVar<SapicLVar>>>) -> SapicFormula {
        ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(proto_fact(
            name, args,
        ))))
    }

    /// `sapicvar` carries the written `name:type` into the binder and into
    /// every term literal (Token.hs:506-510), and a binder closes the
    /// occurrences equal to its whole `SapicLVar`, so the untagged `x` of the
    /// same name and sort stays free.
    #[test]
    fn sapic_from_parser_keeps_the_written_type_tag() {
        let want = ProtoFormula::exists(
            hint("x", LSort::Msg),
            sapic_pred("P", vec![sapic_bound(0), sapic_free("x", LSort::Msg, None)]),
        );
        assert_eq!(sapic_parsed("Ex x:foo. P(x:foo, x)"), want);
    }

    /// `nodevarTerm` reads its variable with `nodep = sapicnodevar`, which
    /// stamps `defaultSapicNodeType` (Token.hs:522-525,
    /// Theory/Sapic/Term.hs:99-100), in the three positions `blatom` writes
    /// it: `last`'s argument, an action's timepoint and both operands of `<`
    /// (Theory/Text/Parser/Formula.hs:46-49).
    #[test]
    fn sapic_from_parser_tags_a_timepoint_operand_node() {
        let node = |n: &str| sapic_free(n, LSort::Node, Some("node"));
        assert_eq!(
            sapic_parsed("#k < #l"),
            ProtoFormula::Atom(ProtoAtom::Less(node("k"), node("l")))
        );
        assert_eq!(
            sapic_parsed("last(#m)"),
            ProtoFormula::Atom(ProtoAtom::Last(node("m")))
        );
        assert_eq!(
            sapic_parsed("Ev(x) @ #n"),
            ProtoFormula::Atom(ProtoAtom::Action(
                node("n"),
                proto_fact("Ev", vec![sapic_free("x", LSort::Msg, None)])
            ))
        );
    }

    /// A predicate's arguments are read by `varp = sapicvar`; current
    /// `sapicvar` defaults a node-sorted variable to type `node`.
    #[test]
    fn sapic_from_parser_tags_a_node_sorted_predicate_argument() {
        assert_eq!(
            sapic_parsed("P(#p, y)"),
            sapic_pred(
                "P",
                vec![
                    sapic_free("p", LSort::Node, Some("node")),
                    sapic_free("y", LSort::Msg, None)
                ]
            )
        );
    }

    /// The node-defaulting fix makes a `sapicvar` quantifier binder equal to
    /// the tagged `sapicnodevar` occurrence, so `quantify` closes it.
    #[test]
    fn a_sapic_node_binder_closes_a_tagged_timepoint_occurrence() {
        let want = ProtoFormula::exists(
            hint("j", LSort::Node),
            ProtoFormula::Atom(ProtoAtom::Action(
                sapic_bound(0),
                proto_fact("Foo", vec![sapic_free("x", LSort::Msg, None)]),
            )),
        );
        let got = sapic_parsed("Ex #j. Foo(x)@#j");
        assert_eq!(got, want);
        assert_eq!(
            formula_frees(&got),
            vec![SapicLVar::untyped(LVar::new("x", LSort::Msg, 0))]
        );
    }

    /// The two instantiations of the closing walk agree once `toLFormula`
    /// drops the tags.
    #[test]
    fn to_lformula_of_sapic_from_parser_equals_from_parser() {
        for src in [
            "All x. P(x) & x = 'a'",
            "Ex y. Q(y) ==> last(#i)",
            "#k < #l",
            "x:foo = 'a'",
            "All x:foo. P(x:foo)",
            "Ex ~k. K(~k) @ #i & #i < #j",
            "Ex #j. Foo(x) @ #j",
        ] {
            assert_eq!(
                crate::sapic::to_lformula(&sapic_parsed(src)),
                parsed(src),
                "{src}"
            );
        }
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
    // map_atoms / apply_subst / apply_rename
    // =========================================================================

    /// The callback's `i` counts the binders between the formula's root and
    /// the atom, so the two atoms of one formula are seen at their own depths.
    #[test]
    fn map_atoms_threads_the_binder_depth() {
        let last_i = || ProtoFormula::Atom(ProtoAtom::Last(free("i", LSort::Node, 0)));
        // All x. ((Ex y. last(#i)) & last(#i))
        let fm: SyntacticLNFormula = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::exists(hint("y", LSort::Msg), last_i()).and(last_i()),
        );
        let mut depths = Vec::new();
        let out = map_atoms(fm.clone(), &mut |i, a| {
            depths.push(i);
            a.clone()
        });
        assert_eq!(depths, vec![2, 1]);
        assert_eq!(out, fm);
    }

    /// The substitution reaches every free occurrence, inside a `Pred`'s fact
    /// too, and leaves a bound index alone.
    #[test]
    fn apply_subst_rewrites_free_occurrences_only() {
        let x = LVar::new("x", LSort::Msg, 0);
        let z = LVar::new("z", LSort::Msg, 0);
        let s: Subst<Name, LVar> = Subst::from_list(vec![(x, var_term(z))]);
        let fm: SyntacticLNFormula = ProtoFormula::exists(
            hint("y", LSort::Msg),
            pred("P", vec![free("x", LSort::Msg, 0), bound(0)]),
        );
        let want: SyntacticLNFormula = ProtoFormula::exists(
            hint("y", LSort::Msg),
            pred("P", vec![free("z", LSort::Msg, 0), bound(0)]),
        );
        assert_eq!(apply_subst(&s, fm), want);
    }

    /// A binder is a De Bruijn index, which no substitution has in its domain,
    /// so an image variable that spells the binder's own hint stays free where
    /// it lands.
    #[test]
    fn a_bound_index_cannot_be_captured_by_a_substitution() {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let s: Subst<Name, LVar> = Subst::from_list(vec![(x, var_term(y))]);
        // Ex y. x = y, with the body's `y` the binder's own index.
        let fm: LNFormula = ProtoFormula::exists(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(free("x", LSort::Msg, 0), bound(0))),
        );
        let want: LNFormula = ProtoFormula::exists(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(free("y", LSort::Msg, 0), bound(0))),
        );
        let out = apply_subst(&s, fm);
        assert_eq!(out, want);
        assert_eq!(formula_frees(&out), vec![y]);
    }

    /// Renaming rewrites each free variable through the caller's function and
    /// keeps the bound indices, whatever the variable type carries.
    #[test]
    fn apply_rename_rewrites_free_variables_and_keeps_bound_indices() {
        let fm: SyntacticLNFormula = ProtoFormula::for_all(
            hint("y", LSort::Msg),
            pred("P", vec![free("x", LSort::Msg, 0), bound(0)]),
        );
        let want: SyntacticLNFormula = ProtoFormula::for_all(
            hint("y", LSort::Msg),
            pred("P", vec![free("x", LSort::Msg, 7), bound(0)]),
        );
        assert_eq!(
            apply_rename(fm, &mut |v| LVar::new(v.name, v.sort, 7)),
            want
        );
    }

    // =========================================================================
    // open_formula / open_formula_prefix
    // =========================================================================

    /// The freshened binder replaces the index that belongs to it and nothing
    /// else: an index of an enclosing binder counts one level further out
    /// under the opened quantifier and stays bound.
    #[test]
    fn open_formula_replaces_only_its_own_index() {
        // All x. Ex y. x = y
        let fm: LNFormula = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::exists(
                hint("y", LSort::Msg),
                ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
            ),
        );
        let mut fresh = PreciseFreshState::nothing_used();
        let (qua, x, body) = open_formula(&fm, &mut fresh).expect("the outermost quantifier");
        assert_eq!(qua, Quantifier::All);
        assert_eq!(x, LVar::new("x", LSort::Msg, 0));
        let want: LNFormula = ProtoFormula::exists(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(free("x", LSort::Msg, 0), bound(0))),
        );
        assert_eq!(body, want);

        let tf: LNFormula = ProtoFormula::ltrue();
        assert!(open_formula(&tf, &mut fresh).is_none());
    }

    /// The prefix is returned in binder order, outermost first, and every
    /// binder's occurrences resolve to its own variable.
    #[test]
    fn open_formula_prefix_returns_the_binders_outermost_first() {
        // All x y. x = y
        let fm: LNFormula = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::for_all(
                hint("y", LSort::Msg),
                ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
            ),
        );
        let mut fresh = PreciseFreshState::nothing_used();
        let (xs, qua, body) = open_formula_prefix(&fm, &mut fresh);
        assert_eq!(
            xs,
            vec![LVar::new("x", LSort::Msg, 0), LVar::new("y", LSort::Msg, 0)]
        );
        assert_eq!(qua, Quantifier::All);
        assert_eq!(
            body,
            ProtoFormula::Atom(ProtoAtom::EqE(
                free("x", LSort::Msg, 0),
                free("y", LSort::Msg, 0)
            ))
        );
    }

    /// A binder of the other quantifier ends the prefix, and HS's guard
    /// `q' == q` runs before the fresh draw, so that binder takes no index.
    #[test]
    fn open_formula_prefix_stops_at_a_different_quantifier() {
        // All x. Ex y. x = y
        let fm: LNFormula = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::exists(
                hint("y", LSort::Msg),
                ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
            ),
        );
        let mut fresh = PreciseFreshState::nothing_used();
        let (xs, qua, body) = open_formula_prefix(&fm, &mut fresh);
        assert_eq!(xs, vec![LVar::new("x", LSort::Msg, 0)]);
        assert_eq!(qua, Quantifier::All);
        assert!(matches!(body, ProtoFormula::Qua(Quantifier::Ex, _, _)));
        assert_eq!(fresh.fresh_ident("y"), 0);
    }

    /// Two binders of one prefix that share a name are drawn as `x` and
    /// `x.1`, so the inner one keeps its own identity after opening.
    #[test]
    fn open_formula_prefix_freshens_a_shadowed_binder() {
        // All x. All x. x = x
        let fm: LNFormula = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::for_all(
                hint("x", LSort::Msg),
                ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
            ),
        );
        let mut fresh = PreciseFreshState::nothing_used();
        let (xs, _, body) = open_formula_prefix(&fm, &mut fresh);
        assert_eq!(
            xs,
            vec![LVar::new("x", LSort::Msg, 0), LVar::new("x", LSort::Msg, 1)]
        );
        assert_eq!(
            body,
            ProtoFormula::Atom(ProtoAtom::EqE(
                free("x", LSort::Msg, 0),
                free("x", LSort::Msg, 1)
            ))
        );
    }

    /// The supply is the caller's and is not rolled back per prefix, so two
    /// sibling prefixes that use one binder name get distinct indices.  HS's
    /// guarded conversion opens its prefixes this way (`convEx`/`convAll`,
    /// Guarded.hs:535-564); its printer wraps each prefix in `scopeFreshness`
    /// instead (Theory/Model/Formula.hs:503-506).
    #[test]
    fn open_formula_draws_from_one_unscoped_supply() {
        let prefix = || -> LNFormula {
            ProtoFormula::exists(
                hint("i", LSort::Node),
                ProtoFormula::Atom(ProtoAtom::Last(bound(0))),
            )
        };
        let mut fresh = PreciseFreshState::nothing_used();
        let (left, _, _) = open_formula_prefix(&prefix(), &mut fresh);
        let (right, _, _) = open_formula_prefix(&prefix(), &mut fresh);
        assert_eq!(left, vec![LVar::new("i", LSort::Node, 0)]);
        assert_eq!(right, vec![LVar::new("i", LSort::Node, 1)]);
    }

    /// `quantify` closes the variable `open_formula` drew, so putting the
    /// binder back rebuilds the formula the opening started from.
    #[test]
    fn quantify_inverts_open_formula() {
        // All x. x = z
        let fm: LNFormula = ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(bound(0), free("z", LSort::Msg, 0))),
        );
        let mut fresh = avoid_precise_lnformula(&fm);
        let (qua, x, body) = open_formula(&fm, &mut fresh).expect("the quantifier");
        assert_eq!(qua, Quantifier::All);
        assert_eq!(for_all_var((x.name.to_string(), x.sort), &x, body), fm);
    }

    /// [`traverse_formula_atom`] hands the callback the atom itself, and the
    /// callback's own `map_atom` walk of an `Action` reads the time point
    /// before the fact's arguments (HS `Functor (ProtoAtom s)`,
    /// Theory/Model/Atom.hs:121-127#fmap).  Atoms arrive left to right and
    /// each returned formula is spliced in place of its atom.
    #[test]
    fn traverse_formula_atom_visits_the_action_timepoint_first() {
        use crate::fact::{FactTag, Multiplicity};

        let v = |n: &str, s| tamarin_term::vterm::var_term(BVar::Free(LVar::new(n, s, 0)));
        let action: LNFormula = ProtoFormula::Atom(ProtoAtom::Action(
            v("i", LSort::Node),
            Fact::new(
                FactTag::Proto(Multiplicity::Linear, "A", 2),
                vec![v("a", LSort::Msg), v("b", LSort::Msg)],
            ),
        ));
        let last: LNFormula = ProtoFormula::Atom(ProtoAtom::Last(v("j", LSort::Node)));
        let fm = ProtoFormula::exists(("z".to_string(), LSort::Msg), action.and(last));

        let mut seen: Vec<String> = Vec::new();
        let out: LNFormula = traverse_formula_atom(&fm, &mut |a| {
            let _ = map_atom(a, &mut |t: &BLNTerm| {
                seen.push(match t {
                    Term::Lit(Lit::Var(BVar::Free(x))) => x.name.to_string(),
                    _ => "?".to_string(),
                });
                t.clone()
            });
            Ok::<LNFormula, ()>(ProtoFormula::ltrue())
        })
        .unwrap();

        assert_eq!(seen, vec!["i", "a", "b", "j"]);
        let expected: LNFormula = ProtoFormula::exists(
            ("z".to_string(), LSort::Msg),
            ProtoFormula::ltrue().and(ProtoFormula::ltrue()),
        );
        assert_eq!(out, expected);
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

    /// `A(x) @ i` as an atom over `BVar` terms.
    fn action_atom(name: &'static str) -> SyntacticAtom<BLNTerm> {
        use crate::fact::{Fact, FactTag, Multiplicity};
        use tamarin_term::vterm::var_term;

        ProtoAtom::Action(
            var_term(BVar::Free(LVar::new("i", LSort::Node, 0))),
            Fact::new(
                FactTag::Proto(Multiplicity::Linear, name, 1),
                vec![var_term(BVar::Free(x_var()))],
            ),
        )
    }

    /// `formulaFacts` yields the fact of an `Action` atom and of nothing else.
    /// A `Syntactic` atom carries a fact too and is skipped, which is the one
    /// arm HS spells out (Theory/Tools/Wellformedness.hs:902).  The facts come
    /// out in `foldFormula` order: left operand before right, through `Not`
    /// and through a binder.
    #[test]
    fn formula_facts_collects_action_atoms_only() {
        use crate::fact::fact_tag_name;
        use tamarin_term::vterm::var_term;

        let eq: SyntacticLNFormula = ProtoFormula::Atom(ProtoAtom::EqE(
            var_term(BVar::Free(x_var())),
            var_term(BVar::Free(x_var())),
        ));
        let fm: SyntacticLNFormula = ProtoFormula::exists(
            ("x".to_string(), LSort::Msg),
            ProtoFormula::Atom(action_atom("A"))
                .and(ProtoFormula::Atom(pred_atom(BVar::Free(x_var()))).or(eq))
                .implies(ProtoFormula::Atom(action_atom("B")).not()),
        );
        let names: Vec<String> = formula_facts(&fm)
            .iter()
            .map(|fa| fact_tag_name(&fa.tag))
            .collect();
        assert_eq!(names, vec!["A".to_string(), "B".to_string()]);
    }
}
