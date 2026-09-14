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
use tamarin_term::term::map_lits;
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
pub enum ProtoFormula<S, H, C, V> {
    Atom(ProtoAtom<S, VTerm<C, BVar<V>>>),
    /// `true`/`false`.
    Tf(bool),
    Not(FormulaBox<S, H, C, V>),
    Conn(Connective, FormulaBox<S, H, C, V>, FormulaBox<S, H, C, V>),
    Qua(Quantifier, H, FormulaBox<S, H, C, V>),
}

impl<S: Clone, H: Clone, C: Clone, V: Clone> Clone for ProtoFormula<S, H, C, V> {
    fn clone(&self) -> Self {
        traverse_formula_atom(self, &mut |a| {
            Ok::<_, std::convert::Infallible>(Self::Atom(a.clone()))
        })
        .unwrap()
    }
}

fn compare_formula<S, H, C, V>(
    left: &ProtoFormula<S, H, C, V>,
    right: &ProtoFormula<S, H, C, V>,
    mut atom: impl FnMut(
        &ProtoAtom<S, VTerm<C, BVar<V>>>,
        &ProtoAtom<S, VTerm<C, BVar<V>>>,
    ) -> Option<std::cmp::Ordering>,
    mut hint: impl FnMut(&H, &H) -> Option<std::cmp::Ordering>,
) -> Option<std::cmp::Ordering> {
    use std::cmp::Ordering::Equal;
    fn tag<S, H, C, V>(f: &ProtoFormula<S, H, C, V>) -> u8 {
        match f {
            ProtoFormula::Atom(_) => 0,
            ProtoFormula::Tf(_) => 1,
            ProtoFormula::Not(_) => 2,
            ProtoFormula::Conn(..) => 3,
            ProtoFormula::Qua(..) => 4,
        }
    }
    let mut current = (left, right);
    let mut pending = Vec::new();
    loop {
        let (l, r) = current;
        let order = tag(l).cmp(&tag(r));
        if order != Equal {
            return Some(order);
        }
        let order = match (l, r) {
            (ProtoFormula::Atom(a), ProtoFormula::Atom(b)) => atom(a, b),
            (ProtoFormula::Tf(a), ProtoFormula::Tf(b)) => Some(a.cmp(b)),
            (ProtoFormula::Not(a), ProtoFormula::Not(b)) => {
                current = (a, b);
                continue;
            }
            (ProtoFormula::Conn(c, a, b), ProtoFormula::Conn(d, x, y)) => {
                if c != d {
                    return Some(c.cmp(d));
                }
                pending.push((&**b, &**y));
                current = (a, x);
                continue;
            }
            (ProtoFormula::Qua(q, h, a), ProtoFormula::Qua(r, j, b)) => {
                if q != r {
                    return Some(q.cmp(r));
                }
                let order = hint(h, j);
                if order != Some(Equal) {
                    return order;
                }
                current = (a, b);
                continue;
            }
            _ => unreachable!(),
        };
        if order != Some(Equal) {
            return order;
        }
        let Some(next) = pending.pop() else {
            return Some(Equal);
        };
        current = next;
    }
}
impl<S: PartialEq, H: PartialEq, C: PartialEq, V: PartialEq> PartialEq
    for ProtoFormula<S, H, C, V>
{
    fn eq(&self, other: &Self) -> bool {
        use std::cmp::Ordering::{Equal, Less};
        compare_formula(
            self,
            other,
            |a, b| Some(if a == b { Equal } else { Less }),
            |a, b| Some(if a == b { Equal } else { Less }),
        ) == Some(Equal)
    }
}
impl<S: Eq, H: Eq, C: Eq, V: Eq> Eq for ProtoFormula<S, H, C, V> {}
impl<S: PartialOrd, H: PartialOrd, C: PartialOrd, V: PartialOrd> PartialOrd
    for ProtoFormula<S, H, C, V>
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        compare_formula(
            self,
            other,
            PartialOrd::partial_cmp,
            PartialOrd::partial_cmp,
        )
    }
}
impl<S: Ord, H: Ord, C: Ord, V: Ord> Ord for ProtoFormula<S, H, C, V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        compare_formula(self, other, |a, b| Some(a.cmp(b)), |a, b| Some(a.cmp(b))).unwrap()
    }
}
impl<S: std::fmt::Debug, H: std::fmt::Debug, C: std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug
    for ProtoFormula<S, H, C, V>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            if f.alternate() {
                return tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                    Self::Atom(a) => f.debug_tuple("Atom").field(a).finish(),
                    Self::Tf(b) => f.debug_tuple("Tf").field(b).finish(),
                    Self::Not(p) => f.debug_tuple("Not").field(p).finish(),
                    Self::Conn(c, p, q) => {
                        f.debug_tuple("Conn").field(c).field(p).field(q).finish()
                    }
                    Self::Qua(q, h, p) => f.debug_tuple("Qua").field(q).field(h).field(p).finish(),
                });
            }
            enum Task<'a, S, H, C, V> {
                Node(&'a ProtoFormula<S, H, C, V>),
                Text(&'static str),
            }
            let mut pending = vec![Task::Node(self)];
            while let Some(task) = pending.pop() {
                match task {
                    Task::Text(s) => f.write_str(s)?,
                    Task::Node(node) => match node {
                        Self::Atom(a) => {
                            f.debug_tuple("Atom").field(a).finish()?;
                        }
                        Self::Tf(b) => {
                            f.debug_tuple("Tf").field(b).finish()?;
                        }
                        Self::Not(p) => {
                            f.write_str("Not(")?;
                            pending.push(Task::Text(")"));
                            pending.push(Task::Node(p));
                        }
                        Self::Conn(c, p, q) => {
                            f.write_str("Conn(")?;
                            std::fmt::Debug::fmt(c, f)?;
                            f.write_str(", ")?;
                            pending.push(Task::Text(")"));
                            pending.push(Task::Node(q));
                            pending.push(Task::Text(", "));
                            pending.push(Task::Node(p));
                        }
                        Self::Qua(q, h, p) => {
                            f.write_str("Qua(")?;
                            std::fmt::Debug::fmt(q, f)?;
                            f.write_str(", ")?;
                            std::fmt::Debug::fmt(h, f)?;
                            f.write_str(", ")?;
                            pending.push(Task::Text(")"));
                            pending.push(Task::Node(p));
                        }
                    },
                }
            }
            Ok(())
        })
    }
}

/// An owned formula child with iterative destruction. Its allocation is the
/// same single Box used by the formula tree; the Option permits safe extraction.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FormulaBox<S, H, C, V>(Option<Box<ProtoFormula<S, H, C, V>>>);

impl<S: std::fmt::Debug, H: std::fmt::Debug, C: std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug
    for FormulaBox<S, H, C, V>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}
impl<S, H, C, V> AsRef<ProtoFormula<S, H, C, V>> for FormulaBox<S, H, C, V> {
    fn as_ref(&self) -> &ProtoFormula<S, H, C, V> {
        self
    }
}
impl<S, H, C, V> From<Box<ProtoFormula<S, H, C, V>>> for FormulaBox<S, H, C, V> {
    fn from(value: Box<ProtoFormula<S, H, C, V>>) -> Self {
        Self(Some(value))
    }
}
impl<S, H, C, V> FormulaBox<S, H, C, V> {
    pub fn into_inner(mut self) -> ProtoFormula<S, H, C, V> {
        *self.0.take().unwrap()
    }
}
impl<S, H, C, V> std::ops::Deref for FormulaBox<S, H, C, V> {
    type Target = ProtoFormula<S, H, C, V>;
    fn deref(&self) -> &Self::Target {
        self.0.as_deref().unwrap()
    }
}
impl<S, H, C, V> Drop for FormulaBox<S, H, C, V> {
    fn drop(&mut self) {
        if let Some(formula) = self.0.take() {
            (*formula).drop_iteratively();
        }
    }
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
    /// Release the formula spine without recursively dropping child boxes.
    /// Atom and binder payloads retain their normal destruction behavior.
    pub fn drop_iteratively(self) {
        // Drop the current subtree before its pending siblings on unwind.
        let mut pending = tamarin_utils::drop_stack::DropStack::from(Vec::new());
        let mut current = self;
        loop {
            match current {
                ProtoFormula::Not(body) | ProtoFormula::Qua(_, _, body) => {
                    current = body.into_inner();
                    continue;
                }
                ProtoFormula::Conn(_, left, right) => {
                    pending.push(right);
                    current = left.into_inner();
                    continue;
                }
                _ => {}
            }
            let Some(next) = pending.pop() else { return };
            current = next.into_inner();
        }
    }

    pub fn ltrue() -> Self {
        ProtoFormula::Tf(true)
    }
    pub fn lfalse() -> Self {
        ProtoFormula::Tf(false)
    }

    pub fn not(self) -> Self {
        ProtoFormula::Not(Box::new(self).into())
    }

    pub fn and(self, other: Self) -> Self {
        ProtoFormula::Conn(
            Connective::And,
            Box::new(self).into(),
            Box::new(other).into(),
        )
    }
    pub fn or(self, other: Self) -> Self {
        ProtoFormula::Conn(
            Connective::Or,
            Box::new(self).into(),
            Box::new(other).into(),
        )
    }
    pub fn implies(self, other: Self) -> Self {
        ProtoFormula::Conn(
            Connective::Imp,
            Box::new(self).into(),
            Box::new(other).into(),
        )
    }
    pub fn iff(self, other: Self) -> Self {
        ProtoFormula::Conn(
            Connective::Iff,
            Box::new(self).into(),
            Box::new(other).into(),
        )
    }

    pub fn for_all(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::All, hint, Box::new(body).into())
    }
    pub fn exists(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::Ex, hint, Box::new(body).into())
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
    t.for_each_lit(|literal| {
        if let Lit::Var(BVar::Free(v)) = literal {
            f(v);
        }
    });
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
    let mut current = fm;
    let mut pending = Vec::new();
    loop {
        match current {
            ProtoFormula::Atom(a) => f(a),
            ProtoFormula::Tf(_) => {}
            ProtoFormula::Not(body) | ProtoFormula::Qua(_, _, body) => {
                current = body;
                continue;
            }
            ProtoFormula::Conn(_, left, right) => {
                pending.push(&**right);
                current = left;
                continue;
            }
        }
        let Some(next) = pending.pop() else {
            return;
        };
        current = next;
    }
}

/// Maximum combined formula-and-term depth on any root-to-leaf path.
#[cfg(test)]
pub(crate) fn formula_depth<S, H, C, V>(fm: &ProtoFormula<S, H, C, V>) -> usize
where
    S: SugarTerms<VTerm<C, BVar<V>>>,
{
    let mut current = (fm, 1usize);
    let mut pending = Vec::new();
    let mut maximum = 1;
    loop {
        let (node, depth) = current;
        match node {
            ProtoFormula::Atom(atom) => {
                maximum = maximum.max(depth);
                fold_atom(atom, &mut |term| {
                    maximum =
                        maximum.max(depth.saturating_add(tamarin_term::term::term_depth(term)));
                });
            }
            ProtoFormula::Tf(_) => maximum = maximum.max(depth),
            ProtoFormula::Not(body) | ProtoFormula::Qua(_, _, body) => {
                current = (body, depth.saturating_add(1));
                continue;
            }
            ProtoFormula::Conn(_, left, right) => {
                let child_depth = depth.saturating_add(1);
                pending.push((&**right, child_depth));
                current = (left, child_depth);
                continue;
            }
        }
        let Some(next) = pending.pop() else {
            return maximum;
        };
        current = next;
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

enum FormulaFrame<I, O, H> {
    Not,
    Qua(Quantifier, H),
    Left(Connective, I),
    Right(Connective, O),
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
    traverse_formula_atom_scoped(fm, &mut |_, atom| f(atom))
}

fn traverse_formula_atom_scoped<S, S2, H, C, C2, V, V2, E>(
    fm: &ProtoFormula<S, H, C, V>,
    f: &mut dyn FnMut(
        u64,
        &ProtoAtom<S, VTerm<C, BVar<V>>>,
    ) -> Result<ProtoFormula<S2, H, C2, V2>, E>,
) -> Result<ProtoFormula<S2, H, C2, V2>, E>
where
    H: Clone,
{
    match fm {
        ProtoFormula::Atom(a) => return f(0, a),
        ProtoFormula::Tf(b) => return Ok(ProtoFormula::Tf(*b)),
        _ => {}
    }
    let mut current = (fm, 0u64);
    let mut pending = Vec::new();
    loop {
        let (input, depth) = current;
        let mut result = match input {
            ProtoFormula::Atom(a) => f(depth, a)?,
            ProtoFormula::Tf(b) => ProtoFormula::Tf(*b),
            ProtoFormula::Not(body) => {
                pending.push(FormulaFrame::Not);
                current = (body, depth);
                continue;
            }
            ProtoFormula::Qua(q, h, body) => {
                // The recursive implementation clones the hint before the body.
                pending.push(FormulaFrame::Qua(*q, h.clone()));
                current = (body, depth + 1);
                continue;
            }
            ProtoFormula::Conn(c, left, right) => {
                pending.push(FormulaFrame::Left(*c, (&**right, depth)));
                current = (left, depth);
                continue;
            }
        };
        loop {
            result = match pending.pop() {
                None => return Ok(result),
                Some(FormulaFrame::Not) => ProtoFormula::Not(Box::new(result).into()),
                Some(FormulaFrame::Qua(q, h)) => ProtoFormula::Qua(q, h, Box::new(result).into()),
                Some(FormulaFrame::Left(c, right)) => {
                    pending.push(FormulaFrame::Right(c, Box::new(result).into()));
                    current = right;
                    break;
                }
                Some(FormulaFrame::Right(c, left)) => {
                    ProtoFormula::Conn(c, left, Box::new(result).into())
                }
            };
        }
    }
}

/// Borrow the input and rebuild its atoms once, retaining binder depths.
/// Unlike cloning before `map_atoms`, this allocates only the result spine.
pub fn map_atoms_ref<S, S2, H: Clone, C, C2, V, V2>(
    fm: &ProtoFormula<S, H, C, V>,
    f: &mut dyn FnMut(u64, &ProtoAtom<S, VTerm<C, BVar<V>>>) -> ProtoAtom<S2, VTerm<C2, BVar<V2>>>,
) -> ProtoFormula<S2, H, C2, V2> {
    traverse_formula_atom_scoped(fm, &mut |depth, atom| {
        Ok::<_, std::convert::Infallible>(ProtoFormula::Atom(f(depth, atom)))
    })
    .unwrap()
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
    let fm = match fm {
        ProtoFormula::Atom(a) => return ProtoFormula::Atom(f(0, &a)),
        ProtoFormula::Tf(b) => return ProtoFormula::Tf(b),
        other => other,
    };
    let mut current = (fm, 0u64);
    let mut pending = Vec::new();
    loop {
        let (input, depth) = current;
        let mut result = match input {
            ProtoFormula::Atom(a) => ProtoFormula::Atom(f(depth, &a)),
            ProtoFormula::Tf(b) => ProtoFormula::Tf(b),
            ProtoFormula::Not(body) => {
                pending.push(FormulaFrame::Not);
                current = (body.into_inner(), depth);
                continue;
            }
            ProtoFormula::Qua(q, h, body) => {
                pending.push(FormulaFrame::Qua(q, h));
                current = (body.into_inner(), depth + 1);
                continue;
            }
            ProtoFormula::Conn(c, left, right) => {
                pending.push(FormulaFrame::Left(c, (right, depth)));
                current = (left.into_inner(), depth);
                continue;
            }
        };
        loop {
            result = match pending.pop() {
                None => return result,
                Some(FormulaFrame::Not) => ProtoFormula::Not(Box::new(result).into()),
                Some(FormulaFrame::Qua(q, h)) => ProtoFormula::Qua(q, h, Box::new(result).into()),
                Some(FormulaFrame::Left(c, right)) => {
                    pending.push(FormulaFrame::Right(c, Box::new(result).into()));
                    let (right, depth) = right;
                    current = (right.into_inner(), depth);
                    break;
                }
                Some(FormulaFrame::Right(c, left)) => {
                    ProtoFormula::Conn(c, left, Box::new(result).into())
                }
            };
        }
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
    traverse_formula_atom(fm, &mut |a| match a {
        ProtoAtom::Syntactic(_) => Err(()),
        _ => Ok(ProtoFormula::Atom(to_atom(a.clone()))),
    })
    .ok()
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
    let mut current = f;
    let mut pending = Vec::new();
    loop {
        let mut result = match current {
            p::Formula::True => ProtoFormula::Tf(true),
            p::Formula::False => ProtoFormula::Tf(false),
            p::Formula::Atom(a) => ProtoFormula::Atom(atom_from_parser::<F>(a, sig)?),
            p::Formula::Not(body) => {
                pending.push(FormulaFrame::Not);
                current = body;
                continue;
            }
            p::Formula::And(l, r)
            | p::Formula::Or(l, r)
            | p::Formula::Implies(l, r)
            | p::Formula::Iff(l, r) => {
                let c = match current {
                    p::Formula::And(..) => Connective::And,
                    p::Formula::Or(..) => Connective::Or,
                    p::Formula::Implies(..) => Connective::Imp,
                    _ => Connective::Iff,
                };
                pending.push(FormulaFrame::Left(c, &**r));
                current = l;
                continue;
            }
            p::Formula::Forall(vs, body) | p::Formula::Exists(vs, body) => {
                let q = if matches!(current, p::Formula::Forall(..)) {
                    Quantifier::All
                } else {
                    Quantifier::Ex
                };
                pending.push(FormulaFrame::Qua(q, vs.as_slice()));
                current = body;
                continue;
            }
        };
        loop {
            result = match pending.pop() {
                None => return Ok(result),
                Some(FormulaFrame::Not) => ProtoFormula::Not(Box::new(result).into()),
                Some(FormulaFrame::Qua(q, vs)) => close_binders::<F>(
                    if q == Quantifier::All {
                        for_all_var
                    } else {
                        exists_var
                    },
                    vs,
                    result,
                ),
                Some(FormulaFrame::Left(c, r)) => {
                    pending.push(FormulaFrame::Right(c, Box::new(result).into()));
                    current = r;
                    break;
                }
                Some(FormulaFrame::Right(c, l)) => {
                    ProtoFormula::Conn(c, l, Box::new(result).into())
                }
            };
        }
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
    let opened = map_atoms_ref(body, &mut |i, a| {
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
    let ProtoFormula::Qua(qua, _, _) = f else {
        panic!("openFormulaPrefix: no outermost quantifier")
    };
    let qua = *qua;
    let mut xs = Vec::new();
    let mut body = f;
    while let ProtoFormula::Qua(next, (name, sort), inner) = body {
        if *next != qua {
            break;
        }
        xs.push(fresh_lvar(fresh, name, *sort));
        body = inner;
    }
    // The prefix is indexed innermost first; binders retained in the body
    // add their depth. Out-of-prefix indices stay bound, just as open_binder
    // leaves them untouched on each of its former successive passes.
    let opened = map_atoms_ref(body, &mut |depth, atom| {
        map_atom(atom, &mut |term| {
            map_lits(term, &mut |lit| match lit {
                Lit::Var(BVar::Bound(index)) => index
                    .checked_sub(depth)
                    .and_then(|offset| usize::try_from(offset).ok())
                    .filter(|offset| *offset < xs.len())
                    .map_or_else(
                        || lit.clone(),
                        |offset| Lit::Var(BVar::Free(xs[xs.len() - 1 - offset])),
                    ),
                _ => lit.clone(),
            })
        })
    });
    (xs, qua, opened)
}

#[cfg(test)]
#[path = "formula_tests.rs"]
mod tests;
