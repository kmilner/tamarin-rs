// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Restriction` from
//! `lib/theory/src/Theory/Model/Restriction.hs` — the
//! `ProtoRestriction`/`Restriction` data type, [`apply_macro_in_restriction`]
//! and the rewrite-then-quantify machinery [`from_rule_restriction`] that
//! turns a rule's `_restrict` formula into a global restriction plus the
//! action fact that references it.

use std::collections::BTreeMap;

use tamarin_term::intern::intern_str;
use tamarin_term::lterm::{BVar, LNTerm, LSort, LVar, Name};
use tamarin_term::macro_expand::LNMacro;
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::term::{map_lits, Term};
use tamarin_term::vterm::{var_term, Lit};
use tamarin_utils::fresh::{FastFreshState, MonadFresh};

use crate::atom::{map_atom, ProtoAtom};
use crate::fact::{Fact, FactTag, LNFact, Multiplicity};
use crate::formula::{
    apply_macro_in_formula, for_all_var, formula_frees, formula_frees_list, traverse_formula_atom,
    BLNTerm, LNFormula, ProtoFormula,
};

// Not yet ported: the `--diff` lhs/rhs restriction attributes
// (HS `RestrictionAttribute`); no caller yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RestrictionAttribute {
    LhsRestriction,
    RhsRestriction,
    BothRestriction,
}

/// `ProtoRestriction f` from the Haskell version. We keep it generic to
/// match the SyntacticRestriction / Restriction split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtoRestriction<F> {
    pub name: String,
    /// `_rstrFormula` — the macro- and predicate-expanded formula, which the
    /// solver converts to a guarded formula and the printer shows in the
    /// `expanded formula:` block.
    pub formula: F,
    /// `_rstrOriginalFormula` — the same formula before macro application,
    /// which the printer shows above that block.  HS's
    /// `applyMacroInRestriction` fills it for every restriction of a closed
    /// theory, macros or none (Theory/Model/Restriction.hs:164-166).
    pub original_formula: Option<F>,
}

pub type Restriction = ProtoRestriction<LNFormula>;

/// HS `applyMacroInRestriction` (Theory/Model/Restriction.hs:164-166): the
/// theory's macros applied to the formula, with the formula as it stood
/// recorded as the original one unless the restriction already carries one.
/// HS runs it over every restriction of a closed theory (`closeTheoryItem`,
/// CloseRule.hs:84), macros or none, so `original_formula` ends up filled
/// either way.
pub fn apply_macro_in_restriction(macros: &[LNMacro], r: Restriction) -> Restriction {
    let original = r.original_formula.unwrap_or_else(|| r.formula.clone());
    Restriction {
        name: r.name,
        formula: apply_macro_in_formula(macros, r.formula),
        original_formula: Some(original),
    }
}

/// HS `varNow = LVar "NOW" LSortNode 0` (Theory/Model/Restriction.hs:87-88):
/// the time point the generated restriction binds and the abstraction treats
/// as not free.
fn var_now() -> LVar {
    LVar::new("NOW", LSort::Node, 0)
}

/// HS `restrPrefix` (Theory/Model/Restriction.hs:130-131).
const RESTR_PREFIX: &str = "Restr_";

/// HS `isFree` (Theory/Model/Restriction.hs:127-128): a bound De Bruijn index
/// is not free, and neither is [`var_now`].
fn is_free(bv: &BVar<LVar>) -> bool {
    match bv {
        BVar::Bound(_) => false,
        BVar::Free(v) => *v != var_now(),
    }
}

/// HS `containsVar p t` (Theory/Model/Restriction.hs:121-124): does a variable
/// of `t` satisfy `p`?  A constant literal satisfies nothing.
fn contains_var(t: &BLNTerm, p: &dyn Fn(&BVar<LVar>) -> bool) -> bool {
    match t {
        Term::Lit(Lit::Var(bv)) => p(bv),
        Term::Lit(_) => false,
        Term::App(_, args) => args.iter().any(|a| contains_var(a, p)),
    }
}

/// The fresh supply and the `{fresh ↦ abstracted term}` map [`rewrite`]
/// threads: HS's `FreshT` over a `State (M.Map LVar (Term (Lit c2 LVar)))`
/// (Theory/Model/Restriction.hs:96).
struct RewriteState {
    fresh: FastFreshState,
    subst: BTreeMap<LVar, LNTerm>,
}

impl RewriteState {
    /// HS `substitute` (Theory/Model/Restriction.hs:114-120): draw a fresh
    /// `LSortMsg` variable, record the term it stands for with its `Free`
    /// wrappers dropped (`fmap (fmap fromFree)`), and return the variable.
    fn substitute(&mut self, t: &BLNTerm) -> BLNTerm {
        let v = LVar::new("x", LSort::Msg, self.fresh.fresh_ident("x"));
        let ground = map_lits(t, &mut |l| match l {
            Lit::Con(c) => Lit::Con(*c),
            Lit::Var(bv) => Lit::Var(bv.clone().into_free()),
        });
        self.subst.insert(v, ground);
        var_term(BVar::Free(v))
    }
}

/// HS `fAt` (Theory/Model/Restriction.hs:99-112): abstract the subterms that
/// carry free variables into fresh ones.  A free variable becomes a fresh
/// variable; an application whose arguments carry a free variable and no
/// bound one is abstracted whole; an application that carries both is rebuilt
/// around its abstracted arguments, through `termViewToTerm`
/// (Term/Term/Raw.hs:103-105), which keeps the argument positions the
/// traversal saw; anything else stays.
fn rewrite_term(t: &BLNTerm, st: &mut RewriteState) -> BLNTerm {
    match t {
        Term::Lit(Lit::Var(bv)) if is_free(bv) => st.substitute(t),
        Term::Lit(_) => t.clone(),
        Term::App(sym, args) => {
            if !args.iter().any(|a| contains_var(a, &is_free)) {
                t.clone()
            } else if args.iter().any(|a| contains_var(a, &|bv| !is_free(bv))) {
                Term::App(*sym, args.iter().map(|a| rewrite_term(a, st)).collect())
            } else {
                st.substitute(t)
            }
        }
    }
}

/// HS `rewrite` (Theory/Model/Restriction.hs:90-128): every atom's terms with
/// their free-variable subterms abstracted, plus the map from each fresh
/// variable to the term it stands for.  `traverseFormulaAtom` threads no De
/// Bruijn depth and `traverse` on an `Action` atom visits the time point
/// before the fact's arguments (Theory/Model/Atom.hs:139-140), which is the
/// order the fresh counter — seeded at `0`, so `x`, `x.1`, … — sees them in.
fn rewrite(f: &LNFormula) -> (LNFormula, BTreeMap<LVar, LNTerm>) {
    let mut st = RewriteState {
        fresh: FastFreshState::seeded(0),
        subst: BTreeMap::new(),
    };
    let out = traverse_formula_atom(f, &mut |a| {
        Ok::<LNFormula, std::convert::Infallible>(ProtoFormula::Atom(map_atom(a, &mut |t| {
            rewrite_term(t, &mut st)
        })))
    })
    .unwrap();
    (out, st.subst)
}

/// HS `mkFact` (Theory/Model/Restriction.hs:162): `protoFactAnn Linear
/// (restrPrefix ++ rname) S.empty`, the linear fact `Restr_<rname>`.
fn mk_fact<T>(rname: &str, terms: Vec<T>) -> Fact<T> {
    let arity = terms.len();
    Fact::new(
        FactTag::Proto(
            Multiplicity::Linear,
            intern_str(&format!("{RESTR_PREFIX}{rname}")),
            arity,
        ),
        terms,
    )
}

/// HS `L.delete varNow` in `getBVarTerms`/`getVarTerms`
/// (Theory/Model/Restriction.hs:159-160): drop the FIRST [`var_now`] of the
/// list.
fn delete_var_now(mut vs: Vec<LVar>) -> Vec<LVar> {
    if let Some(i) = vs.iter().position(|v| *v == var_now()) {
        vs.remove(i);
    }
    vs
}

/// HS `fromRuleRestriction rname f` (Theory/Model/Restriction.hs:141-162): the
/// restriction `Restr_<rname>` that states `f` of the time point a rule fired
/// at, and the action fact the rule carries to reach it.
///
/// The restriction's body is `(Restr_<rname>(vs) @ #NOW) ⇒ f'`, where `f'` is
/// `f` with its free-variable subterms abstracted and `vs` are the abstracted
/// variables in `freesList` order (occurrence order, `#NOW` dropped); the
/// binder prefix is `frees` of that whole implication (sorted and
/// deduplicated), so it reads `∀ x #NOW x.1.`.  The action carries the terms
/// the abstraction stood in for, in the same order as `vs`.
pub fn from_rule_restriction(rname: &str, f: &LNFormula) -> (Restriction, LNFact) {
    let (rewritten, abstracted) = rewrite(f);
    let vars = delete_var_now(formula_frees_list(&rewritten));

    // HS `mkRestriction`: `f'' = Ato (Action timepoint fact) .==>. f'` under
    // `foldr (hinted forAll) f'' (frees f'')`, whose first variable is the
    // outermost binder.
    let fact = mk_fact(
        rname,
        vars.iter().map(|v| var_term(BVar::Free(*v))).collect(),
    );
    let body = ProtoFormula::Atom(ProtoAtom::Action(var_term(BVar::Free(var_now())), fact))
        .implies(rewritten);
    let formula = formula_frees(&body).iter().rev().fold(body, |acc, v| {
        for_all_var((v.name.to_string(), v.sort), v, acc)
    });
    let restriction = Restriction {
        name: format!("{RESTR_PREFIX}{rname}"),
        formula,
        original_formula: None,
    };

    // HS `getVarTerms subst`: each abstracted variable back to the term it
    // stands for; `substFromMap` drops the identity mappings, so a variable
    // the abstraction left alone stays itself.
    let subst: Subst<Name, LVar> = Subst::from_map(abstracted);
    let args = vars
        .into_iter()
        .map(|v| apply_vterm(&subst, var_term(v)))
        .collect();
    (restriction, mk_fact(rname, args))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborate::parse_time_signature;
    use crate::fact::show_fact_tag;
    use crate::formula::{Connective, Quantifier};
    use crate::predicate::{expand_formula, Predicate};
    use crate::pretty_formula::pretty_lnformula;
    use tamarin_parser::ast as p;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::maude_sig::MaudeSig;

    /// The signature and the predicates of a theory that declares nothing
    /// else, closed the way `rule_restriction::lift_rule_restrictions` closes
    /// them.
    fn theory(decls: &str) -> (MaudeSig, Vec<Predicate>) {
        let src = format!("theory T begin\n{decls}\nend");
        let thy = tamarin_parser::parse_theory(&src, &[]).unwrap();
        let sig = parse_time_signature(&thy).unwrap();
        let preds = thy
            .items
            .iter()
            .filter_map(|it| match it {
                p::TheoryItem::Predicates(ps) => Some(ps),
                _ => None,
            })
            .flatten()
            .map(|pd| crate::predicate::from_parser(pd, &sig).unwrap())
            .collect();
        (sig, preds)
    }

    /// One `_restrict` formula as the lifting sees it: parsed, closed against
    /// the signature and expanded against the predicates.
    fn restrict(src: &str, sig: &MaudeSig, preds: &[Predicate]) -> LNFormula {
        let f = parse_formula_str(src, sig).unwrap();
        expand_formula(preds, &crate::formula::from_parser(&f, sig).unwrap()).unwrap()
    }

    #[test]
    fn minimal_trace() {
        // True(x) <=> (x = true()); restriction True(eq(x,x)).
        let (sig, preds) = theory("functions: true/0, eq/2\npredicates: True(x) <=> (x = true())");
        let (restr, action) =
            from_rule_restriction("A_1", &restrict("True(eq(x, x))", &sig, &preds));

        assert_eq!(restr.name, "Restr_A_1");
        // Action fact name + ORIGINAL args: the single abstracted argument is
        // the whole `eq(x,x)`.
        assert_eq!(show_fact_tag(&action.tag), "Restr_A_1");
        assert_eq!(action.terms.len(), 1);
        match &action.terms[0] {
            Term::App(FunSym::NoEq(sym), args) => {
                assert_eq!(sym.name, b"eq");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected eq(x,x), got {other:?}"),
        }

        // The formula has two binders: the abstracted `x` (Msg) and `#NOW`
        // (Node), in `frees`' sorted order — `x` then `NOW`.
        let ProtoFormula::Qua(Quantifier::All, outer, body) = &restr.formula else {
            panic!("expected a universal, got {:?}", restr.formula);
        };
        assert_eq!(outer, &("x".to_string(), LSort::Msg));
        let ProtoFormula::Qua(Quantifier::All, inner, body) = &**body else {
            panic!("expected a second universal, got {body:?}");
        };
        assert_eq!(inner, &("NOW".to_string(), LSort::Node));

        // HS `f'' = (Action #NOW fact) ==> f'`.  The generated action is the
        // antecedent and the rewritten body the consequent.  A swap of the two
        // keeps the formula an implication and inverts the restriction.
        let ProtoFormula::Conn(Connective::Imp, ante, conseq) = &**body else {
            panic!("expected an implication, got {body:?}");
        };
        assert_eq!(
            **ante,
            ProtoFormula::Atom(ProtoAtom::Action(
                var_term(BVar::Bound(0)),
                mk_fact("A_1", vec![var_term(BVar::Bound(1))]),
            ))
        );
        // The consequent is the body of the predicate.  The complete `eq(x,x)`
        // subterm becomes the fresh `x`.  The nullary constant `true` stays
        // inline as a 0-ary application: the abstraction never reaches it.
        let ProtoFormula::Atom(ProtoAtom::EqE(l, r)) = &**conseq else {
            panic!("expected an equality, got {conseq:?}");
        };
        assert_eq!(*l, var_term(BVar::Bound(1)));
        assert!(
            matches!(r, Term::App(FunSym::NoEq(sym), args) if sym.name == b"true" && args.is_empty()),
            "expected the nullary `true`, got {r:?}"
        );
    }

    #[test]
    fn restriction_binder_identity_is_the_full_variable() {
        // `∀ #i` binds a De Bruijn index; the `i` in the message position of
        // `A(i)` is a free variable, so the abstraction takes it and leaves
        // the time point alone.
        let (sig, _) = theory("functions: h/1");
        let phi = restrict("All #i. A(i) @ #i", &sig, &[]);
        let (rewr, subst) = rewrite(&phi);
        let ProtoFormula::Qua(Quantifier::All, hint, body) = &rewr else {
            panic!("expected a universal, got {rewr:?}");
        };
        assert_eq!(hint, &("i".to_string(), LSort::Node));
        let ProtoFormula::Atom(ProtoAtom::Action(tp, fa)) = &**body else {
            panic!("expected an action atom, got {body:?}");
        };
        let fresh = LVar::new("x", LSort::Msg, 0);
        assert_eq!(fa.terms.to_vec(), vec![var_term(BVar::Free(fresh))]);
        assert_eq!(*tp, var_term(BVar::Bound(0)));
        assert_eq!(
            subst.get(&fresh),
            Some(&var_term(LVar::new("i", LSort::Msg, 0)))
        );

        // `∀ x:msg` binds the message-sorted `x`, and the bare body `x` is
        // that binder's index: nothing is abstracted.
        let phi = restrict("All x:msg #i. A(x) @ #i", &sig, &[]);
        let (rewr, subst) = rewrite(&phi);
        assert!(subst.is_empty(), "nothing to abstract, got {subst:?}");
        assert_eq!(rewr, phi);
    }

    /// HS's `Traversable (ProtoAtom s)` runs `Action <$> f i <*> traverse f fa`
    /// (Theory/Model/Atom.hs:139-140) and its `Foldable` folds in the same
    /// order (Theory/Model/Atom.hs:130-131), so an action atom's time point is
    /// abstracted — and folded into `freesList` — before the fact's arguments.
    /// Only a `_restrict` whose time point is FREE tells the two orders apart.
    #[test]
    fn abstracted_timepoint_precedes_the_fact_arguments() {
        let (sig, _) = theory("functions: f/2");
        let (restr, action) = from_rule_restriction("A_1", &restrict("B(f(x,y)) @ #i", &sig, &[]));
        assert_eq!(
            pretty_lnformula(&restr.formula),
            "∀ x #NOW x.1. (Restr_A_1( x, x.1 ) @ #NOW) ⇒ (B( x.1 ) @ x)"
        );
        assert_eq!(action.terms.len(), 2);
        assert_eq!(
            action.terms[0],
            var_term(LVar::new("i", LSort::Node, 0)),
            "the time point's abstraction comes first"
        );
        match &action.terms[1] {
            Term::App(FunSym::NoEq(sym), args) => {
                assert_eq!(sym.name, b"f");
                assert_eq!(
                    args.to_vec(),
                    vec![
                        var_term(LVar::new("x", LSort::Msg, 0)),
                        var_term(LVar::new("y", LSort::Msg, 0)),
                    ]
                );
            }
            other => panic!("expected f(x, y), got {other:?}"),
        }
    }
}
