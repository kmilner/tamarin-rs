// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Syntactic.Predicate` from
//! `lib/theory/src/Theory/Syntactic/Predicate.hs`.
//!
//! A predicate names a fact pattern and a formula body; a use site
//! `P(t_1, ..., t_n)` is replaced by that body with the declared parameters
//! bound to the use-site terms. The module holds:
//! - the [`Predicate`] data type, its smart constructor
//!   ([`Predicate::new`], HS `mkPredicate`) and the reading of a
//!   `predicates:` declaration ([`from_parser`], HS's `predicate` production);
//! - [`smaller_fact`] and [`builtin_predicates`], the multiset `(<)`
//!   expansion;
//! - [`lookup_predicate`] and [`expand_formula`], HS `expandFormula`.
//!
//! [`expand_formula`] runs on a [`SyntacticLNFormula`] and returns an
//! [`LNFormula`]: the expansion is what strips the `Pred` sugar.  Every
//! consumer goes through it — the `_restrict` lift, the elaborated lemmas and
//! restrictions, the wellformedness formula reports, the accountability
//! lemma injection, and the `--parse-only` display bridge
//! (`pretty_theory::expand_predicates_for_display`), which projects the
//! result back to the parser AST it prints.

use crate::atom::{map_atom, to_atom, ProtoAtom, SyntacticSugar};
use crate::elaborate::{copy_fact_annotations, fact_tag_of, varspec_to_lvar, ElabError};
use crate::fact::{fact_tag_arity, show_fact_tag, Fact, FactTag, Multiplicity};
use crate::formula::{
    exists_var, map_atoms, traverse_formula_atom, BLNTerm, LNFormula, ProtoFormula,
    SyntacticLNFormula,
};
use tamarin_parser::ast as p;
use tamarin_term::lterm::{BVar, LSort, LVar, Name};
use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::term::map_lits;
use tamarin_term::vterm::{var_term, Lit};

/// A user-defined predicate: a fact-pattern paired with a formula that
/// expands every reference to it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Predicate {
    pub fact: Fact<LVar>,
    pub formula: LNFormula,
}

/// The one failure of [`expand_formula`]: HS `Left $ factTag fa`
/// (Theory/Syntactic/Predicate.hs:90-91), a use site no predicate matches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpandError {
    pub tag: FactTag,
}

impl std::fmt::Display for ExpandError {
    /// HS `show (UndefinedPredicate facttag)`
    /// (Theory/Text/Parser/Exceptions.hs:33-34) = `"undefined predicate " ++
    /// showFactTagArity facttag`, and `showFactTagArity`
    /// (Theory/Model/Fact.hs:555-557) is the name with its multiplicity
    /// prefix, a slash and the arity.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "undefined predicate {}/{}",
            show_fact_tag(&self.tag),
            fact_tag_arity(&self.tag)
        )
    }
}
impl std::error::Error for ExpandError {}

impl Predicate {
    /// `mk_predicate name formula` — capitalise the leading character of
    /// `name`, then build a linear protocol fact carrying the formula's
    /// free variables.
    pub fn new(name: &str, formula: LNFormula, free_vars: Vec<LVar>) -> Self {
        let mut chars = name.chars();
        let cap = match chars.next() {
            Some(c) => c.to_ascii_uppercase().to_string() + chars.as_str(),
            None => String::new(),
        };
        let arity = free_vars.len();
        Predicate {
            fact: Fact::new(
                FactTag::Proto(
                    Multiplicity::Linear,
                    tamarin_term::intern::intern_str(&cap),
                    arity,
                ),
                free_vars,
            ),
            formula,
        }
    }
}

/// One `predicates:` declaration, HS `predicate = Predicate <$> fact' lvar <*
/// symbol "<=>" <*> plainFormula` (Theory/Text/Parser/Signature.hs:271-275).
///
/// The fact comes from the DECLARATION — `fact' lvar` reads the written
/// parameter list — not from the body's free variables, so
/// `Report(x,y) <=> not(y = 'loc')` keeps arity 2.  `plainFormula`
/// (Theory/Text/Parser/Formula.hs:112-117) fails on a body that carries
/// syntactic sugar, which is the sugar check here.
pub fn from_parser(pred: &p::Predicate, sig: &MaudeSig) -> Result<Predicate, ElabError> {
    let mut params: Vec<LVar> = Vec::with_capacity(pred.fact.args.len());
    for a in &pred.fact.args {
        match a {
            p::Term::Var(v) => params.push(varspec_to_lvar(v)),
            _ => {
                return Err(ElabError {
                    message: format!(
                        "predicate `{}` has non-variable parameter; \
                         predicate definitions must use plain variables",
                        pred.fact.name
                    ),
                })
            }
        }
    }
    let fact = Fact::new(fact_tag_of(&pred.fact), params)
        .with_annotations(copy_fact_annotations(&pred.fact));
    let body = crate::formula::from_parser(&pred.formula, sig)?;
    let formula = crate::formula::to_lnformula(&body).ok_or_else(|| ElabError {
        message: "Syntactic sugar is not allowed, guarded formula expected.".to_string(),
    })?;
    Ok(Predicate { fact, formula })
}

/// `smallerFact t1 t2` — the pattern fact for the built-in `Smaller`
/// predicate.
pub fn smaller_fact<T>(t1: T, t2: T) -> Fact<T> {
    Fact::new(
        FactTag::Proto(Multiplicity::Linear, "Smaller", 2),
        vec![t1, t2],
    )
}

/// HS `builtinPredicates` (Theory/Syntactic/Predicate.hs:58-74): the single
/// predicate `Smaller(x, y) <=> ∃ z. y = x ++ z`, over `x`, `y`, `z` all
/// `LVar _ LSortMsg 0`.  The multiset `(<)` operator parses to a `Smaller`
/// use site (`smallerp`, Theory/Text/Parser/Formula.hs:30-38), so this is
/// also its expansion.
///
/// `exists_var` abstracts `z` to `Bound 0` and the union's `f_app` rebuild
/// re-sorts, so the stored body reads `y = (Bound 0 ++ Free x)`.
pub fn builtin_predicates() -> Vec<Predicate> {
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let free = |v: LVar| var_term(BVar::Free(v));
    let body: LNFormula = ProtoFormula::Atom(ProtoAtom::EqE(
        free(y),
        tamarin_term::builtin::union(free(x), free(z)),
    ));
    vec![Predicate {
        fact: smaller_fact(x, y),
        formula: exists_var((z.name.to_string(), z.sort), &z, body),
    }]
}

/// HS `lookupPredicate fact = find (sameName fact . pFact) . (++
/// builtinPredicates)` (Theory/Syntactic/Predicate.hs:76-79): the first
/// predicate whose fact tag equals `fa`'s, searching the declared ones before
/// the built-in list.  `FactTag` carries multiplicity, name and arity, so all
/// three must agree.
pub fn lookup_predicate<T>(fa: &Fact<T>, preds: &[Predicate]) -> Option<Predicate> {
    if let Some(pr) = preds.iter().find(|p| p.fact.tag == fa.tag) {
        return Some(pr.clone());
    }
    builtin_predicates()
        .into_iter()
        .find(|p| p.fact.tag == fa.tag)
}

/// HS `expandFormula` (Theory/Syntactic/Predicate.hs:82-105): replace every
/// `Pred` atom by the matching predicate's body, with the declared parameters
/// bound to the use-site terms.
///
/// The substitution is `compSubst`'s De Bruijn shift: at an atom that sits
/// under `i` of the BODY's own binders, a use-site term's bound indices are
/// raised by `i` so they still name the binders of the use site.  Nothing is
/// renamed, so a body binder and a use-site variable may share a name — they
/// are distinct because one is an index and the other a free variable, and
/// the printer tells them apart by allocating a fresh display index.
pub fn expand_formula(
    preds: &[Predicate],
    fm: &SyntacticLNFormula,
) -> Result<LNFormula, ExpandError> {
    traverse_formula_atom(fm, &mut |a| match a {
        ProtoAtom::Syntactic(SyntacticSugar::Pred(fa)) => match lookup_predicate(fa, preds) {
            Some(pr) => Ok(apply_at_use_site(&pr, fa)),
            None => Err(ExpandError { tag: fa.tag }),
        },
        other => Ok(ProtoFormula::Atom(to_atom(other.clone()))),
    })
}

/// HS `apply' (compSubst (pFact pr) fa) (pFormula pr)`
/// (Theory/Syntactic/Predicate.hs:88, :96-105): the predicate's body with
/// `Free param ↦ use-site term` applied through `mapAtoms`, the substitution
/// rebuilt at each atom's depth so [`shift_bound`] raises the use-site terms
/// past the body's binders.
fn apply_at_use_site(pr: &Predicate, fa: &Fact<BLNTerm>) -> LNFormula {
    let pairs: Vec<(LVar, BLNTerm)> = pr
        .fact
        .terms
        .iter()
        .copied()
        .zip(fa.terms.iter().cloned())
        .collect();
    map_atoms(pr.formula.clone(), &mut |i, a| {
        let s: Subst<Name, BVar<LVar>> = Subst::from_list(
            pairs
                .iter()
                .map(|(v, t)| (BVar::Free(*v), shift_bound(t, i))),
        );
        map_atom(a, &mut |t| apply_vterm(&s, t.clone()))
    })
}

/// HS `up` (Theory/Syntactic/Predicate.hs:103-105): raise every bound index
/// of a use-site term by the number of binders the predicate body wraps it
/// in.  A free variable is left alone.  The rebuild is order-preserving, so
/// the AC argument lists `map_lits` re-sorts come back unchanged.
fn shift_bound(t: &BLNTerm, i: u64) -> BLNTerm {
    if i == 0 {
        return t.clone();
    }
    map_lits(t, &mut |l| match l {
        Lit::Var(BVar::Bound(j)) => Lit::Var(BVar::Bound(j + i)),
        other => other.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_formula::pretty_lnformula;
    use crate::theory::TheoryItem;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_term::term::Term;

    /// The predicates of a theory that declares nothing else.
    fn pred(decl: &str) -> Vec<Predicate> {
        let src = format!("theory T begin\npredicates: {}\nend", decl);
        let thy = tamarin_parser::parse_theory(&src, &[]).unwrap();
        thy.items
            .iter()
            .filter_map(|it| match it {
                p::TheoryItem::Predicates(ps) => Some(ps),
                _ => None,
            })
            .flatten()
            .map(|pd| from_parser(pd, &pair_maude_sig()).unwrap())
            .collect()
    }

    fn closed(src: &str) -> SyntacticLNFormula {
        let f = parse_formula_str(src, &pair_maude_sig()).unwrap();
        crate::formula::from_parser(&f, &pair_maude_sig()).unwrap()
    }

    fn has_pred_atom<H>(f: &ProtoFormula<SyntacticSugar<BLNTerm>, H, Name, LVar>) -> bool {
        match f {
            ProtoFormula::Atom(ProtoAtom::Syntactic(_)) => true,
            ProtoFormula::Atom(_) | ProtoFormula::Tf(_) => false,
            ProtoFormula::Not(g) => has_pred_atom(g),
            ProtoFormula::Conn(_, a, b) => has_pred_atom(a) || has_pred_atom(b),
            ProtoFormula::Qua(_, _, b) => has_pred_atom(b),
        }
    }

    #[test]
    fn capitalisation_in_constructor() {
        let f: LNFormula = ProtoFormula::ltrue();
        let pr = Predicate::new("smaller", f, vec![]);
        assert!(matches!(pr.fact.tag, FactTag::Proto(_, n, _) if n == "Smaller"));
    }

    /// HS `smallerFact` builds `protoFact Linear "Smaller" [t1, t2]`
    /// (Theory/Syntactic/Predicate.hs:50-56).  This is the tag that
    /// [`lookup_predicate`] matches on.  It is also the operand order that
    /// the `∃ z. t2 = t1 ++ z` expansion depends on.
    #[test]
    fn smaller_fact_tag_and_operand_order() {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let f: Fact<LVar> = smaller_fact(x, y);
        assert_eq!(
            f.tag,
            FactTag::Proto(Multiplicity::Linear, "Smaller", 2),
            "linear, named `Smaller`, arity 2"
        );
        assert_eq!(f.terms.to_vec(), vec![x, y], "operands keep source order");
    }

    /// The built-in body is `∃ z. y = (x ++ z)` with `z` abstracted, and the
    /// union is AC-sorted after the abstraction — `Bound 0` sorts before
    /// `Free x` under the derived `Ord BVar` (`Bound` is the first variant,
    /// LTerm.hs:476-478).
    #[test]
    fn builtin_smaller_binds_z_as_the_first_union_operand() {
        let bs = builtin_predicates();
        assert_eq!(bs.len(), 1, "one built-in predicate");
        let body = match &bs[0].formula {
            ProtoFormula::Qua(q, h, b) => {
                assert_eq!(*q, crate::formula::Quantifier::Ex);
                assert_eq!(h, &("z".to_string(), LSort::Msg));
                b.as_ref().clone()
            }
            other => panic!("expected an existential, got {other:?}"),
        };
        let (lhs, rhs) = match body {
            ProtoFormula::Atom(ProtoAtom::EqE(l, r)) => (l, r),
            other => panic!("expected an equality, got {other:?}"),
        };
        assert_eq!(lhs, var_term(BVar::Free(LVar::new("y", LSort::Msg, 0))));
        match rhs {
            Term::App(_, args) => assert_eq!(
                args.to_vec(),
                vec![
                    var_term(BVar::Bound(0)),
                    var_term(BVar::Free(LVar::new("x", LSort::Msg, 0)))
                ],
            ),
            other => panic!("expected a union application, got {other:?}"),
        }
    }

    #[test]
    fn lookup_finds_a_declared_predicate_before_the_builtin() {
        let preds = pred("Smaller(a, b) <=> a = b");
        let probe: Fact<LVar> = Fact::new(preds[0].fact.tag, vec![]);
        assert_eq!(lookup_predicate(&probe, &preds).unwrap(), preds[0]);
        assert_eq!(
            lookup_predicate(&probe, &[]).unwrap(),
            builtin_predicates()[0],
            "with nothing declared the built-in answers the same tag"
        );
    }

    /// HS's `predicate` production reads the body with `plainFormula`, which
    /// fails with "Syntactic sugar is not allowed, guarded formula expected."
    /// (Theory/Text/Parser/Formula.hs:112-117).  A predicate call inside a
    /// predicate body is exactly that sugar.
    #[test]
    fn a_sugared_predicate_body_is_rejected() {
        let src = "theory T begin\npredicates: P(x) <=> Q(x)\nend";
        let thy = tamarin_parser::parse_theory(src, &[]).unwrap();
        let decl = thy
            .items
            .iter()
            .find_map(|it| match it {
                p::TheoryItem::Predicates(ps) => ps.first(),
                _ => None,
            })
            .unwrap();
        let err = from_parser(decl, &pair_maude_sig()).expect_err("expected a rejection");
        assert_eq!(
            err.message,
            "Syntactic sugar is not allowed, guarded formula expected."
        );
    }

    /// The expansion replaces the use-site atom with the predicate's body and
    /// maps the declared parameter to the use-site argument.  The oracle
    /// (Git revision ef3f0468) renders this lemma as `∀ x. ∃ #i. A( x ) @ #i`.
    #[test]
    fn expand_simple_predicate() {
        let preds = pred("P(x) <=> Ex #i. A(x) @ #i");
        let out = expand_formula(&preds, &closed("All x. P(x)")).unwrap();
        assert_eq!(
            pretty_lnformula(&out),
            "\u{2200} x. \u{2203} #i. A( x ) @ #i"
        );
    }

    #[test]
    fn expand_undefined_predicate_errors() {
        // `UndefinedPred(x)` closes to a `Pred` atom; with no matching
        // predicate the expansion reports `UndefinedPredicate`.  Probed
        // against the v1.13.0 prover: `... ==> P(x)` reports
        // `undefined predicate P/1`.
        let err = expand_formula(&[], &closed("All x. UndefinedPred(x)"))
            .expect_err("expected undefined-predicate error");
        assert_eq!(err.to_string(), "undefined predicate UndefinedPred/1");
    }

    #[test]
    fn expand_arity_mismatch_is_undefined_predicate() {
        // `lookup_predicate` matches the FULL `FactTag` (multiplicity, name
        // and arity), so a use site whose arity differs from the declaration
        // does not match and falls through to `UndefinedPredicate`.  Probed
        // against the v1.13.0 prover: `predicates: P(x) <=> ...` used as
        // `P(a, b)` reports `undefined predicate P/2` — NOT a bespoke "arity
        // mismatch".
        let preds = pred("P(x) <=> Ex #i. A(x) @ #i");
        let err = expand_formula(&preds, &closed("All a b. P(a, b)"))
            .expect_err("expected undefined-predicate error");
        assert_eq!(err.to_string(), "undefined predicate P/2");
    }

    /// HS adds case tests and accountability lemmas verbatim
    /// (`liftedAddCaseTest` / `liftedAddAccLemma`,
    /// Theory/Text/Parser.hs:153-163) with NO predicate expansion — their
    /// `Pred` sugar stays intact for the accountability translation.  Only
    /// `liftedAddLemma` and the restriction path expand
    /// (TheoryObject.hs:433-449).
    #[test]
    fn case_test_and_acc_lemma_keep_pred_atoms() {
        let src = "theory T begin\n\
            predicates: P(x) <=> Ex #i. A(x) @ #i\n\
            test ct:\n  \"P(a)\"\n\
            lemma acc:\n  ct account for\n    \"All x. P(x)\"\n\
            lemma reg:\n  \"All x. P(x)\"\n\
            end";
        let thy = tamarin_parser::parse_theory(src, &[]).unwrap();
        let elab = crate::elaborate::elaborate(&thy).unwrap();
        let mut saw_ct = false;
        let mut saw_acc = false;
        let mut saw_reg = false;
        for item in &elab.items {
            match item {
                TheoryItem::Translation(crate::theory::TranslationElement::CaseTest(c)) => {
                    saw_ct = true;
                    assert!(
                        has_pred_atom(&c.formula),
                        "case test must keep its Pred atom: {:?}",
                        c.formula
                    );
                }
                TheoryItem::Translation(crate::theory::TranslationElement::AccLemma(a)) => {
                    saw_acc = true;
                    assert!(
                        has_pred_atom(&a.formula),
                        "accountability lemma must keep its Pred atom: {:?}",
                        a.formula
                    );
                }
                TheoryItem::Lemma(l) => {
                    saw_reg = true;
                    assert_eq!(
                        pretty_lnformula(&l.formula),
                        "\u{2200} x. \u{2203} #i. A( x ) @ #i",
                        "regular lemma must carry the predicate's body"
                    );
                }
                _ => {}
            }
        }
        assert!(
            saw_ct && saw_acc && saw_reg,
            "expected all three item kinds (ct={saw_ct}, acc={saw_acc}, reg={saw_reg})"
        );
    }

    /// `P(x) <=> Ex z #i. Act(x, z) @ #i` applied at `P(z)` splices the body
    /// unrenamed: the body's binder stays the index it was, and the use-site
    /// `z` stays free, so the two are distinct.  The printer allocates the
    /// binder a display index past the free `z`.  Oracle bytes (Git revision
    /// ef3f0468, probe `S6_pred_capture.spthy`): `∃ z.1 #i. Act( z, z.1 ) @ #i`.
    #[test]
    fn expand_avoids_variable_capture() {
        let preds = pred("P(x) <=> Ex z #i. Act(x, z) @ #i");
        let out = expand_formula(&preds, &closed("P(z)")).unwrap();
        assert_eq!(
            pretty_lnformula(&out),
            "\u{2203} z.1 #i. Act( z, z.1 ) @ #i"
        );
    }

    /// The multiset `(<)` operator has no dedicated atom: it closes to a
    /// `Smaller` `Pred` atom, which the built-in predicate rewrites to
    /// `∃ z. rhs = lhs ++ z`.  Probed against the v1.13.0 prover on
    /// `All x y #i. Foo(x,y)@#i ==> x (<) y`, which prints
    /// `∀ x y #i. (Foo( x, y ) @ #i) ⇒ (∃ z. y = (x++z))`.
    #[test]
    fn expand_lessmset_to_smaller_existential() {
        let out = expand_formula(&[], &closed("x (<) y")).unwrap();
        assert_eq!(pretty_lnformula(&out), "\u{2203} z. y = (x++z)");
    }

    /// The built-in's binder and a use site that mentions `z` stay apart the
    /// same way: the binder is an index, the use-site `z` is free.  Oracle
    /// bytes (Git revision ef3f0468, probe `S6_pred_capture.spthy`):
    /// `∃ z.1. y = (z++z.1)`.
    #[test]
    fn expand_lessmset_capture_avoids_z() {
        let out = expand_formula(&[], &closed("z (<) y")).unwrap();
        assert_eq!(pretty_lnformula(&out), "\u{2203} z.1. y = (z++z.1)");
    }
}
