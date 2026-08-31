// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.Report` (`lib/sapic/src/Sapic/Report.hs`) — the
//! `locations-report` (`builtins: locations-report`) translation, gated on
//! `_transReport` (`OpenTheory` option set from the `locations-report` builtin).
//!
//! Two passes, both run only when `_transReport` is set:
//!
//!   1. `translateTermsReport` (Report.hs:100-101): `reportMapTerms subst
//!      Nothing` — propagate the per-process `@location` annotation down the
//!      tree and, where a `Just loc` is in scope, rewrite every `report(t)`
//!      term to `rep(subst loc t, loc)` (`subst`, Report.hs:91-98). This also
//!      reaches condition and embedded-MSR formulas, matching upstream #922.
//!
//!   2. `reportInit` (Report.hs:28-41): prepend the fixed `ReportRule`
//!         [ In( <x, loc> ) ] --[ <Report(x,loc) predicate restriction> ]->
//!         [ Out( rep(x, loc) ) ]
//!      to the initial rules.  Its embedded restriction is the syntactic
//!      predicate atom `Pred (Report x loc)`, which `liftedAddProtoRule`
//!      (`apply.rs`) binds to the user-defined `Report` predicate, producing
//!      the `Restr_ReportRule_1` restriction and the `Restr_ReportRule_1(...)`
//!      action.
//!
//! `x` and `loc` are HS `LVar s LSortMsg 0` (Report.hs:37-39).

use std::collections::BTreeSet;

use tamarin_term::lterm::{BVar, LNTerm, LSort, LVar, Name};
use tamarin_term::term::map_lits;
use tamarin_term::vterm::{var_term, Lit, VTerm};

use tamarin_theory::atom::{map_atom, ProtoAtom, SyntacticSugar};
use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
use tamarin_theory::formula::{map_atoms, ProtoFormula};
use tamarin_theory::sapic::{
    Process, ProcessCombinator, SapicAction, SapicFormula, SapicLVar, SapicTerm,
};

use crate::annotation::ProcessAnnotation;
use crate::facts::{AnnotatedRule, RulePosition, SpecialPosition, TransFact};

type AnnProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// `reportInit` (Report.hs:28-41): prepend the `ReportRule` to the initial
/// rules.  `init_tx` is threaded unchanged.
///
///   reportrule = AnnotatedRule (Just "ReportRule") anP (Right NoPosition)
///                  [In $ fAppPair (varTerm x, varTerm loc)]   -- prem
///                  []                                          -- acts
///                  [Out $ fAppNoEq repSym [varTerm x, varTerm loc]]  -- concl
///                  [Ato protFact]                              -- restr
///                  0
///   protFact = Syntactic . Pred $ protoFact Linear "Report" [varTerm x, varTerm loc]
pub(crate) fn report_init(
    an_proc: &AnnProc,
    init_rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>>,
    init_tx: BTreeSet<LVar>,
) -> (Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>) {
    // `x`, `loc` :: LVar _ LSortMsg 0.
    let x = LVar::new("x", LSort::Msg, 0);
    let loc = LVar::new("loc", LSort::Msg, 0);
    let xt: LNTerm = var_term(x);
    let loct: LNTerm = var_term(loc);

    // prem: In( <x, loc> )
    let prem = TransFact::In(tamarin_term::builtin::pair(xt.clone(), loct.clone()));
    // concl: Out( rep(x, loc) )  (rep = private constructor)
    let rep = tamarin_term::term::f_app_no_eq(tamarin_term::builtin::rep_sym(), vec![xt, loct]);
    let concl = TransFact::Out(rep);

    // restr: `Syntactic . Pred $ protoFact Linear "Report" [varTerm (Free x),
    // varTerm (Free loc)]` (Report.hs:41).  The `_restrict` expansion
    // (`apply.rs`) binds it to the user `Report` predicate.
    let report_pred = ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(
        FactTag::Proto(Multiplicity::Linear, "Report", 2),
        vec![var_term(BVar::Free(x)), var_term(BVar::Free(loc))],
    ))));

    let report_rule = AnnotatedRule {
        process_name: Some("ReportRule".to_string()),
        process: an_proc.clone(),
        position: RulePosition::Special(SpecialPosition::NoPosition),
        prems: vec![prem],
        acts: vec![],
        concs: vec![concl],
        restr: vec![report_pred],
        index: 0,
    };

    // `reportrule : initrules` — prepend.
    let mut out = Vec::with_capacity(init_rules.len() + 1);
    out.push(report_rule);
    out.extend(init_rules);
    (out, init_tx)
}

// =============================================================================
// translateTermsReport (Report.hs:50-101)
// =============================================================================

/// `translateTermsReport = reportMapTerms subst Nothing` (Report.hs:100-101):
/// walk the process, threading the in-scope `@location` annotation down via
/// `opt_loc`, and rewrite `report(t)` terms in actions / combinators to
/// `rep(subst loc t, loc)` wherever a `Just loc` is in scope.
pub(crate) fn translate_terms_report(p: AnnProc) -> AnnProc {
    report_map_terms(None, p)
}

/// `opt_loc loc ann` (Report.hs:44-48): the location at this node — the node's
/// own parsed `location` if set, otherwise the inherited `loc`.
fn opt_loc(loc: &Option<SapicTerm>, ann: &ProcessAnnotation<LVar>) -> Option<SapicTerm> {
    match &ann.parsing_ann.location {
        Some(x) => Some(x.clone()),
        None => loc.clone(),
    }
}

/// `reportMapTerms f loc` (Report.hs:54-59).  `f = subst`.
fn report_map_terms(loc: Option<SapicTerm>, p: AnnProc) -> AnnProc {
    match p {
        Process::Null(ann) => Process::Null(ann),
        Process::Action(ac, ann, body) => {
            let here = opt_loc(&loc, &ann);
            let ac2 = report_map_terms_action(&here, ac);
            Process::Action(ac2, ann, Box::new(report_map_terms(here, *body)))
        }
        Process::Comb(c, ann, l, r) => {
            let here = opt_loc(&loc, &ann);
            let c2 = report_map_terms_comb(&here, c);
            Process::Comb(
                c2,
                ann,
                Box::new(report_map_terms(here.clone(), *l)),
                Box::new(report_map_terms(here, *r)),
            )
        }
    }
}

/// `reportMapTermsAction f loc ac` (Report.hs:60-79): apply `subst loc` to the
/// terms of each action.  `New`, `Rep`, `ProcessCall` are identity.
/// Upstream #922 also maps embedded MSR restriction formulas.
fn report_map_terms_action(
    loc: &Option<SapicTerm>,
    ac: SapicAction<SapicLVar>,
) -> SapicAction<SapicLVar> {
    match ac {
        SapicAction::New(v) => SapicAction::New(v),
        SapicAction::Rep => SapicAction::Rep,
        SapicAction::ProcessCall(name, args) => SapicAction::ProcessCall(name, args),
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => SapicAction::ChIn {
            chan: chan.map(|t| subst(loc, &t)),
            msg: subst(loc, &msg),
            match_vars,
        },
        SapicAction::ChOut { chan, msg } => SapicAction::ChOut {
            chan: chan.map(|t| subst(loc, &t)),
            msg: subst(loc, &msg),
        },
        SapicAction::Insert(t1, t2) => SapicAction::Insert(subst(loc, &t1), subst(loc, &t2)),
        SapicAction::Delete(t) => SapicAction::Delete(subst(loc, &t)),
        SapicAction::Lock(t) => SapicAction::Lock(subst(loc, &t)),
        SapicAction::Unlock(t) => SapicAction::Unlock(subst(loc, &t)),
        SapicAction::Event(fa) => SapicAction::Event(map_fact_terms(loc, fa)),
        SapicAction::Msr {
            prems,
            acts,
            concs,
            rest,
            match_vars,
        } => SapicAction::Msr {
            prems: prems.into_iter().map(|f| map_fact_terms(loc, f)).collect(),
            acts: acts.into_iter().map(|f| map_fact_terms(loc, f)).collect(),
            concs: concs.into_iter().map(|f| map_fact_terms(loc, f)).collect(),
            rest: rest
                .into_iter()
                .map(|formula| subst_formula(loc, formula))
                .collect(),
            match_vars,
        },
    }
}

/// `reportMapTermsComb f loc c` (Report.hs:80-89): `CondEq`, `Let`, `Lookup`
/// have their terms `subst`'d; upstream #922 maps formula terms in `Cond`.
fn report_map_terms_comb(
    loc: &Option<SapicTerm>,
    c: ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    match c {
        ProcessCombinator::Cond(formula) => ProcessCombinator::Cond(subst_formula(loc, formula)),
        ProcessCombinator::CondEq(t1, t2) => {
            ProcessCombinator::CondEq(subst(loc, &t1), subst(loc, &t2))
        }
        ProcessCombinator::Let {
            left,
            right,
            match_vars,
        } => ProcessCombinator::Let {
            left: subst(loc, &left),
            right: subst(loc, &right),
            match_vars,
        },
        ProcessCombinator::Lookup(t, v) => ProcessCombinator::Lookup(subst(loc, &t), v),
        other => other,
    }
}

/// Apply `subst loc` to every argument term of a SAPIC fact.
fn map_fact_terms(
    loc: &Option<SapicTerm>,
    fa: tamarin_theory::sapic::SapicLNFact,
) -> tamarin_theory::sapic::SapicLNFact {
    fa.map(|t| subst(loc, &t))
}

/// Upstream #922's `substFormula`: lift the location's free variables into
/// the formula term representation, then rewrite every atom term.
fn subst_formula(loc: &Option<SapicTerm>, formula: SapicFormula) -> SapicFormula {
    let formula_loc = loc.as_ref().map(|location| {
        map_lits(location, &mut |lit| match lit {
            Lit::Con(name) => Lit::Con(*name),
            Lit::Var(var) => Lit::Var(BVar::Free(var.clone())),
        })
    });
    map_atoms(formula, &mut |_, atom| {
        map_atom(atom, &mut |term| subst(&formula_loc, term))
    })
}

/// `subst` (Report.hs:91-98): rewrite `report(a)` to `rep(subst loc a, loc)`
/// when a `Just loc` is in scope.  With `Nothing` location it is the identity
/// (`subst Nothing t = t`).
fn subst<V: Clone + Ord>(loc: &Option<VTerm<Name, V>>, t: &VTerm<Name, V>) -> VTerm<Name, V> {
    match loc {
        Some(loc) => subst_at(loc, t),
        None => t.clone(),
    }
}

/// The `subst (Just loc)` arm (Report.hs:93-98).
fn subst_at<V: Clone + Ord>(loc: &VTerm<Name, V>, t: &VTerm<Name, V>) -> VTerm<Name, V> {
    use tamarin_term::function_symbols::FunSym;
    match t {
        // `Lit _ -> t`.
        VTerm::Lit(_) => t.clone(),
        // Upstream #922 makes only the actual report symbol special; another
        // unary application falls through to generic recursion.
        VTerm::App(FunSym::NoEq(s), args) if args.len() == 1 && s.name == b"report" => {
            tamarin_term::term::f_app_no_eq(
                tamarin_term::builtin::rep_sym(),
                vec![subst_at(loc, &args[0]), loc.clone()],
            )
        }
        // `FApp k as -> fApp k (map (subst loc) as)`: use smart constructors
        // so rewriting below an AC symbol leaves its arguments normalised.
        VTerm::App(sym, args) => {
            let new_args = args.iter().map(|a| subst_at(loc, a)).collect();
            tamarin_term::term::f_app(*sym, new_args)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn null() -> AnnProc {
        Process::Null(ProcessAnnotation::default())
    }

    #[test]
    fn report_init_prepends_report_rule() {
        let p = null();
        let (rules, _) = report_init(&p, vec![], BTreeSet::new());
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].process_name.as_deref(), Some("ReportRule"));
        // One premise In(<x,loc>), one conclusion Out(rep(x,loc)), no actions,
        // one embedded restriction (the Report predicate).
        assert_eq!(rules[0].prems.len(), 1);
        assert_eq!(rules[0].concs.len(), 1);
        assert!(rules[0].acts.is_empty());
        assert_eq!(rules[0].restr.len(), 1);
    }

    /// `protFact = Syntactic . Pred $ protoFact Linear "Report" [varTerm
    /// (Free x), varTerm (Free loc)]` (Report.hs:41), over `x` and `loc` =
    /// `LVar s LSortMsg 0` (Report.hs:37-39).  Both arguments are FREE
    /// `BVar`s: the atom stands under no binder, so a `Bound` index there
    /// would resolve against an empty scope.
    #[test]
    fn report_init_builds_the_report_predicate_over_free_bvars() {
        let (rules, _) = report_init(&null(), vec![], BTreeSet::new());
        let ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(fa))) = &rules[0].restr[0]
        else {
            panic!("expected Syntactic (Pred …), got {:?}", rules[0].restr[0]);
        };
        assert_eq!(fa.tag, FactTag::Proto(Multiplicity::Linear, "Report", 2));
        assert!(fa.annotations.is_empty());
        let free = |n: &str| var_term(BVar::Free(LVar::new(n, LSort::Msg, 0)));
        assert_eq!(fa.terms.as_ref(), &[free("x"), free("loc")]);
    }

    #[test]
    fn subst_none_is_identity() {
        let t: SapicTerm = tamarin_term::term::f_app_no_eq(
            tamarin_term::builtin::report_sym(),
            vec![tamarin_term::lterm::pub_term("c")],
        );
        assert_eq!(subst(&None, &t), t);
    }

    #[test]
    fn subst_just_rewrites_report_to_rep() {
        // report('c') with location 'loc' becomes rep('c', 'loc').
        let c: SapicTerm = tamarin_term::lterm::pub_term("c");
        let report_c =
            tamarin_term::term::f_app_no_eq(tamarin_term::builtin::report_sym(), vec![c.clone()]);
        let loc: SapicTerm = tamarin_term::lterm::pub_term("loc");
        let out = subst(&Some(loc.clone()), &report_c);
        match &out {
            VTerm::App(tamarin_term::function_symbols::FunSym::NoEq(s), args) => {
                assert_eq!(s.name, b"rep");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], c);
                assert_eq!(args[1], loc);
            }
            other => panic!("expected rep('c','loc'), got {other:?}"),
        }
    }

    /// Upstream #922 restricts the unary special case to `report` itself, so
    /// another unary application recurses into its argument.
    #[test]
    fn subst_recurses_through_other_unary_applications() {
        use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
        use tamarin_term::term::f_app_no_eq;

        let sym = |n: &[u8], k| {
            NoEqSym::new(
                n.to_vec(),
                k,
                Privacy::Public,
                Constructability::Constructor,
            )
        };
        let loc: SapicTerm = tamarin_term::lterm::pub_term("loc");
        let c: SapicTerm = tamarin_term::lterm::pub_term("c");
        let report_c = f_app_no_eq(tamarin_term::builtin::report_sym(), vec![c.clone()]);

        // The unary `h(report('c'))` keeps h and rewrites its argument.
        let unary = f_app_no_eq(sym(b"h", 1), vec![report_c.clone()]);
        let rewritten = subst(&Some(loc.clone()), &unary);
        let VTerm::App(_, args) = &rewritten else {
            panic!("expected h(..) to survive as an application");
        };
        assert_eq!(
            args[0],
            f_app_no_eq(
                tamarin_term::builtin::rep_sym(),
                vec![c.clone(), loc.clone()]
            )
        );

        // In the binary `g(report('c'), 'c')`, the generic arm rewrites the
        // nested `report`.  That difference is what makes the unary case
        // above a real check.
        let binary = f_app_no_eq(sym(b"g", 2), vec![report_c, c.clone()]);
        let rewritten = subst(&Some(loc.clone()), &binary);
        assert_ne!(rewritten, binary);
        let VTerm::App(_, args) = &rewritten else {
            panic!("expected g(..) to survive as an application");
        };
        assert_eq!(
            args[0],
            f_app_no_eq(tamarin_term::builtin::rep_sym(), vec![c.clone(), loc])
        );
        assert_eq!(args[1], c);
    }

    #[test]
    fn subst_formula_rewrites_report_terms() {
        let c = tamarin_term::lterm::pub_term("c");
        let report_c =
            tamarin_term::term::f_app_no_eq(tamarin_term::builtin::report_sym(), vec![c.clone()]);
        let formula: SapicFormula = ProtoFormula::Atom(ProtoAtom::EqE(report_c.clone(), report_c));
        let loc: SapicTerm = tamarin_term::lterm::pub_term("loc");
        let expected = tamarin_term::term::f_app_no_eq(
            tamarin_term::builtin::rep_sym(),
            vec![c, tamarin_term::lterm::pub_term("loc")],
        );

        let ProtoFormula::Atom(ProtoAtom::EqE(left, right)) = subst_formula(&Some(loc), formula)
        else {
            panic!("expected equality formula");
        };
        assert_eq!(left, expected);
        assert_eq!(right, expected);
    }
}
