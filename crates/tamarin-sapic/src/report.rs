// Currently GPL 3.0 until granted permission by the following authors:
//   charlie-j, rkunnema, arcz
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Report.hs

//! Port of `Sapic.Report` (`lib/sapic/src/Sapic/Report.hs`) — the
//! `locations-report` (`builtins: locations-report`) translation, gated on
//! `_transReport` (`OpenTheory` option set from the `locations-report` builtin).
//!
//! Two passes, both run only when `_transReport` is set:
//!
//!   1. `translateTermsReport` (Report.hs:100-101): `reportMapTerms subst
//!      Nothing` — propagate the per-process `@location` annotation down the
//!      tree and, where a `Just loc` is in scope, rewrite every `report(t)`
//!      term to `rep(subst loc t, loc)` (`subst`, Report.hs:91-98).  With the
//!      initial location `Nothing` this is the identity until a `(p)@loc`
//!      annotation supplies a `Just loc`.  In practice the location does not
//!      reach the term-level annotation `reportMapTerms` reads, so `report`
//!      survives verbatim in every corpus file — but the pass is ported
//!      faithfully so a future `Just loc` propagation rewrites correctly.
//!
//!   2. `reportInit` (Report.hs:28-41): prepend the fixed `ReportRule`
//!         [ In( <x, loc> ) ] --[ <Report(x,loc) predicate restriction> ]->
//!         [ Out( rep(x, loc) ) ]
//!      to the initial rules.  Its embedded restriction is the syntactic
//!      predicate atom `Pred (Report x loc)`, which `liftedAddProtoRule`
//!      (`apply.rs` / `rule_restriction::lift_one_rule`) binds to the
//!      user-defined `Report` predicate, producing the `Restr_ReportRule_1`
//!      restriction and the `Restr_ReportRule_1(...)` action.
//!
//! `x` and `loc` are HS `LVar s LSortMsg 0` (Report.hs:37-39).

use std::collections::BTreeSet;

use tamarin_term::lterm::{LSort, LVar, LNTerm};
use tamarin_term::vterm::{Lit, VTerm};

use tamarin_theory::sapic::{
    Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm,
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
pub fn report_init(
    an_proc: &AnnProc,
    init_rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>>,
    init_tx: BTreeSet<LVar>,
) -> (Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>) {
    // `x`, `loc` :: LVar _ LSortMsg 0.
    let x = LVar::new("x", LSort::Msg, 0);
    let loc = LVar::new("loc", LSort::Msg, 0);
    let xt: LNTerm = VTerm::Lit(Lit::Var(x.clone()));
    let loct: LNTerm = VTerm::Lit(Lit::Var(loc.clone()));

    // prem: In( <x, loc> )
    let prem = TransFact::In(tamarin_term::builtin::pair(xt.clone(), loct.clone()));
    // concl: Out( rep(x, loc) )  (rep = private constructor)
    let rep = tamarin_term::term::f_app_no_eq(
        tamarin_term::builtin::rep_sym(),
        vec![xt, loct],
    );
    let concl = TransFact::Out(rep);

    // restr: the syntactic predicate atom `Pred (Report( x, loc ))`, as a
    // parser-AST formula so it flows through the `_restrict` expansion
    // (`lift_one_rule`), which binds it to the user `Report` predicate.
    let report_pred = tamarin_parser::ast::Formula::Atom(tamarin_parser::ast::Atom::Pred(
        tamarin_parser::ast::Fact {
            persistent: false,
            name: "Report".to_string(),
            args: vec![lvar_to_parser(&x), lvar_to_parser(&loc)],
            annotations: Vec::new(),
        },
    ));

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

/// `LVar` → parser-AST `Term::Var` (message-sorted predicate argument).
fn lvar_to_parser(v: &LVar) -> tamarin_parser::ast::Term {
    tamarin_parser::ast::Term::Var(crate::convert::lvar_to_varspec(v))
}

// =============================================================================
// translateTermsReport (Report.hs:50-101)
// =============================================================================

/// `translateTermsReport = reportMapTerms subst Nothing` (Report.hs:100-101):
/// walk the process, threading the in-scope `@location` annotation down via
/// `opt_loc`, and rewrite `report(t)` terms in actions / combinators to
/// `rep(subst loc t, loc)` wherever a `Just loc` is in scope.
pub fn translate_terms_report(p: AnnProc) -> AnnProc {
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
/// terms of each action.  `New`, `Rep`, `ProcessCall` are identity; `MSR`'s
/// restriction-formula map is `undefined` in HS (never exercised) and left
/// unchanged here.
fn report_map_terms_action(
    loc: &Option<SapicTerm>,
    ac: SapicAction<SapicLVar>,
) -> SapicAction<SapicLVar> {
    match ac {
        SapicAction::New(v) => SapicAction::New(v),
        SapicAction::Rep => SapicAction::Rep,
        SapicAction::ProcessCall(name, args) => SapicAction::ProcessCall(name, args),
        SapicAction::ChIn { chan, msg, match_vars } => SapicAction::ChIn {
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
        SapicAction::Msr { prems, acts, concs, rest, match_vars } => SapicAction::Msr {
            prems: prems.into_iter().map(|f| map_fact_terms(loc, f)).collect(),
            acts: acts.into_iter().map(|f| map_fact_terms(loc, f)).collect(),
            concs: concs.into_iter().map(|f| map_fact_terms(loc, f)).collect(),
            // HS `formulaMap = undefined` — never forced; leave unchanged.
            rest,
            match_vars,
        },
    }
}

/// `reportMapTermsComb f loc c` (Report.hs:80-89): `CondEq`, `Let`, `Lookup`
/// have their terms `subst`'d; `Cond` is `undefined` in HS (never forced) and
/// every other combinator is identity.
fn report_map_terms_comb(
    loc: &Option<SapicTerm>,
    c: ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    match c {
        ProcessCombinator::CondEq(t1, t2) => {
            ProcessCombinator::CondEq(subst(loc, &t1), subst(loc, &t2))
        }
        ProcessCombinator::Let { left, right, match_vars } => ProcessCombinator::Let {
            left: subst(loc, &left),
            right: subst(loc, &right),
            match_vars,
        },
        ProcessCombinator::Lookup(t, v) => ProcessCombinator::Lookup(subst(loc, &t), v),
        // `Cond _` is `undefined` in HS (Report.hs:80-89, see line 85); never reached because
        // location-report theories use `if t1 = t2` (CondEq) conditionals.
        // Leave any other combinator unchanged.
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

/// `subst` (Report.hs:91-98): rewrite `report(a)` to `rep(subst loc a, loc)`
/// when a `Just loc` is in scope; recurse structurally otherwise.  With
/// `Nothing` location it is the identity.
fn subst(loc: &Option<SapicTerm>, t: &SapicTerm) -> SapicTerm {
    let Some(loc) = loc else { return t.clone() };
    match t {
        // `Lit _ -> t`.
        VTerm::Lit(_) => t.clone(),
        VTerm::App(sym, args) => {
            use tamarin_term::function_symbols::FunSym;
            // `FApp (NoEq sym) [a] | sym == reportSym = rep(subst loc a, loc)`.
            if let FunSym::NoEq(s) = sym {
                if s.name == b"report" && args.len() == 1 {
                    let inner = subst(&Some(loc.clone()), &args[0]);
                    return tamarin_term::term::f_app_no_eq(
                        tamarin_term::builtin::rep_sym(),
                        vec![inner, loc.clone()],
                    );
                }
            }
            // `FApp k as -> FApp k (map (subst loc) as)`.
            let new_args: Vec<SapicTerm> = args.iter().map(|a| subst(&Some(loc.clone()), a)).collect();
            match sym {
                FunSym::Ac(o) => tamarin_term::term::f_app_ac(*o, new_args),
                FunSym::C(o) => tamarin_term::term::f_app_c(*o, new_args),
                FunSym::NoEq(o) => tamarin_term::term::f_app_no_eq(*o, new_args),
                FunSym::List => tamarin_term::term::f_app_list(new_args),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::sapic::ProcessParsedAnnotation;

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
        // The embedded restriction is a Pred(Report(...)) atom.
        match &rules[0].restr[0] {
            tamarin_parser::ast::Formula::Atom(tamarin_parser::ast::Atom::Pred(fa)) => {
                assert_eq!(fa.name, "Report");
                assert_eq!(fa.args.len(), 2);
            }
            other => panic!("expected Pred(Report(..)), got {other:?}"),
        }
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
        let report_c = tamarin_term::term::f_app_no_eq(
            tamarin_term::builtin::report_sym(),
            vec![c.clone()],
        );
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

    // Force the import (annotation type used in the AnnProc alias).
    #[allow(dead_code)]
    fn _force_annotation(_: ProcessParsedAnnotation) {}
}
