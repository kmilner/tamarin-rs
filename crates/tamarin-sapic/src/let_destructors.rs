// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Strict, innermost-first SAPIC destructor evaluation. Plans stay on the
//! source let, sharing both continuations and separating equation matching
//! from the user's pattern (upstream Sapic.LetDestructors).

use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::function_symbols::{Constructability, FunSym};
use tamarin_term::lterm::{avoid, frees, rename_avoiding, LNTerm, LSort, LVar, Name};
use tamarin_term::subst::Subst;
use tamarin_term::subterm_rule::CtxtStRule;
use tamarin_term::term::f_app;
use tamarin_term::vterm::{var_term, Lit, VTerm};
use tamarin_theory::formula::apply_subst;
use tamarin_theory::sapic::{
    apply_match_vars, map_process, map_terms_action, map_terms_comb, subst_term, Process,
    ProcessCombinator, SapicLVar, SapicTerm,
};
use tamarin_utils::fresh::{FastFreshState, MonadFresh};

use crate::annotation::{AnnotatedProcess, LetStage, ProcessAnnotation};

type Equations = BTreeMap<FunSym, Vec<(Vec<LNTerm>, LNTerm)>>;

pub(crate) fn translate_let_destr(
    macros: &[tamarin_theory::theory::LNMacro],
    rules: &BTreeSet<CtxtStRule>,
    source: AnnotatedProcess<LVar>,
) -> Result<AnnotatedProcess<LVar>, String> {
    let sapic_macros: Vec<_> = macros
        .iter()
        .map(|m| {
            tamarin_term::macro_expand::Macro::new(
                m.name.clone(),
                m.params.iter().map(|v| SapicLVar::untyped(*v)).collect(),
                ln_to_sapic(&m.body),
            )
        })
        .collect();
    let p = if macros.is_empty() {
        source
    } else {
        map_process(
            &source,
            &mut Clone::clone,
            &mut |comb| match comb {
                ProcessCombinator::Let {
                    left,
                    right,
                    match_vars,
                } => ProcessCombinator::Let {
                    left: tamarin_term::macro_expand::apply_macros(&sapic_macros, left.clone()),
                    right: tamarin_term::macro_expand::apply_macros(&sapic_macros, right.clone()),
                    match_vars: match_vars.clone(),
                },
                _ => comb.clone(),
            },
            &mut Clone::clone,
        )
    };
    let source_vars: Vec<_> = crate::typing::vars_proc(&p)
        .into_iter()
        .map(|v| v.var)
        .collect();
    let mut equations = Equations::new();
    for rule in rules {
        let rr = rule.to_rrule();
        if let VTerm::App(f, args) = rr.lhs {
            equations
                .entry(f)
                .or_default()
                .push((args.to_vec(), rr.rhs));
        }
    }
    let mut reserved = source_vars.clone();
    for group in equations.values_mut() {
        *group = rename_avoiding(std::mem::take(group), &source_vars);
        reserved.extend(frees(group));
    }
    let mut fresh = avoid(&reserved);
    map_proc(&equations, &mut fresh, p)
}

fn destructor(t: &SapicTerm) -> bool {
    matches!(t, VTerm::App(FunSym::NoEq(f), _) if f.constructability == Constructability::Destructor)
}

fn contains_destructor(t: &LNTerm) -> bool {
    t.any_fun_sym(
        |f| matches!(f, FunSym::NoEq(s) if s.constructability == Constructability::Destructor),
    )
}

fn fresh_result(fresh: &mut FastFreshState) -> LVar {
    LVar::new("destructor", LSort::Msg, fresh.fresh_ident(""))
}

/// Left-to-right postorder, accumulating each binding exactly once.
fn split_term(
    term: SapicTerm,
    extract: bool,
    fresh: &mut FastFreshState,
    bindings: &mut Vec<(SapicTerm, SapicTerm)>,
) -> SapicTerm {
    let VTerm::App(f, args) = term else {
        return term;
    };
    let args = args
        .iter()
        .cloned()
        .map(|a| split_term(a, true, fresh, bindings))
        .collect();
    let term = f_app(f, args);
    if extract && destructor(&term) {
        let result = var_term(SapicLVar::untyped(fresh_result(fresh)));
        bindings.push((result.clone(), term));
        result
    } else {
        term
    }
}

fn stages(
    equations: &Equations,
    fresh: &mut FastFreshState,
    bindings: Vec<(SapicTerm, SapicTerm)>,
) -> Result<Option<Vec<LetStage>>, String> {
    let mut plan = Vec::new();
    for (pattern, term) in bindings {
        let result = crate::base_translation::to_ln_term(&pattern);
        let bound = frees(&result).into_iter().collect();
        let term = crate::base_translation::to_ln_term(&term);
        if let VTerm::App(f @ FunSym::NoEq(sym), args) = &term
            && sym.constructability == Constructability::Destructor
        {
            let Some(alternatives) = equations.get(f).filter(|es| !es.is_empty()) else {
                return Ok(None);
            };
            if alternatives.iter().any(|(_, rhs)| contains_destructor(rhs)) {
                return Err(
                    "SAPIC destructor equation results must not contain destructor calls.".into(),
                );
            }
            let reduct = fresh_result(fresh);
            plan.push(LetStage {
                input: to_pairs(args),
                alternatives: alternatives
                    .iter()
                    .map(|(args, rhs)| (to_pairs(args), Some(rhs.clone())))
                    .collect(),
                bound: BTreeSet::new(),
            });
            plan.push(LetStage {
                input: var_term(reduct),
                alternatives: vec![(result, None)],
                bound,
            });
        } else {
            plan.push(LetStage {
                input: term,
                alternatives: vec![(result, None)],
                bound,
            });
        }
    }
    Ok(Some(plan))
}

fn map_proc(
    equations: &Equations,
    fresh: &mut FastFreshState,
    p: AnnotatedProcess<LVar>,
) -> Result<AnnotatedProcess<LVar>, String> {
    Ok(match p {
        Process::Null(ann) => Process::Null(ann),
        Process::Action(ac, ann, body) => {
            Process::Action(ac, ann, Box::new(map_proc(equations, fresh, *body)?))
        }
        Process::Comb(c @ ProcessCombinator::Let { .. }, mut ann, pl, pr) => {
            let ProcessCombinator::Let {
                left,
                right,
                match_vars,
            } = &c
            else {
                unreachable!()
            };
            let mut bindings = Vec::new();
            let rhs = split_term(right.clone(), false, fresh, &mut bindings);
            let simple = bindings.is_empty() && !destructor(right);
            bindings.push((left.clone(), rhs));
            let Some(plan) = stages(equations, fresh, bindings)? else {
                return map_proc(equations, fresh, *pr);
            };
            if simple
                && let VTerm::Lit(Lit::Var(v)) = left
                && !match_vars.contains(v)
            {
                return map_proc(
                    equations,
                    fresh,
                    apply_subst_process(&make_let_subst(v, right), *pl),
                );
            }
            ann.let_plan = plan;
            ann.else_branch = !matches!(*pr, Process::Null(_));
            let pl = map_proc(equations, fresh, *pl)?;
            let pr = map_proc(equations, fresh, *pr)?;
            Process::Comb(c, ann, Box::new(pl), Box::new(pr))
        }
        Process::Comb(c, ann, pl, pr) => {
            let pl = map_proc(equations, fresh, *pl)?;
            let pr = map_proc(equations, fresh, *pr)?;
            Process::Comb(c, ann, Box::new(pl), Box::new(pr))
        }
    })
}

/// `toPairs` (LetDestructors.hs): fold a list of terms into a
/// right-nested pair.  `[] -> fAppOne`, `[s] -> s`, `(p:q) -> <p, toPairs q>`.
fn to_pairs(ts: &[LNTerm]) -> LNTerm {
    match ts {
        [] => tamarin_term::term::f_app_no_eq(tamarin_term::function_symbols::one_sym(), vec![]),
        [s] => s.clone(),
        [head, tail @ ..] => {
            let rest = to_pairs(tail);
            tamarin_term::builtin::pair(head.clone(), rest)
        }
    }
}

/// `make_untyped_variant` + `substFromList` (LetDestructors.hs): the
/// substitution `svar -> t2` where a typed `svar` also maps its untyped
/// variant.  Keys are `LVar` (type-erased) for the `apply` over LN terms in the
/// process; the process terms carry SAPIC types, so we substitute over the
/// SAPIC-typed term world keyed by both the typed and untyped SapicLVar.
fn make_let_subst(svar: &SapicLVar, t2: &SapicTerm) -> Subst<Name, SapicLVar> {
    let mut pairs: Vec<(SapicLVar, SapicTerm)> = vec![(svar.clone(), t2.clone())];
    if svar.stype.is_some() {
        pairs.push((SapicLVar::untyped(svar.var), t2.clone()));
    }
    Subst::from_list(pairs)
}

/// Apply a SAPIC substitution to every term in a process subtree. HS `applyM`
/// also applies ordinary term substitution to parsed location annotations
/// (fixed upstream in #922). Case B only substitutes a `let`-bound variable
/// that, by typing, does not occur as an inner binder of `pl` — so a plain
/// substitution is faithful for the in-scope cases.
fn apply_subst_process(
    subst: &Subst<Name, SapicLVar>,
    p: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    map_process(
        &p,
        &mut |action| subst_action(subst, action),
        &mut |comb| subst_comb(subst, comb),
        &mut |ann| subst_annotation(subst, ann.clone()),
    )
}

fn subst_annotation(
    subst: &Subst<Name, SapicLVar>,
    mut ann: ProcessAnnotation<LVar>,
) -> ProcessAnnotation<LVar> {
    ann.parsing_ann = ann
        .parsing_ann
        .map_location(|location| subst_term(subst, &location));
    ann
}

/// `apply subst` for a `SapicAction SapicLVar` (Sapic/Process.hs):
/// `mapTermsAction`, with `ChIn` and `Msr` match variables rewritten by
/// [`apply_match_vars`].
fn subst_action(
    subst: &Subst<Name, SapicLVar>,
    ac: &tamarin_theory::sapic::SapicAction<SapicLVar>,
) -> tamarin_theory::sapic::SapicAction<SapicLVar> {
    use tamarin_theory::sapic::SapicAction as A;
    match ac {
        A::ChIn {
            chan,
            msg,
            match_vars,
        } => {
            return A::ChIn {
                chan: chan.as_ref().map(|t| subst_term(subst, t)),
                msg: subst_term(subst, msg),
                // HS special-cases `ChIn` in `Apply SapicSubst (SapicAction
                // SapicLVar)` (Sapic/Process.hs) to reach this rewrite: a
                // `let`-bound match var `=t` (where `t = <a,'test'>`) becomes the
                // match-var set `{a}`.
                match_vars: apply_match_vars(subst, match_vars),
            };
        }
        A::Msr { match_vars, .. } => {
            // Pinned HS reaches `Set.map (apply subst)` here and aborts if a
            // match variable maps to a compound term.  Keep the robust
            // `ChIn`/`Let` policy instead: collect the image's free variables
            // so a compound match pattern remains usable.
            let mut mapped = map_terms_action(
                |t| subst_term(subst, t),
                |f| apply_subst(subst, f.clone()),
                |v| v.clone(),
                ac,
            );
            let A::Msr {
                match_vars: mapped_match_vars,
                ..
            } = &mut mapped
            else {
                unreachable!("mapping an MSR action preserves its constructor")
            };
            *mapped_match_vars = apply_match_vars(subst, match_vars);
            return mapped;
        }
        _ => {}
    }
    map_terms_action(
        |t| subst_term(subst, t),
        // A `let`-bound value that an embedded `_restrict` mentions is
        // rewritten there as it is in the fact rows.  A quantifier binder is a
        // `Bound` De Bruijn index, outside the substitution's domain, so it
        // cannot capture a variable of the image.
        |f| apply_subst(subst, f.clone()),
        // The `let` pass substitutes values, not binders, so a variable the
        // action binds on its own stands for itself.
        |v| v.clone(),
        ac,
    )
}

/// `apply subst` for a `ProcessCombinator SapicLVar` (Sapic/Process.hs).
fn subst_comb(
    subst: &Subst<Name, SapicLVar>,
    c: &ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    let mut mapped = map_terms_comb(
        |t| subst_term(subst, t),
        // A Case-B `let`-elimination (`let z = t in P`) rewrites the free
        // variable `z` inside a downstream conditional's formula too: `z` is a
        // value bound by the `let`, not a process binder, so the `Cond`
        // payload's `z` references the same value.
        |f| apply_subst(subst, f.clone()),
        |v| v.clone(),
        c,
    );
    if let ProcessCombinator::Let { match_vars, .. } = c {
        let ProcessCombinator::Let {
            match_vars: mapped_match_vars,
            ..
        } = &mut mapped
        else {
            unreachable!("mapping a Let combinator preserves its constructor")
        };
        *mapped_match_vars = apply_match_vars(subst, match_vars);
    }
    mapped
}

/// Lift an `LNTerm` (untyped) back to a SAPIC term (all variables untyped).
fn ln_to_sapic(t: &LNTerm) -> SapicTerm {
    tamarin_term::term::map_lits(t, &mut |lit| match lit {
        Lit::Var(v) => Lit::Var(SapicLVar::untyped(*v)),
        Lit::Con(c) => Lit::Con(*c),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::vterm::var_term;
    use tamarin_theory::sapic::{ProcessParsedAnnotation, SapicAction};

    fn ann() -> ProcessAnnotation<LVar> {
        ProcessAnnotation {
            parsing_ann: ProcessParsedAnnotation::empty(),
            ..Default::default()
        }
    }

    fn svar(name: &str) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, LSort::Msg, 0))
    }

    fn pub_name(s: &str) -> SapicTerm {
        VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, s)))
    }

    #[test]
    fn strict_plan_preserves_equations_and_separates_user_pattern() {
        let source = "theory T begin functions: d/1 [destructor], a/1, b/1 equations: d(a(x))=x, d(b(x))=x process: in(x); let y=d(x) in event Done(y) else event Failed() end";
        let theory = tamarin_theory::elaborate::elaborate(
            &tamarin_parser::parse_theory(source, &[]).unwrap(),
        )
        .unwrap();
        let p = crate::annotation::to_annotated(theory.processes().next().unwrap());
        let planned = translate_let_destr(&[], &theory.signature.st_rules, p).unwrap();
        let Process::Action(_, _, rest) = planned else {
            panic!("input")
        };
        let plan = &rest.annotation().let_plan;
        assert_eq!(plan.len(), 2);
        assert_eq!(plan[0].alternatives.len(), 2);
        assert!(plan[0].bound.is_empty());
        assert!(plan[0]
            .alternatives
            .iter()
            .all(|(_, reduct)| reduct.is_some()));
        assert!(frees(&plan[0].alternatives).iter().all(|v| v.idx > 0));
        assert_eq!(plan[1].alternatives.len(), 1);
        assert!(plan[1].alternatives[0].1.is_none());
        assert_eq!(plan[1].bound, BTreeSet::from([svar("y").var]));
    }

    #[test]
    fn unary_stage_payload_stays_bounded_as_depth_grows() {
        for depth in [4, 8, 10] {
            let mut term = "'ok'".to_string();
            for _ in 0..depth {
                term = format!("d(c({term}))");
            }
            let source = format!("theory T begin functions: d/1 [destructor], c/1 equations: d(c(x))=x process: let x={term} in event Done(x) else event Fail() end");
            let mut theory = tamarin_theory::elaborate::elaborate(
                &tamarin_parser::parse_theory(&source, &[]).unwrap(),
            )
            .unwrap();
            crate::apply::apply_sapic(&mut theory, false).unwrap();
            // Two stages per call, success/failure per stage, plus the
            // initial state, plan entry, two events and two terminal rules.
            assert_eq!(theory.rules().count(), 4 * depth + 6);
            let mut let_facts = 0;
            for rule in theory.rules() {
                for fact in rule.rule.premises.iter().chain(&rule.rule.conclusions) {
                    if matches!(fact.tag, tamarin_theory::fact::FactTag::Proto(_, name, _) if name.starts_with("Let_"))
                    {
                        let_facts += 1;
                        assert!(fact.terms.len() <= 2, "depth {depth}: {fact:?}");
                    }
                }
            }
            assert!(let_facts >= 2 * depth);
        }
    }

    #[test]
    fn case_b_eliminates_var_rhs_let() {
        // `let h = 't' in out(h)` (h not a match-var) → `out('t')`, Let gone.
        let h = svar("h");
        let body = Process::Action(
            SapicAction::ChOut {
                chan: None,
                msg: var_term(h.clone()),
            },
            ann(),
            Box::new(Process::Null(ann())),
        );
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: var_term(h),
                right: pub_name("t"),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(body),
            Box::new(Process::Null(ann())),
        );
        let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
        let out = translate_let_destr(&[], &rules, lett).unwrap();
        // The Let must be gone.  The top node is the substituted `out('t')`.
        // That is the RHS term itself, not just some constant.
        let Process::Action(SapicAction::ChOut { msg, .. }, _, body) = out else {
            panic!("expected Let to be eliminated to ChOut");
        };
        assert_eq!(msg, pub_name("t"), "h must be replaced by 't'");
        assert!(matches!(*body, Process::Null(_)));
    }

    #[test]
    fn let_elimination_substitutes_compound_location() {
        // Upstream #922: annotations use ordinary term substitution, so an
        // eliminated let may replace its location variable with a pair.
        let h = svar("h");
        let location = tamarin_term::builtin::pair(pub_name("site"), pub_name("device"));
        let mut body_ann = ann();
        body_ann.parsing_ann.location = Some(var_term(h.clone()));
        let body = Process::Action(
            SapicAction::ChOut {
                chan: None,
                msg: pub_name("payload"),
            },
            body_ann,
            Box::new(Process::Null(ann())),
        );
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: var_term(h),
                right: location.clone(),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(body),
            Box::new(Process::Null(ann())),
        );

        let out = translate_let_destr(&[], &BTreeSet::new(), lett).unwrap();
        assert_eq!(out.annotation().parsing_ann.location, Some(location));
    }

    /// HS `mapTermsAction .. (fmap ff rest) ..` (Sapic/Process.hs) under
    /// `apply subst` (Sapic/Process.hs): a Case-B `let`-elimination
    /// rewrites the `let`-bound variable inside an embedded MSR's
    /// `_restrict` formula, not only inside its fact rows.
    #[test]
    fn let_elimination_substitutes_into_an_msr_restriction() {
        use tamarin_theory::atom::ProtoAtom;
        use tamarin_theory::formula::ProtoFormula;

        let h = svar("h");
        // `[ ] --[ Ev(h) ]-> [ ]` restricted by `h = 'b'`.
        let ev = tamarin_theory::fact::Fact::new(
            tamarin_theory::fact::FactTag::Proto(
                tamarin_theory::fact::Multiplicity::Linear,
                "Ev",
                1,
            ),
            vec![var_term(h.clone())],
        );
        let restr = ProtoFormula::Atom(ProtoAtom::EqE(
            var_term(tamarin_term::lterm::BVar::Free(h.clone())),
            VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "b"))),
        ));
        let msr = Process::Action(
            SapicAction::Msr {
                prems: Vec::new(),
                acts: vec![ev],
                concs: Vec::new(),
                rest: vec![restr],
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(Process::Null(ann())),
        );
        // `let h = 't' in <msr>` — Case B drops the Let and substitutes `'t'`.
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: var_term(h),
                right: pub_name("t"),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(msr),
            Box::new(Process::Null(ann())),
        );
        let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
        let out = translate_let_destr(&[], &rules, lett).unwrap();
        let Process::Action(SapicAction::Msr { acts, rest, .. }, _, _) = out else {
            panic!("expected Let to be eliminated to the MSR");
        };
        assert_eq!(
            acts[0].terms[0],
            pub_name("t"),
            "the action row is rewritten"
        );
        assert_eq!(
            rest[0],
            ProtoFormula::Atom(ProtoAtom::EqE(
                VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "t"))),
                VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "b"))),
            )),
            "and so is the embedded restriction"
        );
    }

    #[test]
    fn let_substitution_rewrites_nested_let_and_msr_match_vars() {
        let x = svar("x");
        let a = svar("a");
        let image = tamarin_term::builtin::pair(var_term(a.clone()), pub_name("tag"));
        let subst = make_let_subst(&x, &image);

        let comb = ProcessCombinator::Let {
            left: var_term(x.clone()),
            right: pub_name("message"),
            match_vars: BTreeSet::from([x.clone()]),
        };
        let ProcessCombinator::Let { match_vars, .. } = subst_comb(&subst, &comb) else {
            panic!("expected Let")
        };
        assert_eq!(match_vars, BTreeSet::from([a.clone()]));

        let action = SapicAction::Msr {
            prems: Vec::new(),
            acts: Vec::new(),
            concs: Vec::new(),
            rest: Vec::new(),
            match_vars: BTreeSet::from([x]),
        };
        let SapicAction::Msr { match_vars, .. } = subst_action(&subst, &action) else {
            panic!("expected MSR")
        };
        assert_eq!(match_vars, BTreeSet::from([a]));
    }

    #[test]
    fn case_c_keeps_nonvar_lhs_let_and_sets_else_branch() {
        // `let <a,b> = m in P else 0`: LHS is a pair (not a plain var), so the
        // Let is KEPT (Case C); else_branch is False (right child is Null).
        let a = svar("a");
        let b = svar("b");
        let pair = tamarin_term::builtin::pair(var_term(a), var_term(b));
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: pair,
                right: pub_name("m"),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(Process::Null(ann())),
            Box::new(Process::Null(ann())),
        );
        let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
        let out = translate_let_destr(&[], &rules, lett).unwrap();
        match out {
            Process::Comb(ProcessCombinator::Let { .. }, a2, _, _) => {
                assert!(
                    !a2.else_branch,
                    "else_branch must be False (Null right child)"
                );
            }
            other => panic!("expected kept Let, got {other:?}"),
        }
    }
}
