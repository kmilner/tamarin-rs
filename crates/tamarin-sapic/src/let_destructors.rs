// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Strict, innermost-first SAPIC destructor evaluation. Plans stay on the
//! source let, sharing both continuations and separating equation matching
//! from the user's pattern (upstream Sapic.LetDestructors).

use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::function_symbols::{AcSym, Constructability, FunSym};
use tamarin_term::lterm::{avoid, frees, rename_avoiding, LNTerm, LSort, LVar, Name};
use tamarin_term::subst::Subst;
use tamarin_term::subterm_rule::CtxtStRule;
use tamarin_term::term::f_app;
use tamarin_term::vterm::{var_term, Lit, VTerm};
use tamarin_theory::sapic::{
    apply_m_process, map_process, Process, ProcessCombinator, SapicLVar, SapicTerm,
};
use tamarin_utils::fresh::{FastFreshState, MonadFresh};

use crate::annotation::{AnnotatedProcess, LetStage};

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
                crate::typing::to_sapic_term(&m.body),
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
    matches!(t, VTerm::App(f, _) if is_destructor_symbol(f))
}

fn is_destructor_symbol(f: &FunSym) -> bool {
    match f {
        FunSym::NoEq(s) => s.constructability == Constructability::Destructor,
        FunSym::Ac(AcSym::AcFct(s)) => s.constructability == Constructability::Destructor,
        _ => false,
    }
}

fn contains_destructor(t: &LNTerm) -> bool {
    t.any_fun_sym(is_destructor_symbol)
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
        let result = tamarin_theory::sapic::to_ln_term(&pattern);
        let bound = frees(&result).into_iter().collect();
        let term = tamarin_theory::sapic::to_ln_term(&term);
        if let VTerm::App(f, args) = &term
            && is_destructor_symbol(f)
        {
            if matches!(f, FunSym::Ac(_)) {
                return Err("This feature is not implemented yet. Sorry! SAPIC does not support AC destructor calls.".into());
            }
            let Some(alternatives) = equations.get(f) else {
                return Ok(None);
            };
            if alternatives.iter().any(|(_, rhs)| contains_destructor(rhs)) {
                return Err(
                    "This feature is not implemented yet. Sorry! SAPIC destructor equation results must not contain destructor calls.".into(),
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
                let pl = apply_m_process(&make_let_subst(v, right), &pl)
                    .map_err(|captured| captured.to_string())?;
                return map_proc(equations, fresh, pl);
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
/// right-nested pair. A public name encodes zero arguments without requiring
/// a builtin signature; stage positions keep the encodings separate.
fn to_pairs(ts: &[LNTerm]) -> LNTerm {
    match ts {
        [] => VTerm::Lit(Lit::Con(Name::new(
            tamarin_term::lterm::NameTag::Pub,
            "unit",
        ))),
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::vterm::var_term;
    use tamarin_theory::sapic::SapicAction;

    fn svar(name: &str) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, LSort::Msg, 0))
    }

    fn pub_name(s: &str) -> SapicTerm {
        VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, s)))
    }

    #[test]
    fn let_substitution_rewrites_nested_let_and_action_match_vars() {
        let x = svar("x");
        let a = svar("a");
        let image = tamarin_term::builtin::pair(var_term(a.clone()), pub_name("tag"));
        let subst = make_let_subst(&x, &image);
        let image_of = |v: &SapicLVar| subst.image_of(v).cloned();

        let comb = ProcessCombinator::Let {
            left: var_term(x.clone()),
            right: pub_name("message"),
            match_vars: BTreeSet::from([x.clone()]),
        };
        let ProcessCombinator::Let { match_vars, .. } =
            tamarin_theory::sapic::apply_comb(&image_of, &comb)
        else {
            panic!("expected Let")
        };
        assert_eq!(match_vars, BTreeSet::from([a.clone()]));

        let input = SapicAction::ChIn {
            chan: Some(var_term(x.clone())),
            msg: var_term(x.clone()),
            match_vars: BTreeSet::from([x.clone()]),
        };
        let SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } = tamarin_theory::sapic::apply_action(&image_of, &input)
        else {
            panic!("expected input")
        };
        assert_eq!(chan, Some(image.clone()));
        assert_eq!(msg, image);
        assert_eq!(match_vars, BTreeSet::from([a.clone()]));

        let action = SapicAction::Msr {
            prems: Vec::new(),
            acts: Vec::new(),
            concs: Vec::new(),
            rest: Vec::new(),
            match_vars: BTreeSet::from([x]),
        };
        let SapicAction::Msr { match_vars, .. } =
            tamarin_theory::sapic::apply_action(&image_of, &action)
        else {
            panic!("expected MSR")
        };
        assert_eq!(match_vars, BTreeSet::from([a]));
    }
}
