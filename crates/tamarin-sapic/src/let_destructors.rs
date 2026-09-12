// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.LetDestructors` (`lib/sapic/src/Sapic/LetDestructors.hs`).
//!
//! `translateLetDestr` (`mapProc`) walks the annotated process and rewrites
//! every `Let t1 t2 mv` combinator (Basetranslation.hs `Let` corresponds to a
//! `ProcessCombinator::Let { left, right, match_vars }`):
//!
//!   * **Case A** (LetDestructors.hs:35-58) — `t1` a plain variable and `t2` a
//!     `Destructor` application.  If the destructor has an associated rewrite
//!     rule `dest(leftterms) = outvar`, the Let is KEPT and annotated with the
//!     `destructorEquation` `(leftterms[outvar↦t1], rightterms)`; otherwise the
//!     destructor never succeeds, so the whole Let is replaced by its
//!     else-branch `pr`.
//!
//!   * **Case B** (LetDestructors.hs:59-61) — `t1` a plain variable `svar` NOT
//!     in the match-vars `mv`.  The Let is ELIMINATED: `svar → t2` is
//!     substituted into the left process `pl` (the else-branch is discarded),
//!     and the rewrite recurses.  This is the `let h = a in …` /
//!     `let x = 't' in …` optimisation.
//!
//!   * **Case C** (LetDestructors.hs:62-65, the `_` fallthrough) — anything
//!     else.  The Let is KEPT, annotated only with `annElse elsebranch`, and
//!     both branches are rewritten.
//!
//! `elsebranch` (LetDestructors.hs:74-76) is `False` iff the right branch is the
//! null process, else `True`.
//!
//! Runs as part of `translate` (HS `sapic/src/Sapic.hs:45-101, see line 55`),
//! AFTER `propagateNames` and BEFORE `annotateLocks`, over the already
//! type-/rename-unique'd process.

use tamarin_term::function_symbols::{Constructability, FunSym};
use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subterm_rule::CtxtStRule;
use tamarin_term::vterm::{Lit, VTerm};
use tamarin_theory::formula::apply_subst;
use tamarin_theory::sapic::{
    apply_match_vars, map_terms_action, map_terms_comb, subst_term, Process, ProcessCombinator,
    SapicLVar, SapicTerm,
};

use crate::annotation::{AnnotatedProcess, ProcessAnnotation};

/// `translateLetDestr rules p` (LetDestructors.hs:98-100) — the entry point.
pub(crate) fn translate_let_destr(
    rules: &std::collections::BTreeSet<CtxtStRule>,
    mut p: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    crate::process_walk::walk_mut(&mut p, (), |node, _| {
        // Eliminating a let exposes a new root, which must be processed before
        // descending. Kept lets retain the upstream fresh-annotation policy.
        while let Process::Comb(
            ProcessCombinator::Let {
                left,
                right,
                match_vars,
            },
            ann,
            _,
            pr,
        ) = node
        {
            let elsebranch = !matches!(**pr, Process::Null(_));
            let t1_ln = crate::base_translation::to_ln_term(left);
            let t2_ln = crate::base_translation::to_ln_term(right);
            if let VTerm::Lit(Lit::Var(_)) = left
                && let VTerm::App(FunSym::NoEq(funsym), rightterms) = &t2_ln
                && funsym.constructability == Constructability::Destructor
            {
                if let Some((leftterms, outvar)) = find_rule(funsym, rules) {
                    let subst = Subst::from_list(vec![(outvar, t1_ln.clone())]);
                    *ann = ProcessAnnotation::with_destructor_equation(
                        apply_vterm(&subst, to_pairs(&leftterms)),
                        to_pairs(rightterms),
                        elsebranch,
                    );
                    let comb = rebuild_let_comb(&t1_ln, funsym, rightterms);
                    let Process::Comb(c, _, _, _) = node else {
                        unreachable!()
                    };
                    *c = comb;
                    break;
                }
                // A destructor without a rule can only take the else branch.
                let old = std::mem::replace(node, Process::Null(ProcessAnnotation::empty()));
                let Process::Comb(_, _, left, right) = old else {
                    unreachable!()
                };
                *node = right.into_inner();
                drop(left);
            } else if let VTerm::Lit(Lit::Var(svar)) = left
                && !match_vars.contains(svar)
            {
                let subst = make_let_subst(svar, right);
                let old = std::mem::replace(node, Process::Null(ProcessAnnotation::empty()));
                let Process::Comb(_, _, left, right) = old else {
                    unreachable!()
                };
                *node = left.into_inner();
                drop(right);
                apply_subst_process_mut(&subst, node);
            } else {
                *ann = ProcessAnnotation::with_else_branch(elsebranch);
                break;
            }
        }
        Ok::<_, std::convert::Infallible>(true)
    })
    .unwrap();
    p
}

/// Reconstruct the original `Let` combinator for the destructor case.  HS keeps
/// the *original* `c = Let t1 t2 mv` (typed); we lift the type-erased
/// `t1`/`t2` back to SAPIC terms (the translation only uses the LN forms
/// thereafter via the `destructorEquation` annotation, so the untyped lift is
/// faithful for the kept combinator's role).
fn rebuild_let_comb(
    t1_ln: &LNTerm,
    funsym: &tamarin_term::function_symbols::NoEqSym,
    rightterms: &[LNTerm],
) -> ProcessCombinator<SapicLVar> {
    let left = ln_to_sapic(t1_ln);
    let right = ln_to_sapic(&tamarin_term::term::f_app_no_eq(
        *funsym,
        rightterms.to_vec(),
    ));
    ProcessCombinator::Let {
        left,
        right,
        match_vars: std::collections::BTreeSet::new(),
    }
}

/// `findRule funsym acc rule` (LetDestructors.hs:87-96): the first destructor
/// rewrite rule `dest(y) = v` whose head symbol matches `funsym`.
fn find_rule(
    funsym: &tamarin_term::function_symbols::NoEqSym,
    rules: &std::collections::BTreeSet<CtxtStRule>,
) -> Option<(Vec<LNTerm>, LVar)> {
    // HS `L.foldl (findRule funsym) Nothing rules`: a left-fold returning the
    // LAST matching rule (each match overwrites `acc`).  Mirror that by keeping
    // the last match.
    let mut acc: Option<(Vec<LNTerm>, LVar)> = None;
    for rule in rules {
        let rr = rule.to_rrule();
        // `case (viewTerm fhs, viewTerm rhs) of (FApp fs y, Lit (Var v)) | fs == funsym`
        if let VTerm::App(FunSym::NoEq(fs), y) = &rr.lhs
            && let VTerm::Lit(Lit::Var(v)) = &rr.rhs
            && fs == funsym
        {
            acc = Some((y.to_vec(), *v));
        }
    }
    acc
}

/// `toPairs` (LetDestructors.hs:71-73): fold a list of terms into a
/// right-nested pair.  `[] -> fAppOne`, `[s] -> s`, `(p:q) -> <p, toPairs q>`.
fn to_pairs(ts: &[LNTerm]) -> LNTerm {
    let Some((last, prefix)) = ts.split_last() else {
        return tamarin_term::term::f_app_no_eq(tamarin_term::function_symbols::one_sym(), vec![]);
    };
    prefix.iter().rev().fold(last.clone(), |rest, head| {
        tamarin_term::builtin::pair(head.clone(), rest)
    })
}

/// `make_untyped_variant` + `substFromList` (LetDestructors.hs:78-80, :60): the
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
fn apply_subst_process_mut(subst: &Subst<Name, SapicLVar>, p: &mut AnnotatedProcess<LVar>) {
    crate::process_walk::walk_mut(p, (), |node, _| {
        let ann = match node {
            Process::Null(ann) => ann,
            Process::Action(ac, ann, _) => {
                *ac = subst_action(subst, ac);
                ann
            }
            Process::Comb(c, ann, _, _) => {
                *c = subst_comb(subst, c);
                ann
            }
        };
        *ann = subst_annotation(subst, std::mem::take(ann));
        Ok::<_, std::convert::Infallible>(true)
    })
    .unwrap();
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

/// `apply subst` for a `SapicAction SapicLVar` (Sapic/Process.hs:319-321):
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
                // SapicLVar)` (Sapic/Process.hs:319-321) to reach this rewrite: a
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

/// `apply subst` for a `ProcessCombinator SapicLVar` (Sapic/Process.hs:330-334).
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
    fn case_b_eliminates_var_rhs_let() {
        // `let h = 't' in out(h)` (h not a match-var) → `out('t')`, Let gone.
        let h = svar("h");
        let body = Process::Action(
            SapicAction::ChOut {
                chan: None,
                msg: var_term(h.clone()),
            },
            ann(),
            Box::new(Process::Null(ann())).into(),
        );
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: var_term(h),
                right: pub_name("t"),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(body).into(),
            Box::new(Process::Null(ann())).into(),
        );
        let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
        let out = translate_let_destr(&rules, lett);
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
            Box::new(Process::Null(ann())).into(),
        );
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: var_term(h),
                right: location.clone(),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(body).into(),
            Box::new(Process::Null(ann())).into(),
        );

        let out = translate_let_destr(&BTreeSet::new(), lett);
        assert_eq!(out.annotation().parsing_ann.location, Some(location));
    }

    /// HS `mapTermsAction .. (fmap ff rest) ..` (Sapic/Process.hs:155) under
    /// `apply subst` (Sapic/Process.hs:319-321): a Case-B `let`-elimination
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
            Box::new(Process::Null(ann())).into(),
        );
        // `let h = 't' in <msr>` — Case B drops the Let and substitutes `'t'`.
        let lett = Process::Comb(
            ProcessCombinator::Let {
                left: var_term(h),
                right: pub_name("t"),
                match_vars: BTreeSet::new(),
            },
            ann(),
            Box::new(msr).into(),
            Box::new(Process::Null(ann())).into(),
        );
        let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
        let out = translate_let_destr(&rules, lett);
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
            Box::new(Process::Null(ann())).into(),
            Box::new(Process::Null(ann())).into(),
        );
        let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
        let out = translate_let_destr(&rules, lett);
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
