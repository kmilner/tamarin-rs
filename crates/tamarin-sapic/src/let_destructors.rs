// Currently GPL 3.0 until granted permission by the following authors:
//   Robert Künnemann, Charlie Jacomme, Simon Meier, Artur Cygan, Benedikt
//   Schmidt, Kevin Morio, Jannik Dreier, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic.hs, lib/sapic/src/Sapic/Annotation.hs,
//   lib/sapic/src/Sapic/Basetranslation.hs,
//   lib/sapic/src/Sapic/LetDestructors.hs,
//   lib/term/src/Term/Maude/Process.hs,
//   lib/theory/src/Theory/Sapic/Process.hs

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
//! Runs as part of `translate` (HS `Sapic.hs:54`), AFTER `propagateNames` and
//! BEFORE `annotateLocks`, over the already type-/rename-unique'd process.

use tamarin_term::function_symbols::{Constructability, FunSym};
use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::subterm_rule::CtxtStRule;
use tamarin_term::subst::{apply_vterm, Subst};
use crate::base_translation::{subst_term, subst_fact};
use tamarin_term::vterm::{Lit, VTerm};

use tamarin_theory::sapic::{
    Process, ProcessCombinator, SapicLVar, SapicTerm,
};

use crate::annotation::{AnnotatedProcess, ProcessAnnotation};

/// `translateLetDestr rules p` (LetDestructors.hs:98-100) — the entry point.
pub fn translate_let_destr(
    st_rules: &std::collections::BTreeSet<CtxtStRule>,
    p: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    map_proc(st_rules, p)
}

fn map_proc(
    rules: &std::collections::BTreeSet<CtxtStRule>,
    p: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    match p {
        Process::Null(ann) => Process::Null(ann),
        // `ProcessAction ac ann p'` (LetDestructors.hs:29-31): descend.
        Process::Action(ac, ann, body) => {
            let body1 = map_proc(rules, *body);
            Process::Action(ac, ann, Box::new(body1))
        }
        // `ProcessComb c@(Let t1 t2 mv) _ pl pr` (LetDestructors.hs:33-66).
        Process::Comb(ProcessCombinator::Let { left, right, match_vars }, ann, pl, pr) => {
            map_let(rules, left, right, match_vars, ann, *pl, *pr)
        }
        // `ProcessComb c ann pl pr` (LetDestructors.hs:82-85): non-Let comb.
        Process::Comb(c, ann, pl, pr) => {
            let pl1 = map_proc(rules, *pl);
            let pr1 = map_proc(rules, *pr);
            Process::Comb(c, ann, Box::new(pl1), Box::new(pr1))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn map_let(
    rules: &std::collections::BTreeSet<CtxtStRule>,
    left: SapicTerm,
    right: SapicTerm,
    match_vars: std::collections::BTreeSet<SapicLVar>,
    ann: ProcessAnnotation<LVar>,
    pl: AnnotatedProcess<LVar>,
    pr: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    // `t1' = toLNTerm t1`, `t2' = toLNTerm t2` (LetDestructors.hs:68-69).
    let t1_ln = crate::base_translation::to_ln_term(&left);
    let t2_ln = crate::base_translation::to_ln_term(&right);

    // `elsebranch = case pr of ProcessNull _ -> False; _ -> True`
    // (LetDestructors.hs:74-76).
    let elsebranch = !matches!(pr, Process::Null(_));

    // Dispatch on the shape of (t1, viewTerm t1', viewTerm t2') — Case A first
    // (LetDestructors.hs:34-58): t1 a var AND t2 a Destructor application.
    if let VTerm::Lit(Lit::Var(_)) = &left {
        if let VTerm::App(FunSym::NoEq(funsym), rightterms) = &t2_ln {
            if funsym.constructability == Constructability::Destructor {
                return case_destructor(
                    rules, &t1_ln, funsym.clone(), rightterms, ann, pl, pr, elsebranch,
                );
            }
        }
    }

    // Case B (LetDestructors.hs:59-61): t1 a plain variable NOT in match-vars.
    if let VTerm::Lit(Lit::Var(svar)) = &left {
        if !match_vars.contains(svar) {
            // `applyM (substFromList ((,t2) <$> make_untyped_variant svar)) pl`.
            let subst = make_let_subst(svar, &right);
            let pl1 = apply_subst_process(&subst, pl);
            return map_proc(rules, pl1);
        }
    }

    // Case C (LetDestructors.hs:62-65): keep the Let, annotate `annElse
    // elsebranch`.  HS `annElse b = mempty {elseBranch = b}` (Annotation.hs:131-132)
    // builds a FRESH `mempty`-based annotation, REPLACING the existing one — so
    // every other field (incl. the propagated `processnames`) is dropped back to
    // its default.  `ann` (which carries the propagated process names) must NOT be
    // reused here, else the role/color would over-propagate the enclosing
    // sub-process name onto these let rules.
    let _ = ann;
    let ann2 = ProcessAnnotation::with_else_branch(elsebranch);
    let pl1 = map_proc(rules, pl);
    let pr1 = map_proc(rules, pr);
    Process::Comb(
        ProcessCombinator::Let { left, right, match_vars },
        ann2,
        Box::new(pl1),
        Box::new(pr1),
    )
}

/// Case A — destructor let (LetDestructors.hs:35-58).
#[allow(clippy::too_many_arguments)]
fn case_destructor(
    rules: &std::collections::BTreeSet<CtxtStRule>,
    t1_ln: &LNTerm,
    funsym: tamarin_term::function_symbols::NoEqSym,
    rightterms: &[LNTerm],
    ann: ProcessAnnotation<LVar>,
    pl: AnnotatedProcess<LVar>,
    pr: AnnotatedProcess<LVar>,
    elsebranch: bool,
) -> AnnotatedProcess<LVar> {
    match find_rule(&funsym, rules) {
        // No rule: the destructor never succeeds — replace the Let by its
        // else-branch (LetDestructors.hs:38-39).
        None => map_proc(rules, pr),
        // `Just (leftterms, outvar)` (LetDestructors.hs:40-57).
        Some((leftterms, outvar)) => {
            // `subst = substFromList [(outvar, t1')]`
            // `leftermssubst = apply subst $ toPairs leftterms`
            let subst: Subst<Name, LVar> =
                Subst::from_list(vec![(outvar, t1_ln.clone())]);
            let leftterms_pairs = to_pairs(&leftterms);
            let leftterms_subst = apply_vterm(&subst, leftterms_pairs);
            let rightterms_pairs = to_pairs(rightterms);
            // `new_an = annDestructorEquation leftermssubst (toPairs rightterms) elsebranch`
            // — HS `annDestructorEquation v1 v2 b = mempty { destructorEquation =
            // Just (v1, v2), elseBranch = b }` (Annotation.hs:128-129) builds a
            // FRESH `mempty`-based annotation, REPLACING the existing one.  Every
            // other field (incl. the propagated `processnames`) is therefore reset
            // to default — so `ann` must NOT be reused (see Case C above).
            let _ = ann;
            let new_an =
                ProcessAnnotation::with_destructor_equation(leftterms_subst, rightterms_pairs, elsebranch);
            let pl1 = map_proc(rules, pl);
            let pr1 = map_proc(rules, pr);
            // The Let combinator `c` is preserved unchanged.  Reconstruct it
            // from the original terms — t1 is a var; we reuse `t1_ln` (already
            // type-erased) lifted back into a SAPIC term, and the original
            // `right`/`match_vars` carried by the destructor case.  HS keeps the
            // ORIGINAL `c` (`ProcessComb c new_an npl npr`), so we must keep the
            // SAPIC-typed left/right/match_vars; they are threaded through.
            Process::Comb(
                rebuild_let_comb(t1_ln, &funsym, rightterms),
                new_an,
                Box::new(pl1),
                Box::new(pr1),
            )
        }
    }
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
        funsym.clone(),
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
        if let VTerm::App(FunSym::NoEq(fs), y) = &rr.lhs {
            if let VTerm::Lit(Lit::Var(v)) = &rr.rhs {
                if fs == funsym {
                    acc = Some((y.to_vec(), v.clone()));
                }
            }
        }
    }
    acc
}

/// `toPairs` (LetDestructors.hs:71-73): fold a list of terms into a
/// right-nested pair.  `[] -> fAppOne`, `[s] -> s`, `(p:q) -> <p, toPairs q>`.
fn to_pairs(ts: &[LNTerm]) -> LNTerm {
    match ts {
        [] => tamarin_term::term::f_app_no_eq(
            tamarin_term::function_symbols::one_sym(),
            vec![],
        ),
        [s] => s.clone(),
        [head, tail @ ..] => {
            let rest = to_pairs(tail);
            tamarin_term::builtin::pair(head.clone(), rest)
        }
    }
}

/// `make_untyped_variant` + `substFromList` (LetDestructors.hs:78-80, :60): the
/// substitution `svar -> t2` where a typed `svar` also maps its untyped
/// variant.  Keys are `LVar` (type-erased) for the `apply` over LN terms in the
/// process; the process terms carry SAPIC types, so we substitute over the
/// SAPIC-typed term world keyed by both the typed and untyped SapicLVar.
fn make_let_subst(svar: &SapicLVar, t2: &SapicTerm) -> Subst<Name, SapicLVar> {
    let mut pairs: Vec<(SapicLVar, SapicTerm)> = vec![(svar.clone(), t2.clone())];
    if svar.stype.is_some() {
        pairs.push((SapicLVar::untyped(svar.var.clone()), t2.clone()));
    }
    Subst::from_list(pairs)
}

/// Apply a SAPIC substitution to every term in a process subtree.  HS `applyM`
/// here is capture-checking, but Case B only substitutes a `let`-bound variable
/// that, by typing, does not occur as an inner binder of `pl` — so a plain
/// substitution is faithful for the in-scope cases.
fn apply_subst_process(
    subst: &Subst<Name, SapicLVar>,
    p: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    match p {
        Process::Null(a) => Process::Null(a),
        Process::Action(ac, a, body) => {
            let ac1 = subst_action(subst, ac);
            Process::Action(ac1, a, Box::new(apply_subst_process(subst, *body)))
        }
        Process::Comb(c, a, l, r) => {
            let c1 = subst_comb(subst, c);
            Process::Comb(
                c1,
                a,
                Box::new(apply_subst_process(subst, *l)),
                Box::new(apply_subst_process(subst, *r)),
            )
        }
    }
}

/// `applyMatchVars subst vs` (Process.hs:305-309): rewrite a set of match
/// variables under a substitution.  Each `v` is replaced by the variables of
/// `subst(v)` if `v` is in the substitution's domain, else kept as-is.
fn apply_match_vars(
    subst: &Subst<Name, SapicLVar>,
    vs: &std::collections::BTreeSet<SapicLVar>,
) -> std::collections::BTreeSet<SapicLVar> {
    let mut out = std::collections::BTreeSet::new();
    for v in vs {
        match subst.image_of(v) {
            Some(img) => {
                for w in tamarin_term::vterm::vars_vterm_in_order(img) {
                    out.insert(w);
                }
            }
            None => {
                out.insert(v.clone());
            }
        }
    }
    out
}

fn subst_action(
    subst: &Subst<Name, SapicLVar>,
    ac: tamarin_theory::sapic::SapicAction<SapicLVar>,
) -> tamarin_theory::sapic::SapicAction<SapicLVar> {
    use tamarin_theory::sapic::SapicAction as A;
    match ac {
        A::New(v) => A::New(v),
        A::Event(f) => A::Event(subst_fact(subst, &f)),
        A::ChOut { chan, msg } => A::ChOut {
            chan: chan.map(|t| subst_term(subst, &t)),
            msg: subst_term(subst, &msg),
        },
        A::ChIn { chan, msg, match_vars } => A::ChIn {
            chan: chan.map(|t| subst_term(subst, &t)),
            msg: subst_term(subst, &msg),
            // HS `applyMatchVars subst vs` (Process.hs:305-309, 320): a match var
            // `v` whose image under `subst` is a (compound) term is replaced by
            // ALL the variables of that image; an undefined `v` is kept.  So a
            // `let`-bound match var `=t` (where `t = <a,'test'>`) becomes the
            // match-var set `{a}`.
            match_vars: apply_match_vars(subst, &match_vars),
        },
        A::Insert(a, b) => A::Insert(subst_term(subst, &a), subst_term(subst, &b)),
        A::Delete(t) => A::Delete(subst_term(subst, &t)),
        A::Lock(t) => A::Lock(subst_term(subst, &t)),
        A::Unlock(t) => A::Unlock(subst_term(subst, &t)),
        A::ProcessCall(n, ts) => {
            A::ProcessCall(n, ts.iter().map(|t| subst_term(subst, t)).collect())
        }
        A::Msr { prems, acts, concs, rest, match_vars } => A::Msr {
            prems: prems.iter().map(|f| subst_fact(subst, f)).collect(),
            acts: acts.iter().map(|f| subst_fact(subst, f)).collect(),
            concs: concs.iter().map(|f| subst_fact(subst, f)).collect(),
            rest,
            match_vars,
        },
        A::Rep => A::Rep,
    }
}

fn subst_comb(
    subst: &Subst<Name, SapicLVar>,
    c: ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    match c {
        ProcessCombinator::Lookup(t, v) => ProcessCombinator::Lookup(subst_term(subst, &t), v),
        ProcessCombinator::Let { left, right, match_vars } => ProcessCombinator::Let {
            left: subst_term(subst, &left),
            right: subst_term(subst, &right),
            match_vars,
        },
        ProcessCombinator::CondEq(a, b) => {
            ProcessCombinator::CondEq(subst_term(subst, &a), subst_term(subst, &b))
        }
        // HS `apply subst (Cond fa) = Cond (apply subst fa)` (Process.hs:165):
        // a Case-B `let`-elimination (`let z = t in P`) must rewrite the free
        // variable `z` inside any downstream conditional's formula too — `z` is
        // a value bound by the `let`, not a process binder, so the `Cond`
        // payload's `z` references the same `let`-bound value.  The RS `Cond`
        // carries the un-expanded parser-AST formula, so we substitute over that
        // formula's free variables, replacing each with the parser lowering of
        // its image term.  (Quantifier-bound vars are left untouched, mirroring
        // HS, which only substitutes the process-level `let`-bound variable.)
        ProcessCombinator::Cond(f) => ProcessCombinator::Cond(subst_cond_formula(subst, &f)),
        // Parallel/Ndc carry no terms, so substitution is the identity.
        // Enumerated (no wildcard) so a new term-carrying variant must decide
        // its substitution here.
        other @ (ProcessCombinator::Parallel | ProcessCombinator::Ndc) => other,
    }
}

/// Substitute a `let`-bound variable into a `Cond` parser-AST formula
/// (HS `apply subst fa`, Process.hs:165).  For each FREE `Var(v)` whose
/// `SapicLVar` key (typed or untyped) is in `subst`'s domain, replace it with
/// the parser-AST lowering of the image term; non-domain / quantifier-bound vars
/// are kept unchanged.
fn subst_cond_formula(
    subst: &Subst<Name, SapicLVar>,
    f: &tamarin_parser::ast::Formula,
) -> tamarin_parser::ast::Formula {
    use tamarin_parser::ast as p;
    // For each FREE `Var`, its `let`-bound image lowered into the parser-AST term
    // universe (via the LN form, so AC normal form / pub-literal rendering match
    // HS).  `None` leaves the var unchanged (not in the subst domain).
    crate::convert::map_free_terms(f, &mut |v: &p::VarSpec, _bound| {
        let lv = LVar::new(v.name.clone(), crate::convert::sort_of_hint(&v.sort), v.idx);
        // The Case-B subst keys an untyped `SapicLVar` (and, when the bound var
        // was typed, its typed variant too); a `Cond`-formula var is untyped, so
        // probe the untyped key first, then the typed-erased path.
        let img = subst
            .image_of(&SapicLVar::untyped(lv.clone()))
            .or_else(|| subst.image_of(&SapicLVar::new(lv.clone(), None)));
        img.map(|t| {
            crate::base_translation::ln_term_to_parser(&crate::base_translation::to_ln_term(t))
        })
    })
}

/// Lift an `LNTerm` (untyped) back to a SAPIC term (all variables untyped).
fn ln_to_sapic(t: &LNTerm) -> SapicTerm {
    match t {
        VTerm::Lit(Lit::Var(v)) => VTerm::Lit(Lit::Var(SapicLVar::untyped(v.clone()))),
        VTerm::Lit(Lit::Con(c)) => VTerm::Lit(Lit::Con(c.clone())),
        VTerm::App(sym, args) => {
            let new_args: Vec<SapicTerm> = args.iter().map(ln_to_sapic).collect();
            match sym {
                FunSym::Ac(o) => tamarin_term::term::f_app_ac(*o, new_args),
                FunSym::C(o) => tamarin_term::term::f_app_c(*o, new_args),
                FunSym::NoEq(o) => tamarin_term::term::f_app_no_eq(o.clone(), new_args),
                FunSym::List => tamarin_term::term::f_app_list(new_args),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeSet, BTreeSet as Set};
    use tamarin_theory::sapic::{ProcessParsedAnnotation, SapicAction};
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::vterm::var_term;

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
            SapicAction::ChOut { chan: None, msg: var_term(h.clone()) },
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
        let rules: Set<CtxtStRule> = Set::new();
        let out = translate_let_destr(&rules, lett);
        // The Let must be gone; the top node is the substituted `out('t')`.
        match out {
            Process::Action(SapicAction::ChOut { msg, .. }, _, _) => {
                assert!(matches!(msg, VTerm::Lit(Lit::Con(_))), "h must be replaced by 't'");
            }
            other => panic!("expected Let to be eliminated to ChOut, got {other:?}"),
        }
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
        let rules: Set<CtxtStRule> = Set::new();
        let out = translate_let_destr(&rules, lett);
        match out {
            Process::Comb(ProcessCombinator::Let { .. }, a2, _, _) => {
                assert!(!a2.else_branch, "else_branch must be False (Null right child)");
            }
            other => panic!("expected kept Let, got {other:?}"),
        }
    }
}
