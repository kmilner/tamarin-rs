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
use tamarin_theory::sapic::{
    map_terms_action, map_terms_comb, Process, ProcessCombinator, SapicLVar, SapicTerm,
};

use crate::annotation::{AnnotatedProcess, ProcessAnnotation};

trait LetSubstitution {
    fn term(&self, term: &SapicTerm) -> SapicTerm;
    fn formula(
        &self,
        formula: &tamarin_theory::sapic::SapicFormula,
    ) -> tamarin_theory::sapic::SapicFormula;
    fn match_vars(
        &self,
        vars: &std::collections::BTreeSet<SapicLVar>,
    ) -> std::collections::BTreeSet<SapicLVar> {
        tamarin_theory::sapic::apply_match_vars_with(
            |v| self.term(&tamarin_term::vterm::var_term(v.clone())),
            vars,
        )
    }
}

#[cfg(test)]
impl LetSubstitution for Subst<Name, SapicLVar> {
    fn term(&self, term: &SapicTerm) -> SapicTerm {
        let bindings = self.to_list();
        tamarin_term::term::bind_lits_cow(term, &mut |lit| match lit {
            Lit::Var(v) => bindings
                .iter()
                .find(|(key, _)| key.var == v.var)
                .map(|(_, image)| image.clone()),
            Lit::Con(_) => None,
        })
        .unwrap_or_else(|| term.clone())
    }
    fn formula(
        &self,
        formula: &tamarin_theory::sapic::SapicFormula,
    ) -> tamarin_theory::sapic::SapicFormula {
        let local = Subst::from_list(
            tamarin_theory::formula::formula_frees(formula)
                .into_iter()
                .map(|v| {
                    let image = self.term(&tamarin_term::vterm::var_term(v.clone()));
                    (v, image)
                }),
        );
        tamarin_theory::formula::apply_subst(&local, formula.clone())
    }
}

/// Ordered substitutions, with a variable index and lazy range composition.
/// An image receives only substitutions introduced AFTER its binding; this
/// preserves simultaneous bindings and self-referential images. Type tags are
/// retained in the images, but do not participate in variable lookup.
/// Branch restoration removes entries rather than copying the entire scope.
#[derive(Default)]
struct LetSubsts {
    entries: Vec<(LVar, SapicTerm, usize)>,
    variables: std::collections::BTreeMap<LVar, Vec<usize>>,
    resolved: std::cell::RefCell<std::collections::BTreeMap<usize, SapicTerm>>,
}

impl LetSubsts {
    fn extend(&mut self, subst: &Subst<Name, SapicLVar>) {
        self.resolved.get_mut().clear();
        let end = self.entries.len() + subst.len();
        for (var, term) in subst.to_list() {
            self.variables
                .entry(var.var)
                .or_default()
                .push(self.entries.len());
            self.entries.push((var.var, term, end));
        }
    }

    fn restore(&mut self, len: usize) {
        if self.entries.len() == len {
            return;
        }
        self.resolved.get_mut().clear();
        while self.entries.len() > len {
            let (var, _, _) = self.entries.pop().unwrap();
            let indices = self.variables.get_mut(&var).unwrap();
            indices.pop();
            if indices.is_empty() {
                self.variables.remove(&var);
            }
        }
    }

    fn image(&self, var: &SapicLVar, after: usize) -> Option<SapicTerm> {
        let indices = self.variables.get(&var.var)?;
        let index = *indices.get(indices.partition_point(|index| *index < after))?;
        if let Some(term) = self.resolved.borrow().get(&index) {
            return Some(term.clone());
        }
        let (_, term, next) = &self.entries[index];
        let resolved =
            tamarin_utils::stack::ensure_sufficient_stack(|| self.apply_after(term, *next));
        self.resolved.borrow_mut().insert(index, resolved.clone());
        Some(resolved)
    }

    fn apply_after(&self, term: &SapicTerm, after: usize) -> SapicTerm {
        if after == self.entries.len() {
            return term.clone();
        }
        tamarin_term::term::bind_lits_cow(term, &mut |lit| match lit {
            Lit::Var(var) => self.image(var, after),
            Lit::Con(_) => None,
        })
        .unwrap_or_else(|| term.clone())
    }
}

impl LetSubstitution for LetSubsts {
    fn term(&self, term: &SapicTerm) -> SapicTerm {
        self.apply_after(term, 0)
    }
    fn formula(
        &self,
        formula: &tamarin_theory::sapic::SapicFormula,
    ) -> tamarin_theory::sapic::SapicFormula {
        // Only materialize images of variables this formula actually mentions.
        let local = Subst::from_list(
            tamarin_theory::formula::formula_frees(formula)
                .into_iter()
                .filter_map(|v| self.image(&v, 0).map(|t| (v, t))),
        );
        tamarin_theory::formula::map_atoms_ref(formula, &mut |_, atom| {
            tamarin_theory::atom::map_atom(atom, &mut |term| {
                tamarin_term::subst::apply_bvterm(&local, term)
            })
        })
    }
}

/// `translateLetDestr rules p` (LetDestructors.hs:98-100) — the entry point.
pub(crate) fn translate_let_destr(
    rules: &std::collections::BTreeSet<CtxtStRule>,
    mut p: AnnotatedProcess<LVar>,
) -> AnnotatedProcess<LVar> {
    enum Work<'a> {
        Visit(&'a mut AnnotatedProcess<LVar>),
        Restore(usize),
    }
    let mut inherited = LetSubsts::default();
    let mut pending = vec![Work::Visit(&mut p)];
    while let Some(work) = pending.pop() {
        let node = match work {
            Work::Visit(node) => node,
            Work::Restore(len) => {
                inherited.restore(len);
                continue;
            }
        };
        loop {
            if !inherited.entries.is_empty() {
                subst_node(&inherited, node);
            }
            let Process::Comb(
                ProcessCombinator::Let {
                    left,
                    right,
                    match_vars,
                },
                ann,
                _,
                pr,
            ) = node
            else {
                break;
            };
            // Eliminating a let exposes a new root, which must be processed before
            // descending. Kept lets retain the upstream fresh-annotation policy.
            let elsebranch = !matches!(**pr, Process::Null(_));
            if let VTerm::Lit(Lit::Var(_)) = left
                && let Some(funsym) = destructor_head(right)
            {
                let t1_ln = crate::base_translation::to_ln_term(left);
                let t2_ln = crate::base_translation::to_ln_term(right);
                let VTerm::App(_, rightterms) = &t2_ln else {
                    unreachable!()
                };
                if let Some((leftterms, outvar)) = find_rule(&funsym, rules) {
                    let subst = Subst::from_list(vec![(outvar, t1_ln.clone())]);
                    *ann = ProcessAnnotation::with_destructor_equation(
                        apply_vterm(&subst, to_pairs(&leftterms)),
                        to_pairs(rightterms),
                        elsebranch,
                    );
                    let comb = rebuild_let_comb(&t1_ln, &funsym, rightterms);
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
                && !match_vars.iter().any(|v| v.var == svar.var)
            {
                let subst = make_let_subst(svar, right);
                let old = std::mem::replace(node, Process::Null(ProcessAnnotation::empty()));
                let Process::Comb(_, _, left, right) = old else {
                    unreachable!()
                };
                *node = left.into_inner();
                drop(right);
                inherited.extend(&subst);
            } else {
                *ann = ProcessAnnotation::with_else_branch(elsebranch);
                break;
            }
        }
        match node {
            Process::Null(_) => {}
            Process::Action(_, _, body) => pending.push(Work::Visit(body)),
            Process::Comb(_, _, left, right) => {
                let checkpoint = inherited.entries.len();
                pending.push(Work::Restore(checkpoint));
                pending.push(Work::Visit(right));
                pending.push(Work::Restore(checkpoint));
                pending.push(Work::Visit(left));
            }
        }
    }
    p
}

// Type erasure preserves the head except for singleton AC wrappers, which
// map_lits normalizes away. Inspect just that spine before converting terms.
fn destructor_head(mut term: &SapicTerm) -> Option<tamarin_term::function_symbols::NoEqSym> {
    loop {
        match term {
            VTerm::App(FunSym::Ac(_), args) if args.len() == 1 => term = &args[0],
            VTerm::App(FunSym::NoEq(sym), _)
                if sym.constructability == Constructability::Destructor =>
            {
                return Some(*sym)
            }
            _ => return None,
        }
    }
}

#[cfg(test)]
fn translate_let_destr_reference(
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
            if let VTerm::Lit(Lit::Var(_)) = left
                && let Some(funsym) = destructor_head(right)
            {
                let t1_ln = crate::base_translation::to_ln_term(left);
                let t2_ln = crate::base_translation::to_ln_term(right);
                let VTerm::App(_, rightterms) = &t2_ln else {
                    unreachable!()
                };
                if let Some((leftterms, outvar)) = find_rule(&funsym, rules) {
                    let subst = Subst::from_list(vec![(outvar, t1_ln.clone())]);
                    *ann = ProcessAnnotation::with_destructor_equation(
                        apply_vterm(&subst, to_pairs(&leftterms)),
                        to_pairs(rightterms),
                        elsebranch,
                    );
                    let comb = rebuild_let_comb(&t1_ln, &funsym, rightterms);
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
                && !match_vars.iter().any(|v| v.var == svar.var)
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

/// The substitution retains typed images; lookup uses the underlying variable
/// so one binding covers every occurrence regardless of its inferred type.
fn make_let_subst(svar: &SapicLVar, t2: &SapicTerm) -> Subst<Name, SapicLVar> {
    Subst::from_list(vec![(svar.clone(), t2.clone())])
}

/// Apply a SAPIC substitution to every term in a process subtree. HS `applyM`
/// also applies ordinary term substitution to parsed location annotations
/// (fixed upstream in #922). Case B only substitutes a `let`-bound variable
/// that, by typing, does not occur as an inner binder of `pl` — so a plain
/// substitution is faithful for the in-scope cases.
#[cfg(test)]
fn apply_subst_process_mut(subst: &Subst<Name, SapicLVar>, p: &mut AnnotatedProcess<LVar>) {
    crate::process_walk::walk_mut(p, (), |node, _| {
        subst_node(subst, node);
        Ok::<_, std::convert::Infallible>(true)
    })
    .unwrap();
}

fn subst_node(subst: &impl LetSubstitution, node: &mut AnnotatedProcess<LVar>) {
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
}

fn subst_annotation(
    subst: &impl LetSubstitution,
    mut ann: ProcessAnnotation<LVar>,
) -> ProcessAnnotation<LVar> {
    ann.parsing_ann = ann
        .parsing_ann
        .map_location(|location| subst.term(&location));
    ann
}

/// `apply subst` for a `SapicAction SapicLVar` (Sapic/Process.hs:319-321):
/// `mapTermsAction`, with `ChIn` and `Msr` match variables rewritten by
/// [`tamarin_theory::sapic::apply_match_vars`].
fn subst_action(
    subst: &impl LetSubstitution,
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
                chan: chan.as_ref().map(|t| subst.term(t)),
                msg: subst.term(msg),
                // HS special-cases `ChIn` in `Apply SapicSubst (SapicAction
                // SapicLVar)` (Sapic/Process.hs:319-321) to reach this rewrite: a
                // `let`-bound match var `=t` (where `t = <a,'test'>`) becomes the
                // match-var set `{a}`.
                match_vars: subst.match_vars(match_vars),
            };
        }
        A::Msr { match_vars, .. } => {
            // Pinned HS reaches `Set.map (apply subst)` here and aborts if a
            // match variable maps to a compound term.  Keep the robust
            // `ChIn`/`Let` policy instead: collect the image's free variables
            // so a compound match pattern remains usable.
            let mut mapped =
                map_terms_action(|t| subst.term(t), |f| subst.formula(f), |v| v.clone(), ac);
            let A::Msr {
                match_vars: mapped_match_vars,
                ..
            } = &mut mapped
            else {
                unreachable!("mapping an MSR action preserves its constructor")
            };
            *mapped_match_vars = subst.match_vars(match_vars);
            return mapped;
        }
        _ => {}
    }
    map_terms_action(
        |t| subst.term(t),
        // A `let`-bound value that an embedded `_restrict` mentions is
        // rewritten there as it is in the fact rows.  A quantifier binder is a
        // `Bound` De Bruijn index, outside the substitution's domain, so it
        // cannot capture a variable of the image.
        |f| subst.formula(f),
        // The `let` pass substitutes values, not binders, so a variable the
        // action binds on its own stands for itself.
        |v| v.clone(),
        ac,
    )
}

/// `apply subst` for a `ProcessCombinator SapicLVar` (Sapic/Process.hs:330-334).
fn subst_comb(
    subst: &impl LetSubstitution,
    c: &ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    let mut mapped = map_terms_comb(
        |t| subst.term(t),
        // A Case-B `let`-elimination (`let z = t in P`) rewrites the free
        // variable `z` inside a downstream conditional's formula too: `z` is a
        // value bound by the `let`, not a process binder, so the `Cond`
        // payload's `z` references the same value.
        |f| subst.formula(f),
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
        *mapped_match_vars = subst.match_vars(match_vars);
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
#[path = "let_destructors_tests.rs"]
mod tests;
