// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.SecretChannels` from
//! `lib/sapic/src/Sapic/SecretChannels.hs`.
//!
//! A channel is *always-secret* iff it is a fresh variable used only as a
//! channel identifier. Annotating such channels lets the translator emit
//! a silent transition instead of a public-channel exchange.

use std::collections::BTreeSet;

use tamarin_term::lterm::LVar;
use tamarin_theory::sapic::{Process, SapicAction, SapicLVar, SapicTerm};

use crate::annotation::ProcessAnnotation;

type AnnotatedProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// Collect every plain `LVar` that appears in `t`'s variables.
fn term_variables(t: &SapicTerm) -> BTreeSet<LVar> {
    tamarin_term::vterm::vars_vterm_in_order(t)
        .into_iter()
        .map(|sv| sv.var)
        .collect()
}

/// Walk the process collecting always-secret channel variables: every
/// fresh `New` adds the variable as a candidate, and every `ChOut` /
/// `Insert` whose RHS uses a candidate disqualifies it.
fn get_secret_channels(p: &AnnotatedProc, candidates: BTreeSet<LVar>) -> BTreeSet<LVar> {
    match p {
        Process::Action(SapicAction::New(v), _, body) => {
            let mut next = candidates;
            next.insert(v.var);
            get_secret_channels(body, next)
        }
        Process::Action(SapicAction::ChOut { msg, .. }, _, body)
        | Process::Action(SapicAction::Insert(_, msg), _, body) => {
            let used = term_variables(msg);
            let mut next = candidates;
            next.retain(|v| !used.contains(v));
            get_secret_channels(body, next)
        }
        Process::Action(_, _, body) => get_secret_channels(body, candidates),
        Process::Null(_) => candidates,
        Process::Comb(_, _, l, r) => {
            let cl = get_secret_channels(l, candidates.clone());
            let cr = get_secret_channels(r, candidates);
            cl.intersection(&cr).copied().collect()
        }
    }
}

/// `annotateSecretChannels`: for every `ChIn` / `ChOut` whose channel is a
/// single secret variable, attach a `secret_channel` annotation.
pub fn annotate_secret_channels(p: AnnotatedProc) -> AnnotatedProc {
    let svars = get_secret_channels(&p, BTreeSet::new());
    annotate_each(p, &svars)
}

fn annotate_each(p: AnnotatedProc, svars: &BTreeSet<LVar>) -> AnnotatedProc {
    match p {
        Process::Null(ann) => Process::Null(ann),
        Process::Comb(c, ann, l, r) => Process::Comb(
            c,
            ann,
            Box::new(annotate_each(*l, svars)),
            Box::new(annotate_each(*r, svars)),
        ),
        Process::Action(action, ann, body) => {
            let inner = Box::new(annotate_each(*body, svars));
            let new_ann = match &action {
                SapicAction::ChIn {
                    chan: Some(chan), ..
                }
                | SapicAction::ChOut {
                    chan: Some(chan), ..
                } => {
                    if let Some(chan_var) = lit_var(chan) {
                        if svars.contains(&chan_var) {
                            ann.append(ProcessAnnotation::with_secret_channel(chan_var))
                        } else {
                            ann
                        }
                    } else {
                        ann
                    }
                }
                _ => ann,
            };
            Process::Action(action, new_ann, inner)
        }
    }
}

/// If `t` is exactly a single variable literal, return its inner `LVar`.
fn lit_var(t: &SapicTerm) -> Option<LVar> {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(sv)) => Some(sv.var),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_term::vterm::var_term;
    use tamarin_theory::sapic::{ProcessCombinator, SapicLVar};

    fn slv(name: &str, sort: LSort) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, sort, 0))
    }

    fn null() -> AnnotatedProc {
        Process::Null(ProcessAnnotation::empty())
    }

    #[test]
    fn fresh_var_starts_as_candidate() {
        // new c; 0 — c is always-secret since it's never sent out.
        let c = slv("c", LSort::Fresh);
        let p: AnnotatedProc = Process::Action(
            SapicAction::New(c.clone()),
            ProcessAnnotation::empty(),
            Box::new(null()),
        );
        let out = get_secret_channels(&p, BTreeSet::new());
        assert!(out.contains(&c.var));
    }

    #[test]
    fn channel_used_in_chout_msg_is_disqualified() {
        // new c; out(d, c); — c was sent on d, so c is no longer secret.
        let c = slv("c", LSort::Fresh);
        let d = slv("d", LSort::Fresh);
        let body: AnnotatedProc = Process::Action(
            SapicAction::ChOut {
                chan: Some(var_term(d)),
                msg: var_term(c.clone()),
            },
            ProcessAnnotation::empty(),
            Box::new(null()),
        );
        let p: AnnotatedProc = Process::Action(
            SapicAction::New(c.clone()),
            ProcessAnnotation::empty(),
            Box::new(body),
        );
        let out = get_secret_channels(&p, BTreeSet::new());
        assert!(!out.contains(&c.var));
    }

    /// The join takes the intersection of the candidates that survive in the
    /// two branches, and it descends into each branch.  The test asserts the
    /// exact surviving set, and not just that the set is empty.  That exact
    /// set tells the intersection apart from three other behaviours.  Those
    /// are a union, either branch alone, and a join that ignores its children
    /// and returns the incoming candidates unchanged.  The equality below
    /// rejects the set that each of those three returns.
    #[test]
    fn parallel_intersects_candidates() {
        let c = slv("c", LSort::Fresh);
        let e = slv("e", LSort::Fresh);
        let d = slv("d", LSort::Fresh);
        // `out(d, c)`.  This action sends `c`, and that disqualifies `c` on
        // the branch that holds the action.
        let out_c = |body: AnnotatedProc| -> AnnotatedProc {
            Process::Action(
                SapicAction::ChOut {
                    chan: Some(var_term(d.clone())),
                    msg: var_term(c.clone()),
                },
                ProcessAnnotation::empty(),
                Box::new(body),
            )
        };
        // `new c; new e; (<l> | <r>)`.
        let with_branches = |l: AnnotatedProc, r: AnnotatedProc| -> AnnotatedProc {
            Process::Action(
                SapicAction::New(c.clone()),
                ProcessAnnotation::empty(),
                Box::new(Process::Action(
                    SapicAction::New(e.clone()),
                    ProcessAnnotation::empty(),
                    Box::new(Process::Comb(
                        ProcessCombinator::Parallel,
                        ProcessAnnotation::empty(),
                        Box::new(l),
                        Box::new(r),
                    )),
                )),
            )
        };
        let only_e: BTreeSet<LVar> = [e.var].into_iter().collect();
        // Only the left branch disqualifies `c`.
        assert_eq!(
            get_secret_channels(&with_branches(out_c(null()), null()), BTreeSet::new()),
            only_e
        );
        // Only the right branch disqualifies `c`.
        assert_eq!(
            get_secret_channels(&with_branches(null(), out_c(null())), BTreeSet::new()),
            only_e
        );
        // A binder under one branch does not escape the join.
        let a = slv("a", LSort::Fresh);
        let new_a: AnnotatedProc = Process::Action(
            SapicAction::New(a.clone()),
            ProcessAnnotation::empty(),
            Box::new(null()),
        );
        let joined = get_secret_channels(&with_branches(new_a, null()), BTreeSet::new());
        assert!(!joined.contains(&a.var));
        assert!(joined.contains(&c.var) && joined.contains(&e.var));
    }
}
