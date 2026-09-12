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
    let mut pending = vec![(p, candidates)];
    let mut result: Option<BTreeSet<LVar>> = None;
    while let Some((node, mut candidates)) = pending.pop() {
        match node {
            Process::Null(_) => {
                // Branch joins are intersections, so intersecting leaf results
                // directly avoids retaining a separate stack of partial joins.
                match &mut result {
                    None => result = Some(candidates),
                    Some(result) => result.retain(|v| candidates.contains(v)),
                }
            }
            Process::Action(ac, _, body) => {
                match ac {
                    SapicAction::New(v) => {
                        candidates.insert(v.var);
                    }
                    SapicAction::ChOut { msg, .. } | SapicAction::Insert(_, msg) => {
                        let used = term_variables(msg);
                        candidates.retain(|v| !used.contains(v));
                    }
                    _ => {}
                }
                pending.push((body, candidates));
            }
            Process::Comb(_, _, left, right) => {
                pending.push((right, candidates.clone()));
                pending.push((left, candidates));
            }
        }
    }
    result.unwrap()
}

/// `annotateSecretChannels`: for every `ChIn` / `ChOut` whose channel is a
/// single secret variable, attach a `secret_channel` annotation.
pub(crate) fn annotate_secret_channels(p: AnnotatedProc) -> AnnotatedProc {
    let svars = get_secret_channels(&p, BTreeSet::new());
    annotate_each(p, &svars)
}

fn annotate_each(mut p: AnnotatedProc, svars: &BTreeSet<LVar>) -> AnnotatedProc {
    crate::process_walk::walk_mut(&mut p, (), |node, _| {
        if let Process::Action(
            SapicAction::ChIn {
                chan: Some(chan), ..
            }
            | SapicAction::ChOut {
                chan: Some(chan), ..
            },
            ann,
            _,
        ) = node
            && let Some(v) = lit_var(chan)
            && svars.contains(&v)
        {
            *ann = std::mem::take(ann).append(ProcessAnnotation::with_secret_channel(v));
        }
        Ok::<_, std::convert::Infallible>(true)
    })
    .unwrap();
    p
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
            Box::new(null()).into(),
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
            Box::new(null()).into(),
        );
        let p: AnnotatedProc = Process::Action(
            SapicAction::New(c.clone()),
            ProcessAnnotation::empty(),
            Box::new(body).into(),
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
                Box::new(body).into(),
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
                        Box::new(l).into(),
                        Box::new(r).into(),
                    ))
                    .into(),
                ))
                .into(),
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
            Box::new(null()).into(),
        );
        let joined = get_secret_channels(&with_branches(new_a, null()), BTreeSet::new());
        assert!(!joined.contains(&a.var));
        assert!(joined.contains(&c.var) && joined.contains(&e.var));
        // Nested joins must still account for every leaf, including leaves
        // reached after a subtree has already narrowed the candidate set.
        let nested = with_branches(
            with_branches(out_c(null()), null()),
            with_branches(null(), null()),
        );
        assert_eq!(get_secret_channels(&nested, BTreeSet::new()), only_e);
    }
}
