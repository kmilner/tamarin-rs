// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.ProgressFunction` (`lib/sapic/src/Sapic/ProgressFunction.hs`).
//!
//! Computes, for each process position, the set of positions a local-progress
//! translation must move to.  Three entry points:
//!   - `pf_from`   (HS `pfFrom`):  the domain of the progress function — the set
//!     of "from" positions (positions that, once reached, must make progress).
//!   - `pf`        (HS `pf`):      per from-position, the CNF set-of-sets of "to"
//!     positions (`{{p1},{p2,p3}}` = go to p1 AND (p2 OR p3)).
//!   - `pf_inv`    (HS `pfInv`):   the inverse map (to → from).
//!
//! HS `pfRange` (the range on its own) has no RS consumer and is not ported;
//! its helper `pfRange'` is [`pf_range_prime`], which `pf_inv` searches.
//!
//! Faithful to HS down to set iteration order: `S.Set ProcessPosition` is
//! modelled as `BTreeSet<Vec<i64>>` (lexicographic position order = HS `Ord
//! [Int]`), and `S.Set (S.Set ProcessPosition)` as a `BTreeSet<BTreeSet<..>>`.

use std::collections::BTreeSet;

use tamarin_term::lterm::LVar;
use tamarin_theory::sapic::{process_at, Process, SapicAction, SapicLVar};

use crate::annotation::ProcessAnnotation;

type Pos = Vec<i64>;
type PosSet = BTreeSet<Pos>;
type PosSetSet = BTreeSet<PosSet>;
type AProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// `(<.>) pos = S.map (pos ++)` (ProgressFunction.hs:29-30): prefix `pos` onto
/// each element of a set of positions.
fn prefix_set(pos: &[i64], s: &PosSet) -> PosSet {
    s.iter()
        .map(|p| {
            let mut np = pos.to_vec();
            np.extend_from_slice(p);
            np
        })
        .collect()
}

/// `(<..>) pos = S.map (pos <.>)` (ProgressFunction.hs:33-34): prefix `pos` onto
/// each element in a set of sets.
fn prefix_set_set(pos: &[i64], s: &PosSetSet) -> PosSetSet {
    s.iter().map(|inner| prefix_set(pos, inner)).collect()
}

/// `isBlockingAct` (ProgressFunction.hs:43-46): `Rep` and `ChIn` are blocking.
fn is_blocking_act(ac: &SapicAction<SapicLVar>) -> bool {
    matches!(ac, SapicAction::Rep | SapicAction::ChIn { .. })
}

/// `blocking` (ProgressFunction.hs:49-54).
fn blocking(p: &AProc) -> bool {
    let mut pending = vec![p];
    while let Some(node) = pending.pop() {
        match node {
            Process::Null(_) => {}
            Process::Action(ac, _, _) if is_blocking_act(ac) => {}
            Process::Comb(tamarin_theory::sapic::ProcessCombinator::Ndc, _, left, right) => {
                pending.push(right);
                pending.push(left);
            }
            _ => return false,
        }
    }
    true
}

/// `next` (ProgressFunction.hs:57-64): next positions to jump to.
fn next(p: &AProc) -> PosSet {
    next_positions(p, false)
}

/// `next0` (ProgressFunction.hs:67-74): retain the empty position for Null.
fn next0(p: &AProc) -> PosSet {
    next_positions(p, true)
}

/// NDC descends through blocking children, retaining nonblocking children
/// themselves. Carry absolute positions to avoid repeatedly prefixing results.
fn next_positions(p: &AProc, include_null: bool) -> PosSet {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    let mut out = PosSet::new();
    let mut pending = vec![(p, Pos::new())];
    while let Some((node, pos)) = pending.pop() {
        match node {
            Process::Null(_) => {
                if include_null {
                    out.insert(pos);
                }
            }
            Process::Action(..) => {
                let mut child = pos;
                child.push(1);
                out.insert(child);
            }
            Process::Comb(c, _, left, right) => {
                for (i, child) in [(2, right), (1, left)] {
                    let mut child_pos = pos.clone();
                    child_pos.push(i);
                    if matches!(c, PC::Ndc) && blocking(child) {
                        pending.push((child, child_pos));
                    } else {
                        out.insert(child_pos);
                    }
                }
            }
        }
    }
    out
}

/// `pfFrom` (ProgressFunction.hs:76-90): the domain of the progress function.
///
/// `from' proc b`:
///   - `ProcessNull` → ∅
///   - otherwise → (if not blocking proc && b then {[]} else ∅)
///                 ∪ ⋃_{pos ∈ next proc} (pos <.> from' (proc@pos) (blocking proc))
///
/// `pfFrom process = from' process True`.
pub(crate) fn pf_from(process: &AProc) -> Result<PosSet, String> {
    // Keep one DFS path, restoring its length before entering each sibling.
    // Saving absolute prefixes would copy O(depth²) entries even for a
    // nonblocking action chain whose only from-position is the root.
    let mut prefix = Pos::new();
    let mut pending = vec![(process, 0, Pos::new(), true)];
    let mut out = PosSet::new();
    while let Some((node, parent_depth, relative, parent_blocking)) = pending.pop() {
        prefix.truncate(parent_depth);
        prefix.extend(relative);
        if matches!(node, Process::Null(_)) {
            continue;
        }
        let blk = blocking(node);
        if !blk && parent_blocking {
            out.insert(prefix.clone());
        }
        for pos in next(node).into_iter().rev() {
            let child = process_at(node, &pos)
                .ok_or_else(|| format!("pfFrom: invalid position {pos:?}"))?;
            pending.push((child, prefix.len(), pos, blk));
        }
    }
    Ok(out)
}

/// `combine x y = { x_i ∪ y_i | x_i ∈ x, y_i ∈ y }` (ProgressFunction.hs:94-99).
///
/// Faithful to HS's `S.foldr` nesting: outer fold over `x`, inner over `y`.
fn combine(x: &PosSetSet, y: &PosSetSet) -> PosSetSet {
    let mut out = PosSetSet::new();
    for x_i in x {
        for y_i in y {
            let mut u = x_i.clone();
            u.extend(y_i.iter().cloned());
            out.insert(u);
        }
    }
    out
}

/// `f` (ProgressFunction.hs:105-122): the CNF set-of-sets of positions the
/// process `p` must go to.
fn f(p: &AProc) -> Result<PosSetSet, String> {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    enum Task<'a> {
        Visit(&'a AProc, Pos),
        Merge(usize, bool),
    }
    let mut tasks = vec![Task::Visit(p, Pos::new())];
    let mut results: Vec<PosSetSet> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Merge(count, parallel) => {
                let start = results.len() - count;
                let mut acc = if parallel {
                    PosSetSet::new()
                } else {
                    [PosSet::new()].into_iter().collect()
                };
                for child in results.drain(start..) {
                    if parallel {
                        acc.extend(child);
                    } else {
                        acc = combine(&child, &acc);
                    }
                }
                results.push(acc);
            }
            Task::Visit(node, prefix) => {
                if blocking(node) {
                    results.push([[prefix].into_iter().collect()].into_iter().collect());
                    continue;
                }
                if let Process::Comb(PC::Parallel, _, left, right) = node {
                    tasks.push(Task::Merge(2, true));
                    for (i, child) in [(2, right), (1, left)] {
                        let mut pos = prefix.clone();
                        pos.push(i);
                        tasks.push(Task::Visit(child, pos));
                    }
                } else {
                    let positions = next0(node);
                    tasks.push(Task::Merge(positions.len(), false));
                    for pos in positions.into_iter().rev() {
                        let child = process_at(node, &pos)
                            .ok_or_else(|| format!("f: invalid position {pos:?}"))?;
                        let mut absolute = prefix.clone();
                        absolute.extend(pos);
                        tasks.push(Task::Visit(child, absolute));
                    }
                }
            }
        }
    }
    Ok(results.pop().unwrap())
}

/// `pf proc pos` (ProgressFunction.hs:125-128): the progress function at a
/// position — `pos <..> f (proc@pos)`.
pub(crate) fn pf(proc: &AProc, pos: &[i64]) -> Result<PosSetSet, String> {
    let p_at = process_at(proc, pos).ok_or_else(|| format!("pf: invalid position {pos:?}"))?;
    let res = f(p_at)?;
    Ok(prefix_set_set(pos, &res))
}

/// `flatten = S.foldr S.union S.empty` (ProgressFunction.hs:130-131).
fn flatten(s: &PosSetSet) -> PosSet {
    let mut out = PosSet::new();
    for inner in s {
        out.extend(inner.iter().cloned());
    }
    out
}

/// `pfRange'` (ProgressFunction.hs:133-139): the set of `(to, from)` pairs.
fn pf_range_prime(proc: &AProc) -> Result<BTreeSet<(Pos, Pos)>, String> {
    let froms = pf_from(proc)?;
    let mut acc: BTreeSet<(Pos, Pos)> = BTreeSet::new();
    for pos in froms {
        let flat = flatten(&pf(proc, &pos)?);
        for to in flat {
            acc.insert((to, pos.clone()));
        }
    }
    Ok(acc)
}

/// `pfInv` (ProgressFunction.hs:146-149): the inverse of the progress function
/// — given a "to" position, the (first matching) "from" position.
///
/// HS uses `L.find` over `S.toList set` (ascending `(to, from)` pair order), so
/// the first `from` for a `to` in lexicographic pair order wins.  The pairs are
/// ascending in `to` first, so keeping the FIRST `from` seen per `to` in a map
/// is that same choice, answered by lookup instead of a scan per query.
pub(crate) fn pf_inv(proc: &AProc) -> Result<impl Fn(&[i64]) -> Option<Pos> + use<>, String> {
    let mut inv: std::collections::BTreeMap<Pos, Pos> = std::collections::BTreeMap::new();
    for (to, from) in pf_range_prime(proc)? {
        inv.entry(to).or_insert(from);
    }
    Ok(move |x: &[i64]| -> Option<Pos> { inv.get(x).cloned() })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn progress_distinguishes_parallel_choice_and_blocking_ndc() {
        use tamarin_theory::sapic::ProcessCombinator as PC;
        let ann = ProcessAnnotation::empty;
        for (comb, expected) in [
            (PC::Parallel, vec![vec![vec![1]], vec![vec![2]]]),
            (
                PC::CondEq(
                    tamarin_term::vterm::const_term(tamarin_term::lterm::Name::new(
                        tamarin_term::lterm::NameTag::Pub,
                        "a",
                    )),
                    tamarin_term::vterm::const_term(tamarin_term::lterm::Name::new(
                        tamarin_term::lterm::NameTag::Pub,
                        "b",
                    )),
                ),
                vec![vec![vec![1], vec![2]]],
            ),
            (PC::Ndc, vec![vec![vec![]]]),
        ] {
            let p = Process::Comb(
                comb,
                ann(),
                Box::new(Process::Null(ann())).into(),
                Box::new(Process::Null(ann())).into(),
            );
            let want = expected
                .into_iter()
                .map(|s| s.into_iter().collect())
                .collect();
            assert_eq!(f(&p).unwrap(), want);
        }
    }

    #[test]
    fn progress_from_restores_paths_across_branches_and_ndc_jumps() {
        use tamarin_theory::sapic::ProcessCombinator as PC;
        fn reference(node: &AProc, parent_blocking: bool) -> PosSet {
            if matches!(node, Process::Null(_)) {
                return PosSet::new();
            }
            let blk = blocking(node);
            let mut result = PosSet::new();
            if !blk && parent_blocking {
                result.insert(Vec::new());
            }
            for pos in next(node) {
                let child = process_at(node, &pos).unwrap();
                result.extend(prefix_set(&pos, &reference(child, blk)));
            }
            result
        }
        fn output(body: AProc) -> AProc {
            Process::Action(
                SapicAction::ChOut {
                    chan: None,
                    msg: tamarin_term::lterm::pub_term("m"),
                },
                ProcessAnnotation::empty(),
                Box::new(body).into(),
            )
        }
        fn rep(body: AProc) -> AProc {
            Process::Action(
                SapicAction::Rep,
                ProcessAnnotation::empty(),
                Box::new(body).into(),
            )
        }
        fn branch(comb: PC<SapicLVar>, left: AProc, right: AProc) -> AProc {
            Process::Comb(
                comb,
                ProcessAnnotation::empty(),
                Box::new(left).into(),
                Box::new(right).into(),
            )
        }
        let null = || Process::Null(ProcessAnnotation::empty());
        let process = branch(
            PC::Parallel,
            branch(PC::Ndc, rep(rep(output(null()))), rep(output(null()))),
            rep(output(null())),
        );
        let expected = [vec![], vec![1, 1, 1, 1], vec![1, 2, 1], vec![2, 1]]
            .into_iter()
            .collect();
        assert_eq!(reference(&process, true), expected);
        assert_eq!(pf_from(&process).unwrap(), expected);

        fn generated(seed: &mut u64, depth: usize) -> AProc {
            *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let choice = (*seed >> 32) % 5;
            if depth == 0 || choice == 0 {
                return Process::Null(ProcessAnnotation::empty());
            }
            let left = generated(seed, depth - 1);
            match choice {
                1 => rep(left),
                2 => output(left),
                _ => branch(
                    if choice == 3 { PC::Ndc } else { PC::Parallel },
                    left,
                    generated(seed, depth - 1),
                ),
            }
        }
        let mut seed = 27321;
        for _ in 0..256 {
            let process = generated(&mut seed, 7);
            assert_eq!(pf_from(&process).unwrap(), reference(&process, true));
        }
    }

    #[test]
    fn deep_progress_keeps_absolute_positions() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut p = Process::Null(ProcessAnnotation::empty());
                for _ in 0..8192 {
                    p = Process::Action(
                        SapicAction::ChOut {
                            chan: None,
                            msg: tamarin_term::term::f_app_no_eq(
                                tamarin_term::function_symbols::one_sym(),
                                vec![],
                            ),
                        },
                        ProcessAnnotation::empty(),
                        Box::new(p).into(),
                    );
                }
                assert_eq!(pf_from(&p).unwrap(), [vec![]].into_iter().collect());
                assert_eq!(
                    f(&p).unwrap(),
                    [[vec![1; 8192]].into_iter().collect()]
                        .into_iter()
                        .collect()
                );
                p.drop_iteratively();
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
