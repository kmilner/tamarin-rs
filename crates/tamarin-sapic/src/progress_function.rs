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
//! `pf_inv` constructs the inverse directly without materializing `pfRange'`.
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
#[cfg(test)]
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

// Only NDC nodes need recursive classification. Cache them for this borrowed
// process tree; action/null classifications require no map lookup or allocation.
struct Blocking<'a> {
    _root: &'a AProc,
    ndc: tamarin_utils::FastMap<*const AProc, bool>,
}

impl<'a> Blocking<'a> {
    fn new(root: &'a AProc) -> Self {
        Self {
            _root: root,
            ndc: Default::default(),
        }
    }

    fn known(&self, p: &AProc) -> Option<bool> {
        match p {
            Process::Null(_) => Some(true),
            Process::Action(ac, _, _) => Some(is_blocking_act(ac)),
            Process::Comb(tamarin_theory::sapic::ProcessCombinator::Ndc, ..) => {
                self.ndc.get(&std::ptr::from_ref(p)).copied()
            }
            _ => Some(false),
        }
    }

    fn get(&mut self, p: &'a AProc) -> bool {
        if let Some(value) = self.known(p) {
            return value;
        }
        let mut pending = vec![(p, false)];
        while let Some((node, finish)) = pending.pop() {
            if self.known(node).is_some() {
                continue;
            }
            let Process::Comb(_, _, left, right) = node else {
                unreachable!()
            };
            if finish {
                self.ndc.insert(
                    std::ptr::from_ref(node),
                    self.known(left).unwrap() && self.known(right).unwrap(),
                );
            } else {
                pending.push((node, true));
                pending.push((right, false));
                pending.push((left, false));
            }
        }
        self.known(p).unwrap()
    }
}

/// NDC descends through blocking children, retaining nonblocking children
/// themselves. Left-first DFS yields unique positions in lexicographic order;
/// retain their subprocesses so callers need no second walk to resolve them.
fn next_processes<'a>(
    p: &'a AProc,
    include_null: bool,
    blocking: &mut Blocking<'a>,
) -> Vec<(Pos, &'a AProc)> {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    let mut out = Vec::new();
    let mut pos = Pos::new();
    let mut pending = vec![(p, 0, None, true)];
    while let Some((node, parent_depth, edge, expand)) = pending.pop() {
        pos.truncate(parent_depth);
        pos.extend(edge);
        if !expand {
            out.push((pos.clone(), node));
            continue;
        }
        match node {
            Process::Null(_) => {
                if include_null {
                    out.push((pos.clone(), node));
                }
            }
            Process::Action(_, _, body) => {
                pos.push(1);
                out.push((pos.clone(), &**body));
            }
            Process::Comb(c, _, left, right) => {
                for (i, child) in [(2, right), (1, left)] {
                    let expand = matches!(c, PC::Ndc) && blocking.get(child);
                    pending.push((child, pos.len(), Some(i), expand));
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
pub(crate) fn pf_from(process: &AProc) -> PosSet {
    // Keep one DFS path, restoring its length before entering each sibling.
    // Saving absolute prefixes would copy O(depth²) entries even for a
    // nonblocking action chain whose only from-position is the root.
    let mut blocking = Blocking::new(process);
    let mut prefix = Pos::new();
    let mut pending = vec![(process, 0, Pos::new(), true)];
    let mut out = PosSet::new();
    while let Some((node, parent_depth, relative, parent_blocking)) = pending.pop() {
        prefix.truncate(parent_depth);
        prefix.extend(relative);
        if matches!(node, Process::Null(_)) {
            continue;
        }
        let blk = blocking.get(node);
        if !blk && parent_blocking {
            out.insert(prefix.clone());
        }
        for (pos, child) in next_processes(node, false, &mut blocking).into_iter().rev() {
            pending.push((child, prefix.len(), pos, blk));
        }
    }
    out
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
fn f(p: &AProc) -> PosSetSet {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    enum Task<'a> {
        Visit(&'a AProc, usize, Pos),
        Merge(usize, bool),
    }
    let mut blocking = Blocking::new(p);
    let mut prefix = Pos::new();
    let mut tasks = vec![Task::Visit(p, 0, Pos::new())];
    let mut results: Vec<PosSetSet> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Merge(count, parallel) => {
                // Both union and Cartesian union leave a sole child unchanged.
                if count == 1 {
                    continue;
                }
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
            Task::Visit(node, parent_depth, relative) => {
                // Restore the shared DFS path before visiting a sibling.
                prefix.truncate(parent_depth);
                prefix.extend(relative);
                if blocking.get(node) {
                    results.push(
                        [[prefix.clone()].into_iter().collect()]
                            .into_iter()
                            .collect(),
                    );
                    continue;
                }
                if let Process::Comb(PC::Parallel, _, left, right) = node {
                    tasks.push(Task::Merge(2, true));
                    for (i, child) in [(2, right), (1, left)] {
                        tasks.push(Task::Visit(child, prefix.len(), vec![i]));
                    }
                } else {
                    let positions = next_processes(node, true, &mut blocking);
                    tasks.push(Task::Merge(positions.len(), false));
                    for (pos, child) in positions.into_iter().rev() {
                        tasks.push(Task::Visit(child, prefix.len(), pos));
                    }
                }
            }
        }
    }
    results.pop().unwrap()
}

/// `pf proc pos` (ProgressFunction.hs:125-128): the progress function at a
/// position — `pos <..> f (proc@pos)`.
pub(crate) fn pf(proc: &AProc, pos: &[i64]) -> Result<PosSetSet, String> {
    let p_at = process_at(proc, pos).ok_or_else(|| format!("pf: invalid position {pos:?}"))?;
    let res = f(p_at);
    Ok(prefix_set_set(pos, &res))
}

/// `pfInv` (ProgressFunction.hs:146-149): the inverse of the progress function
/// — given a "to" position, the (first matching) "from" position.
///
/// HS uses `L.find` over `S.toList set` (ascending `(to, from)` pair order), so
/// the smallest `from` for each `to` wins. Visiting the domain in ascending
/// order and retaining the first entry gives the same inverse directly.
pub(crate) fn pf_inv(proc: &AProc) -> Result<impl Fn(&[i64]) -> Option<Pos> + use<>, String> {
    let mut inv: std::collections::BTreeMap<Pos, Pos> = std::collections::BTreeMap::new();
    for from in pf_from(proc) {
        for tos in pf(proc, &from)? {
            for to in tos {
                inv.entry(to).or_insert_with(|| from.clone());
            }
        }
    }
    Ok(move |x: &[i64]| -> Option<Pos> { inv.get(x).cloned() })
}

#[cfg(test)]
#[path = "progress_function_tests.rs"]
mod tests;
