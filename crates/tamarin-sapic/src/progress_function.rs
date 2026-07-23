// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, charlie-j, arcz, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/ProgressFunction.hs

//! Port of `Sapic.ProgressFunction` (`lib/sapic/src/Sapic/ProgressFunction.hs`).
//!
//! Computes, for each process position, the set of positions a local-progress
//! translation must move to.  The two key outputs consumed by
//! `progress_translation` are:
//!   - `pf_from`   (HS `pfFrom`):  the domain of the progress function — the set
//!     of "from" positions (positions that, once reached, must make progress).
//!   - `pf`        (HS `pf`):      per from-position, the CNF set-of-sets of "to"
//!     positions (`{{p1},{p2,p3}}` = go to p1 AND (p2 OR p3)).
//!   - `pf_range`  (HS `pfRange`): the set of all "to" positions (the range), and
//!   - `pf_inv`    (HS `pfInv`):   the inverse map (to → from).
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
    match p {
        Process::Null(_) => true,
        Process::Action(ac, _, _) => is_blocking_act(ac),
        Process::Comb(tamarin_theory::sapic::ProcessCombinator::Ndc, _, pl, pr) => {
            blocking(pl) && blocking(pr)
        }
        Process::Comb(..) => false,
    }
}

/// `next` (ProgressFunction.hs:57-64): next positions to jump to.
fn next(p: &AProc) -> PosSet {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    match p {
        Process::Null(_) => PosSet::new(),
        Process::Action(..) => [vec![1i64]].into_iter().collect(),
        Process::Comb(PC::Ndc, _, pl, pr) => {
            let mut out = next_or_child(pl, &[1]);
            out.extend(next_or_child(pr, &[2]));
            out
        }
        Process::Comb(..) => [vec![1i64], vec![2i64]].into_iter().collect(),
    }
}

/// `nextOrChild` (ProgressFunction.hs:61-63): if the child is blocking, prefix
/// `pos` onto its `next`; otherwise the singleton `{pos}`.
fn next_or_child(p: &AProc, pos: &[i64]) -> PosSet {
    if blocking(p) {
        prefix_set(pos, &next(p))
    } else {
        [pos.to_vec()].into_iter().collect()
    }
}

/// `next0` (ProgressFunction.hs:67-74): like `next` but the null process maps to
/// the singleton of the EMPTY position.
fn next0(p: &AProc) -> PosSet {
    use tamarin_theory::sapic::ProcessCombinator as PC;
    match p {
        Process::Null(_) => [Vec::<i64>::new()].into_iter().collect(),
        Process::Action(..) => [vec![1i64]].into_iter().collect(),
        Process::Comb(PC::Ndc, _, pl, pr) => {
            let mut out = next0_or_child(pl, &[1]);
            out.extend(next0_or_child(pr, &[2]));
            out
        }
        Process::Comb(..) => [vec![1i64], vec![2i64]].into_iter().collect(),
    }
}

fn next0_or_child(p: &AProc, pos: &[i64]) -> PosSet {
    if blocking(p) {
        prefix_set(pos, &next0(p))
    } else {
        [pos.to_vec()].into_iter().collect()
    }
}

/// `pfFrom` (ProgressFunction.hs:76-90): the domain of the progress function.
///
/// `from' proc b`:
///   - `ProcessNull` → ∅
///   - otherwise → (if not blocking proc && b then {[]} else ∅)
///                 ∪ ⋃_{pos ∈ next proc} (pos <.> from' (proc@pos) (blocking proc))
///
/// `pfFrom process = from' process True`.
pub fn pf_from(process: &AProc) -> Result<PosSet, String> {
    fn from(process: &AProc, proc: &AProc, b: bool) -> Result<PosSet, String> {
        if let Process::Null(_) = proc {
            return Ok(PosSet::new());
        }
        // `conditionAction proc b = not (blocking proc) && b`
        let condition = !blocking(proc) && b;
        let mut res = if condition {
            [Vec::<i64>::new()].into_iter().collect::<PosSet>()
        } else {
            PosSet::new()
        };
        let blk = blocking(proc);
        for pos in next(proc) {
            // `p' <- processAt proc pos; res <- from' p' (blocking proc)`
            let p_at = process_at(proc, &pos)
                .ok_or_else(|| format!("pfFrom: invalid position {pos:?}"))?;
            let sub = from(process, p_at, blk)?;
            res.extend(prefix_set(&pos, &sub));
        }
        Ok(res)
    }
    from(process, process, true)
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
    // `ss x = S.singleton (S.singleton x)`.
    let ss = |x: Pos| -> PosSetSet { [[x].into_iter().collect::<PosSet>()].into_iter().collect() };
    if blocking(p) {
        return Ok(ss(Vec::new()));
    }
    if let Process::Comb(PC::Parallel, _, pl, pr) = p {
        let ll = f(pl)?;
        let lr = f(pr)?;
        let mut out = prefix_set_set(&[1], &ll);
        out.extend(prefix_set_set(&[2], &lr));
        return Ok(out);
    }
    // `foldM combineWithRecursive (S.singleton S.empty) (next0 p)`.
    // The accumulator starts as the singleton-of-the-empty-set (combine's unit).
    let mut acc: PosSetSet = [PosSet::new()].into_iter().collect();
    for pos in next0(p) {
        let p_at = process_at(p, &pos).ok_or_else(|| format!("f: invalid position {pos:?}"))?;
        let lpos = f(p_at)?;
        // `combine (pos <..> lpos) acc`
        acc = combine(&prefix_set_set(&pos, &lpos), &acc);
    }
    Ok(acc)
}

/// `pf proc pos` (ProgressFunction.hs:125-128): the progress function at a
/// position — `pos <..> f (proc@pos)`.
pub fn pf(proc: &AProc, pos: &[i64]) -> Result<PosSetSet, String> {
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
/// the first `from` for a `to` in lexicographic pair order wins.
pub fn pf_inv(proc: &AProc) -> Result<impl Fn(&[i64]) -> Option<Pos>, String> {
    let set = pf_range_prime(proc)?;
    Ok(move |x: &[i64]| -> Option<Pos> {
        set.iter()
            .find(|(to, _)| to.as_slice() == x)
            .map(|(_, from)| from.clone())
    })
}
