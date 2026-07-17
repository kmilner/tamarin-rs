// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, "sans-sucre" (github), and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Data/DAG/Simple.hs

//! Port of `Data.DAG.Simple` from `lib/utils/src/Data/DAG/Simple.hs`.
//!
//! Vertex-list-based DAG operations. A `Relation<T>` is `Vec<(T, T)>`.
//!
//! `dfs_loop_breakers` is the live loop-breaker selector used by the
//! constraint-solver context (`useAutoLoopBreakersAC`). `cyclic` and
//! `trans_red` back the display-graph compression pass
//! (`tamarin-server`'s `graph::simplify::transitive_reduction`); `trans_red`
//! in turn drives `toposort` (and thus `inverse`) and `reachable_set`. The
//! remaining operations (`restrict`, `image`) are a faithful port of the
//! rest of `Data.DAG.Simple` retained for completeness and have no live
//! caller yet.

use std::collections::BTreeSet;

pub type Relation<T> = Vec<(T, T)>;

/// `restrict p rel`: keep edges where both endpoints satisfy `p`.
pub fn restrict<T: Clone, F: FnMut(&T) -> bool>(rel: &Relation<T>, mut p: F) -> Relation<T> {
    rel.iter()
        .filter(|(x, y)| p(x) && p(y))
        .cloned()
        .collect()
}

/// `image x rel`: every successor of `x` in `rel`.
pub fn image<T: Eq + Clone>(x: &T, rel: &Relation<T>) -> Vec<T> {
    rel.iter()
        .filter_map(|(a, b)| if a == x { Some(b.clone()) } else { None })
        .collect()
}

/// `inverse rel`: every edge reversed.
pub fn inverse<T: Clone>(rel: &Relation<T>) -> Relation<T> {
    rel.iter().map(|(a, b)| (b.clone(), a.clone())).collect()
}

/// `reachableSet start rel`: every node reachable from any element of `start`.
pub fn reachable_set<T: Ord + Clone>(start: &[T], rel: &Relation<T>) -> BTreeSet<T> {
    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut stack: Vec<T> = start.to_vec();
    while let Some(x) = stack.pop() {
        if visited.insert(x.clone()) {
            // Inlined `image(&x, rel)`: scan `rel` front-to-back, cloning only
            // the unvisited successors actually pushed (avoids a per-node Vec).
            for (a, b) in rel {
                if a == &x && !visited.contains(b) {
                    stack.push(b.clone());
                }
            }
        }
    }
    visited
}

/// `cyclic rel`: whether `rel` contains a directed cycle.
pub fn cyclic<T: Ord + Clone>(rel: &Relation<T>) -> bool {
    fn find_loop<T: Ord + Clone>(
        rel: &Relation<T>,
        parents: &mut BTreeSet<T>,
        visited: &mut BTreeSet<T>,
        x: T,
    ) -> bool {
        if parents.contains(&x) { return true; }
        if visited.contains(&x) { return false; }
        parents.insert(x.clone());
        // Inlined `image(&x, rel)`: scan `rel` front-to-back, recursing into each
        // successor in the same order (no `visited` guard here, matching the
        // original `image` snapshot which has none). `rel` is not mutated during
        // the scan, so the snapshot and the inlined scan are equivalent.
        for (a, b) in rel {
            if a == &x && find_loop(rel, parents, visited, b.clone()) {
                return true;
            }
        }
        parents.remove(&x);
        visited.insert(x);
        false
    }

    let mut visited = BTreeSet::new();
    for (src, _) in rel {
        if !visited.contains(src) {
            let mut parents = BTreeSet::new();
            if find_loop(rel, &mut parents, &mut visited, src.clone()) {
                return true;
            }
        }
    }
    false
}

/// `toposort rel`: topological order. If `rel` is cyclic the returned order
/// is some permutation of all vertices but is not guaranteed to be a valid
/// topological sort — matching the Haskell semantics.
pub fn toposort<T: Ord + Clone>(rel: &Relation<T>) -> Vec<T> {
    let inv = inverse(rel);

    // Collect all vertices in source-then-target order, like Haskell's
    // `map fst dag ++ map snd dag`.
    let mut order_input: Vec<T> = Vec::with_capacity(rel.len() * 2);
    for (a, _) in rel { order_input.push(a.clone()); }
    for (_, b) in rel { order_input.push(b.clone()); }

    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut out: Vec<T> = Vec::new();

    fn visit<T: Ord + Clone>(
        rel: &Relation<T>,
        inv: &Relation<T>,
        visited: &mut BTreeSet<T>,
        out: &mut Vec<T>,
        x: T,
    ) {
        if visited.contains(&x) { return; }
        visited.insert(x.clone());
        // Inlined `image(&x, inv)`: scan `inv` front-to-back, recursing into each
        // predecessor in the same order (avoids a per-node Vec). `inv` is
        // immutable during the scan, so this matches the snapshot form.
        for (a, b) in inv {
            if a == &x {
                visit(rel, inv, visited, out, b.clone());
            }
        }
        out.push(x);
    }

    for x in order_input {
        visit(rel, &inv, &mut visited, &mut out, x);
    }
    out
}

/// `dfsLoopBreakers rel`: a minimal set of vertices whose removal breaks
/// every cycle, found by greedy DFS. Faithful port of HS
/// `Data.DAG.Simple.dfsLoopBreakers` (`lib/utils/src/Data/DAG/Simple.hs:111-128`):
///
/// ```haskell
/// dfsLoopBreakers rel =
///     D.toList $ snd $ execRWS (mapM_ (visit . fst) rel) () S.empty
///   where
///     visit x = do
///         visited <- gets (S.member x)
///         unless visited $ findLoopBreakers S.empty x
///     findLoopBreakers parents0 x = do
///         modify (S.insert x)
///         let parents = S.insert x parents0
///             ys      = x `image` rel
///         if any (`S.member` parents) ys
///           then tell (return x)
///           else forM_ ys $ \y -> do
///                    visited <- gets (S.member y)
///                    unless visited $ findLoopBreakers parents y
/// ```
///
/// Semantics replicated exactly (the picked set reaches printed output, so
/// order matters):
/// - Iterate the relation in **list order**, using each tuple's first
///   component as a DFS root — callers must build `rel` in HS's order.
/// - A single **monotonic `visited` set** shared across all roots: once a
///   node is visited it is never re-explored, even from a later root.
/// - On the **first** successor that is already a parent (back-edge), emit
///   the **current node** (the back-edge source, not the ancestor target) and
///   stop descending.
/// - Emission order = DFS discovery order (`tell`/`DList` append), mirrored
///   by pushing onto the `breakers` `Vec`.
///
/// `parents` is threaded down the current DFS path; here it is a single set
/// mutated with insert-on-enter / remove-on-leave, so at each node it holds
/// exactly that node's path ancestors — equivalent to HS's persistent
/// `S.insert x parents0`, because the monotonic `visited` set explores each
/// node only once.
pub fn dfs_loop_breakers<T: Ord + Clone>(rel: &Relation<T>) -> Vec<T> {
    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut breakers: Vec<T> = Vec::new();

    fn find<T: Ord + Clone>(
        rel: &Relation<T>,
        parents: &mut BTreeSet<T>,
        visited: &mut BTreeSet<T>,
        breakers: &mut Vec<T>,
        x: T,
    ) {
        visited.insert(x.clone());
        parents.insert(x.clone());
        // Inlined `image(&x, rel)`, preserving the two-phase structure: first
        // check whether ANY successor is already a parent (back-edge), then
        // otherwise recurse into the unvisited successors front-to-back. `rel` is
        // immutable so the two scans see the same successors as the snapshot.
        let hits_parent = rel
            .iter()
            .any(|(a, b)| a == &x && parents.contains(b));
        if hits_parent {
            breakers.push(x.clone());
        } else {
            for (a, b) in rel {
                if a == &x && !visited.contains(b) {
                    find(rel, parents, visited, breakers, b.clone());
                }
            }
        }
        parents.remove(&x);
    }

    for (src, _) in rel {
        if !visited.contains(src) {
            let mut parents = BTreeSet::new();
            find(rel, &mut parents, &mut visited, &mut breakers, src.clone());
        }
    }
    breakers
}

/// `transRed dag`: transitive reduction of a DAG. Pre: `dag` is acyclic.
pub fn trans_red<T: Ord + Clone>(dag: &Relation<T>) -> Relation<T> {
    let topo = toposort(dag);
    let n = topo.len();
    if n < 2 { return Vec::new(); }

    let dag_set: BTreeSet<(T, T)> = dag.iter().cloned().collect();

    // Pairs (j, i) with j < i, longest gap first, mirroring the Haskell
    // `[reverse [0..x-1] zip repeat x | x <- [1..n-1]]`.
    let mut indexed: Vec<(usize, usize)> = Vec::new();
    for i in 1..n {
        for j in (0..i).rev() {
            indexed.push((j, i));
        }
    }

    // Haskell `foldl' visit []` prepends kept edges (`x : newEdges`), so the
    // returned list is in reverse processing order. We build forward (push) and
    // reverse at the end to reproduce that order exactly. The reachability
    // decision reads `new_edges` only as a set, so it is order-independent.
    let mut new_edges: Relation<T> = Vec::new();
    for (j, i) in indexed {
        let edge = (topo[j].clone(), topo[i].clone());
        if !dag_set.contains(&edge) { continue; }
        let reachable = reachable_set(std::slice::from_ref(&edge.0), &new_edges);
        if !reachable.contains(&edge.1) {
            new_edges.push(edge);
        }
    }
    new_edges.reverse();
    new_edges
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rel<T: Clone>(es: &[(T, T)]) -> Relation<T> { es.to_vec() }

    #[test]
    fn image_and_inverse() {
        let r = rel(&[(1, 2), (1, 3), (2, 3)]);
        let mut img = image(&1, &r);
        img.sort();
        assert_eq!(img, vec![2, 3]);
        let inv = inverse(&r);
        assert!(inv.contains(&(2, 1)));
        assert!(inv.contains(&(3, 1)));
        assert!(inv.contains(&(3, 2)));
    }

    #[test]
    fn restrict_filters() {
        let r = rel(&[(1, 2), (2, 3), (3, 4)]);
        let r2 = restrict(&r, |x| *x != 3);
        assert_eq!(r2, vec![(1, 2)]);
    }

    #[test]
    fn reachable_basic() {
        let r = rel(&[(1, 2), (2, 3), (4, 5)]);
        let s = reachable_set(&[1], &r);
        assert_eq!(s, BTreeSet::from([1, 2, 3]));
        let s = reachable_set(&[4], &r);
        assert_eq!(s, BTreeSet::from([4, 5]));
    }

    #[test]
    fn cyclic_detection() {
        assert!(!cyclic(&rel(&[(1, 2), (2, 3)])));
        assert!(cyclic(&rel(&[(1, 2), (2, 1)])));
        assert!(cyclic(&rel(&[(1, 1)]))); // self-loop
        assert!(cyclic(&rel(&[(1, 2), (2, 3), (3, 1)])));
        assert!(!cyclic(&rel::<i32>(&[])));
    }

    #[test]
    fn toposort_acyclic_is_valid() {
        let r = rel(&[(1, 2), (1, 3), (3, 4), (2, 4)]);
        let order = toposort(&r);
        for (a, b) in &r {
            let pa = order.iter().position(|x| x == a).unwrap();
            let pb = order.iter().position(|x| x == b).unwrap();
            assert!(pa < pb, "{} should come before {} in {:?}", a, b, order);
        }
    }

    #[test]
    fn loop_breakers_break_cycles() {
        let r = rel(&[(1, 2), (2, 3), (3, 1), (3, 4)]);
        let breakers = dfs_loop_breakers(&r);
        assert!(!breakers.is_empty());
        let kept: Relation<i32> = restrict(&r, |x| !breakers.contains(x));
        assert!(!cyclic(&kept));
    }

    #[test]
    fn loop_breakers_empty_for_acyclic() {
        let r = rel(&[(1, 2), (2, 3)]);
        assert_eq!(dfs_loop_breakers(&r), Vec::<i32>::new());
    }

    #[test]
    fn loop_breakers_simple_cycle_breaks_one() {
        // 1 -> 2 -> 1: breaking either makes it acyclic.
        let breakers = dfs_loop_breakers(&rel(&[(1, 2), (2, 1)]));
        assert_eq!(breakers.len(), 1);
        assert!(breakers[0] == 1 || breakers[0] == 2);
    }

    #[test]
    fn loop_breakers_three_cycle_breaks_one() {
        // 1 -> 2 -> 3 -> 1.
        assert_eq!(dfs_loop_breakers(&rel(&[(1, 2), (2, 3), (3, 1)])).len(), 1);
    }

    #[test]
    fn loop_breakers_two_independent_cycles_break_both() {
        let breakers = dfs_loop_breakers(&rel(&[(1, 2), (2, 1), (3, 4), (4, 3)]));
        assert_eq!(breakers.len(), 2);
    }

    #[test]
    fn trans_red_removes_redundant_edges() {
        // 1 -> 2 -> 3, plus shortcut 1 -> 3
        let r = rel(&[(1, 2), (2, 3), (1, 3)]);
        let red = trans_red(&r);
        let red_set: BTreeSet<(i32, i32)> = red.iter().cloned().collect();
        // The reduction must drop (1,3) and keep (1,2),(2,3).
        assert!(red_set.contains(&(1, 2)));
        assert!(red_set.contains(&(2, 3)));
        assert!(!red_set.contains(&(1, 3)));
    }
}
