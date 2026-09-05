// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Data.DAG.Simple` from `lib/utils/src/Data/DAG/Simple.hs`.
//!
//! Vertex-list-based DAG operations. A `Relation<T>` is `Vec<(T, T)>`.
//!
//! `dfs_loop_breakers` is the live loop-breaker selector used by the
//! constraint-solver context (`useAutoLoopBreakersAC`). `cyclic` and
//! `trans_red` back the display-graph compression pass
//! (`tamarin-theory`'s
//! `constraint::system::graph::simplify::transitive_reduction`); `trans_red`
//! in turn drives `toposort` (and thus `inverse`) and `reachable_set`.
//! The remaining operations cover the subset of `Data.DAG.Simple` used by
//! the port.

use std::collections::{BTreeMap, BTreeSet};

pub type Relation<T> = Vec<(T, T)>;

/// `inverse rel`: every edge reversed.
pub fn inverse<T: Clone>(rel: &Relation<T>) -> Relation<T> {
    rel.iter().map(|(a, b)| (b.clone(), a.clone())).collect()
}

/// `reachableSet start rel`: every node reachable from any element of `start`.
pub fn reachable_set<T: Ord + Clone>(start: &[T], rel: &Relation<T>) -> BTreeSet<T> {
    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut stack: Vec<T> = start.to_vec();
    loop {
        let Some(x) = stack.pop() else { break };
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
    let mut adj: BTreeMap<T, Vec<T>> = BTreeMap::new();
    for (a, b) in rel {
        adj.entry(a.clone()).or_default().push(b.clone());
    }

    fn visit<T: Ord + Clone>(
        node: &T,
        adj: &BTreeMap<T, Vec<T>>,
        color: &mut BTreeMap<T, u8>,
    ) -> bool {
        match color.get(node).copied().unwrap_or(0) {
            1 => return true,
            2 => return false,
            _ => {}
        }
        color.insert(node.clone(), 1);
        if let Some(succs) = adj.get(node) {
            for succ in succs {
                if visit(succ, adj, color) {
                    return true;
                }
            }
        }
        color.insert(node.clone(), 2);
        false
    }

    let mut color = BTreeMap::new();
    for node in adj.keys() {
        if color.get(node).copied().unwrap_or(0) == 0 && visit(node, &adj, &mut color) {
            return true;
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
    for (a, _) in rel {
        order_input.push(a.clone());
    }
    for (_, b) in rel {
        order_input.push(b.clone());
    }

    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut out: Vec<T> = Vec::new();

    fn visit<T: Ord + Clone>(
        rel: &Relation<T>,
        inv: &Relation<T>,
        visited: &mut BTreeSet<T>,
        out: &mut Vec<T>,
        x: T,
    ) {
        if visited.contains(&x) {
            return;
        }
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
        let hits_parent = rel.iter().any(|(a, b)| a == &x && parents.contains(b));
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
    if n < 2 {
        return Vec::new();
    }

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
        if !dag_set.contains(&edge) {
            continue;
        }
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

    fn rel<T: Clone>(es: &[(T, T)]) -> Relation<T> {
        es.to_vec()
    }

    #[test]
    fn inverse_keeps_relation_order() {
        let r = rel(&[(1, 3), (1, 2), (2, 3)]);
        assert_eq!(inverse(&r), vec![(3, 1), (2, 1), (3, 2)]);
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
        // `trans_red` enumerates index pairs over this order.  The exact
        // permutation therefore reaches the reduced edge list, and not only
        // the fact that the order is valid.  HS visits
        // `map fst dag ++ map snd dag` and emits each vertex after its
        // predecessors.  That puts 3 before 2.  The sorted order differs, and
        // the validity check above would accept it just as well.
        assert_eq!(order, vec![1, 3, 2, 4]);
    }

    #[test]
    fn loop_breakers_break_cycles() {
        // The graph holds two cycles, 1->2->3->1 and 2->3->4->2, that share
        // the 2->3 edge.  The single breaker picked at the first back edge
        // therefore cuts both cycles.
        let r = rel(&[(1, 2), (2, 3), (3, 1), (3, 4), (4, 2)]);
        let breakers = dfs_loop_breakers(&r);
        assert!(!breakers.is_empty());
        let kept: Relation<i32> = r
            .iter()
            .filter(|(x, y)| !breakers.contains(x) && !breakers.contains(y))
            .cloned()
            .collect();
        assert!(!cyclic(&kept));
    }

    #[test]
    fn dfs_loop_breakers_pins_hs_selection_and_order() {
        // The picked set reaches the printed output.  The vertices that come
        // back, and their order, are therefore part of the port's contract.
        // They are not an incidental choice.  HS emits the source of the back
        // edge, stops the descent at that vertex, and shares one `visited` set
        // across all roots.  That set only grows.
        let cases: Vec<(&str, Relation<i32>, Vec<i32>)> = vec![
            ("acyclic", rel(&[(1, 2), (2, 3)]), vec![]),
            (
                "2-cycle: the back-edge source is 2",
                rel(&[(1, 2), (2, 1)]),
                vec![2],
            ),
            (
                "3-cycle: the back-edge source is 3",
                rel(&[(1, 2), (2, 3), (3, 1)]),
                vec![3],
            ),
            (
                // The DFS never visits 4.  The back edge at 3 stops the
                // descent before the DFS explores the other successors of 3.
                "back edge suppresses the sibling successor",
                rel(&[(1, 2), (2, 3), (3, 1), (3, 4)]),
                vec![3],
            ),
            (
                "two independent cycles, one breaker each",
                rel(&[(1, 2), (2, 1), (3, 4), (4, 3)]),
                vec![2, 4],
            ),
            (
                // Both successors of 1 close a cycle back onto 1.  The
                // emission order is therefore the order in which the
                // successors appear in `rel`.  A reversed successor scan
                // flips this row.
                "sibling successors are descended in relation order",
                rel(&[(1, 2), (1, 3), (2, 1), (3, 1)]),
                vec![2, 3],
            ),
            (
                // The root 3 re-enters the cycle {1,2}, which is already
                // broken.  The shared `visited` set stops the descent, so the
                // function emits no second breaker.
                "later root re-entering a visited cycle",
                rel(&[(1, 2), (2, 1), (3, 2)]),
                vec![2],
            ),
        ];
        for (label, r, want) in cases {
            assert_eq!(dfs_loop_breakers(&r), want, "{}", label);
        }
    }

    #[test]
    fn trans_red_removes_redundant_edges() {
        // 1 -> 2 -> 3, plus shortcut 1 -> 3
        let r = rel(&[(1, 2), (2, 3), (1, 3)]);
        // `trans_red` drops the shortcut (1,3), because 3 is already
        // reachable.  The kept edges come back in HS's order.  `foldl' visit
        // []` prepends each kept edge.  The processing order takes the longest
        // gap first, and the output reverses that order.
        assert_eq!(trans_red(&r), vec![(2, 3), (1, 2)]);
    }
}
