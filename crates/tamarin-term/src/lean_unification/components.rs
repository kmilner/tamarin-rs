//! Rows of a directional match that share no pattern variable are independent:
//! each group can be decided on its own.
use crate::lterm::{HasFrees, LNTerm};
use crate::rewriting::Equal;
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;

fn root(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

/// Group the rows by the variables of their patterns (left sides). Empty
/// when all rows form one group.
pub(super) fn pattern_components(equations: &[Equal<LNTerm>]) -> Vec<Vec<Equal<LNTerm>>> {
    let mut parent: Vec<_> = (0..equations.len()).collect();
    let mut owners = FxHashMap::default();
    for (i, eq) in equations.iter().enumerate() {
        eq.lhs.for_each_free(&mut |v| {
            let previous = *owners.entry(*v).or_insert(i);
            let a = root(&mut parent, previous);
            let b = root(&mut parent, i);
            parent[a.max(b)] = a.min(b);
        });
    }
    if (1..equations.len()).all(|i| root(&mut parent, i) == 0) {
        return Vec::new();
    }
    let mut parts = BTreeMap::<usize, Vec<Equal<LNTerm>>>::new();
    for (i, eq) in equations.iter().enumerate() {
        parts
            .entry(root(&mut parent, i))
            .or_default()
            .push(eq.clone());
    }
    parts.into_values().collect()
}
