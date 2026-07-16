//! Port of `Extension.Prelude` (and `Extension.Data.Monoid::MinMax`) from
//! `lib/utils/src/Extension/Prelude.hs` and `Extension/Data/Monoid.hs`.
//!
//! Small list / pair / string helpers.
//!
//! Intentionally retained: faithful `Extension.Prelude` mirror. Only `nub_on`
//! and `flush_right` have a live caller; the remaining helpers and the `MinMax`
//! type are kept for completeness of the port.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::hash::Hash;

// -- Bool ---------------------------------------------------------------------

/// `implies p q`: classical material implication.
pub fn implies(p: bool, q: bool) -> bool { !p || q }

// -- List helpers -------------------------------------------------------------

pub fn singleton<T>(x: T) -> Vec<T> { vec![x] }

/// `unique xs`: whether `xs` has no repeated element. O(n^2); prefer
/// [`crate::misc::no_duplicates`] for `Ord` types.
pub fn unique<T: PartialEq>(xs: &[T]) -> bool {
    for i in 0..xs.len() {
        for j in (i + 1)..xs.len() {
            if xs[i] == xs[j] {
                return false;
            }
        }
    }
    true
}

/// `sortednub xs`: sort and dedupe.
pub fn sortednub<T: Ord + Clone>(xs: &[T]) -> Vec<T> {
    let mut v = xs.to_vec();
    v.sort();
    v.dedup();
    v
}

/// `sortednubOn proj xs`: sort by `proj` and drop later duplicates with the
/// same projection.
pub fn sortednub_on<T, K, F>(mut xs: Vec<T>, mut proj: F) -> Vec<T>
where
    K: Ord,
    F: FnMut(&T) -> K,
{
    xs.sort_by_key(|a| proj(a));
    xs.dedup_by(|a, b| proj(a) == proj(b));
    xs
}

/// `nubOn proj xs`: keep the first occurrence of each projection value.
/// Order-preserving. O(n) via a `HashSet` of seen projections, hence the
/// `K: Eq + Hash` bound.
pub fn nub_on<T: Clone, K: Eq + Hash, F: FnMut(&T) -> K>(xs: &[T], mut proj: F) -> Vec<T> {
    let mut seen: crate::FastSet<K> = crate::FastSet::default();
    let mut out = Vec::with_capacity(xs.len());
    for x in xs {
        if seen.insert(proj(x)) {
            out.push(x.clone());
        }
    }
    out
}

/// `groupOn proj xs`: like `Data.List.groupBy ((==) `on` proj)`. Groups
/// *consecutive* equal-projection elements; does not sort.
pub fn group_on<T: Clone, K: Eq, F: FnMut(&T) -> K>(xs: &[T], mut proj: F) -> Vec<Vec<T>> {
    let mut out: Vec<Vec<T>> = Vec::new();
    let mut iter = xs.iter().cloned();
    let Some(first) = iter.next() else { return out; };
    let mut cur_key = proj(&first);
    let mut cur_grp = vec![first];
    for x in iter {
        let k = proj(&x);
        if k == cur_key {
            cur_grp.push(x);
        } else {
            out.push(std::mem::take(&mut cur_grp));
            cur_grp.push(x);
            cur_key = k;
        }
    }
    if !cur_grp.is_empty() {
        out.push(cur_grp);
    }
    out
}

/// `collectBy pairs`: gather all values per key, preserving the order in
/// which keys first appear.
pub fn collect_by<K: Eq + Hash + Clone, V>(pairs: Vec<(K, V)>) -> Vec<(K, Vec<V>)> {
    let mut indices: crate::FastMap<K, usize> = crate::FastMap::default();
    let mut out: Vec<(K, Vec<V>)> = Vec::new();
    for (k, v) in pairs {
        match indices.get(&k) {
            Some(&i) => out[i].1.push(v),
            None => {
                indices.insert(k.clone(), out.len());
                out.push((k, vec![v]));
            }
        }
    }
    out
}

/// `sortOn proj xs`: stable sort by projection.
pub fn sort_on<T, K, F>(mut xs: Vec<T>, mut proj: F) -> Vec<T>
where
    K: Ord,
    F: FnMut(&T) -> K,
{
    xs.sort_by_key(|a| proj(a));
    xs
}

/// `groupSortOn proj xs`: sort by projection, then group consecutive equal-
/// projection elements.
pub fn group_sort_on<T: Clone, K: Ord + Clone, F: FnMut(&T) -> K>(
    xs: Vec<T>,
    mut proj: F,
) -> Vec<Vec<T>> {
    let sorted = sort_on(xs, &mut proj);
    group_on(&sorted, &mut proj)
}

/// `eqClasses proj xs`: group elements by their projection's equivalence
/// class. Output uses sorted-then-grouped semantics, matching Haskell.
pub fn eq_classes<T: Clone, K: Ord + Clone, F: FnMut(&T) -> K>(
    xs: Vec<T>,
    proj: F,
) -> Vec<Vec<T>> {
    group_sort_on(xs, proj)
}

/// `splitBy p xs`: split on every element satisfying `p`. Separators are
/// dropped; a trailing separator does *not* produce a final empty chunk.
pub fn split_by<T: Clone, F: FnMut(&T) -> bool>(xs: &[T], mut p: F) -> Vec<Vec<T>> {
    if xs.is_empty() { return vec![]; }
    let mut out: Vec<Vec<T>> = Vec::new();
    let mut cur: Vec<T> = Vec::new();
    let mut had_separator = false;
    for x in xs {
        if p(x) {
            out.push(std::mem::take(&mut cur));
            had_separator = true;
        } else {
            cur.push(x.clone());
            had_separator = false;
        }
    }
    // Matches Haskell `unfoldr split`: a chunk is emitted before every
    // separator and once more for the final (non-separator-terminated)
    // remainder. The final partial chunk `cur` is emitted unless the input
    // ended on a separator AND `cur` is empty, i.e. `!had_separator ||
    // !cur.is_empty()`.
    if !had_separator || !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// `choose n xs`: every n-element ordered subsequence.
pub fn choose<T: Clone>(n: usize, xs: &[T]) -> Vec<Vec<T>> {
    if n == 0 { return vec![vec![]]; }
    if xs.is_empty() { return vec![]; }
    let head = xs[0].clone();
    let tail = &xs[1..];
    let mut with_head: Vec<Vec<T>> = choose(n - 1, tail)
        .into_iter()
        .map(|mut v| { v.insert(0, head.clone()); v })
        .collect();
    let without_head = choose(n, tail);
    with_head.extend(without_head);
    with_head
}

/// `leaveOneOut xs`: each list with one element omitted (preserving order).
pub fn leave_one_out<T: Clone>(xs: &[T]) -> Vec<Vec<T>> {
    (0..xs.len())
        .map(|i| {
            let mut v = Vec::with_capacity(xs.len() - 1);
            v.extend_from_slice(&xs[..i]);
            v.extend_from_slice(&xs[i + 1..]);
            v
        })
        .collect()
}

/// `keepFirst mask xs`: greedy left-to-right filter. After picking each
/// element, drop all later elements that the predicate `mask(picked, .)`
/// flags as masked.
pub fn keep_first<T: Clone, F: FnMut(&T, &T) -> bool>(xs: &[T], mut mask: F) -> Vec<T> {
    let mut out: Vec<T> = Vec::new();
    // `alive[i]` tracks whether element `i` survives the masking by earlier
    // picks. Iterating with a cursor avoids the O(n) front-shift of
    // `Vec::remove(0)` while preserving Haskell's left-to-right semantics:
    // `keepFirst mask (x:xs) = x : keepFirst mask (filter (not . mask x) xs)`.
    let mut alive: Vec<bool> = vec![true; xs.len()];
    for i in 0..xs.len() {
        if !alive[i] {
            continue;
        }
        out.push(xs[i].clone());
        for j in (i + 1)..xs.len() {
            if alive[j] && mask(&xs[i], &xs[j]) {
                alive[j] = false;
            }
        }
    }
    out
}

// -- Pairs --------------------------------------------------------------------

pub fn swap<A, B>(p: (A, B)) -> (B, A) { (p.1, p.0) }

pub fn sort_pair<T: Ord>(p: (T, T)) -> (T, T) {
    if p.0 <= p.1 { p } else { swap(p) }
}

// -- Result (≈ Either) -------------------------------------------------------

pub fn is_ok<A, B>(r: &Result<A, B>) -> bool { r.is_ok() }
pub fn is_err<A, B>(r: &Result<A, B>) -> bool { r.is_err() }

// -- Strings ------------------------------------------------------------------

/// `flushRightBy sep n s`: pad `s` on the left with cycles of `sep` so the
/// result is at least `n` *characters* (Unicode scalars) wide.
pub fn flush_right_by(sep: &str, n: usize, s: &str) -> String {
    flush_by(sep, n, s, /*right*/ true)
}

pub fn flush_right(n: usize, s: &str) -> String { flush_right_by(" ", n, s) }

pub fn flush_left_by(sep: &str, n: usize, s: &str) -> String {
    flush_by(sep, n, s, /*right*/ false)
}

pub fn flush_left(n: usize, s: &str) -> String { flush_left_by(" ", n, s) }

fn flush_by(sep: &str, n: usize, s: &str, right: bool) -> String {
    let s_len = s.chars().count();
    if s_len >= n || sep.is_empty() {
        return s.to_string();
    }
    let needed = n - s_len;
    // Build the result in a single buffer: padding (cycled from `sep`) on the
    // correct side of `s`, avoiding a second `format!` allocation.
    let mut out = String::with_capacity(sep.len() * needed + s.len());
    if !right { out.push_str(s); }
    for c in sep.chars().cycle().take(needed) { out.push(c); }
    if right { out.push_str(s); }
    out
}

/// Mark a string as a warning. Mirrors `warning` in Haskell.
pub fn warning(s: &str) -> String {
    format!("warning: {}", s)
}

// -- MinMax monoid (from Extension.Data.Monoid) -------------------------------

/// `MinMax`: combines values via `min`/`max`. Identity is `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinMax<T>(pub Option<(T, T)>);

impl<T> MinMax<T> {
    pub fn empty() -> Self { MinMax(None) }
    pub fn singleton(x: T) -> Self where T: Clone { MinMax(Some((x.clone(), x))) }
    pub fn into_inner(self) -> Option<(T, T)> { self.0 }
}

impl<T: Ord + Clone> MinMax<T> {
    pub fn combine(self, other: Self) -> Self {
        match (self.0, other.0) {
            (None, y) => MinMax(y),
            (x, None) => MinMax(x),
            (Some((xmin, xmax)), Some((ymin, ymax))) => {
                MinMax(Some((std::cmp::min(xmin, ymin), std::cmp::max(xmax, ymax))))
            }
        }
    }
}

// -- Equiv classes by an Ord projection (sorted-then-grouped) ----------------

/// Group `xs` into equivalence classes by `proj`, returning a deterministic
/// `BTreeMap` keyed by the projection.
pub fn classes_by<T, K, F>(xs: Vec<T>, mut proj: F) -> BTreeMap<K, Vec<T>>
where
    K: Ord,
    F: FnMut(&T) -> K,
{
    let mut m: BTreeMap<K, Vec<T>> = BTreeMap::new();
    for x in xs {
        let k = proj(&x);
        m.entry(k).or_default().push(x);
    }
    m
}

/// Generic comparison via projection. Useful when callers need `Ordering`.
pub fn comparing<T, K, F>(mut proj: F) -> impl FnMut(&T, &T) -> Ordering
where
    K: Ord,
    F: FnMut(&T) -> K,
{
    move |a, b| proj(a).cmp(&proj(b))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implies_truth_table() {
        assert!(implies(false, false));
        assert!(implies(false, true));
        assert!(!implies(true, false));
        assert!(implies(true, true));
    }

    #[test]
    fn unique_basic() {
        assert!(unique::<i32>(&[]));
        assert!(unique(&[1, 2, 3]));
        assert!(!unique(&[1, 2, 1]));
    }

    #[test]
    fn sortednub_basic() {
        assert_eq!(sortednub(&[3, 1, 2, 3, 1, 4]), vec![1, 2, 3, 4]);
        assert_eq!(sortednub::<i32>(&[]), Vec::<i32>::new());
    }

    #[test]
    fn nub_on_preserves_first_occurrence() {
        let xs = vec!["aa", "bb", "ab", "bc", "ac"];
        let got = nub_on(&xs, |s| s.chars().next().unwrap());
        assert_eq!(got, vec!["aa", "bb"]);
    }

    #[test]
    fn group_on_consecutive_only() {
        let xs = vec![1, 1, 2, 2, 1, 3, 3];
        let g = group_on(&xs, |x| *x);
        assert_eq!(g, vec![vec![1, 1], vec![2, 2], vec![1], vec![3, 3]]);
    }

    #[test]
    fn collect_by_groups_preserve_key_order() {
        let pairs = vec![("a", 1), ("b", 2), ("a", 3), ("c", 4), ("b", 5)];
        let g = collect_by(pairs);
        assert_eq!(
            g,
            vec![("a", vec![1, 3]), ("b", vec![2, 5]), ("c", vec![4])]
        );
    }

    #[test]
    fn split_by_basic() {
        let xs = vec![1, 0, 2, 3, 0, 4];
        assert_eq!(split_by(&xs, |x| *x == 0), vec![vec![1], vec![2, 3], vec![4]]);
        let trail = vec![1, 2, 0];
        // Haskell: trailing separator yields a single chunk [1,2] and no trailing empty.
        assert_eq!(split_by(&trail, |x| *x == 0), vec![vec![1, 2]]);
        // Adjacent and leading separators lock the Haskell `unfoldr split` semantics:
        // a chunk (possibly empty) is emitted before every separator.
        let empty_i32: Vec<i32> = vec![];
        assert_eq!(split_by(&[0, 0], |x| *x == 0), vec![empty_i32.clone(), empty_i32.clone()]);
        assert_eq!(split_by(&[0], |x| *x == 0), vec![empty_i32.clone()]);
        assert_eq!(split_by(&[1, 0, 0, 2], |x| *x == 0), vec![vec![1], empty_i32.clone(), vec![2]]);
        assert_eq!(split_by(&[0, 1, 2], |x| *x == 0), vec![empty_i32.clone(), vec![1, 2]]);
    }

    #[test]
    fn choose_basic() {
        assert_eq!(choose(2, &[1, 2, 3]), vec![vec![1, 2], vec![1, 3], vec![2, 3]]);
        assert_eq!(choose(0, &[1, 2, 3]), vec![Vec::<i32>::new()]);
        let empty: Vec<Vec<i32>> = choose(2, &[]);
        assert_eq!(empty, Vec::<Vec<i32>>::new());
    }

    #[test]
    fn leave_one_out_basic() {
        assert_eq!(
            leave_one_out(&[1, 2, 3]),
            vec![vec![2, 3], vec![1, 3], vec![1, 2]]
        );
    }

    #[test]
    fn keep_first_dedup_via_mask() {
        // mask: same value masks duplicates
        let xs = vec![1, 2, 1, 3, 2, 4];
        assert_eq!(keep_first(&xs, |a, b| a == b), vec![1, 2, 3, 4]);
    }

    #[test]
    fn pairs() {
        assert_eq!(swap((1, 'a')), ('a', 1));
        assert_eq!(sort_pair((3, 1)), (1, 3));
        assert_eq!(sort_pair((1, 3)), (1, 3));
    }

    #[test]
    fn flush_helpers() {
        assert_eq!(flush_right(5, "ab"), "   ab");
        assert_eq!(flush_left(5, "ab"), "ab   ");
        assert_eq!(flush_right_by("0", 4, "12"), "0012");
        assert_eq!(flush_right(2, "abcd"), "abcd"); // no truncation
    }

    #[test]
    fn warning_prefix() {
        assert_eq!(warning("oops"), "warning: oops");
    }

    #[test]
    fn min_max_combines() {
        let a = MinMax::singleton(3);
        let b = MinMax::singleton(7);
        let c = MinMax::singleton(1);
        let combined = a.combine(b).combine(c);
        assert_eq!(combined.into_inner(), Some((1, 7)));
        assert_eq!(MinMax::<i32>::empty().combine(MinMax::singleton(5)).into_inner(), Some((5, 5)));
    }

    #[test]
    fn classes_by_groups() {
        let m = classes_by(vec![1, 2, 3, 4, 5, 6], |x| x % 3);
        assert_eq!(m[&0], vec![3, 6]);
        assert_eq!(m[&1], vec![1, 4]);
        assert_eq!(m[&2], vec![2, 5]);
    }
}
