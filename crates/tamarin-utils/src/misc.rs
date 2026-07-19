// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, beschmi, sans-sucre, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Utils/Misc.hs

//! Port of `Utils.Misc` from `lib/utils/src/Utils/Misc.hs`.
//!
//! Pure helpers named after their Haskell originals where reasonable;
//! signatures adapted to idiomatic Rust.
//!
//! Intentionally retained: faithful `Utils.Misc` mirror. Only `two_partitions`
//! has a live caller; the rest are kept for completeness of the port.

// generic map-utility import; invert_map returns a new map, never rendered;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::hash::Hash;

use base64::Engine as _;
use base64::engine::general_purpose::STANDARD as B64;
use sha2::{Digest, Sha256};

// -- Environment --------------------------------------------------------------

/// `getEnvMaybe k`: value of `k` if present.
pub fn get_env_maybe(key: &str) -> Option<String> {
    env::var(key).ok()
}

/// `envIsSet k`: whether `k` is present in the environment.
pub fn env_is_set(key: &str) -> bool {
    env::var_os(key).is_some()
}

// -- Triples ------------------------------------------------------------------

pub fn fst3<A, B, C>(t: (A, B, C)) -> A { t.0 }
pub fn snd3<A, B, C>(t: (A, B, C)) -> B { t.1 }
pub fn thd3<A, B, C>(t: (A, B, C)) -> C { t.2 }

pub fn duplicate<A: Clone>(x: A) -> (A, A) {
    (x.clone(), x)
}

// -- List / set predicates ----------------------------------------------------

/// `subsetOf xs ys`: whether every element of `xs` appears in `ys`.
pub fn subset_of<T: Ord + Clone>(xs: &[T], ys: &[T]) -> bool {
    if xs.is_empty() { return true; }
    let ys_set: BTreeSet<&T> = ys.iter().collect();
    xs.iter().all(|x| ys_set.contains(x))
}

/// `noDuplicates xs`: whether `xs` has no repeated elements.
pub fn no_duplicates<T: Ord>(xs: &[T]) -> bool {
    let mut seen = BTreeSet::new();
    for x in xs {
        if !seen.insert(x) {
            return false;
        }
    }
    true
}

// -- Equivalence classes ------------------------------------------------------

/// `equivClasses pairs`: group the first components by their second component.
///
/// Uses `BTreeMap` so iteration order is deterministic, matching the
/// `Data.Map` flavour in the Haskell original.
pub fn equiv_classes<A, B>(pairs: impl IntoIterator<Item = (A, B)>) -> BTreeMap<B, BTreeSet<A>>
where
    A: Ord,
    B: Ord,
{
    let mut m: BTreeMap<B, BTreeSet<A>> = BTreeMap::new();
    for (from, to) in pairs {
        m.entry(to).or_default().insert(from);
    }
    m
}

// -- Map helpers --------------------------------------------------------------

/// `invertMap`: swap keys and values of a bijective map.
// generic map inverter; returns a map by key, never iterated into output;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub fn invert_map<K, V>(m: HashMap<K, V>) -> HashMap<V, K>
where
    V: Eq + Hash,
{
    m.into_iter().map(|(k, v)| (v, k)).collect()
}

// -- Multiplication -----------------------------------------------------------

/// `multiply f (a, c)`: cross `f(a)` with the constant `c`.
pub fn multiply<A, B, C, I>(f: impl FnOnce(A) -> I, pair: (A, C)) -> Vec<(B, C)>
where
    I: IntoIterator<Item = B>,
    C: Clone,
{
    let (a, c) = pair;
    f(a).into_iter().map(|b| (b, c.clone())).collect()
}

// -- Hashing ------------------------------------------------------------------

/// `stringSHA256`: URL-safe base64 of the SHA-256 of `s`'s UTF-8 bytes,
/// with `=` padding stripped (matching the Haskell `C8.init` after base64).
pub fn string_sha256(s: &str) -> String {
    let digest = Sha256::digest(s.as_bytes());
    let mut out = B64.encode(digest);
    // Haskell does `C8.init` (drop the final byte *unconditionally*) and then
    // replaces `/`→`_`, `+`→`-`. The SHA-256 digest is always 32 bytes, so its
    // standard base64 is always 44 chars ending in exactly one `=` (32 mod 3 ==
    // 2 → one pad char). `out.pop()` removes the final *char* (Unicode scalar);
    // since base64 output is ASCII, that final char is exactly one byte (`=`),
    // so this matches Haskell's byte-based `C8.init`.
    out.pop();
    // In-place ASCII byte substitution: `/`→`_`, `+`→`-`. Both are
    // single-ASCII-for-single-ASCII and length-preserving, so UTF-8 validity is
    // preserved and the resulting String is identical to the round-trip form.
    // SAFETY: the base64 alphabet is pure ASCII and we only swap one ASCII byte
    // for another, keeping the buffer valid UTF-8.
    for b in unsafe { out.as_mut_vec() } {
        match *b {
            b'/' => *b = b'_',
            b'+' => *b = b'-',
            _ => {}
        }
    }
    out
}

// -- Partitions ---------------------------------------------------------------

/// `partitions xs`: every way to split `xs` into non-empty groups.
pub fn partitions<T: Clone>(xs: &[T]) -> Vec<Vec<Vec<T>>> {
    if xs.is_empty() {
        return vec![vec![]];
    }
    let head = xs[0].clone();
    let tail_parts = partitions(&xs[1..]);
    let mut out = Vec::new();
    for yss in tail_parts {
        out.extend(bloat(head.clone(), yss));
    }
    out
}

fn bloat<T: Clone>(x: T, yss: Vec<Vec<T>>) -> Vec<Vec<Vec<T>>> {
    if yss.is_empty() {
        return vec![vec![vec![x]]];
    }
    // (x:xs):xss
    let mut prepended = Vec::with_capacity(yss.len());
    {
        let mut first = Vec::with_capacity(yss[0].len() + 1);
        first.push(x.clone());
        first.extend(yss[0].iter().cloned());
        prepended.push(first);
        for grp in &yss[1..] {
            prepended.push(grp.clone());
        }
    }
    let mut out = vec![prepended];
    // map (xs:) (bloat x xss)
    let head = yss[0].clone();
    let rest = yss[1..].to_vec();
    for sub in bloat(x, rest) {
        let mut row = Vec::with_capacity(sub.len() + 1);
        row.push(head.clone());
        row.extend(sub);
        out.push(row);
    }
    out
}

/// `nonTrivialPartitions xs`: all partitions of `xs` except `[xs]` itself.
pub fn non_trivial_partitions<T: Clone + Eq>(xs: &[T]) -> Vec<Vec<Vec<T>>> {
    let trivial: Vec<Vec<T>> = vec![xs.to_vec()];
    partitions(xs).into_iter().filter(|p| p != &trivial).collect()
}

/// `twoPartitions xs`: every way to split `xs` into an ordered pair of lists,
/// preserving original order within each side. Mirrors Haskell `twoPartitions`,
/// whose base case `twoPartitions [x] = [([x],[])]` forces the last element
/// into the first list. Consequently the first list is never empty (so
/// `([], [1,2,3])` is never produced) and there are `2^(n-1)` results, not all
/// `2^n` ordered pairs.
pub fn two_partitions<T: Clone>(xs: &[T]) -> Vec<(Vec<T>, Vec<T>)> {
    match xs.len() {
        0 => vec![],
        1 => vec![(vec![xs[0].clone()], vec![])],
        _ => {
            let head = xs[0].clone();
            let rest = two_partitions(&xs[1..]);
            let mut out = Vec::with_capacity(rest.len() * 2);
            for (a, b) in &rest {
                let mut a2 = Vec::with_capacity(a.len() + 1);
                a2.push(head.clone());
                a2.extend(a.iter().cloned());
                out.push((a2, b.clone()));
            }
            for (a, b) in rest {
                let mut b2 = Vec::with_capacity(b.len() + 1);
                b2.push(head.clone());
                b2.extend(b);
                out.push((a, b2));
            }
            out
        }
    }
}

// -- Edit distance ------------------------------------------------------------

/// Levenshtein distance between two strings, counting Unicode scalars.
/// Mirrors the Haskell version which indexes by `length`.
pub fn edit_distance(s: &str, t: &str) -> usize {
    let s: Vec<char> = s.chars().collect();
    let t: Vec<char> = t.chars().collect();
    let n = s.len();
    let m = t.len();
    if n == 0 { return m; }
    if m == 0 { return n; }

    let mut prev: Vec<usize> = (0..=m).collect();
    let mut cur = vec![0usize; m + 1];
    for i in 1..=n {
        cur[0] = i;
        for j in 1..=m {
            let cost = if s[i - 1] == t[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1)
                .min(cur[j - 1] + 1)
                .min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[m]
}

// -- Iterate-while ------------------------------------------------------------

/// `whileTrue m`: run `m` until it returns `false`; return iteration count.
pub fn while_true<F: FnMut() -> bool>(mut m: F) -> usize {
    let mut n = 0;
    while m() {
        n += 1;
    }
    n
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn triples() {
        assert_eq!(fst3((1, 2, 3)), 1);
        assert_eq!(snd3((1, 2, 3)), 2);
        assert_eq!(thd3((1, 2, 3)), 3);
        assert_eq!(duplicate("x"), ("x", "x"));
    }

    #[test]
    fn subset_basic() {
        assert!(subset_of::<i32>(&[], &[1, 2]));
        assert!(subset_of(&[1, 2], &[2, 1, 3]));
        assert!(!subset_of(&[1, 4], &[2, 1, 3]));
        // duplicates in xs should not matter
        assert!(subset_of(&[1, 1, 2], &[1, 2]));
    }

    #[test]
    fn no_duplicates_basic() {
        assert!(no_duplicates::<i32>(&[]));
        assert!(no_duplicates(&[1, 2, 3]));
        assert!(!no_duplicates(&[1, 2, 1]));
    }

    #[test]
    fn equiv_classes_basic() {
        let pairs = vec![(1, 'a'), (2, 'a'), (3, 'b'), (4, 'a'), (5, 'b')];
        let m = equiv_classes(pairs);
        assert_eq!(m[&'a'], BTreeSet::from([1, 2, 4]));
        assert_eq!(m[&'b'], BTreeSet::from([3, 5]));
    }

    #[test]
    // unit test over a deterministic literal map;
    // std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    fn invert_map_bijective() {
        let m: HashMap<i32, &str> =
            HashMap::from([(1, "a"), (2, "b"), (3, "c")]);
        let inv = invert_map(m);
        assert_eq!(inv[&"a"], 1);
        assert_eq!(inv[&"b"], 2);
        assert_eq!(inv[&"c"], 3);
    }

    #[test]
    fn multiply_basic() {
        let pair = (3i32, "k");
        let got = multiply(|n| 0..n, pair);
        assert_eq!(got, vec![(0, "k"), (1, "k"), (2, "k")]);
    }

    #[test]
    fn sha256_known_values() {
        // Empty string SHA-256 = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
        // Standard base64: 47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU=
        // After Haskell's URL-replace + drop final '=':
        //   '/' -> '_', '+' -> '-', then drop trailing '='
        assert_eq!(
            string_sha256(""),
            "47DEQpj8HBSa-_TImW-5JCeuQeRkm5NMpJWZG3hSuFU"
        );
        // "abc" SHA-256 base64: ungWv48Bz+pBQUDeXa4iI7ADYaOWF3qctBD/YfIAFa0=
        // No '/' or '+' here, so URL-safe form is the same up to the '='.
        assert_eq!(
            string_sha256("abc"),
            "ungWv48Bz-pBQUDeXa4iI7ADYaOWF3qctBD_YfIAFa0"
        );
    }

    #[test]
    fn partitions_small() {
        let p0: Vec<Vec<Vec<i32>>> = partitions::<i32>(&[]);
        assert_eq!(p0, vec![vec![] as Vec<Vec<i32>>]);

        let p1 = partitions(&[1]);
        assert_eq!(p1, vec![vec![vec![1]]]);

        // {1,2}: { {{1,2}}, {{1},{2}} }  — the Haskell order is
        // ((x:xs):xss) first, then bloat-recurse.
        let p2 = partitions(&[1, 2]);
        // Two partitions of a 2-element set.
        assert_eq!(p2.len(), 2);
        // Bell numbers: 1, 1, 2, 5, 15, ...
        assert_eq!(partitions(&[1, 2, 3]).len(), 5);
        assert_eq!(partitions(&[1, 2, 3, 4]).len(), 15);
    }

    #[test]
    fn partitions_each_partition_covers_input() {
        let xs = vec![1, 2, 3, 4];
        for parts in partitions(&xs) {
            let mut flat: Vec<i32> = parts.into_iter().flatten().collect();
            flat.sort();
            assert_eq!(flat, xs);
        }
    }

    #[test]
    fn non_trivial_excludes_singleton_grouping() {
        let xs = vec![1, 2, 3];
        let all = partitions(&xs);
        let nt = non_trivial_partitions(&xs);
        assert_eq!(all.len(), nt.len() + 1);
        assert!(!nt.contains(&vec![xs.clone()]));
    }

    #[test]
    fn two_partitions_basic() {
        // Haskell:
        //   twoPartitions []     = []
        //   twoPartitions [x]    = [([x], [])]
        let empty: Vec<i32> = vec![];
        assert_eq!(two_partitions(&empty), Vec::<(Vec<i32>, Vec<i32>)>::new());
        assert_eq!(two_partitions(&[1]), vec![(vec![1], vec![])]);

        let tp = two_partitions(&[1, 2, 3]);
        // There are 2^(n-1) results (the first list is never empty); here just
        // check that each pair covers the input.
        for (a, b) in &tp {
            let mut combined: Vec<i32> = a.iter().chain(b.iter()).cloned().collect();
            combined.sort();
            assert_eq!(combined, vec![1, 2, 3]);
        }
    }

    #[test]
    fn edit_distance_basic() {
        assert_eq!(edit_distance("", ""), 0);
        assert_eq!(edit_distance("abc", "abc"), 0);
        assert_eq!(edit_distance("", "abc"), 3);
        assert_eq!(edit_distance("abc", ""), 3);
        assert_eq!(edit_distance("kitten", "sitting"), 3);
        assert_eq!(edit_distance("flaw", "lawn"), 2);
    }

    #[test]
    fn while_true_counts_iterations() {
        let mut n = 0;
        let count = while_true(|| {
            n += 1;
            n < 5
        });
        assert_eq!(count, 4);
        assert_eq!(n, 5);
    }

    // -- Properties -----------------------------------------------------------

    proptest! {
        #[test]
        fn prop_subset_self(xs in proptest::collection::vec(0i32..50, 0..20)) {
            prop_assert!(subset_of(&xs, &xs));
        }

        #[test]
        fn prop_no_duplicates_matches_btreeset_size(
            xs in proptest::collection::vec(0i32..20, 0..30)
        ) {
            let unique = xs.iter().collect::<BTreeSet<_>>().len();
            prop_assert_eq!(no_duplicates(&xs), unique == xs.len());
        }

        #[test]
        fn prop_partition_count_is_bell(
            n in 0usize..6
        ) {
            let bell = [1, 1, 2, 5, 15, 52, 203];
            let xs: Vec<usize> = (0..n).collect();
            prop_assert_eq!(partitions(&xs).len(), bell[n]);
        }

        #[test]
        fn prop_partition_covers_input(
            xs in proptest::collection::vec(0i32..6, 0..5)
        ) {
            for parts in partitions(&xs) {
                let mut flat: Vec<i32> = parts.into_iter().flatten().collect();
                flat.sort();
                let mut sorted = xs.clone();
                sorted.sort();
                prop_assert_eq!(flat, sorted);
            }
        }

        #[test]
        fn prop_edit_distance_symmetric(
            s in "[a-z]{0,8}",
            t in "[a-z]{0,8}"
        ) {
            prop_assert_eq!(edit_distance(&s, &t), edit_distance(&t, &s));
        }

        #[test]
        fn prop_edit_distance_triangle(
            s in "[a-z]{0,6}",
            t in "[a-z]{0,6}",
            u in "[a-z]{0,6}"
        ) {
            prop_assert!(edit_distance(&s, &u) <= edit_distance(&s, &t) + edit_distance(&t, &u));
        }

        #[test]
        fn prop_edit_distance_bounded_by_length(
            s in "[a-z]{0,10}",
            t in "[a-z]{0,10}"
        ) {
            prop_assert!(edit_distance(&s, &t) <= s.chars().count().max(t.chars().count()));
        }

        #[test]
        fn prop_two_partitions_count(
            n in 1usize..7
        ) {
            // For n>=1 the recursion gives 2 * |twoPartitions(n-1)| with base 1 at n=1,
            // so the count is 2^(n-1).
            let xs: Vec<usize> = (0..n).collect();
            prop_assert_eq!(two_partitions(&xs).len(), 1 << (n - 1));
        }
    }
}
