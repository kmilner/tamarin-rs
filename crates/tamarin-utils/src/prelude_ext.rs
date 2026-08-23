// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `nubOn` (Extension/Prelude.hs:92) and `flushRightBy`/`flushRight`
//! (Extension/Prelude.hs:204-209) from `lib/utils/src/Extension/Prelude.hs`.

use std::hash::Hash;

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

/// `flushRightBy sep n s`: pad `s` on the left with cycles of `sep` so the
/// result is at least `n` *characters* (Unicode scalars) wide.
pub fn flush_right_by(sep: &str, n: usize, s: &str) -> String {
    let s_len = s.chars().count();
    // An empty `sep` would make HS's `cycle sep` diverge; pad nothing instead.
    if s_len >= n || sep.is_empty() {
        return s.to_string();
    }
    let needed = n - s_len;
    let mut out = String::with_capacity(sep.len() * needed + s.len());
    for c in sep.chars().cycle().take(needed) {
        out.push(c);
    }
    out.push_str(s);
    out
}

pub fn flush_right(n: usize, s: &str) -> String {
    flush_right_by(" ", n, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nub_on_preserves_first_occurrence() {
        let xs = vec!["aa", "bb", "ab", "bc", "ac"];
        let got = nub_on(&xs, |s| s.chars().next().unwrap());
        assert_eq!(got, vec!["aa", "bb"]);
    }

    #[test]
    fn flush_helpers() {
        assert_eq!(flush_right(5, "ab"), "   ab");
        assert_eq!(flush_right_by("0", 4, "12"), "0012");
        assert_eq!(flush_right(2, "abcd"), "abcd"); // no truncation
                                                    // The code cycles a multi-character
                                                    // separator.  It cycles only as far
                                                    // as the padding needs.  HS uses
                                                    // `take (n - length s) (cycle sep)`.
        assert_eq!(flush_right_by("ab", 5, "x"), "ababx");
        // The width counts characters, not bytes.  "é" is one column and
        // two bytes.
        assert_eq!(flush_right(3, "é"), "  é");
        assert_eq!(flush_right_by("é", 3, "x"), "ééx");
        // HS `cycle ""` diverges.  The port adds no padding and does not hang.
        assert_eq!(flush_right_by("", 5, "ab"), "ab");
    }
}
