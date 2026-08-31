// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `nubOn` (Extension/Prelude.hs:92-93) and `flushRight`
//! (Extension/Prelude.hs:208-209) from `lib/utils/src/Extension/Prelude.hs`.

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

/// `flushRight n s`: pad `s` on the left with spaces so the result is at
/// least `n` *characters* (Unicode scalars) wide.
pub fn flush_right(n: usize, s: &str) -> String {
    let s_len = s.chars().count();
    if s_len >= n {
        return s.to_string();
    }
    let pad = n - s_len;
    let mut out = String::with_capacity(pad + s.len());
    for _ in 0..pad {
        out.push(' ');
    }
    out.push_str(s);
    out
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
    fn flush_right_pads_to_a_character_width() {
        assert_eq!(flush_right(5, "ab"), "   ab");
        assert_eq!(flush_right(2, "abcd"), "abcd"); // no truncation
        assert_eq!(flush_right(0, "ab"), "ab");
        // The width counts characters, not bytes.  "é" is one column and
        // two bytes.
        assert_eq!(flush_right(3, "é"), "  é");
    }
}
