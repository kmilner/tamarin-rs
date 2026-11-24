// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! `Data.List.nub` and `flushRight` (lib/utils/src/Extension/Prelude.hs).

/// Keep the first occurrence of each equal value, in input order.
pub fn nub<T: PartialEq>(xs: impl IntoIterator<Item = T>) -> Vec<T> {
    let mut unique = Vec::new();
    for value in xs {
        if !unique.contains(&value) {
            unique.push(value);
        }
    }
    unique
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
    fn flush_right_pads_to_a_character_width() {
        assert_eq!(flush_right(5, "ab"), "   ab");
        assert_eq!(flush_right(2, "abcd"), "abcd"); // no truncation
        assert_eq!(flush_right(0, "ab"), "ab");
        // The width counts characters, not bytes.  "é" is one column and
        // two bytes.
        assert_eq!(flush_right(3, "é"), "  é");
    }
}
