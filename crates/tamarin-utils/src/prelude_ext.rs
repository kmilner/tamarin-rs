// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! `Data.List.nub` and `flushRight` (lib/utils/src/Extension/Prelude.hs),
//! and GHC's `show` on a `String`.

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

/// GHC's `show` on a `String`: a quoted literal in which every character
/// above DEL is a decimal escape (`"\304tem"` for `İtem`), unlike Rust's
/// `{:?}`.
pub fn show_string(s: &str) -> String {
    const ASCII_TAB: [&str; 32] = [
        "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "a", "b", "t", "n", "v", "f", "r", "SO",
        "SI", "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM", "SUB", "ESC",
        "FS", "GS", "RS", "US",
    ];
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        // `showLitString`'s `\&` separates an escape from a following
        // character that would otherwise extend it.
        let protect: fn(char) -> bool = match c {
            '"' => {
                out.push_str("\\\"");
                continue;
            }
            '\\' => {
                out.push_str("\\\\");
                continue;
            }
            '\u{7f}' => {
                out.push_str("\\DEL");
                continue;
            }
            ' '..='~' => {
                out.push(c);
                continue;
            }
            '\u{0}'..='\u{1f}' => {
                out.push('\\');
                out.push_str(ASCII_TAB[c as usize]);
                if c != '\u{e}' {
                    continue;
                }
                |next| next == 'H'
            }
            _ => {
                out.push('\\');
                out.push_str(&(c as u32).to_string());
                |next: char| next.is_ascii_digit()
            }
        };
        if chars.peek().is_some_and(|&next| protect(next)) {
            out.push_str("\\&");
        }
    }
    out.push('"');
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

    #[test]
    fn show_string_matches_ghc_show() {
        assert_eq!(show_string("Item"), r#""Item""#);
        assert_eq!(show_string("İtem"), r#""\304tem""#);
        assert_eq!(show_string("İ1"), r#""\304\&1""#);
        assert_eq!(show_string("a\"b\\c"), r#""a\"b\\c""#);
        assert_eq!(show_string("\n\u{7f}\u{1}"), r#""\n\DEL\SOH""#);
        assert_eq!(show_string("\u{e}H\u{e}I"), r#""\SO\&H\SOI""#);
    }
}
