//! Port of `Text.Unicode` from `lib/utils/src/Text/Unicode.hs`.
//!
//! `pretty_theory::goal_subscript` routes its subscript rendering through
//! [`subscript`]; since it only ever receives digits, the extra `+ - = ( )`
//! mappings in [`subscript_char`] are inert on that path but faithful to HS.

/// Convert a subscriptable character to its subscript codepoint.
pub fn subscript_char(c: char) -> char {
    match c {
        '0' => '₀', '1' => '₁', '2' => '₂', '3' => '₃', '4' => '₄',
        '5' => '₅', '6' => '₆', '7' => '₇', '8' => '₈', '9' => '₉',
        '+' => '₊', '-' => '₋', '=' => '₌', '(' => '₍', ')' => '₎',
        x => x,
    }
}

/// Convert all subscriptable characters in `s` to subscripts.
pub fn subscript(s: &str) -> String {
    s.chars().map(subscript_char).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digits() {
        assert_eq!(subscript("0123456789"), "₀₁₂₃₄₅₆₇₈₉");
    }

    #[test]
    fn punctuation_and_passthrough() {
        assert_eq!(subscript("(+1)"), "₍₊₁₎");
        // All digits and '=', '-' are subscriptable; only 'a','b','c' pass through.
        assert_eq!(subscript("abc=42-7"), "abc₌₄₂₋₇");
        assert_eq!(subscript("hello"), "hello");
    }
}
