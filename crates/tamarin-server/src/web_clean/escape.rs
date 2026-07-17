//! HTML entity escaping used by the web layer.
//!
//! Observed escape set (from oracle output): the five characters
//! `& < > " '` map to `&amp; &lt; &gt; &quot; &#39;` respectively; every other
//! byte (including all non-ASCII UTF-8, e.g. the logic operators the prover
//! emits) passes through unchanged. Escaping is applied left-to-right in a
//! single pass, and `&` is handled first so already-produced entities are not
//! double-escaped.
//!
//! Witnesses:
//!   `'` -> `&#39;`   (the "'smart' heuristic" comment in proof-method pages)
//!   `<`,`>` -> `&lt;`,`&gt;`   (pair terms `<x.1, x.2>` in the signature view)
//!   `"` -> `&quot;`  (loaded-from path, and lemma text in the edit form)
//!   `&` -> `&amp;`   (a literal `&` inside a lemma formula)

/// Escape a plain string into HTML text, matching the web layer's entity set.
pub fn html_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_the_five_special_characters() {
        assert_eq!(html_escape("a<b>c"), "a&lt;b&gt;c");
        assert_eq!(html_escape("x & y"), "x &amp; y");
        assert_eq!(html_escape("say \"hi\""), "say &quot;hi&quot;");
        assert_eq!(html_escape("'smart'"), "&#39;smart&#39;");
    }

    #[test]
    fn passes_through_non_ascii_unchanged() {
        // Prover-emitted logic operators are not part of the escape set.
        assert_eq!(html_escape("∃ x ▶₀ #i"), "∃ x ▶₀ #i");
    }

    #[test]
    fn does_not_double_escape() {
        assert_eq!(html_escape("<&>"), "&lt;&amp;&gt;");
    }
}
