// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `escapeHtmlEntities` from `lib/utils/src/Text/PrettyPrint/Html.hs`
//! (Text/PrettyPrint/Html.hs:140-149).
//!
//! [`escape_html_entities`] is the one HTML escaper in the tree: the theory
//! crate re-exports it as `tamarin_theory::pretty_hpj::escape_html_entities`
//! and the server aliases it as `root::html_escape`.  The HTML `Doc` mode
//! (`HtmlDoc` of the same Haskell module) lives in
//! `tamarin_theory::pretty_hpj`.

/// Escape the five HTML metacharacters.
pub fn escape_html_entities(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            x => out.push(x),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escape_basics() {
        assert_eq!(
            escape_html_entities("<a href=\"x\">&'</a>"),
            "&lt;a href=&quot;x&quot;&gt;&amp;&#39;&lt;/a&gt;"
        );
    }
}
