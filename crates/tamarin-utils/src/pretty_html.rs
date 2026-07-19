// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Text/PrettyPrint/Html.hs

//! Port of `Text.PrettyPrint.Html` from `lib/utils/src/Text/PrettyPrint/Html.hs`.
//!
//! We reuse the plain `Doc` from `pretty.rs`. Two helpers do the work:
//! [`escape_html_entities`] for safe text, and [`render_html_doc`] which calls
//! `Doc::render_with` to wrap highlight spans in `<span class="hl_...">` tags
//! and post-processes the output to convert newlines and leading whitespace.
//!
//! NOTE: [`escape_html_entities`] is the canonical live escaper — the theory
//! crate re-exports it (`tamarin_theory::pretty_hpj::escape_html_entities`) and
//! the server aliases it (`root::html_escape`), so every web-pane escape routes
//! here. The rest of the module (`with_tag`/`closed_tag`/`render_html_doc`/
//! `postprocess`) remains a reserved faithful port with no consumer in the tree.

use crate::pretty::{Doc, HighlightStyle};

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

fn class_name(s: HighlightStyle) -> &'static str {
    match s {
        HighlightStyle::Comment => "hl_comment",
        HighlightStyle::Keyword => "hl_keyword",
        HighlightStyle::Operator => "hl_operator",
    }
}

/// `withTag tag attrs inner`: wrap `inner` in `<tag …>…</tag>`. Attributes
/// values are HTML-escaped.
pub fn with_tag(tag: &str, attrs: &[(&str, &str)], inner: &str) -> String {
    let mut s = String::new();
    s.push('<');
    s.push_str(tag);
    for (k, v) in attrs {
        s.push(' ');
        s.push_str(k);
        s.push_str("=\"");
        s.push_str(&escape_html_entities(v));
        s.push('"');
    }
    s.push('>');
    s.push_str(inner);
    s.push_str("</");
    s.push_str(tag);
    s.push('>');
    s
}

/// `closedTag tag attrs` → `<tag k="v"/>`.
pub fn closed_tag(tag: &str, attrs: &[(&str, &str)]) -> String {
    let mut s = String::new();
    s.push('<');
    s.push_str(tag);
    for (k, v) in attrs {
        s.push(' ');
        s.push_str(k);
        s.push_str("=\"");
        s.push_str(&escape_html_entities(v));
        s.push('"');
    }
    s.push_str("/>");
    s
}

/// Render a `Doc` to HTML: highlight spans → `<span class="hl_...">…</span>`,
/// newlines → `<br/>`, and leading whitespace per line → `&nbsp;`.
///
/// Note: this is HTML-escape-aware *only* for highlight bodies. The caller is
/// expected to either feed already-safe text, or use `Doc::text` of escaped
/// content when text might contain `< > & " '`.
pub fn render_html_doc(doc: &Doc) -> String {
    // `render_with` wraps each highlighted span once (HS `withTag`): the
    // closure returns the `(open, close)` tag pair for a style.
    let body = doc.render_with(&|style| {
        let open = format!(
            "<span class=\"{}\">",
            escape_html_entities(class_name(style))
        );
        (open, "</span>".to_string())
    });
    postprocess(&body)
}

/// Convert line breaks to `<br/>` and replace leading whitespace per line
/// with `&nbsp;` runs.
///
/// Mirrors `postprocessHtmlDoc = unlines . map (addBreak . indent) . lines`
/// (Html.hs). Note both `lines` (treats `\n` as a terminator, so a
/// trailing `\n` does not yield an extra empty line) and `unlines` (appends
/// `\n` after *every* line, including the last) are matched here.
pub fn postprocess(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    // Haskell `lines`: split on '\n' where '\n' is a line terminator. An empty
    // input yields no lines; a trailing '\n' does not produce a trailing empty
    // segment (`lines "a\n" == ["a"]`).
    let mut rest = s;
    loop {
        let (line, tail, more) = match rest.find('\n') {
            Some(idx) => (&rest[..idx], &rest[idx + 1..], true),
            None => {
                if rest.is_empty() {
                    break;
                }
                (rest, "", false)
            }
        };
        // Single pass: emit `&nbsp;` per leading-whitespace char and accumulate
        // its byte length, giving the suffix byte offset without re-walking.
        let mut suffix_offset = 0;
        for c in line.chars() {
            if !c.is_whitespace() { break; }
            out.push_str("&nbsp;");
            suffix_offset += c.len_utf8();
        }
        out.push_str(&line[suffix_offset..]);
        // addBreak + unlines: `<br/>` then a trailing newline for every line.
        out.push_str("<br/>");
        out.push('\n');
        if !more {
            break;
        }
        rest = tail;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty::{keyword, Doc};

    #[test]
    fn escape_basics() {
        assert_eq!(
            escape_html_entities("<a href=\"x\">&'</a>"),
            "&lt;a href=&quot;x&quot;&gt;&amp;&#39;&lt;/a&gt;"
        );
    }

    #[test]
    fn with_tag_includes_attrs() {
        assert_eq!(
            with_tag("span", &[("class", "hl")], "x"),
            "<span class=\"hl\">x</span>"
        );
    }

    #[test]
    fn closed_tag_self_closes() {
        assert_eq!(
            closed_tag("img", &[("src", "a.png")]),
            "<img src=\"a.png\"/>"
        );
    }

    #[test]
    fn render_with_highlight_wraps_keyword() {
        let d = keyword(Doc::text("rule")).cat_with(Doc::text(" foo"));
        let html = render_html_doc(&d);
        assert_eq!(html, "<span class=\"hl_keyword\">rule</span> foo<br/>\n");
    }

    #[test]
    fn postprocess_handles_indent_and_newlines() {
        let s = "a\n  b\nc";
        let p = postprocess(s);
        assert_eq!(p, "a<br/>\n&nbsp;&nbsp;b<br/>\nc<br/>\n");
    }
}
