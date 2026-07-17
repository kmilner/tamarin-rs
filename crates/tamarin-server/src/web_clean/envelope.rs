//! JSON response envelopes for the `main/*` (and `method/*`, `autoprove/*`)
//! AJAX handlers.
//!
//! Observed: every `kind=json` response body is one of exactly two compact
//! JSON objects, with keys in this order and no insignificant whitespace:
//!   * content:  `{"html":<string>,"title":<string>}`
//!   * redirect: `{"redirect":<string>}`
//!
//! There is no trailing newline. Non-ASCII is emitted as literal UTF-8 (no
//! `\uXXXX`), and `/ < > &` are NOT backslash/entity escaped inside the JSON
//! string — i.e. standard JSON string escaping (only `" \` and control chars).
//! `serde_json`'s default serialization reproduces this exactly.

use serde::Serialize;

/// A content pane response: rendered HTML plus the pane title.
#[derive(Serialize)]
pub struct Content<'a> {
    pub html: &'a str,
    pub title: &'a str,
}

/// A redirect response instructing the client to navigate to `redirect`.
#[derive(Serialize)]
pub struct Redirect<'a> {
    pub redirect: &'a str,
}

/// Serialize `{"html":..,"title":..}` exactly as the web layer does.
pub fn render_content(html: &str, title: &str) -> String {
    serde_json::to_string(&Content { html, title }).expect("Content serializes")
}

/// Serialize `{"redirect":..}` exactly as the web layer does.
pub fn render_redirect(path: &str) -> String {
    serde_json::to_string(&Redirect { redirect: path }).expect("Redirect serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn content_envelope_shape() {
        assert_eq!(
            render_content("this is a mistake<br/>\n", "Lemma: exec"),
            r#"{"html":"this is a mistake<br/>\n","title":"Lemma: exec"}"#
        );
    }

    #[test]
    fn redirect_envelope_shape() {
        assert_eq!(
            render_redirect("/thy/trace/4/overview/proof/exec/_"),
            r#"{"redirect":"/thy/trace/4/overview/proof/exec/_"}"#
        );
    }

    #[test]
    fn keeps_literal_utf8_and_unescaped_angle_brackets() {
        let s = render_content("<span>∃</span>", "t");
        assert!(s.contains("<span>∃</span>"), "got {s}");
        assert!(!s.contains("\\u"), "should not \\u-escape: {s}");
    }
}
