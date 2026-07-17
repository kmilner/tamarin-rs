//! Error response pages.
//!
//! Observed by live probing: a request that does not match any route (unknown
//! handler, non-existent theory index, or a path segment the router rejects
//! such as a URL-encoded `%23`) returns HTTP 404 with a full HTML page. The
//! page reuses the standard `<head>` link set and the standard page tail; its
//! body is just the loading bar, an `<h1>Not Found</h1>`, and the echoed
//! request path in a `<p>`. The echoed path is HTML-escaped.

use super::escape::html_escape;
use super::notfound_template::NOT_FOUND;

/// Render the 404 Not Found page for a given (already percent-encoded) request
/// path. The path is HTML-escaped before being echoed into the body.
pub fn render_not_found(request_path: &str) -> String {
    NOT_FOUND.replace("§PATH§", &html_escape(request_path))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn not_found_echoes_path() {
        let p = render_not_found("/thy/trace/1/main/nope");
        assert!(p.contains("<title>Not Found</title>"));
        assert!(p.contains("<h1>Not Found</h1>\n<p>/thy/trace/1/main/nope</p>"));
        assert!(p.ends_with("</body></html>"));
    }
}
