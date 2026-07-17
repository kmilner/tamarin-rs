//! The full-page theory-view HTML shell returned by the `overview/*` routes.
//!
//! Observed structure (constant across theories after substituting the four
//! parameters below): a fixed `<head>` of stylesheet/script links, a north
//! header bar, then four layout panes — west "Proof scripts", east "Debug
//! information" (always empty), and center "Visualization display". The west
//! pane embeds the proof-script markup (see [`super::proofscript`]); the center
//! pane embeds the currently-selected main content HTML (the same HTML the
//! corresponding `main/*` route returns in its JSON `html` field).
//!
//! Scaffolding constants in `shell_template` are byte-exact copies of oracle
//! output with four `§`-delimited slots: NAME, IDX, VERSION, FILENAME. The
//! body has no trailing newline (ends `</html>`). All internal links use the
//! resolved numeric theory index, never `#`.

use super::escape::html_escape;
use super::shell_template::{PAGE_MID, PAGE_PREFIX, PAGE_TAIL};

/// Parameters that vary between rendered pages.
pub struct PageParams<'a> {
    /// Theory name, shown in `<title>Theory: NAME</title>`.
    pub theory_name: &'a str,
    /// Resolved numeric theory index used in every internal URL.
    pub index: u64,
    /// Tamarin version string shown in the header (e.g. `"1.13.0"`).
    pub version: &'a str,
    /// Source filename used in the download / append links (e.g. `"foo.spthy"`).
    pub filename: &'a str,
}

/// Render the full theory-view page from the shell parameters plus the already
/// rendered west (proof-script) and center (main content) pane inner HTML.
pub fn render_page(p: &PageParams, west_inner: &str, center_inner: &str) -> String {
    let idx = p.index.to_string();
    let prefix = PAGE_PREFIX
        .replace("§NAME§", &html_escape(p.theory_name))
        .replace("§IDX§", &idx)
        .replace("§VERSION§", p.version)
        .replace("§FILENAME§", p.filename);
    let mut out = String::with_capacity(
        prefix.len() + west_inner.len() + PAGE_MID.len() + center_inner.len() + PAGE_TAIL.len(),
    );
    out.push_str(&prefix);
    out.push_str(west_inner);
    out.push_str(PAGE_MID);
    out.push_str(center_inner);
    out.push_str(PAGE_TAIL);
    out
}
