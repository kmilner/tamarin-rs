// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Page furniture: the two HTML frames a response is wrapped in and the
//! Options menu both of them splice.
//!
//! HS keeps the frames in `src/Web/Types.hs` (`defaultLayout'`,
//! `intdotLayout`, `optionsMenuItemTpl`, `popoutOptionsTpl`) and the widget
//! bodies they wrap in `src/Web/Hamlet.hs`; this module is the frame half.
//! All four are `$newline never` hamlet, and the fixtures under
//! `tests/assets/` pin them together byte-for-byte.

use axum::{http::StatusCode, response::Response};

use super::html_with_status;

/// Byte-faithful port of HS `defaultLayout'` (`src/Web/Types.hs:699-736`): the
/// `$newline never` frame Yesod's `defaultLayout` puts around a page's
/// `setTitle` text and its widget markup.  The standalone graph shell is the
/// one page with a frame of its own ([`intdot_shell_html`], HS `intdotLayout`).
///
/// Includes upstream PR #928’s HTML fixes. `title` and `body` are spliced
/// as given; every caller escapes what needs escaping.
pub(crate) fn default_layout(title: &str, body: &str) -> String {
    format!(
        r##"<!DOCTYPE html>
<html lang="en"><head><title>{title}</title><link rel="stylesheet" href="/static/css/intdot-style.css"><link rel="stylesheet" href="/static/css/tamarin-prover-ui.css"><link rel="stylesheet" href="/static/css/jquery-contextmenu.css"><link rel="stylesheet" href="/static/css/smoothness/jquery-ui.css"><script src="/static/js/jquery.js"></script><script src="/static/js/jquery-ui.js"></script><script src="/static/js/jquery-layout.js"></script><script src="/static/js/jquery-cookie.js"></script><script src="/static/js/jquery-superfish.js"></script><script src="/static/js/jquery-contextmenu.js"></script><script src="/static/js/tamarin-prover-ui.js"></script><script type="module" src="/static/js/intdot-graph.es.js"></script><script type="module" src="/static/js/intdot-staticgraph.es.js"></script><script type="module" src="/static/js/intdot-dynamicgraph.es.js"></script></head><body><p class="loading">Analyzing, please wait...  <a id=cancel href='#'>Cancel</a></p>{body}<div id="dialog"></div><div id="confirm-dialog"></div><ul id="contextMenu"><li class="autoprove"><a href="#autoprove">Autoprove</a></li></ul></body></html>"##
    )
}

/// Shared error-response constructor: the [`default_layout`] frame around the
/// widget yesod-core's `defaultErrorHandler` builds for an error response, sent
/// with `status`.  `title` is the widget's `setTitle`, `body` its markup.
///
/// The error widgets themselves are not `$newline never`, so their markup
/// arrives with the newlines hamlet puts between their lines.
pub(super) fn error_page(status: StatusCode, title: &str, body: &str) -> Response {
    html_with_status(status, default_layout(title, body))
}

/// The "Options" drop-down's `<li>` run, from the `Options` anchor through the
/// closing `</ul></li>` of the toggle list.
///
/// HS splices the same `optionsMenuItemTpl True` (Web/Types.hs:749-763) into
/// both the theory-page header (Web/Hamlet.hs:190, via
/// `handlers::theory_html::header`) and the standalone graph shell's popout bar
/// (`popoutOptionsTpl True`, Web/Types.hs:769-777, via [`intdot_shell_html`]),
/// so the two pages carry byte-identical menu markup.
pub(crate) const OPTIONS_MENU_ITEMS: &str =
    "<li><a href=\"#\">Options</a><ul class=\"list-with-toggles\">\
<li><a id=abbrv-toggle href=\"#\">Abbreviate terms</a></li>\
<li><a id=agent-toggle href=\"#\">Clustering by role</a></li>\
<li><a id=auto-toggle href=\"#\">Show annotation auto-sources</a></li>\
<li><a id=abstr-toggle href=\"#\">Abstract node content</a></li>\
<li><a id=lvl0-toggle href=\"#\">Graph simplification off</a></li>\
<li><a id=lvl1-toggle href=\"#\">Graph simplification L1</a></li>\
<li><a id=lvl2-toggle href=\"#\">Graph simplification L2</a></li>\
<li><a id=lvl3-toggle href=\"#\">Graph simplification L3</a></li>\
</ul></li>";

/// Byte-for-byte reproduction of `intdotLayout True` (`src/Web/Types.hs:795-824`)
/// wrapping `popoutOptionsTpl True` (`src/Web/Types.hs:769-777`) and
/// `optionsMenuItemTpl True` (`src/Web/Types.hs:749-763`).
///
pub(crate) fn intdot_shell_html(title: &str, dotsrc: &str) -> String {
    format!(
        "<!DOCTYPE html>\n<html lang=\"en\"><head>\
         <meta charset=\"UTF-8\" />\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\" />\
         <title>{title}</title>\
         <style> body,html{{width: 100%; height: 100%; overflow: hidden; margin: 0; padding: 0; }}</style>\
         <link rel=\"stylesheet\" href=\"/static/css/intdot-style.css\">\
         <link rel=\"stylesheet\" href=\"/static/css/tamarin-prover-ui.css\">\
         <script src=\"/static/js/jquery.js\"></script>\
         <script src=\"/static/js/jquery-cookie.js\"></script>\
         <script src=\"/static/js/jquery-superfish.js\"></script>\
         <script>window.tamarinPopoutGraph = (window.self === window.top); if (!window.tamarinPopoutGraph) {{ document.documentElement.classList.add(\"graph-embedded\"); }}</script>\
         <script src=\"/static/js/tamarin-prover-ui.js\"></script>\
         <script type=\"module\" src=\"/static/js/intdot-graph.es.js\"></script>\
         </head><body><div class=\"graph-page\">\
         <div id=\"popout-options\"><ul id=\"navigation\">\
         {options}</ul></div>\
         <dot-graph-viz dotsrc=\"{dotsrc}\"></dot-graph-viz>\n</div></body></html>",
        options = OPTIONS_MENU_ITEMS,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intdot_shell_matches_haskell_layout() {
        let html = intdot_shell_html(
            "Theory: RevealingSignatures",
            "/thy/trace/1/json/lemma/debug",
        );
        assert_eq!(
            html,
            include_str!("../../tests/fixtures/haskell-responses/intdot.html")
        );
    }
}
