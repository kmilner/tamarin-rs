//! HTTP handlers, organised by area.

use axum::{
    http::{header, HeaderMap, StatusCode},
    response::{IntoResponse, Response},
};

/// Shared HTML response constructor (`text/html; charset=utf-8`).
fn html_with_status(status: StatusCode, html: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static("text/html; charset=utf-8"),
    );
    (status, headers, html).into_response()
}

/// Shared `200 OK` HTML response constructor.
pub(crate) fn html_response(html: String) -> Response {
    html_with_status(StatusCode::OK, html)
}

/// Shared `200 OK` plain-text response constructor (`text/plain; charset=utf-8`).
pub(crate) fn text_response(s: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static("text/plain; charset=utf-8"),
    );
    (StatusCode::OK, headers, s).into_response()
}

/// Byte-faithful port of HS `defaultLayout'` (`src/Web/Types.hs:699-733`): the
/// `$newline never` frame Yesod's `defaultLayout` puts around a page's
/// `setTitle` text and its widget markup.  The standalone graph shell is the
/// one page with a frame of its own (HS `intdotLayout`, see
/// `handlers::theory::intdot_shell_html`).
///
/// The hamlet quirks are verbatim (unquoted URL attrs, doubled
/// `</script></script>` closes, the `<p class="loading">` banner, the doubled
/// `</a>` in the context menu).  `title` and `body` are spliced as given —
/// every caller escapes what needs escaping.
pub(crate) fn default_layout(title: &str, body: &str) -> String {
    format!(
        r##"<!DOCTYPE html>
<html><head><title>{title}</title><link rel="stylesheet" href="/static/css/intdot-style.css"><link rel="stylesheet" href="/static/css/tamarin-prover-ui.css"><link rel="stylesheet" href="/static/css/jquery-contextmenu.css"><link rel="stylesheet" href="/static/css/smoothness/jquery-ui.css"><script src="/static/js/jquery.js"></script></script><script src="/static/js/jquery-ui.js"></script></script><script src="/static/js/jquery-layout.js"></script></script><script src="/static/js/jquery-cookie.js"></script></script><script src="/static/js/jquery-superfish.js"></script></script><script src="/static/js/jquery-contextmenu.js"></script></script><script src="/static/js/tamarin-prover-ui.js"></script></script><script type="module" src="/static/js/intdot-graph.es.js"></script></script><script type="module" src="/static/js/intdot-staticgraph.es.js"></script></script><script type="module" src="/static/js/intdot-dynamicgraph.es.js"></script></script></head><body><p class="loading">Analyzing, please wait...  <a id=cancel href='#'>Cancel</a></p>{body}<div id="dialog"></div><div id="confirm-dialog"></div><ul id="contextMenu"><li class="autoprove"><a href="#autoprove">Autoprove</a></a></li></ul></body></html>"##
    )
}

/// Shared error-response constructor: the [`default_layout`] frame around the
/// widget yesod-core's `defaultErrorHandler` builds for an error response, sent
/// with `status`.  `title` is the widget's `setTitle`, `body` its markup.
///
/// The error widgets themselves are not `$newline never`, so their markup
/// arrives with the newlines hamlet puts between their lines.
fn error_page(status: StatusCode, title: &str, body: &str) -> Response {
    html_with_status(status, default_layout(title, body))
}

/// Shared `500 Internal Server Error` response constructor: the page Yesod
/// renders when a handler raises.
///
/// yesod-core's `defaultErrorHandler` answers an `InternalError e` with
/// `<h1>Internal Server Error</h1>` over the exception text in a `<pre>`,
/// titled `Internal Server Error`, in the [`error_page`] frame.
///
/// The page is route-independent: `message` is the raised exception's text and
/// is the only thing that varies.  `defaultErrorHandler` offers this rendering
/// alongside a `{"error":<message>,"message":"Internal Server Error"}` one
/// through `selectRep`; the HTML rendering is first, so it is what every
/// Tamarin client gets — the browser pages, and the frontend's plain `fetch`
/// of the JSON graph route (`frontend/src/wcs/graph.ts:426`), which sends
/// `Accept: */*` and discards the body of a non-`ok` response anyway.  A client
/// that explicitly asks for `application/json` gets the JSON rendering from HS
/// and this HTML one here.
pub(crate) fn internal_server_error(message: &str) -> Response {
    error_page(
        StatusCode::INTERNAL_SERVER_ERROR,
        "Internal Server Error",
        &format!(
            "<h1>Internal Server Error</h1>\n<pre>{}</pre>\n",
            root::html_escape(message)
        ),
    )
}

/// Shared `404 Not Found` response constructor: the page Yesod renders for a
/// `NotFound` error response.
///
/// `defaultErrorHandler`'s `NotFound` widget is `<h1>Not Found</h1>` over the
/// request's `rawPathInfo` in a `<p>`, titled `Not Found`, in the
/// [`error_page`] frame.  `raw_path` is that path: still percent-encoded,
/// without the query string, HTML-escaped by hamlet's `#{}` as it is spliced in.
///
/// Yesod renders this for every `notFound` — the routing-level one for a URL
/// that matches no route, and the handler-raised one for a theory index or
/// theory path that does not resolve.  The port routes all of those through the
/// `not_found_page` layer in [`crate::routes`], which is where the request path
/// is at hand.
pub(crate) fn not_found_response(raw_path: &str) -> Response {
    error_page(
        StatusCode::NOT_FOUND,
        "Not Found",
        &format!(
            "<h1>Not Found</h1>\n<p>{}</p>\n",
            root::html_escape(raw_path)
        ),
    )
}

pub mod dot;
pub mod json_resp;
pub mod path_parse;
pub mod proof_tree;
pub mod root;
pub mod static_files;
pub mod theory;
pub mod theory_html;
