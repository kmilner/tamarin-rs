//! HTTP handlers, organised by area.

use axum::{
    http::{header, HeaderMap, StatusCode},
    response::{IntoResponse, Response},
};

use layout::error_page;

/// The page frames live in the `layout` module; they are re-exported here so
/// every renderer reaches them through the `handlers` facade, as it does the
/// response constructors below.
pub(crate) use layout::{default_layout, intdot_shell_html, OPTIONS_MENU_ITEMS};

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
mod layout;
pub mod path_parse;
pub mod proof_tree;
pub mod root;
pub mod static_files;
pub mod theory;
pub mod theory_html;
