//! HTTP handlers, organised by area.

use axum::{
    http::{header, HeaderMap, StatusCode},
    response::{IntoResponse, Response},
};

/// Shared `200 OK` HTML response constructor (`text/html; charset=utf-8`).
pub(crate) fn html_response(html: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static("text/html; charset=utf-8"),
    );
    (StatusCode::OK, headers, html).into_response()
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

pub mod dot;
pub mod json_resp;
pub mod path_parse;
pub mod proof_tree;
pub mod root;
pub mod static_files;
pub mod theory;
pub mod theory_html;
