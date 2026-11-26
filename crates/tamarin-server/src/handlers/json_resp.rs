//! Mirror Haskell `JsonResponse` envelope:
//!
//!   - `JsonHtml { title, content }`    -> `{ "title": .., "html": .. }`
//!   - `JsonAlert msg`                  -> `{ "alert": .. }`
//!   - `JsonRedirect url`               -> `{ "redirect": .. }`
//!
//! The frontend's `server.handleJson` inspects `data.redirect` /
//! `data.alert` / `data.html` (in that order), see
//! `data/js/tamarin-prover-ui.js`.

use axum::http::header;
use axum::response::{IntoResponse, Response};
use serde_json::{json, Value};

/// One envelope, served as Yesod's `typeJson`: `application/json;
/// charset=utf-8` (axum's `Json` omits the charset).
#[derive(Debug)]
pub struct Envelope(pub Value);

impl IntoResponse for Envelope {
    fn into_response(self) -> Response {
        (
            [(header::CONTENT_TYPE, "application/json; charset=utf-8")],
            self.0.to_string(),
        )
            .into_response()
    }
}

/// Build a `{ html, title }` JSON response.
pub fn html(title: impl Into<String>, content: impl Into<String>) -> Envelope {
    Envelope(json!({ "title": title.into(), "html": content.into() }))
}

/// Build a `{ alert }` JSON response.
pub fn alert(msg: impl Into<String>) -> Envelope {
    Envelope(json!({ "alert": msg.into() }))
}

/// Build a `{ redirect }` JSON response.
pub fn redirect(url: impl Into<String>) -> Envelope {
    Envelope(json!({ "redirect": url.into() }))
}
