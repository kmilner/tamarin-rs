//! Mirror Haskell `JsonResponse` envelope:
//!
//!   - `JsonHtml { title, content }`    -> `{ "title": .., "html": .. }`
//!   - `JsonAlert msg`                  -> `{ "alert": .. }`
//!   - `JsonRedirect url`               -> `{ "redirect": .. }`
//!
//! The frontend's `server.handleJson` inspects `data.redirect` /
//! `data.alert` / `data.html` (in that order), see
//! `data/js/tamarin-prover-ui.js`.

use axum::Json;
use serde_json::{json, Value};

/// Build a `{ html, title }` JSON response.
pub fn html(title: impl Into<String>, content: impl Into<String>) -> Json<Value> {
    Json(json!({ "title": title.into(), "html": content.into() }))
}

/// Build a `{ alert }` JSON response.
pub fn alert(msg: impl Into<String>) -> Json<Value> {
    Json(json!({ "alert": msg.into() }))
}

/// Build a `{ redirect }` JSON response.
pub fn redirect(url: impl Into<String>) -> Json<Value> {
    Json(json!({ "redirect": url.into() }))
}

