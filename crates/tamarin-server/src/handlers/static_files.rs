//! Static asset serving.
//!
//! Tamarin's frontend pulls JS/CSS from two places:
//!
//!   1. `data/` — jQuery, jQuery-UI, smoothness theme,
//!      tamarin-prover-ui.js, base CSS, images
//!   2. `frontend/dist/` — built `intdot-graph.es.js`,
//!      `intdot-staticgraph.es.js`,
//!      `intdot-dynamicgraph.es.js`, plus
//!      `intdot-style.css`
//!
//! Strategy:
//!   - Serve `data/<rest>` via tower-http `ServeDir`.
//!   - For `js/intdot-*.es.js` and `css/intdot-*.css`, look the
//!     file up in `frontend/dist/` and stream it back from a small
//!     async handler.
//!   - Everything else 404s.
//!
//! We wire the dist-hoisting routes BEFORE the catch-all ServeDir so
//! they take precedence.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use axum::extract::State;
use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Response};
use tower_http::services::ServeDir;

use crate::state::AppState;

/// Build the static-files router, to be nested at `/static`.
pub fn serve(state: Arc<AppState>) -> axum::Router<Arc<AppState>> {
    let serve_data = ServeDir::new(&state.cfg.data_dir);
    let mut router: axum::Router<Arc<AppState>> = axum::Router::new();

    if state.cfg.frontend_dist.is_some() {
        router = router
            .route("/js/:name", axum::routing::get(intdot_js_or_data))
            .route("/css/:name", axum::routing::get(intdot_css_or_data));
    }

    router.fallback_service(serve_data)
}

/// `/static/js/<name>` — if the name is `intdot-*.es.js`, serve from
/// the frontend dist; otherwise hand off to `data/js/<name>`.
async fn intdot_js_or_data(
    State(state): State<Arc<AppState>>,
    axum::extract::Path(name): axum::extract::Path<String>,
) -> Response {
    if name.starts_with("intdot-") && name.ends_with(".es.js") {
        if let Some(ref dist) = state.cfg.frontend_dist {
            if let Some(resp) = try_file(&dist.join(&name), "application/javascript").await {
                return resp;
            }
        }
    }
    // Fall through to data/js/<name>.
    fallback_to_data(state, "js", &name).await
}

async fn intdot_css_or_data(
    State(state): State<Arc<AppState>>,
    axum::extract::Path(name): axum::extract::Path<String>,
) -> Response {
    if name.starts_with("intdot-") && name.ends_with(".css") {
        if let Some(ref dist) = state.cfg.frontend_dist {
            if let Some(resp) = try_file(&dist.join(&name), "text/css").await {
                return resp;
            }
        }
    }
    fallback_to_data(state, "css", &name).await
}

async fn fallback_to_data(
    state: Arc<AppState>,
    subdir: &str,
    name: &str,
) -> Response {
    let candidate = state.cfg.data_dir.join(subdir).join(name);
    let mime = guess_mime(&candidate);
    if let Some(resp) = try_file(&candidate, mime).await {
        return resp;
    }
    (StatusCode::NOT_FOUND, "static asset not found").into_response()
}

async fn try_file(path: &Path, mime: &str) -> Option<Response> {
    if !path.is_file() { return None; }
    let bytes = tokio::fs::read(path).await.ok()?;
    Some((StatusCode::OK,
          [(header::CONTENT_TYPE, mime.to_string())],
          bytes).into_response())
}

fn guess_mime(path: &Path) -> &'static str {
    match path.extension().and_then(|s| s.to_str()) {
        Some("js") => "application/javascript",
        Some("css") => "text/css",
        Some("html") => "text/html; charset=utf-8",
        Some("png") => "image/png",
        Some("jpg") | Some("jpeg") => "image/jpeg",
        Some("gif") => "image/gif",
        Some("svg") => "image/svg+xml",
        Some("ico") => "image/x-icon",
        Some("woff") => "font/woff",
        Some("woff2") => "font/woff2",
        Some("ttf") => "font/ttf",
        Some("json") => "application/json",
        Some("txt") => "text/plain; charset=utf-8",
        _ => "application/octet-stream",
    }
}

/// Convenience: turn an optional explicit data dir into a usable path.
///
/// An explicit path (e.g. from `--data-dir`) always wins.  Otherwise we
/// probe a fixed list relative to the current working directory:
/// `data` (running from inside `tamarin-prover/`), `tamarin-prover/data`
/// (running from the repo root, where the assets live in the submodule),
/// then `../data` / `../../data` (older nested layouts).  The first
/// existing directory is used; if none match we fall back to `data`.
pub fn resolve_data_dir(explicit: Option<PathBuf>) -> PathBuf {
    if let Some(d) = explicit { return d; }
    for c in ["data", "tamarin-prover/data", "../data", "../../data"] {
        let p = Path::new(c);
        if p.exists() && p.is_dir() {
            if let Ok(abs) = std::fs::canonicalize(p) { return abs; }
            return p.to_path_buf();
        }
    }
    PathBuf::from("data")
}
