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
//!     file up in `frontend/dist/` and stream it with `ServeFile`.
//!   - Everything else 404s.
//!
//! We wire the dist-hoisting routes BEFORE the catch-all ServeDir so
//! they take precedence.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use axum::body::Body;
use axum::extract::State;
use axum::handler::HandlerWithoutStateExt;
use axum::http::{header, HeaderMap, Method, Request, StatusCode};
use axum::response::{IntoResponse, Response};
use tower_http::services::{ServeDir, ServeFile};

use crate::state::AppState;

/// Build the static-files router, to be nested at `/static`.
pub fn serve(state: Arc<AppState>) -> axum::Router<Arc<AppState>> {
    let serve_data =
        ServeDir::new(&state.cfg.data_dir).not_found_service(asset_not_found.into_service());
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
    method: Method,
    headers: HeaderMap,
) -> Response {
    dist_or_data(state, "js", ".es.js", name, method, headers).await
}

/// `/static/css/<name>` — the [`intdot_js_or_data`] rule for `intdot-*.css`.
async fn intdot_css_or_data(
    State(state): State<Arc<AppState>>,
    axum::extract::Path(name): axum::extract::Path<String>,
    method: Method,
    headers: HeaderMap,
) -> Response {
    dist_or_data(state, "css", ".css", name, method, headers).await
}

/// Serve `frontend/dist/<name>` for an `intdot-*<suffix>` asset, falling
/// through to `data/<subdir>/<name>` for anything else (or a dist miss).
async fn dist_or_data(
    state: Arc<AppState>,
    subdir: &str,
    suffix: &str,
    name: String,
    method: Method,
    headers: HeaderMap,
) -> Response {
    if name.starts_with("intdot-") && name.ends_with(suffix) {
        if let Some(dist) = &state.cfg.frontend_dist {
            if let Some(resp) = try_file(&dist.join(&name), &method, &headers).await {
                return resp;
            }
        }
    }
    fallback_to_data(state, subdir, &name, &method, &headers).await
}

async fn fallback_to_data(
    state: Arc<AppState>,
    subdir: &str,
    name: &str,
    method: &Method,
    headers: &HeaderMap,
) -> Response {
    let candidate = state.cfg.data_dir.join(subdir).join(name);
    if let Some(resp) = try_file(&candidate, method, headers).await {
        return resp;
    }
    asset_not_found().await
}

/// A missing static asset.  HS serves `/static` from wai-app-static, whose miss
/// is the bare `File not found` — `text/plain` with no charset — and never
/// reaches Yesod's error handler, so this subtree carries no framed page.
async fn asset_not_found() -> Response {
    (
        StatusCode::NOT_FOUND,
        [(header::CONTENT_TYPE, "text/plain")],
        "File not found",
    )
        .into_response()
}

async fn try_file(path: &Path, method: &Method, headers: &HeaderMap) -> Option<Response> {
    let mut request = Request::builder()
        .method(method.clone())
        .uri("/")
        .body(Body::empty())
        .ok()?;
    *request.headers_mut() = headers.clone();
    let response = ServeFile::new(path).try_call(request).await.ok()?;
    if response.status() == StatusCode::NOT_FOUND {
        return None;
    }
    let (parts, body) = response.into_parts();
    Some(Response::from_parts(parts, Body::new(body)))
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
    if let Some(d) = explicit {
        return d;
    }
    for c in ["data", "tamarin-prover/data", "../data", "../../data"] {
        let p = Path::new(c);
        if p.is_dir() {
            if let Ok(abs) = std::fs::canonicalize(p) {
                return abs;
            }
            return p.to_path_buf();
        }
    }
    PathBuf::from("data")
}
