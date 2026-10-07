//! Serve the embedded GUI, or an explicit on-disk override for development.
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
//! Assets are embedded at compile time. For an explicit `data_dir` override:
//!   - Serve `data/<rest>` via tower-http `ServeDir`.
//!   - For `js/*.js` and `css/*.css`, look the
//!     file up in `frontend/dist/` and stream it with `ServeFile`.
//!   - Everything else 404s.
//!
//! We wire the dist-hoisting routes BEFORE the catch-all ServeDir so
//! they take precedence.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use axum::body::Body;
use axum::extract::State;
use axum::handler::HandlerWithoutStateExt;
use axum::http::{header, HeaderMap, Method, Request, StatusCode};
use axum::response::{IntoResponse, Response};
use tower_http::services::{ServeDir, ServeFile};

use crate::state::AppState;

include!(concat!(env!("OUT_DIR"), "/gui_assets.rs"));

/// Serve directly from the binary, with content-based validators so an upgraded
/// binary cannot leave an old graph renderer in the browser cache.
async fn embedded_asset(
    axum::extract::Path(path): axum::extract::Path<String>,
    method: Method,
    headers: HeaderMap,
) -> Response {
    let Some(&(_, bytes, etag)) = EMBEDDED_ASSETS.iter().find(|(name, _, _)| *name == path) else {
        return asset_not_found().await;
    };
    let cached = headers
        .get(header::IF_NONE_MATCH)
        .and_then(|value| value.to_str().ok())
        .is_some_and(|value| {
            value.split(',').any(|tag| {
                let tag = tag.trim().strip_prefix("W/").unwrap_or(tag.trim());
                tag == etag || tag == "*"
            })
        });
    let mut response = if cached {
        StatusCode::NOT_MODIFIED.into_response()
    } else {
        let mime = match path.rsplit('.').next().unwrap_or("") {
            "js" => "text/javascript; charset=utf-8",
            "css" => "text/css; charset=utf-8",
            "png" => "image/png",
            "gif" => "image/gif",
            "ico" => "image/x-icon",
            "svg" => "image/svg+xml",
            "json" => "application/json",
            "txt" => "text/plain; charset=utf-8",
            _ => "application/octet-stream",
        };
        let body = if method == Method::HEAD {
            Body::empty()
        } else {
            Body::from(bytes)
        };
        let mut response = body.into_response();
        response
            .headers_mut()
            .insert(header::CONTENT_TYPE, mime.parse().unwrap());
        response
            .headers_mut()
            .insert(header::CONTENT_LENGTH, bytes.len().into());
        response
    };
    response
        .headers_mut()
        .insert(header::ETAG, etag.parse().unwrap());
    response
        .headers_mut()
        .insert(header::CACHE_CONTROL, "no-cache".parse().unwrap());
    response
}

/// Build the static-files router, to be nested at `/static`.
pub fn serve(state: Arc<AppState>) -> axum::Router<Arc<AppState>> {
    let Some(data_dir) = &state.cfg.data_dir else {
        return axum::Router::new()
            .route("/", axum::routing::get(asset_not_found))
            .route("/{*path}", axum::routing::get(embedded_asset))
            .fallback(asset_not_found);
    };
    let serve_data = ServeDir::new(data_dir).not_found_service(asset_not_found.into_service());
    let mut router: axum::Router<Arc<AppState>> = axum::Router::new();

    if state.cfg.frontend_dist.is_some() {
        router = router
            .route("/js/{name}", axum::routing::get(intdot_js_or_data))
            .route("/css/{name}", axum::routing::get(intdot_css_or_data));
    }

    match patched_ui_css(data_dir) {
        Ok(Some(file)) => {
            let service = ServeFile::new(file.path());
            router = router.route(
                "/css/tamarin-prover-ui.css",
                axum::routing::get_service(service).layer(axum::Extension(Arc::new(file))),
            );
        }
        Ok(None) => {}
        Err(error) => {
            tracing::warn!(%error, "Could not prepare lemma CSS; serving original assets")
        }
    }
    router.fallback_service(serve_data)
}

/// Until the submodule includes PR #928, prepare its CSS addition once.
/// The route owns the temporary file and ServeFile supplies normal HTTP caching.
fn patched_ui_css(data_dir: &Path) -> std::io::Result<Option<tempfile::NamedTempFile>> {
    let css = std::fs::read(data_dir.join("css/tamarin-prover-ui.css"))?;
    let instructions = include_bytes!("lemma_instructions.css");
    if css.ends_with(instructions) {
        return Ok(None);
    }
    let mut file = tempfile::Builder::new().suffix(".css").tempfile()?;
    file.write_all(&css)?;
    file.write_all(instructions)?;
    Ok(Some(file))
}

/// `/static/js/<name>` — if the name is `*.js`, serve from
/// the frontend dist; otherwise hand off to `data/js/<name>`.
async fn intdot_js_or_data(
    State(state): State<Arc<AppState>>,
    axum::extract::Path(name): axum::extract::Path<String>,
    method: Method,
    headers: HeaderMap,
) -> Response {
    dist_or_data(state, "js", ".js", name, method, headers).await
}

/// `/static/css/<name>` — the [`intdot_js_or_data`] rule for `*.css`.
async fn intdot_css_or_data(
    State(state): State<Arc<AppState>>,
    axum::extract::Path(name): axum::extract::Path<String>,
    method: Method,
    headers: HeaderMap,
) -> Response {
    dist_or_data(state, "css", ".css", name, method, headers).await
}

/// Serve `frontend/dist/<name>` for a `*<suffix>` asset, falling
/// through to `data/<subdir>/<name>` for anything else (or a dist miss).
async fn dist_or_data(
    state: Arc<AppState>,
    subdir: &str,
    suffix: &str,
    name: String,
    method: Method,
    headers: HeaderMap,
) -> Response {
    // Axum decodes path captures, including escaped separators. Only accept
    // a filename before joining it to either asset directory.
    if name.contains(['/', '\\']) || name == "." || name == ".." {
        return asset_not_found().await;
    }
    // Vite may split shared code into chunks without the intdot- prefix.
    if name.ends_with(suffix)
        && let Some(dist) = &state.cfg.frontend_dist
        && let Some(resp) = try_file(&dist.join(&name), &method, &headers).await
    {
        return resp;
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
    let Some(data_dir) = &state.cfg.data_dir else {
        return asset_not_found().await;
    };
    let candidate = data_dir.join(subdir).join(name);
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
    // Match the old `fs::read(path).ok()?` fallback: a missing or unreadable
    // preferred asset lets the data directory try the same name rather than
    // turning the preferred path's I/O failure into the final response.
    if response.status() == StatusCode::NOT_FOUND || response.status().is_server_error() {
        return None;
    }
    let (parts, body) = response.into_parts();
    Some(Response::from_parts(parts, Body::new(body)))
}

/// Upstream's built graph modules live alongside data/ in frontend/dist/.
pub fn frontend_dist(data_dir: &Path) -> Option<PathBuf> {
    let candidate = data_dir.parent()?.join("frontend/dist");
    candidate.is_dir().then_some(candidate)
}

/// Fail before loading theories when the browser cannot load the GUI.
pub fn validate_assets(data_dir: &Path, dist: Option<&Path>) -> std::io::Result<()> {
    let required = [
        "js/jquery.js",
        "js/jquery-ui.js",
        "js/jquery-layout.js",
        "js/jquery-cookie.js",
        "js/jquery-superfish.js",
        "js/jquery-contextmenu.js",
        "js/tamarin-prover-ui.js",
        "css/tamarin-prover-ui.css",
        "css/jquery-contextmenu.css",
        "css/smoothness/jquery-ui.css",
        "js/intdot-graph.es.js",
        "js/intdot-staticgraph.es.js",
        "js/intdot-dynamicgraph.es.js",
        "css/intdot-style.css",
    ];
    let readable = |path: &Path| {
        std::fs::File::open(path)
            .and_then(|file| file.metadata())
            .is_ok_and(|metadata| metadata.is_file() && metadata.len() > 0)
    };
    let missing: Vec<_> = required
        .into_iter()
        .filter(|rel| {
            let filename = Path::new(rel).file_name().expect("asset filename");
            !(filename.to_string_lossy().starts_with("intdot-")
                && dist.is_some_and(|dir| readable(&dir.join(filename))))
                && !readable(&data_dir.join(rel))
        })
        .collect();
    if missing.is_empty() {
        return Ok(());
    }
    Err(std::io::Error::new(std::io::ErrorKind::NotFound, format!(
        "GUI assets missing or unreadable in {}: {}. Remove --data-dir to use the embedded GUI, or pass --data-dir=/path/to/complete/data (with compiled graph assets in data/js and data/css or a sibling frontend/dist).",
        data_dir.display(), missing.join(", "),
    )))
}
