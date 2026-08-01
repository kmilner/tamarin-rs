//! Axum router wiring, mirroring `Web.Dispatch`'s route table.

use std::sync::Arc;

use axum::{
    extract::{DefaultBodyLimit, Request},
    http::StatusCode,
    middleware::Next,
    response::Response,
    routing::{get, post},
    Router,
};
use tower_http::trace::TraceLayer;

use crate::handlers;
use crate::state::AppState;

/// Render every `404` this router produces as Yesod's Not Found page.
///
/// Yesod raises `notFound` as an error response and renders it centrally in
/// `defaultErrorHandler`, which has the request at hand and embeds its
/// `rawPathInfo` in the page; the handlers themselves only decide *that* the
/// request is a miss.  The port keeps that split: handlers answer with a bare
/// `404` status, and this layer turns each one — plus the routing-level miss
/// for a URL that matches no route at all — into the page.
///
/// The `/static` subtree is nested after this layer is applied, so it keeps its
/// own `File not found`, as in HS, where the static route is a separate
/// wai-app-static WAI app that Yesod's error handler never sees.
async fn not_found_page(req: Request, next: Next) -> Response {
    // `Uri::path` is the raw, still-percent-encoded path, query excluded —
    // WAI's `rawPathInfo`.
    let raw_path = req.uri().path().to_owned();
    // The theory-index route piece is `#Int` (`src/Web/Types.hs:580-616`), and
    // Yesod's `PathPiece Int` takes an optional sign and decimal digits that
    // fit an `Int`, nothing else: `01` and `+1` are theory 1, while `1x`, ` 1`,
    // `(1)` and an over-long literal make the route not match at all, so
    // routing answers `notFound`.  A piece that parses but is negative is a
    // theory that was never issued, which the handlers answer with the same
    // miss — so every index the port's `usize` route parameter would reject
    // lands on this page, never on a path-extractor 400.
    if theory_index_piece(&raw_path).is_some_and(|piece| piece.parse::<usize>().is_err()) {
        return handlers::not_found_response(&raw_path);
    }
    let res = next.run(req).await;
    if res.status() == StatusCode::NOT_FOUND {
        return handlers::not_found_response(&raw_path);
    }
    res
}

/// The theory-index piece of a `/thy/trace/<idx>/…` or `/thy/equiv/<idx>/…`
/// URL, for URLs of that shape.
fn theory_index_piece(raw_path: &str) -> Option<&str> {
    let rest = raw_path.strip_prefix("/thy/")?;
    let rest = rest
        .strip_prefix("trace/")
        .or_else(|| rest.strip_prefix("equiv/"))?;
    rest.split('/').next()
}

pub fn router(state: Arc<AppState>) -> Router {
    // Serving HTTP means an oracle exec failure is request-scoped, not
    // process-fatal (HS confines the `readProcess` exception to the Warp
    // request thread).  `run_interactive` sets this before theory load;
    // repeating it here covers in-process embedders and the test harness,
    // which build the router directly.
    tamarin_theory::constraint::solver::search::ORACLE_ERROR_UNWINDS
        .store(true, std::sync::atomic::Ordering::Relaxed);

    // 100 MB upload cap — generous, but bounded.
    let upload_limit = DefaultBodyLimit::max(100 * 1024 * 1024);

    Router::new()
        // ----------------------------------------------------------------
        // Root + housekeeping.
        // ----------------------------------------------------------------
        .route("/", get(handlers::root::get).post(handlers::root::post))
        .route("/favicon.ico", get(handlers::root::favicon))
        .route("/robots.txt", get(handlers::root::robots))
        .route("/kill", get(handlers::root::kill_thread))
        // ----------------------------------------------------------------
        // Theory routes (trace lemmas only — diff is stubbed).
        // ----------------------------------------------------------------
        .route(
            "/thy/trace/:idx/overview/*path",
            get(handlers::theory::interactive_overview),
        )
        .route(
            "/thy/trace/:idx/main/*path",
            get(handlers::theory::theory_path_main),
        )
        .route("/thy/trace/:idx/source", get(handlers::theory::source_))
        .route(
            "/thy/trace/:idx/message",
            get(handlers::theory::message_deduction),
        )
        .route(
            "/thy/trace/:idx/autoprove/:extractor/:bound/:quit/*path",
            get(handlers::theory::autoprove),
        )
        .route(
            "/thy/trace/:idx/autoproveAll/:extractor/:bound/*path",
            get(handlers::theory::autoprove_all),
        )
        .route(
            "/thy/trace/:idx/verify/*path",
            get(handlers::theory::verify),
        )
        .route("/thy/trace/:idx/unload", get(handlers::theory::unload))
        .route(
            "/thy/trace/:idx/next/:section/*path",
            get(handlers::theory::next_path),
        )
        .route(
            "/thy/trace/:idx/prev/:section/*path",
            get(handlers::theory::prev_path),
        )
        .route(
            "/thy/trace/:idx/download/:name",
            get(handlers::theory::download),
        )
        // -- graph rendering (live: DOT pipeline) --
        .route(
            "/thy/trace/:idx/intdot/*path",
            get(handlers::theory::intdot),
        )
        .route("/thy/trace/:idx/graph/*path", get(handlers::theory::graph))
        .route(
            "/thy/trace/:idx/json/*path",
            get(handlers::theory::graph_json),
        )
        .route(
            "/thy/trace/:idx/interactive-graph-def/*path",
            get(handlers::theory::interactive_graph_def),
        )
        // -- live proof-tree mutation --
        .route(
            "/thy/trace/:idx/proof-step/*path",
            get(handlers::theory::proof_step),
        )
        .route(
            "/thy/trace/:idx/edit/*path",
            post(handlers::theory::edit_stub),
        )
        .route(
            "/thy/trace/:idx/del/path/*path",
            get(handlers::theory::delete_step),
        )
        .route("/thy/trace/:idx/reload", post(handlers::theory::reload))
        .route(
            "/thy/trace/:idx/get_and_append/:name",
            post(handlers::theory::append_new_lemmas),
        )
        // ----------------------------------------------------------------
        // Diff theory routes — stubbed (return alert).
        // ----------------------------------------------------------------
        .route(
            "/thy/equiv/:idx/overview/*path",
            get(handlers::theory::diff_stub),
        )
        .route(
            "/thy/equiv/:idx/main/*path",
            get(handlers::theory::diff_stub),
        )
        // Every miss among the routes above — and the routing-level miss for a
        // URL matching none of them — is rendered as Yesod's Not Found page.
        .layer(axum::middleware::from_fn(not_found_page))
        // ----------------------------------------------------------------
        // Static assets: serve `data/` with frontend-dist hoisting —
        // the bundled `frontend/dist/` is served first for the
        // `intdot-*` JS/CSS assets, falling back to `data/`.  Nested after
        // the layer above, so a missing asset keeps wai-app-static's own
        // `File not found` (HS serves `/static` from that separate WAI app).
        // ----------------------------------------------------------------
        .nest("/static", handlers::static_files::serve(state.clone()))
        .layer(upload_limit)
        .layer(TraceLayer::new_for_http())
        .with_state(state)
}
