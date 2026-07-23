//! Axum router wiring, mirroring `Web.Dispatch`'s route table.

use std::sync::Arc;

use axum::{
    extract::DefaultBodyLimit,
    routing::{get, post},
    Router,
};
use tower_http::trace::TraceLayer;

use crate::handlers;
use crate::state::AppState;

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
        // Static assets: serve `data/` with frontend-dist hoisting —
        // the bundled `frontend/dist/` is served first for the
        // `intdot-*` JS/CSS assets, falling back to `data/`.
        // ----------------------------------------------------------------
        .nest("/static", handlers::static_files::serve(state.clone()))
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
        .layer(upload_limit)
        .layer(TraceLayer::new_for_http())
        .with_state(state)
}
