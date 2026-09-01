// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Axum router wiring, mirroring `Web.Dispatch`'s route table.

use std::sync::Arc;

use axum::{
    extract::{DefaultBodyLimit, Request},
    http::StatusCode,
    middleware::Next,
    response::Response,
    routing::{get, post, MethodRouter},
    Router,
};
use percent_encoding::percent_decode_str;
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
    if theory_index_piece(&raw_path).is_some_and(|piece| !reads_as_theory_index(piece)) {
        return handlers::not_found_response(&raw_path);
    }
    let res = next.run(req).await;
    if res.status() == StatusCode::NOT_FOUND {
        return handlers::not_found_response(&raw_path);
    }
    res
}

/// The URL prefixes whose next segment is a theory index — the `/thy/<kind>/`
/// of every route in [`theory_routes`] that captures `{idx}`.
///
/// [`theory_index_piece`] probes exactly these, and
/// `every_idx_route_sits_behind_a_probed_prefix` pins the two together, so a
/// new route family carrying an index cannot quietly lose the probe.
const THEORY_INDEX_PREFIXES: [&str; 2] = ["/thy/trace/", "/thy/equiv/"];

/// The still-encoded theory-index piece of a URL under one of
/// [`THEORY_INDEX_PREFIXES`], for URLs of that shape.
///
/// Split on the raw path, as WAI splits `rawPathInfo` on `/` and only then
/// decodes each segment: an escaped separator (`%2F`) belongs to the piece, it
/// does not end it.
fn theory_index_piece(raw_path: &str) -> Option<&str> {
    let rest = THEORY_INDEX_PREFIXES
        .iter()
        .find_map(|prefix| raw_path.strip_prefix(prefix))?;
    rest.split('/').next()
}

/// Whether an index piece names a theory the port's `usize` route parameter
/// accepts.
///
/// The piece is percent-decoded first, because that is what both sides route
/// on: Yesod dispatches on WAI's `pathInfo`, whose segments are decoded, so
/// `%31` is theory 1 upstream, and axum's `Path` extractor decodes each capture
/// the same way — so this probe and the extractor read every piece alike, and
/// the extractor never sees an index it would answer with a `400`.  A piece
/// whose escapes are not valid UTF-8 names no theory on either side: HS's
/// lenient decode leaves replacement characters that `PathPiece Int` cannot
/// read, and the extractor rejects the capture outright.
fn reads_as_theory_index(piece: &str) -> bool {
    percent_decode_str(piece)
        .decode_utf8()
        .is_ok_and(|idx| idx.parse::<usize>().is_ok())
}

/// The `/thy/…` half of `Web.Dispatch`'s route table, as `(path, handler)`
/// pairs.
///
/// Kept as data rather than a `.route()` chain so the theory-index probe above
/// can be checked against it — every path here that captures `{idx}` has to sit
/// behind a prefix [`theory_index_piece`] recognises.
fn theory_routes() -> Vec<(&'static str, MethodRouter<Arc<AppState>>)> {
    vec![
        // ----------------------------------------------------------------
        // Theory routes (trace lemmas only — diff is stubbed).
        // ----------------------------------------------------------------
        (
            "/thy/trace/{idx}/overview/{*path}",
            get(handlers::theory::interactive_overview),
        ),
        (
            "/thy/trace/{idx}/main/{*path}",
            get(handlers::theory::theory_path_main),
        ),
        ("/thy/trace/{idx}/source", get(handlers::theory::source_)),
        ("/thy/trace/{idx}/message", get(handlers::theory::source_)),
        (
            "/thy/trace/{idx}/autoprove/{extractor}/{bound}/{quit}/{*path}",
            get(handlers::theory::autoprove),
        ),
        (
            "/thy/trace/{idx}/autoproveAll/{extractor}/{bound}/{*path}",
            get(handlers::theory::autoprove_all),
        ),
        (
            "/thy/trace/{idx}/verify/{*path}",
            get(handlers::theory::verify),
        ),
        ("/thy/trace/{idx}/unload", get(handlers::theory::unload)),
        (
            "/thy/trace/{idx}/next/{section}/{*path}",
            get(handlers::theory::next_path),
        ),
        (
            "/thy/trace/{idx}/prev/{section}/{*path}",
            get(handlers::theory::prev_path),
        ),
        (
            "/thy/trace/{idx}/download/{name}",
            get(handlers::theory::download),
        ),
        // -- graph rendering (live: DOT pipeline) --
        (
            "/thy/trace/{idx}/intdot/{*path}",
            get(handlers::theory::intdot),
        ),
        (
            "/thy/trace/{idx}/graph/{*path}",
            get(handlers::theory::graph),
        ),
        (
            "/thy/trace/{idx}/json/{*path}",
            get(handlers::theory::graph_json),
        ),
        (
            "/thy/trace/{idx}/interactive-graph-def/{*path}",
            get(handlers::theory::interactive_graph_def),
        ),
        // -- live proof-tree mutation --
        (
            "/thy/trace/{idx}/proof-step/{*path}",
            get(handlers::theory::proof_step),
        ),
        (
            "/thy/trace/{idx}/edit/{*path}",
            post(handlers::theory::edit_stub),
        ),
        (
            "/thy/trace/{idx}/del/path/{*path}",
            get(handlers::theory::delete_step),
        ),
        ("/thy/trace/{idx}/reload", post(handlers::theory::reload)),
        (
            "/thy/trace/{idx}/get_and_append/{name}",
            post(handlers::theory::append_new_lemmas),
        ),
        // ----------------------------------------------------------------
        // Diff theory routes — stubbed (return alert).
        // ----------------------------------------------------------------
        (
            "/thy/equiv/{idx}/overview/{*path}",
            get(handlers::theory::diff_stub),
        ),
        (
            "/thy/equiv/{idx}/main/{*path}",
            get(handlers::theory::diff_stub),
        ),
    ]
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

    // ----------------------------------------------------------------
    // Root + housekeeping.
    // ----------------------------------------------------------------
    let mut router = Router::new()
        .route("/", get(handlers::root::get).post(handlers::root::post))
        .route("/favicon.ico", get(handlers::root::favicon))
        .route("/robots.txt", get(handlers::root::robots))
        .route("/kill", get(handlers::root::kill_thread));
    for (path, handler) in theory_routes() {
        router = router.route(path, handler);
    }
    router
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

#[cfg(test)]
mod tests {
    use super::*;

    // A route that captures `{idx}` behind a prefix `theory_index_piece` does
    // not recognise would answer a non-numeric index with the `Path`
    // extractor's `400`, where Yesod's routing answers its Not Found page.
    #[test]
    fn every_idx_route_sits_behind_a_probed_prefix() {
        let mut probed = [false; THEORY_INDEX_PREFIXES.len()];
        for (path, _) in theory_routes() {
            if !path.contains("/{idx}") {
                continue;
            }
            let which = THEORY_INDEX_PREFIXES
                .iter()
                .position(|prefix| path.starts_with(prefix))
                .unwrap_or_else(|| panic!("route {path} captures {{idx}} behind no probed prefix"));
            probed[which] = true;
            // End to end: an index the `usize` capture would reject is caught
            // by the probe, so the layer answers the Not Found page.
            let url = path.replace("{idx}", "1x");
            assert_eq!(theory_index_piece(&url), Some("1x"), "probing {url}");
            assert!(!reads_as_theory_index("1x"));
        }
        for (prefix, seen) in THEORY_INDEX_PREFIXES.iter().zip(probed) {
            assert!(
                seen,
                "{prefix} is probed but no route captures an index behind it"
            );
        }
    }
}
