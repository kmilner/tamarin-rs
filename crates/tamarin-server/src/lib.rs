//! HTTP server for the Tamarin prover (Rust port) interactive UI.
//!
//! Goal: serve the existing `frontend/` (TypeScript + d3 + viz-js)
//! and the static assets under `data/` (jQuery, CSS, images) without
//! modifying any frontend code.  The route shape closely mirrors
//! Haskell's `Web.Dispatch` — same URL layout and the same JSON
//! response envelope (`{ html, title }` / `{ alert }` / `{ redirect }`)
//! — with one Rust-specific addition: `/thy/trace/:idx/proof-step/*path`
//! for the progressive UI, which has no counterpart in Haskell's route
//! table (`Web/Types.hs`).
//!
//! Wiring:
//!
//!   `tamarin-prover interactive theory.spthy`  →
//!     - load theory via `tamarin_parser::parse_theory`
//!     - elaborate via `tamarin_theory::elaborate::elaborate`
//!     - boot Maude (`tamarin_term::maude_proc::MaudeHandle`)
//!     - register the theory in a `TheoryStore`
//!     - serve the bundled `frontend/dist/` (+ `data/`) on a TCP port
//!
//! Routes (subset, matching Haskell):
//!
//!   GET  /                                                  RootR
//!   POST /                                                  RootR (file upload)
//!   GET  /thy/trace/<idx>/overview/*path                    InteractiveOverviewR
//!   GET  /thy/trace/<idx>/main/*path                        TheoryPathMR
//!   GET  /thy/trace/<idx>/source                            TheorySourceR
//!   GET  /thy/trace/<idx>/autoprove/<ext>/<bound>/<quit>/*p AutoProverR
//!   GET  /thy/trace/<idx>/unload                            UnloadTheoryR
//!   GET  /static/*                                          StaticR (serve data/ + frontend/dist/)
//!   GET  /favicon.ico                                       FaviconR
//!   GET  /robots.txt                                        RobotsR
//!
//! Implemented: most trace-theory routes are wired (see `routes.rs`),
//! including `overview`, `main`, `source`, `message`, `autoprove`,
//! `autoproveAll`, `verify`, `next`, `prev`, `download`, `reload`,
//! `get_and_append`, `proof-step`, `del/path`, `unload`, and graph
//! rendering (`intdot`/`graph`/`interactive-graph-def` render live SVG
//! via the DOT pipeline, with a DOT-text fallback).
//!
//! Stubs (return a JSON `{alert}` envelope, HTTP 200):
//!   - diff theories (`/thy/equiv/...`)
//!   - lemma editing (`edit`)

// Sanctioned stdout path: the interactive server prints its "server ready at
// …" / "shutting down…" startup+lifecycle messages to stdout by design
// (mirroring HS's `Interactive.hs` ready message).  These are not the batch
// `--prove` byte-parity surface, so `println!` is the intended mechanism and
// the `disallowed_macros` freeze is allowed for this file.
#![allow(clippy::disallowed_macros)]

pub mod graph;
pub mod handlers;
pub mod routes;
pub mod state;
pub mod theory_io;

pub use routes::router;
pub use state::{AppState, TheoryEntry, TheoryStore};

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

/// Configuration for the server.
#[derive(Debug, Clone)]
pub struct ServerConfig {
    /// Address to bind, e.g. `127.0.0.1:3001`.
    pub bind_addr: SocketAddr,
    /// Path to the `data/` directory (CSS, JS, images, fonts).
    pub data_dir: PathBuf,
    /// Path to the bundled frontend output (`frontend/dist/`), if any.
    pub frontend_dist: Option<PathBuf>,
    /// Path to the Maude binary.
    pub maude_path: String,
    /// Proof-search step budget threaded to `prove_lemma` for API
    /// compatibility. Currently a no-op: the solver bounds search by
    /// ID-DFS depth + wall-clock deadline (HS-faithful), so this value
    /// is accepted but ignored.
    pub max_steps: usize,
    /// `--derivcheck-timeout` for the dynamic message-derivation checks
    /// run at theory load (HS interactive default 5s; 0 disables).  Set
    /// from the CLI flag by `interactive` setup.
    pub derivcheck_timeout: u32,
    /// CLI `--stop-on-trace` (None = flag absent).  Merged with each
    /// theory's in-file `configuration:` block at `ProofState::new` time
    /// per HS `closeTheory` precedence (TheoryLoader.hs:640-666): the CLI
    /// value wins; the block is consulted only when this is `None`.
    pub stop_on_trace: Option<tamarin_theory::constraint::solver::context::CutStrategy>,
}

impl ServerConfig {
    pub fn new(bind_addr: SocketAddr, data_dir: PathBuf, maude_path: String) -> Self {
        Self {
            bind_addr,
            data_dir,
            frontend_dist: None,
            maude_path,
            max_steps: 500,
            derivcheck_timeout: 5,
            stop_on_trace: None,
        }
    }
}

/// Start the server, blocking until shutdown.
///
/// Initial theory files (paths) are loaded eagerly.
pub async fn serve(
    cfg: ServerConfig,
    theory_paths: Vec<PathBuf>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // The web UI renders every HTTP response at HS's web width (100/67),
    // not the CLI console width (110/73) — HS `getTheorySourceR` uses
    // `render` (HughesPJ default `style`) and every HTML fragment goes
    // through `renderHtmlDoc`, both width 100.  Set process-wide before
    // any rendering.  (Console-only `renderDoc` at 110 has no HTTP
    // analogue here.)
    tamarin_theory::pretty_hpj::set_display_width(
        tamarin_theory::pretty_hpj::WEB_LINE_LENGTH,
        tamarin_theory::pretty_hpj::WEB_RIBBON,
    );

    // Retain each proof node's constraint `System` after expansion.  The
    // `--prove` CLI drops them post-expansion to keep RSS low (the text
    // proof never reprints a per-node system), but the interactive UI
    // renders the annotated system + applicable proof methods at every
    // proof path — HS keeps a `Just System` on every `IncrementalProof`
    // node.  Must be set before the first `autoprove` runs a search.
    tamarin_theory::constraint::solver::search::set_keep_sys(true);

    let store = TheoryStore::default();

    // Eager-load every command-line theory.  Per-theory stdout reporting
    // mirrors HS `loadTheories` (Web/Dispatch.hs:157-198): a non-empty
    // wellformedness report is echoed via `ppInteractive`
    // (Dispatch.hs:200-209), and a load failure prints the dashed
    // `reportFailure` block (Dispatch.hs:191-198) and skips the theory.
    for p in &theory_paths {
        match theory_io::load_from_path(p, &cfg.maude_path, cfg.derivcheck_timeout) {
            Ok(entry) => {
                let name = entry.name.clone();
                if !entry.wf_report.is_empty() {
                    let dashes = "-".repeat(78);
                    let report = tamarin_theory::pretty_theory::render_wf_error_report(
                        &entry.wf_report,
                    );
                    println!(
                        "{dashes}\nTheory file '{}'\n{dashes}\n\nWARNING: ignoring the following wellformedness errors\n\n{}\n{dashes}\n",
                        p.display(),
                        report.trim_end_matches('\n'),
                    );
                }
                let idx = store.insert(entry);
                tracing::info!(idx, ?name, path = ?p, "loaded theory");
            }
            Err(e) => {
                tracing::error!(error = %e, path = ?p, "failed to load theory");
                let dashes = "-".repeat(78);
                println!(
                    "{dashes}\nUnable to load theory file `{}'\n{dashes}\n\n{}\n{dashes}\n",
                    p.display(),
                    e,
                );
            }
        }
    }

    let state = Arc::new(AppState {
        cfg: cfg.clone(),
        store,
    });

    let app = router(state.clone());
    let listener = tokio::net::TcpListener::bind(cfg.bind_addr).await?;
    // HS ready message (Interactive.hs:104, printed after all theories
    // load, Dispatch.hs:160) — note the trailing space after "at" and the
    // indented URL line.
    println!(
        "Finished loading theories ... server ready at \n\n    http://{}\n",
        cfg.bind_addr,
    );
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await?;
    Ok(())
}

async fn shutdown_signal() {
    let ctrl_c = async { let _ = tokio::signal::ctrl_c().await; };
    #[cfg(unix)]
    let term = async {
        // Degrade gracefully if the SIGTERM handler can't be installed
        // (e.g. resource limits): only ctrl_c drives shutdown, instead
        // of panicking at startup.  Mirrors the non-unix branch.
        match tokio::signal::unix::signal(
            tokio::signal::unix::SignalKind::terminate())
        {
            Ok(mut s) => { s.recv().await; }
            Err(e) => {
                tracing::warn!(error = %e, "could not install SIGTERM handler; \
                    only ctrl_c will trigger shutdown");
                std::future::pending::<()>().await;
            }
        }
    };
    #[cfg(not(unix))]
    let term = std::future::pending::<()>();
    tokio::select! {
        _ = ctrl_c => {}
        _ = term => {}
    }
    println!("\ntamarin-prover: shutting down...");
}
