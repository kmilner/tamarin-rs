// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HTTP server for the Tamarin prover (Rust port) interactive UI.
//!
//! Goal: serve the existing `frontend/` (TypeScript + d3 + viz-js)
//! and the static assets under `data/` (jQuery, CSS, images) without
//! modifying any frontend code.  The route shape closely mirrors
//! Haskell's `Web.Dispatch` — same URL layout and the same JSON
//! response envelope (`{ html, title }` / `{ alert }` / `{ redirect }`)
//! used by the progressive UI.
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
//! `get_and_append`, `del/path`, `unload`, and graph
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

pub mod handlers;
pub mod routes;
pub mod state;
pub mod theory_io;
// `Web.Utils`' `abbrev` is reached only from the JSON graph handler; nothing
// outside this crate names it.
pub(crate) mod web_utils_abbrev;

pub use routes::router;
pub use state::{AppState, StoreError, TheoryEntry, TheorySnapshot, TheoryStore};

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
    /// `--derivcheck-timeout` for the dynamic message-derivation checks
    /// run at theory load (HS interactive default 5s; 0 disables).  Set
    /// from the CLI flag by `interactive` setup.
    pub derivcheck_timeout: u32,
    /// Source-solver limits from `-c/--open-chains` and `-s/--saturation`.
    pub solver_parameters: tamarin_theory::constraint::solver::sources::IntegerParameters,
    /// CLI `--stop-on-trace` (None = flag absent).  Merged with each
    /// theory's in-file `configuration:` block at `ProofState::new` time
    /// per HS `closeTheory`'s `configStopOnTrace` (TheoryLoader.hs:759-763):
    /// the CLI value wins; the block is consulted only when this is `None`.
    pub stop_on_trace: Option<tamarin_theory::constraint::solver::context::CutStrategy>,
    /// CLI `--with-dot` — the GraphViz binary every graph render shells out
    /// to, the bare `"dot"` (resolved through `$PATH`) when the flag is
    /// absent.  That is HS `readOutputCommand`'s `OutDot` branch
    /// (Environment.hs:41-45), whose string `dotToImg` invokes verbatim
    /// (Web/Theory.hs:1494-1497).
    pub dot_path: String,
    /// CLI `--with-json` — when given, HS `readOutputCommand` switches to
    /// `OutJSON` (Environment.hs:41-45, overriding `--with-dot`) and the
    /// graph route renders through `jsonToImg`: the system's JSON graph is
    /// written to a file and `<json-cmd> <img> <json>` produces the image
    /// (`imgThyPath` → `renderGraphCode`, Web/Theory.hs:1404-1412, 1484-1491).
    /// `None` = flag absent, the `dot` pipeline above.
    pub json_path: Option<String>,
    /// Options applied consistently to every startup, upload, and reload.
    pub theory_load: TheoryLoadOptions,
}

/// CLI-derived options captured by the interactive theory loader.
#[derive(Debug, Clone)]
pub struct TheoryLoadOptions {
    /// Run the no-deconstruction-chain check.
    pub ndc_check: bool,
    /// CLI `--prove`/`--lemma` selections copied into each theory.
    pub lemmas_to_prove: Vec<String>,
    /// Parser defines and warning behavior.
    pub parser_flags: Vec<String>,
}

impl Default for TheoryLoadOptions {
    fn default() -> Self {
        Self {
            ndc_check: true,
            lemmas_to_prove: Vec::new(),
            parser_flags: Vec::new(),
        }
    }
}

impl ServerConfig {
    pub fn new(bind_addr: SocketAddr, data_dir: PathBuf, maude_path: String) -> Self {
        Self {
            bind_addr,
            data_dir,
            frontend_dist: None,
            maude_path,
            derivcheck_timeout: 5,
            solver_parameters:
                tamarin_theory::constraint::solver::sources::IntegerParameters::default(),
            stop_on_trace: None,
            dot_path: "dot".to_string(),
            json_path: None,
            theory_load: TheoryLoadOptions::default(),
        }
    }
}

/// Apply the process-wide rendering width the web UI depends on.
pub fn init_process_globals() {
    // The web UI renders every HTTP response at HS's web width (100/67),
    // not the CLI console width (110/73) — HS `getTheorySourceR` uses
    // `render` (HughesPJ default `style`) and every HTML fragment goes
    // through `renderHtmlDoc`, both width 100.  Set process-wide before
    // any rendering.  (Console-only `renderDoc` at 110 has no HTTP
    // analogue here.)
    tamarin_theory::pretty_hpj::set_display_width(
        tamarin_theory::pretty_hpj::DEFAULT_LINE_LENGTH,
        tamarin_theory::pretty_hpj::DEFAULT_RIBBON,
    );
}

/// Start the server, blocking until shutdown.
///
/// Initial theory files (paths) are loaded eagerly.
pub async fn serve(
    cfg: ServerConfig,
    theory_paths: Vec<PathBuf>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    init_process_globals();

    let store = TheoryStore::default();

    // Eager-load every command-line theory.  Per-theory stdout reporting
    // mirrors HS `loadTheories` (Web/Dispatch.hs:160-212): a non-empty
    // wellformedness report is echoed via `ppInteractive`
    // (Dispatch.hs:203-212), and a load failure prints the dashed
    // `reportFailure` block (Dispatch.hs:194-201) and skips the theory.
    for p in &theory_paths {
        match theory_io::load_from_path(p, &cfg) {
            Ok(entry) => {
                let name = entry.typed_theory.name.clone();
                if !entry.wf_report.is_empty() {
                    let dashes = "-".repeat(78);
                    let report =
                        tamarin_theory::pretty_theory::render_wf_error_report(&entry.wf_report);
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
    // HS ready message (Interactive.hs:125), printed by `loadTheories` after
    // every theory has loaded (Dispatch.hs:160-164, see line 163) — note the
    // trailing space after "at" and the indented URL line.
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
    let ctrl_c = async {
        let _ = tokio::signal::ctrl_c().await;
    };
    #[cfg(unix)]
    let term = async {
        // Degrade gracefully if the SIGTERM handler can't be installed
        // (e.g. resource limits): only ctrl_c drives shutdown, instead
        // of panicking at startup.  Mirrors the non-unix branch.
        match tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate()) {
            Ok(mut s) => {
                s.recv().await;
            }
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
