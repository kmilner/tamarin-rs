// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! HTTP server for the Tamarin prover (Rust port) interactive UI.
//!
//! Goal: serve the existing `frontend/` (TypeScript + d3 + viz-js)
//! and the static assets under `data/` (jQuery, CSS, images), embedded into
//! the binary at compile time. The route shape closely mirrors
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

pub mod cancellation;
pub mod handlers;
pub mod routes;
pub mod state;
pub mod theory_io;
pub mod theory_loader;
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
    /// Optional override for the embedded GUI (CSS, JS, images, fonts).
    pub data_dir: Option<PathBuf>,
    /// Path to the bundled frontend output (`frontend/dist/`), if any.
    pub frontend_dist: Option<PathBuf>,
    /// The CLI's theory-load options, which every web load (startup,
    /// upload, reload) runs with (HS `withWebUI`'s `loadTheory` /
    /// `closeTheory thyLoadOptions` closures, Interactive.hs).
    pub load: theory_loader::TheoryLoadOptions,
    /// CLI `--with-dot` — the GraphViz binary every graph render shells out
    /// to, the bare `"dot"` (resolved through `$PATH`) when the flag is
    /// absent.  That is HS `readOutputCommand`'s `OutDot` branch
    /// (Environment.hs), whose string `dotToImg` invokes verbatim
    /// (Web/Theory.hs).
    pub dot_path: String,
    /// CLI `--with-json` — when given, HS `readOutputCommand` switches to
    /// `OutJSON` (Environment.hs, overriding `--with-dot`) and the
    /// graph route renders through `jsonToImg`: the system's JSON graph is
    /// written to a file and `<json-cmd> <img> <json>` produces the image
    /// (`imgThyPath` → `renderGraphCode`, Web/Theory.hs).
    /// `None` = flag absent, the `dot` pipeline above.
    pub json_path: Option<String>,
    /// Optional allocator cleanup after Stop's callbacks and proof workers finish.
    /// Runs once on a separate thread before Stop responds; must not panic.
    pub cancel_cleanup: Option<fn()>,
}

impl ServerConfig {
    pub fn new(
        bind_addr: SocketAddr,
        data_dir: impl Into<Option<PathBuf>>,
        maude_path: String,
    ) -> Self {
        Self {
            bind_addr,
            data_dir: data_dir.into(),
            frontend_dist: None,
            load: theory_loader::TheoryLoadOptions::new(maude_path),
            dot_path: "dot".to_string(),
            json_path: None,
            cancel_cleanup: None,
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

/// [`serve`] stopped while loading its startup theories: one had
/// wellformedness warnings under `--quit-on-warning`. The report and the
/// abort message are already printed; HS `loadTheories` exits with
/// `exitFailure` here.
#[derive(Debug)]
pub struct QuitOnWarning;

impl std::fmt::Display for QuitOnWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("quit-on-warning mode selected - aborting on wellformedness errors.")
    }
}

impl std::error::Error for QuitOnWarning {}

/// Start the server, blocking until shutdown.
///
/// Initial theory files (paths) are loaded eagerly.
pub async fn serve(
    cfg: ServerConfig,
    theory_paths: Vec<PathBuf>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    if let Some(data_dir) = &cfg.data_dir {
        handlers::static_files::validate_assets(data_dir, cfg.frontend_dist.as_deref())?;
    }
    init_process_globals();

    let store = TheoryStore::default();

    // Eager-load every command-line theory.  Per-theory stdout reporting
    // mirrors HS `loadTheories` (Web/Dispatch.hs): a non-empty
    // wellformedness report is echoed via `ppInteractive`
    // (Dispatch.hs), and a load failure prints the dashed
    // `reportFailure` block (Dispatch.hs) and skips the theory.
    for p in &theory_paths {
        match theory_io::load_from_path(p, &cfg) {
            Ok(entry) => {
                let name = entry.typed_theory.name.clone();
                if !entry.wf_report.is_empty() {
                    println!("{}", pp_interactive(&entry.wf_report, p));
                }
                let idx = store.insert(entry);
                tracing::info!(idx, ?name, path = ?p, "loaded theory");
            }
            Err(theory_io::LoadError::Close(theory_loader::LoadError::Warning(report))) => {
                println!("{}", pp_interactive(&report, p));
                eprintln!("quit-on-warning mode selected - aborting on wellformedness errors.");
                return Err(Box::new(QuitOnWarning));
            }
            Err(theory_io::LoadError::Close(theory_loader::LoadError::UnsupportedInput(
                report,
            ))) => {
                println!("{}", pp_interactive(&report, p));
                println!("Rejected {}: unsupported rule semantics.", p.display());
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
        proof_requests: cancellation::ProofRequests::new(cfg.cancel_cleanup),
    });

    let app = router(state.clone());
    let listener = tokio::net::TcpListener::bind(cfg.bind_addr).await?;
    // HS ready message (Interactive.hs), printed by `loadTheories` after
    // every theory has loaded (Dispatch.hs) — note the
    // trailing space after "at" and the indented URL line.
    println!(
        "Finished loading theories ... server ready at \n\n    http://{}\n",
        listener.local_addr()?,
    );
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await?;
    Ok(())
}

/// HS `ppInteractive` (Web/Dispatch.hs): the load-time report block.
fn pp_interactive(
    report: &[tamarin_theory::wellformedness::WfError],
    path: &std::path::Path,
) -> String {
    let dashes = "-".repeat(78);
    let report = tamarin_theory::pretty_theory::render_wf_error_report(report);
    format!(
        "{dashes}\nTheory file '{}'\n{dashes}\n\nWARNING: ignoring the following wellformedness errors\n\n{}\n{dashes}\n",
        path.display(),
        report.trim_end_matches('\n'),
    )
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
