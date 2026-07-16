//! Shared test harness: spin up a real `axum` server on an ephemeral
//! port with a small fixture theory pre-loaded.  Returns the base URL
//! to hit and a `reqwest` client.
//!
//! Each test uses its own server so they don't share state.

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

use tamarin_server::{
    handlers::static_files::resolve_data_dir,
    router, AppState, ServerConfig, TheoryStore,
};

/// One running test server.
pub struct TestServer {
    pub base: String,
    pub client: reqwest::Client,
    _shutdown_tx: tokio::sync::oneshot::Sender<()>,
    _handle: tokio::task::JoinHandle<()>,
}

impl TestServer {
    pub fn url(&self, path: &str) -> String {
        format!("{}{}", self.base, path)
    }
}

/// Resolve the workspace root from `CARGO_MANIFEST_DIR`
/// (`<repo>/crates/tamarin-server/`).  Used to locate the shared
/// `tamarin-prover/data/` directory in the submodule.
pub fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is `<repo>/crates/tamarin-server`
    let mf = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    mf.parent() // crates
        .and_then(|p| p.parent()) // repo root
        .expect("workspace root above crates/tamarin-server/")
        .to_path_buf()
}

pub fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
}

/// Spawn the server with one theory eagerly loaded.  The server lives
/// until the returned [`TestServer`] is dropped (`oneshot` cancels the
/// listener, then the task exits).
pub async fn start_server_with_theory(fixture_name: &str) -> TestServer {
    let theory_path = fixture_path(fixture_name);
    assert!(
        theory_path.is_file(),
        "fixture {} missing at {}",
        fixture_name, theory_path.display(),
    );

    // Resolve a real data dir if we have one; tests that don't touch
    // /static won't care if it doesn't exist.
    let data_dir = resolve_data_dir(Some(workspace_root().join("tamarin-prover/data")));

    let cfg = ServerConfig {
        bind_addr: "127.0.0.1:0".parse().unwrap(),
        data_dir,
        frontend_dist: None,
        maude_path: detect_maude(),
        max_steps: 200,
        // Match ServerConfig::new's default (HS interactive default 5s).
        derivcheck_timeout: 5,
        stop_on_trace: None,
    };

    // Load theory before starting server.
    let store = TheoryStore::default();
    let entry = tamarin_server::theory_io::load_from_path(
        &theory_path, &detect_maude(), cfg.derivcheck_timeout)
        .expect("fixture should parse + elaborate");
    let _idx = store.insert(entry);

    let state = Arc::new(AppState { cfg, store });
    let app = router(state.clone());

    // Bind to an ephemeral port; remember the resolved socket addr.
    let listener = tokio::net::TcpListener::bind(
        "127.0.0.1:0".parse::<SocketAddr>().unwrap(),
    )
    .await
    .expect("bind to 127.0.0.1:0");
    let addr = listener.local_addr().expect("local_addr after bind");

    let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel::<()>();

    let handle = tokio::spawn(async move {
        let svc = app.into_make_service();
        let _ = axum::serve(listener, svc)
            .with_graceful_shutdown(async move {
                let _ = shutdown_rx.await;
            })
            .await;
    });

    // The listener is bound before we returned; client retries are not
    // needed for in-process axum::serve.
    let base = format!("http://{}", addr);
    let client = reqwest::Client::builder()
        .redirect(reqwest::redirect::Policy::none())
        .timeout(std::time::Duration::from_secs(20))
        .build()
        .expect("build reqwest client");

    TestServer {
        base,
        client,
        _shutdown_tx: shutdown_tx,
        _handle: handle,
    }
}

/// Extract a response header as an owned `String`, or `""` if absent
/// or non-UTF-8.  Used by the header-assertion tests.
#[allow(dead_code)]
pub fn header(res: &reqwest::Response, name: reqwest::header::HeaderName) -> String {
    res.headers()
        .get(name)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("")
        .to_string()
}

/// Convenience wrapper for the most-checked header.
#[allow(dead_code)]
pub fn content_type(res: &reqwest::Response) -> String {
    header(res, reqwest::header::CONTENT_TYPE)
}

/// Absolute Maude locations probed by the test harness, in priority order.
const MAUDE_CANDIDATES: [&str; 3] = [
    "/usr/local/bin/maude",
    "/opt/homebrew/bin/maude",
    "/usr/bin/maude",
];

fn detect_maude() -> String {
    for c in MAUDE_CANDIDATES {
        if std::path::Path::new(c).exists() {
            return c.into();
        }
    }
    "maude".into()
}

/// True when a Maude binary exists at one of [`MAUDE_CANDIDATES`].  Tests
/// that boot a real `ProofContext` use this as a skip-guard.
#[allow(dead_code)]
pub fn maude_available() -> bool {
    MAUDE_CANDIDATES
        .iter()
        .any(|c| std::path::Path::new(c).exists())
}

/// Read a captured Haskell response from `tests/fixtures/haskell-responses/`.
#[allow(dead_code)]
pub fn haskell_capture(name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("haskell-responses")
        .join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read capture {}: {}", path.display(), e))
}

/// Parse a captured Haskell JSON response and return its top-level keys.
/// Used for the "same JSON envelope" assertion.
#[allow(dead_code)]
pub fn haskell_capture_keys(name: &str) -> std::collections::BTreeSet<String> {
    let s = haskell_capture(name);
    let v: serde_json::Value =
        serde_json::from_str(&s).unwrap_or_else(|e| panic!("parse capture {}: {}", name, e));
    json_top_keys(&v)
}

#[allow(dead_code)]
pub fn json_top_keys(v: &serde_json::Value) -> std::collections::BTreeSet<String> {
    match v {
        serde_json::Value::Object(m) => m.keys().cloned().collect(),
        _ => Default::default(),
    }
}
