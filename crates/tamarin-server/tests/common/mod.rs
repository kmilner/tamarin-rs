// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Shared test harness: spin up a real `axum` server on an ephemeral
//! port with a small fixture theory pre-loaded.  Returns the base URL
//! to hit and a `reqwest` client.
//!
//! Each test uses its own server so they don't share state.

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

use tamarin_server::{
    handlers::static_files::resolve_data_dir, router, AppState, ServerConfig, TheoryStore,
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
    // The same process-wide setup `serve` applies.  Without it the harness
    // runs with the `--prove` CLI defaults: searched proof nodes drop their
    // `System` (so every post-autoprove graph renders empty) and bare
    // `render()` uses the console width instead of the web one.
    tamarin_server::init_process_globals();

    let theory_path = fixture_path(fixture_name);
    assert!(
        theory_path.is_file(),
        "fixture {} missing at {}",
        fixture_name,
        theory_path.display(),
    );

    // Resolve a real data dir if we have one; tests that don't touch
    // /static won't care if it doesn't exist.
    let data_dir = resolve_data_dir(Some(workspace_root().join("tamarin-prover/data")));

    // One probe, shared by the config and the eager load below, so the two
    // cannot disagree about which binary they mean.
    let maude_path = detect_maude();

    let cfg = ServerConfig {
        bind_addr: "127.0.0.1:0".parse().unwrap(),
        data_dir,
        frontend_dist: None,
        maude_path: maude_path.clone(),
        max_steps: 200,
        // Match ServerConfig::new's default (HS interactive default 5s).
        derivcheck_timeout: 5,
        stop_on_trace: None,
        // Match ServerConfig::new's defaults (HS `dotPath`,
        // Environment.hs:37-38, and an absent `--with-json`).
        dot_path: "dot".to_string(),
        json_path: None,
    };

    // Load theory before starting server.
    let store = TheoryStore::default();
    let entry = tamarin_server::theory_io::load_from_path(
        &theory_path,
        &maude_path,
        cfg.derivcheck_timeout,
    )
    .expect("fixture should parse + elaborate");
    let _idx = store.insert(entry);

    let state = Arc::new(AppState { cfg, store });
    let app = router(state.clone());

    // Bind to an ephemeral port; remember the resolved socket addr.
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0".parse::<SocketAddr>().unwrap())
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
/// A `MAUDE_PATH` env var overrides the probe entirely (the convention the
/// rest of the workspace's maude-gated tests follow, and what CI sets).
/// `$PATH` and the linuxbrew prefix are probed after these — see
/// [`resolve_maude`].
const MAUDE_CANDIDATES: [&str; 3] = [
    "/usr/local/bin/maude",
    "/opt/homebrew/bin/maude",
    "/usr/bin/maude",
];

/// Last resort, after the absolute candidates and `$PATH` both miss: the
/// machines here install maude under linuxbrew, which is not on the `$PATH`
/// every shell exports to `cargo test`.
const MAUDE_LINUXBREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The maude this crate's tests run against, or `None` when the machine has
/// none: `$MAUDE_PATH`, else an absolute [`MAUDE_CANDIDATES`] entry, else a
/// `maude` on `$PATH`, else [`MAUDE_LINUXBREW`].
///
/// A `MAUDE_PATH` naming a file that does not exist is a MISCONFIGURATION,
/// not a reason to skip: answering `None` there would turn every
/// maude-backed pin in this crate green on a CI whose image moved maude
/// (`.github/workflows/ci.yml` sets `MAUDE_PATH=/opt/maude/maude`).  Panic
/// instead, so the run goes red.
fn resolve_maude() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?}, or point it at a real maude — skipping \
             every maude-backed pin here would report green vacuously"
        );
        return Some(p);
    }
    for c in MAUDE_CANDIDATES {
        if std::path::Path::new(c).exists() {
            return Some(c.into());
        }
    }
    let on_path = std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|d| d.join("maude"))
            .find(|c| c.is_file())
            .map(|c| c.display().to_string())
    });
    if let Some(p) = on_path {
        return Some(p);
    }
    std::path::Path::new(MAUDE_LINUXBREW)
        .exists()
        .then(|| MAUDE_LINUXBREW.to_string())
}

fn detect_maude() -> String {
    // The bare name is a last resort for a run that got past
    // [`maude_available`] with no maude anywhere (`TAM_ALLOW_NO_MAUDE=1`, or a
    // test that boots a server without consulting the guard): let the spawn
    // fail with the real error rather than inventing a path.
    resolve_maude().unwrap_or_else(|| "maude".into())
}

/// True when a Maude binary is available — [`resolve_maude`] answering
/// `Some`.  Tests that boot a real `ProofContext` use this as a skip-guard.
///
/// With no maude anywhere this PANICS instead of answering `false`: a silent
/// skip makes `cargo test` green identically with and without maude, which is
/// how a maude-backed pin rots unnoticed.  Set `TAM_ALLOW_NO_MAUDE=1` to keep
/// the old skip when that is genuinely what you want.
#[allow(dead_code)]
pub fn maude_available() -> bool {
    if resolve_maude().is_some() {
        return true;
    }
    assert!(
        matches!(std::env::var("TAM_ALLOW_NO_MAUDE").as_deref(), Ok("1")),
        "no maude found: MAUDE_PATH is unset, none of {MAUDE_CANDIDATES:?} \
         exists, $PATH has no `maude` and {MAUDE_LINUXBREW} is missing — the \
         maude-backed pins in this crate would report green having compared \
         nothing.  Install maude, point MAUDE_PATH at it, or set \
         TAM_ALLOW_NO_MAUDE=1 to skip them deliberately."
    );
    false
}

/// The oracle revision the captures under `tests/fixtures/haskell-responses/`
/// were taken from, written by `tests/capture_haskell_fixtures.sh` at the end
/// of a successful capture.
fn captured_oracle_rev() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("haskell-responses")
        .join("oracle_rev");
    std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "read {}: {e} — the capture stamp is missing; re-run \
             crates/tamarin-server/tests/capture_haskell_fixtures.sh",
            path.display()
        )
    })
}

/// Every byte-equality assertion in `routes_*.rs` compares the port against
/// captures of ONE oracle build.  Pin them to the submodule the tests actually
/// run against: `tamarin-prover/`'s checked-out HEAD (the working tree, which
/// is also where the tests read `data/` from — not the recorded gitlink, which
/// a half-finished bump can leave it out of step with).
///
/// git missing, or a submodule that is not a checkout, FAILS here: skipping
/// would leave the whole capture suite comparing against an oracle nobody can
/// name.
#[test]
fn haskell_captures_match_the_submodule_pin() {
    let sub = workspace_root().join("tamarin-prover");
    // Without this, an uninitialised (empty) submodule directory would let
    // `git rev-parse` search UPWARDS and answer the superproject's HEAD.
    assert!(
        sub.join(".git").exists(),
        "{} is not a git checkout — run ./setup.sh to initialise the submodule",
        sub.display()
    );
    let out = std::process::Command::new("git")
        .arg("-C")
        .arg(&sub)
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap_or_else(|e| {
            panic!(
                "run `git -C {} rev-parse HEAD`: {e} — git and an initialised \
                 submodule are required to validate the Haskell captures",
                sub.display()
            )
        });
    assert!(
        out.status.success(),
        "`git -C {} rev-parse HEAD` failed ({}): {} — run ./setup.sh to \
         initialise the submodule",
        sub.display(),
        out.status,
        String::from_utf8_lossy(&out.stderr).trim(),
    );
    let head = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let stamp = captured_oracle_rev();
    let stamped = stamp.trim();
    assert_eq!(
        stamped, head,
        "tests/fixtures/haskell-responses/ was captured from oracle {stamped} \
         but tamarin-prover/ is checked out at {head} — re-run \
         crates/tamarin-server/tests/capture_haskell_fixtures.sh against the \
         pinned oracle and review the diff, or ./setup.sh the submodule back \
         onto the pin"
    );
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

/// GET `path`, assert the status and content type of Yesod's Not Found page,
/// and hand the body back for the caller's own assertion.
#[allow(dead_code)]
async fn not_found_body(s: &TestServer, path: &str) -> String {
    let res = s.client.get(s.url(path)).send().await.expect("send");
    assert_eq!(res.status(), 404, "{path} must be a 404");
    assert_eq!(
        content_type(&res),
        "text/html; charset=utf-8",
        "{path} must carry the Not Found page's content type"
    );
    res.text().await.expect("text")
}

/// Assert that `path` answers Yesod's Not Found page: 404, the error page's
/// content type, and the `defaultErrorHandler` widget — `<h1>Not Found</h1>`
/// over the request's raw path.  Every `notFound` carries this one page
/// (`handlers::mod::not_found_response`), whatever raised it, so this is the
/// shared assertion for the routes that answer a miss without a capture.
#[allow(dead_code)]
pub async fn assert_not_found_page(s: &TestServer, path: &str) {
    let body = not_found_body(s, path).await;
    assert!(
        body.contains(&format!("<h1>Not Found</h1>\n<p>{path}</p>\n")),
        "{path} must carry the Not Found widget over its own path; got: {body}"
    );
}

/// The same page, pinned byte-for-byte against the captured Haskell body.
#[allow(dead_code)]
pub async fn assert_not_found_capture(s: &TestServer, path: &str, capture: &str) {
    assert_eq!(
        not_found_body(s, path).await,
        haskell_capture(capture),
        "{path}"
    );
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

/// The key set a single-field JSON envelope (`{alert}`, `{redirect}`) has.
#[allow(dead_code)]
pub fn one_key_set(k: &str) -> std::collections::BTreeSet<String> {
    std::iter::once(k.to_string()).collect()
}

#[allow(dead_code)]
pub fn json_top_keys(v: &serde_json::Value) -> std::collections::BTreeSet<String> {
    match v {
        serde_json::Value::Object(m) => m.keys().cloned().collect(),
        _ => Default::default(),
    }
}
