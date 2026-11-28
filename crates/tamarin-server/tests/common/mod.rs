// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Shared test harness: spin up a real `axum` server on an ephemeral
//! port with a small fixture theory pre-loaded.  Returns the base URL
//! to hit and a `reqwest` client.
//!
//! Each test uses its own server so they don't share state.

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

use tamarin_server::{router, AppState, ServerConfig, TheoryStore};

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

    /// Send a GET to a server-relative path, retaining the path in failures.
    #[allow(dead_code)]
    pub async fn get(&self, path: &str) -> reqwest::Response {
        self.client
            .get(self.url(path))
            .send()
            .await
            .unwrap_or_else(|e| panic!("GET {path}: {e}"))
    }

    /// Send a body-less POST to a server-relative path.
    #[allow(dead_code)]
    pub async fn post(&self, path: &str) -> reqwest::Response {
        self.client
            .post(self.url(path))
            .send()
            .await
            .unwrap_or_else(|e| panic!("POST {path}: {e}"))
    }
}

/// Validate a route's `{redirect}` target and extract its theory index.
#[allow(dead_code)]
pub fn redirect_idx(response: &serde_json::Value, expected_tail: &str) -> usize {
    let path = response["redirect"]
        .as_str()
        .expect("response contains a string redirect");
    let remainder = path
        .strip_prefix("/thy/trace/")
        .expect("redirect starts with /thy/trace/");
    let (index, tail) = remainder
        .split_once('/')
        .expect("redirect contains a theory index and target");
    assert!(
        tail == expected_tail || tail.starts_with(&format!("{expected_tail}/")),
        "redirect {path:?} does not target {expected_tail:?}"
    );
    index
        .parse()
        .expect("redirect contains a numeric theory index")
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

/// The corpus theory most route tests serve (the capture script's too).
#[allow(dead_code)]
pub const ISSUE193: &str = "tamarin-prover/examples/regression/trace/issue193.spthy";

/// Resolve a theory a test serves: a bare file name is one of this crate's
/// `tests/fixtures/`, anything with a `/` is relative to the workspace root
/// (a corpus file) or absolute.
pub fn theory_path(name: &str) -> PathBuf {
    if name.contains('/') {
        workspace_root().join(name)
    } else {
        fixture_path(name)
    }
}

/// Spawn the server with one theory eagerly loaded.  The server lives
/// until the returned [`TestServer`] is dropped (`oneshot` cancels the
/// listener, then the task exits).
#[allow(dead_code)]
pub async fn start_server_with_theory(fixture_name: &str) -> TestServer {
    start_server_with_theory_and(fixture_name, |_| {}).await
}

/// [`start_server_with_theory`] with a config hook: `mutate` runs on the
/// harness defaults before the server stands up (e.g. set `json_path` to a
/// stub renderer for the `--with-json` graph route).
#[allow(dead_code)]
pub async fn start_server_with_theory_and(
    fixture_name: &str,
    mutate: impl FnOnce(&mut ServerConfig),
) -> TestServer {
    // The same process-wide setup `serve` applies.  Without it the harness
    // runs with the `--prove` CLI defaults: searched proof nodes drop their
    // `System` (so every post-autoprove graph renders empty) and bare
    // `render()` uses the console width instead of the web one.
    tamarin_server::init_process_globals();

    let theory_path = theory_path(fixture_name);
    assert!(
        theory_path.is_file(),
        "fixture {} missing at {}",
        fixture_name,
        theory_path.display(),
    );

    // Resolve a real data dir if we have one; tests that don't touch
    // /static won't care if it doesn't exist.
    let data_dir = Some(workspace_root().join("tamarin-prover/data"));

    // One probe, shared by the config and the eager load below, so the two
    // cannot disagree about which binary they mean.
    let maude_path = detect_maude();

    let mut cfg = ServerConfig::new("127.0.0.1:0".parse().unwrap(), data_dir, maude_path.clone());
    mutate(&mut cfg);

    // Load theory before starting server. A web load closes the theory with
    // Maude, so it uses the probed binary even when `mutate` points the
    // server's later proof sessions elsewhere.
    let store = TheoryStore::default();
    let mut load_cfg = cfg.clone();
    load_cfg.load.maude_path = maude_path.clone();
    let entry = tamarin_server::theory_io::load_from_path(&theory_path, &load_cfg)
        .expect("fixture should parse + elaborate");
    let _idx = store.insert(entry);

    let proof_requests = tamarin_server::cancellation::ProofRequests::new(cfg.cancel_cleanup);
    let state = Arc::new(AppState {
        cfg,
        store,
        proof_requests,
    });
    let app = router(state);

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

/// The maude the harness hands the server, with a bare `maude` as the last
/// resort for a run that got past [`maude_available`] with none resolved
/// (`TAM_ALLOW_NO_MAUDE=1`, or a test that boots a server without consulting
/// the guard): let the spawn fail with the real error rather than inventing a
/// path.
fn detect_maude() -> String {
    tamarin_test_support::maude_path().unwrap_or_else(|| "maude".into())
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

/// Replace every `HH:MM:SS` run with `<TIME>`.  The pages compared below hold
/// only one such run, the theory's load time.  It appears in `theoryTpl`'s
/// `%T` column and in the `Loaded at …` line of the theory header.
pub fn blank_times(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < b.len() {
        let is_time = i + 8 <= b.len()
            && b[i..i + 8].iter().zip(b"00:00:00").all(|(c, k)| {
                if *k == b':' {
                    *c == b':'
                } else {
                    c.is_ascii_digit()
                }
            });
        if is_time {
            out.push_str("<TIME>");
            i += 8;
            continue;
        }
        let ch = s[i..].chars().next().expect("char boundary");
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Blank the two fields that a captured page cannot share with a test run.
/// The first field is the theory's load time.  The second field is the
/// theory's origin path.  The oracle serves `./<fixture>` out of its own work
/// directory (see `tests/capture_haskell_fixtures.sh`).  The harness loads the
/// fixture by absolute path.
#[allow(dead_code)]
pub fn blank_load_stamp(s: &str, fixture: &str) -> String {
    let path = theory_path(fixture);
    let name = path
        .file_name()
        .expect("theory file name")
        .to_string_lossy();
    let s = s.replace(&path.display().to_string(), "<THEORY>");
    let s = s.replace(&format!("./{name}"), "<THEORY>");
    blank_times(&s)
}

/// The build-specific lines of the `Generated from:` block.  The oracle's
/// values are its own Maude version, its own git revision and its own build
/// timestamp.  No test run can reproduce those values.  The comparison still
/// covers the prefixes themselves.
///
/// The port writes these three values as empty strings on the live routes.
/// `handlers::theory::render_theory_source` builds a `BuildInfo` with an empty
/// `maude_version`, `git_revision`, `git_branch` and `compiled_at`.  This is a
/// recorded divergence that waits for a production fix.  The blanking hides
/// the divergence, so a pass here does not show parity on these lines.  After
/// the fix lands, make these prefixes stricter and compare the values that the
/// batch binary already fills in.
const VERSION_BANNER_PREFIXES: [&str; 3] = ["Maude version", "Git revision:", "Compiled at:"];

#[allow(dead_code)]
pub fn blank_version_banner(s: &str) -> String {
    s.split_inclusive('\n')
        .map(|line| {
            let (text, nl) = match line.strip_suffix('\n') {
                Some(t) => (t, "\n"),
                None => (line, ""),
            };
            match VERSION_BANNER_PREFIXES
                .iter()
                .find(|p| text.starts_with(**p))
            {
                Some(p) => format!("{p}<BUILD>{nl}"),
                None => line.to_string(),
            }
        })
        .collect()
}
