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
    #[allow(dead_code)]
    pub state: Arc<AppState>,
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

    let mut cfg = ServerConfig {
        bind_addr: "127.0.0.1:0".parse().unwrap(),
        data_dir,
        frontend_dist: None,
        maude_path: maude_path.clone(),
        // Match ServerConfig::new's default (HS interactive default 5s).
        derivcheck_timeout: 5,
        solver_parameters: Default::default(),
        stop_on_trace: None,
        // Match ServerConfig::new's defaults (HS `dotPath`,
        // Environment.hs:37-38, and an absent `--with-json`).
        dot_path: "dot".to_string(),
        json_path: None,
    };
    mutate(&mut cfg);

    // Load theory before starting server.
    let store = TheoryStore::default();
    let entry = tamarin_server::theory_io::load_from_path(
        &theory_path,
        &maude_path,
        cfg.derivcheck_timeout,
        cfg.solver_parameters,
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
        state,
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

/// True when a Maude binary is available — the guard the tests that boot a
/// real `ProofContext` open with.  With no maude anywhere this PANICS instead
/// of answering `false`; `tamarin_test_support` documents why and names the
/// opt-out.
#[allow(dead_code)]
pub fn maude_available() -> bool {
    tamarin_test_support::maude_available()
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

/// Replace every `HH:MM:SS` run with `<TIME>`.  The pages compared below hold
/// only one such run, the theory's load time.  It appears in `theoryTpl`'s
/// `%T` column and in the `Loaded at …` line of the theory header.
fn blank_times(s: &str) -> String {
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
fn blank_load_stamp(s: &str, fixture: &str) -> String {
    let s = s.replace(&fixture_path(fixture).display().to_string(), "<THEORY>");
    let s = s.replace(&format!("./{fixture}"), "<THEORY>");
    blank_times(&s)
}

/// Compare an HTML page that carries a theory's load stamp against its
/// capture.  Every byte of the template outside the load time and the origin
/// path must be the same as the byte in the oracle's capture.
#[allow(dead_code)]
pub fn assert_page_matches_capture(body: &str, capture: &str, fixture: &str) {
    assert_eq!(
        blank_load_stamp(body, fixture),
        blank_load_stamp(&haskell_capture(capture), fixture),
        "{capture} (load time and origin path blanked)"
    );
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

fn blank_version_banner(s: &str) -> String {
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

/// Compare a `prettyClosedTheory` rendering against its capture.  This
/// function blanks only the build-specific values of the `Generated from:`
/// banner.
///
/// Three routes serve that one document: `getTheorySourceR`
/// (`src/Web/Handler.hs:1015-1022`), `getTheoryMessageDeductionR`
/// (`src/Web/Handler.hs:1050-1055`) and `getDownloadTheoryR`
/// (`src/Web/Handler.hs:1763-1766`).  `getDownloadTheoryR` returns the body of
/// `getTheorySourceR`.
#[allow(dead_code)]
pub fn assert_theory_source_matches_capture(body: &str, capture: &str) {
    assert_eq!(
        blank_version_banner(body),
        blank_version_banner(&haskell_capture(capture)),
        "{capture} (Generated-from banner values blanked)"
    );
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
