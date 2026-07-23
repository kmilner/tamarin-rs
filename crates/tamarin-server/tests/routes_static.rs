//! Static-asset routing.
//!
//! The Haskell server serves `data/css/*` and `data/js/*` (jQuery,
//! CSS, images) from a single `/static/` namespace.  The Rust port
//! does the same via tower-http's `ServeDir`.  We verify a few
//! known-existing files come back with correct Content-Type.
//!
//! If the workspace `data/` directory isn't present, these tests are
//! skipped (they `print!` a message and return early — they still
//! count as passing).

mod common;

use common::*;
use std::path::PathBuf;

fn data_dir() -> PathBuf {
    workspace_root().join("tamarin-prover/data")
}

#[tokio::test]
async fn test_static_css_served_as_text_css() {
    let path = data_dir().join("css").join("tamarin-prover-ui.css");
    if !path.is_file() {
        eprintln!("skipping: {} not present in workspace", path.display());
        return;
    }
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/static/css/tamarin-prover-ui.css"))
        .send()
        .await
        .expect("send /static/css/...");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/css"), "expected text/css, got {}", ct);
    let body = res.text().await.expect("read");
    assert!(!body.is_empty(), "css file should not be empty");
}

#[tokio::test]
async fn test_static_js_served_as_javascript() {
    let path = data_dir().join("js").join("tamarin-prover-ui.js");
    if !path.is_file() {
        eprintln!("skipping: {} not present in workspace", path.display());
        return;
    }
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/static/js/tamarin-prover-ui.js"))
        .send()
        .await
        .expect("send /static/js/...");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    // tower-http's ServeDir defaults to application/javascript (or
    // text/javascript on some setups).  Either is acceptable per RFC.
    assert!(ct.contains("javascript"), "expected JS mime, got {}", ct);
}

#[tokio::test]
async fn test_static_missing_returns_404() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/static/does-not-exist.txt"))
        .send()
        .await
        .expect("send missing static");
    assert_eq!(res.status(), 404);
}
