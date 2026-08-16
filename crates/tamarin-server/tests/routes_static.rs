//! Static-asset routing.
//!
//! The Haskell server serves `data/css/*` and `data/js/*` (jQuery, CSS,
//! images) from a single `/static/` namespace; the Rust port does the same via
//! tower-http's `ServeDir`.  The `/static` miss is a separate matter — HS
//! serves it from its own wai-app-static WAI app, so it never reaches Yesod's
//! error handler — and is pinned against the oracle's body by
//! `routes_basic::test_missing_static_asset_matches_haskell`.

mod common;

use common::*;
use std::path::PathBuf;

fn data_dir() -> PathBuf {
    workspace_root().join("tamarin-prover/data")
}

/// Each `/static/<p>` must serve `data/<p>` — the exact bytes on disk, under
/// the mime `ServeDir` infers.  The two assets below are the ones every page
/// this crate renders links to.
///
/// A missing `data/` is a MISCONFIGURATION, not a reason to skip: the
/// directory is the submodule's, and `haskell_captures_match_the_submodule_pin`
/// (which every test binary here carries) already fails without it.
#[tokio::test]
async fn test_static_assets_are_served_from_the_data_dir() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (url, rel, mime) in [
        (
            "/static/css/tamarin-prover-ui.css",
            "css/tamarin-prover-ui.css",
            "text/css",
        ),
        // tower-http answers `application/javascript` or `text/javascript`
        // depending on its mime database; either is correct per RFC 9239.
        (
            "/static/js/tamarin-prover-ui.js",
            "js/tamarin-prover-ui.js",
            "javascript",
        ),
    ] {
        let on_disk = std::fs::read_to_string(data_dir().join(rel)).unwrap_or_else(|e| {
            panic!(
                "read {}: {e} — run ./setup.sh to initialise the submodule",
                data_dir().join(rel).display()
            )
        });
        let res = s.client.get(s.url(url)).send().await.expect("send");
        assert_eq!(res.status(), 200, "{url}");
        let ct = content_type(&res);
        assert!(ct.contains(mime), "{url}: expected {mime} mime, got {ct}");
        assert_eq!(
            res.text().await.expect("read"),
            on_disk,
            "{url} must serve data/{rel} verbatim"
        );
    }
}
