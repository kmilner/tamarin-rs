//! Static-asset routing.
//!
//! The Haskell server serves `data/css/*` and `data/js/*` (jQuery, CSS,
//! images) from a single `/static/` namespace.  The Rust port does the same
//! with the `ServeDir` of tower-http.  The miss case for `/static` is a
//! separate matter.  HS serves that case from its own wai-app-static WAI app,
//! so the request never reaches the error handler of Yesod.  The test
//! `routes_basic::test_missing_static_asset_matches_haskell` compares that
//! case against the body of the oracle.

mod common;

use common::*;
use std::path::PathBuf;

fn data_dir() -> PathBuf {
    workspace_root().join("tamarin-prover/data")
}

/// Each `/static/<p>` must serve `data/<p>`.  It must serve the exact bytes
/// on disk, under the mime type that `ServeDir` infers.  Every page this
/// crate renders links to the two assets below.
///
/// A missing `data/` is a misconfiguration.  It is not a reason to skip the
/// test.  The directory belongs to the submodule, and the test
/// `haskell_captures_match_the_submodule_pin` already fails without it.
/// Every test binary here carries that test.
#[tokio::test]
async fn test_static_assets_are_served_from_the_data_dir() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (url, rel, mime) in [
        (
            "/static/css/tamarin-prover-ui.css",
            "css/tamarin-prover-ui.css",
            "text/css",
        ),
        // tower-http answers `application/javascript` or `text/javascript`,
        // depending on its mime database.  RFC 9239 allows both answers.
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
