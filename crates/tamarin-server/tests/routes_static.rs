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
use std::sync::atomic::{AtomicU64, Ordering};

fn data_dir() -> PathBuf {
    workspace_root().join("tamarin-prover/data")
}

#[tokio::test]
async fn embedded_gui_serves_page_dependencies_and_cache_validators() {
    let s = start_server_with_theory_and("issue193.spthy", |cfg| {
        cfg.data_dir = None;
    })
    .await;
    let html = s.get("/").await.text().await.unwrap();
    let assets: Vec<_> = html
        .split('"')
        .filter(|value| value.starts_with("/static/"))
        .collect();
    assert!(assets.contains(&"/static/js/intdot-graph.es.js"));
    for path in assets {
        let response = s.get(path).await;
        assert_eq!(response.status(), 200, "{path}");
        if path.ends_with(".js") {
            assert!(content_type(&response).contains("javascript"), "{path}");
        } else if path.ends_with(".css") {
            assert!(content_type(&response).contains("text/css"), "{path}");
        }
        let etag = response.headers()["etag"].clone();
        let bytes = response.bytes().await.unwrap();
        assert!(!bytes.is_empty(), "{path}");
        let cached = s
            .client
            .get(s.url(path))
            .header("if-none-match", etag)
            .send()
            .await
            .unwrap();
        assert_eq!(cached.status(), 304, "{path}");
        assert!(cached.bytes().await.unwrap().is_empty());
        let fresh = s
            .client
            .get(s.url(path))
            .header("if-none-match", "\"old-binary\"")
            .send()
            .await
            .unwrap();
        assert_eq!(fresh.status(), 200, "{path}");
        let head = s.client.head(s.url(path)).send().await.unwrap();
        assert_eq!(head.status(), 200);
        assert_eq!(head.headers()["content-length"], bytes.len().to_string());
        assert!(head.bytes().await.unwrap().is_empty());
    }
    for path in ["/static/unknown.js", "/static/js/..%2Foutside.js"] {
        let response = s.get(path).await;
        assert_eq!(response.status(), 404, "{path}");
        assert_eq!(response.text().await.unwrap(), "File not found", "{path}");
    }
}

/// Each `/static/<p>` must serve `data/<p>`.  It must serve the exact bytes
/// on disk, plus PR #928’s lemma CSS until the submodule includes it. Every page this
/// crate renders links to the two assets below.
///
/// A missing `data/` is a misconfiguration.  It is not a reason to skip the
/// test.  The directory belongs to the submodule, whose checkout is validated
/// separately by `capture_provenance`.
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
        let mut on_disk = std::fs::read_to_string(data_dir().join(rel)).unwrap_or_else(|e| {
            panic!(
                "read {}: {e} — run ./setup.sh to initialise the submodule",
                data_dir().join(rel).display()
            )
        });
        if rel == "css/tamarin-prover-ui.css" {
            on_disk.push_str(include_str!("../src/handlers/lemma_instructions.css"));
        }
        let res = s.get(url).await;
        assert_eq!(res.status(), 200, "{url}");
        let ct = content_type(&res);
        assert!(ct.contains(mime), "{url}: expected {mime} mime, got {ct}");
        let modified = res.headers()["last-modified"].clone();
        assert_eq!(
            res.text().await.expect("read"),
            on_disk,
            "{url} must serve data/{rel} with the upstream CSS fix"
        );
        let cached = s
            .client
            .get(s.url(url))
            .header("if-modified-since", modified)
            .send()
            .await
            .unwrap();
        assert_eq!(cached.status(), 304);
        assert!(cached.bytes().await.unwrap().is_empty());
        let head = s.client.head(s.url(url)).send().await.unwrap();
        assert_eq!(head.status(), 200);
        assert_eq!(head.headers()["content-length"], on_disk.len().to_string());
        assert!(head.bytes().await.unwrap().is_empty());
        let range = s
            .client
            .get(s.url(url))
            .header("range", "bytes=0-5")
            .send()
            .await
            .unwrap();
        assert_eq!(range.status(), 206);
        assert_eq!(range.bytes().await.unwrap(), &on_disk.as_bytes()[..6]);
    }
}

#[tokio::test]
async fn test_frontend_dist_assets_stream_and_fall_back_to_data() {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "tamarin-static-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let dist = root.join("dist");
    let data = root.join("data");
    std::fs::create_dir_all(data.join("js")).unwrap();
    std::fs::create_dir_all(data.join("css")).unwrap();
    std::fs::create_dir_all(&dist).unwrap();
    std::fs::write(dist.join("intdot-graph.es.js"), b"dist-contents").unwrap();
    std::fs::write(dist.join("shared-abc123.js"), b"export const shared = 1;").unwrap();
    std::fs::write(data.join("js/intdot-graph.es.js"), b"data-contents").unwrap();
    std::fs::write(data.join("js/intdot-staticgraph.es.js"), b"fallback-graph").unwrap();
    std::fs::write(data.join("js/ordinary.js"), b"ordinary-data").unwrap();
    std::fs::write(root.join("outside.js"), b"must not be served").unwrap();

    let patched_css = format!(
        "custom {{ color: blue; }}{}",
        include_str!("../src/handlers/lemma_instructions.css")
    );
    std::fs::write(data.join("css/tamarin-prover-ui.css"), &patched_css).unwrap();

    let s = start_server_with_theory_and("issue193.spthy", |cfg| {
        cfg.data_dir = Some(data);
        cfg.frontend_dist = Some(dist);
    })
    .await;

    let dist_response = s
        .client
        .get(s.url("/static/js/intdot-graph.es.js"))
        .header("range", "bytes=5-12")
        .send()
        .await
        .unwrap();
    assert_eq!(dist_response.status(), 206);
    assert_eq!(dist_response.bytes().await.unwrap(), &b"contents"[..]);

    let fallback = s.get("/static/js/ordinary.js").await;
    assert_eq!(fallback.status(), 200);
    assert_eq!(fallback.bytes().await.unwrap(), &b"ordinary-data"[..]);

    let chunk = s.get("/static/js/shared-abc123.js").await;
    assert_eq!(chunk.status(), 200);
    assert!(content_type(&chunk).contains("javascript"));
    assert_eq!(chunk.text().await.unwrap(), "export const shared = 1;");

    let graph_fallback = s.get("/static/js/intdot-staticgraph.es.js").await;
    assert_eq!(graph_fallback.status(), 200);
    assert_eq!(graph_fallback.text().await.unwrap(), "fallback-graph");

    for path in ["/static/js/..%2Foutside.js", "/static/js/..%5Coutside.js"] {
        assert_eq!(s.get(path).await.status(), 404, "{path}");
    }

    let css = s.get("/static/css/tamarin-prover-ui.css").await;
    assert_eq!(css.status(), 200);
    assert_eq!(css.text().await.unwrap(), patched_css);

    drop(s);
    std::fs::remove_dir_all(root).unwrap();
}

#[tokio::test]
async fn missing_gui_assets_fail_before_loading_theories() {
    let dir = tempfile::tempdir().unwrap();
    let cfg = tamarin_server::ServerConfig::new(
        "127.0.0.1:0".parse().unwrap(),
        Some(dir.path().to_path_buf()),
        "unused-maude".into(),
    );
    let error = tamarin_server::serve(cfg, vec![dir.path().join("missing.spthy")])
        .await
        .unwrap_err()
        .to_string();
    assert!(error.contains("GUI assets missing"), "{error}");
    assert!(error.contains("js/jquery.js"), "{error}");
    assert!(error.contains("intdot-graph.es.js"), "{error}");
    assert!(error.contains("Remove --data-dir"), "{error}");
}
