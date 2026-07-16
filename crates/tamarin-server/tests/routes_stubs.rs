//! Integration tests for the STUBBED routes.
//!
//! This file mixes:
//!   - Live route assertions (compared against Haskell fixtures)
//!   - Genuine stubs that still return {alert} or 501
//!
//! Coverage matrix:
//!   - GET  /thy/trace/<idx>/intdot/*path                 LIVE — text/plain DOT
//!   - GET  /thy/trace/<idx>/graph/*path                  LIVE — SVG or DOT fallback
//!   - GET  /thy/trace/<idx>/interactive-graph-def/*path  LIVE — text/plain DOT
//!   - POST /thy/trace/<idx>/edit/*path                   ({alert})
//!   - GET  /thy/trace/<idx>/del/path/*path               LIVE — returns {redirect}
//!   - GET  /thy/trace/<idx>/next/<section>/*path         LIVE — text/plain URL
//!   - GET  /thy/trace/<idx>/prev/<section>/*path         LIVE — text/plain URL
//!   - POST /thy/trace/<idx>/get_and_append/<name>        ({alert})
//!   - GET  /thy/trace/<idx>/autoproveAll/...             LIVE — returns {redirect}
//!   - GET  /thy/trace/<idx>/verify/lemma/<x>             LIVE — returns {html,title}
//!   - GET  /thy/trace/<idx>/verify/proof/<x>             LIVE — returns {redirect}
//!   - GET  /thy/equiv/<idx>/...                          ({alert}; Haskell: 404 HTML — needs ClosedDiffTheory)

mod common;

use common::*;

fn one_key_set(k: &str) -> std::collections::BTreeSet<String> {
    std::iter::once(k.to_string()).collect()
}

// ---------------------------------------------------------------------
// Graph routes — now LIVE (DOT pipeline).
//
// `intdot` returns the HS `intdotLayout` HTML shell page (a
// `<dot-graph-viz>` pointing at `interactive-graph-def`);
// `interactive-graph-def` returns the raw DOT source; `graph` returns
// SVG (or DOT fallback when `dot` is missing).  `intdot` is
// system-agnostic (HS `getInteractiveDotGraphR` only does `withTheory`),
// so it returns the shell for any valid idx+path.
// ---------------------------------------------------------------------
#[tokio::test]
async fn test_intdot_returns_html_shell() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/intdot/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    // HS returns the shell page regardless of whether the path has a
    // system — the `<dot-graph-viz>` fetches the DOT lazily.
    assert!(body.contains("<dot-graph-viz"),
        "intdot must return the HTML shell; got: {}", &body[..body.len().min(200)]);
}

#[tokio::test]
async fn test_graph_returns_image_or_dot() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/graph/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let ct = res.headers().get("content-type").cloned();
    let body = res.text().await.expect("text");
    let ct_str = ct.as_ref().map(|v| v.to_str().unwrap_or("")).unwrap_or("");
    // Accept either SVG or DOT fallback — both are valid responses.
    assert!(
        ct_str.starts_with("image/svg+xml")
            || ct_str.starts_with("text/plain"),
        "unexpected content-type: {:?}", ct_str,
    );
    assert!(
        body.contains("<svg") || body.contains("digraph"),
        "graph response should contain svg or digraph; got {}",
        &body[..body.len().min(200)],
    );
}

#[tokio::test]
async fn test_interactive_graph_def_returns_dot_text() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/interactive-graph-def/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    assert!(body.contains("digraph"));
}

#[tokio::test]
async fn test_edit_stub_returns_alert() {
    // Still stubbed — needs the parser-mutation pipeline.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .post(s.url("/thy/trace/1/edit/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(json_top_keys(&v), one_key_set("alert"));
}

// ---------------------------------------------------------------------
// /del/path/lemma/<name> — LIVE
//
// Haskell `getDeleteStepR` (`src/Web/Handler.hs:1587-1604`) uses
// `modifyTheory` → allocates a new idx and returns
// `{redirect: /thy/trace/<newIdx>/overview/lemma/<name>}`.
// We mirror the SHAPE (new idx + same lemma path); Haskell's exact
// idx depends on session history (capture used idx 5).
// ---------------------------------------------------------------------
#[tokio::test]
async fn test_del_path_lemma_returns_redirect_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/del/path/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");

    // Envelope matches Haskell.
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("del_path.json");
    assert_eq!(
        rust_keys, haskell_keys,
        "del/path keys must match Haskell; rust={:?}, haskell={:?}",
        rust_keys, haskell_keys
    );

    let redir = v.get("redirect").and_then(|t| t.as_str()).unwrap_or("");
    // Same SHAPE as Haskell: /thy/trace/<NEW>/overview/lemma/<name>
    assert!(
        redir.contains("/overview/lemma/debug"),
        "del/path should redirect to lemma view; got {:?}",
        redir
    );
    // And new idx — must NOT reuse the source idx.
    assert!(
        !redir.starts_with("/thy/trace/1/"),
        "del/path must allocate a fresh idx; got {:?}",
        redir
    );
}

#[tokio::test]
async fn test_del_path_unsupported_returns_alert() {
    // Haskell returns {"alert":"Can't delete the given theory path!"}
    // for paths that aren't `lemma` or `proof`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/del/path/rules"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(json_top_keys(&v), one_key_set("alert"));
    let alert = v.get("alert").and_then(|x| x.as_str()).unwrap_or("");
    assert!(
        alert.contains("delete the given theory path"),
        "alert text should mention deletion failure; got {:?}",
        alert,
    );
}

// ---------------------------------------------------------------------
// /next/<section>/<path> + /prev/<section>/<path> — LIVE
//
// Both return text/plain with the URL of the next/prev `/main/...`
// path.  Captured Haskell response for /next/main/lemma/debug:
// `/thy/trace/1/main/lemma/debug` (same path — there's no next sibling
// for a single-lemma theory).
// ---------------------------------------------------------------------
#[tokio::test]
async fn test_next_main_lemma_matches_haskell() {
    // `next/main/lemma/debug` — section "main" is no-op per Haskell's
    // `_ -> const id` fallthrough, so the URL stays at `lemma/debug`.
    // Captured Haskell response: `/thy/trace/1/main/lemma/debug`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/next/main/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
    let body = res.text().await.expect("read body");

    let captured = haskell_capture("next.txt");
    assert_eq!(
        body.trim_end(),
        captured.trim_end(),
        "next/main/lemma must match Haskell verbatim"
    );
}

#[tokio::test]
async fn test_prev_main_lemma_matches_haskell() {
    // Same property: section "main" is a no-op for prev too.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/prev/main/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read body");
    let captured = haskell_capture("prev.txt");
    assert_eq!(
        body.trim_end(),
        captured.trim_end(),
        "prev/main/lemma must match Haskell verbatim"
    );
}

#[tokio::test]
async fn test_next_normal_help_to_message_matches_haskell() {
    // Haskell `next "normal" = nextThyPath` walks Help → Message.
    // Other section strings (like `main`) are no-ops per
    // `next _ = const id` (`src/Web/Handler.hs:1452-1455`).  This
    // test exercises the `normal` arm; the `main` no-op is covered
    // by `test_next_main_help_is_noop_matches_haskell`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/next/normal/help"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read");
    assert_eq!(
        body, "/thy/trace/1/main/message",
        "help → next/normal is `message` (matches Haskell nextThyPath)"
    );
}

#[tokio::test]
async fn test_next_main_help_is_noop_matches_haskell() {
    // Haskell's `next "main"` is the `_ -> const id` arm — same path.
    // Captured Haskell response confirms this.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/next/main/help"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read");
    let captured = haskell_capture("next_help.txt");
    assert_eq!(
        body.trim_end(),
        captured.trim_end(),
        "next/main/help must match Haskell verbatim (no-op when section not normal/smart)"
    );
}

// ---------------------------------------------------------------------
// /autoproveAll/<extractor>/<bound>/*path — LIVE
// ---------------------------------------------------------------------
#[tokio::test]
async fn test_autoprove_all_returns_redirect_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/autoproveAll/idfs/0/proof/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);

    let v: serde_json::Value = res.json().await.expect("decode");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("autoprove_all.json");
    assert_eq!(
        rust_keys, haskell_keys,
        "autoproveAll envelope keys must match Haskell; rust={:?}, haskell={:?}",
        rust_keys, haskell_keys
    );

    let redir = v.get("redirect").and_then(|t| t.as_str()).unwrap_or("");
    // SHAPE check: /thy/trace/<NEW>/overview/proof/<lastLemma>/...
    // For issue193 the only lemma is `debug`.
    assert!(
        redir.contains("/overview/proof/debug"),
        "autoproveAll redirect should point at debug proof view; got {:?}",
        redir
    );
    assert!(
        !redir.starts_with("/thy/trace/1/"),
        "autoproveAll must allocate a fresh idx; got {:?}",
        redir
    );
}

// ---------------------------------------------------------------------
// /verify/*path — LIVE
//
// Haskell:
//   verify/lemma/<x>  → {html, title}   (help fallback)
//   verify/proof/<x>  → {redirect}      (editProof rebuild)
// ---------------------------------------------------------------------
#[tokio::test]
async fn test_verify_lemma_returns_html_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/verify/lemma/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");

    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("verify.json");
    assert_eq!(
        rust_keys, haskell_keys,
        "verify/lemma keys must match Haskell {{html,title}}; rust={:?}, haskell={:?}",
        rust_keys, haskell_keys
    );
    let title = v.get("title").and_then(|t| t.as_str()).unwrap_or("");
    let html = v.get("html").and_then(|t| t.as_str()).unwrap_or("");
    assert!(!title.is_empty());
    assert!(!html.is_empty());
}

#[tokio::test]
async fn test_verify_proof_returns_redirect_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/verify/proof/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(
        json_top_keys(&v),
        one_key_set("redirect"),
        "verify/proof must be {{redirect}} per Haskell editProof success path",
    );
    let redir = v.get("redirect").and_then(|t| t.as_str()).unwrap_or("");
    assert!(
        redir.contains("/overview/proof/debug"),
        "verify redirect should point at the proof view; got {:?}",
        redir
    );
    // Haskell's editProof uses replaceTheory at the SAME idx (no
    // fresh allocation).  Match exactly.
    assert!(
        redir.starts_with("/thy/trace/1/"),
        "verify/proof must reuse the source idx (replaceTheory); got {:?}",
        redir
    );
}

#[tokio::test]
async fn test_equiv_overview_stub_returns_alert() {
    // Diff theories aren't yet ported (needs `ClosedDiffTheory`).
    // Haskell returns 404 HTML; we return {alert} — still a
    // documented divergence to align when diff support lands.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/equiv/1/overview/help"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(json_top_keys(&v), one_key_set("alert"));
}

#[tokio::test]
async fn test_get_and_append_returns_appended_alert() {
    // For a local-origin theory with no "modified" lemmas (our port
    // doesn't yet track that flag), Haskell's branch returns
    // `{alert: "Appended lemmas to <path>"}`.  We mirror exactly.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .post(s.url("/thy/trace/1/get_and_append/whatever"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(json_top_keys(&v), one_key_set("alert"));
    let alert = v.get("alert").and_then(|x| x.as_str()).unwrap_or("");
    assert!(
        alert.starts_with("Appended lemmas to "),
        "alert must say 'Appended lemmas to ...'; got {:?}",
        alert,
    );
    // SHAPE: the path component must include `issue193.spthy`.
    assert!(
        alert.contains("issue193.spthy"),
        "appended-lemmas alert should mention the source file; got {:?}",
        alert,
    );
}
