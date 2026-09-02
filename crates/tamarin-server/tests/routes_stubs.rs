// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Integration tests for the STUBBED routes.
//!
//! This file mixes:
//!   - Live route assertions (compared against Haskell fixtures)
//!   - Genuine stubs, which answer a 200 `{alert}` envelope
//!
//! Coverage matrix:
//!   - GET  /thy/trace/<idx>/graph/*path                  LIVE — SVG or DOT fallback
//!   - POST /thy/trace/<idx>/edit/*path                   ({alert})
//!   - GET  /thy/trace/<idx>/del/path/*path               LIVE — returns {redirect}
//!   - GET  /thy/trace/<idx>/next/<section>/*path         LIVE — text/plain URL
//!   - GET  /thy/trace/<idx>/prev/<section>/*path         LIVE — text/plain URL
//!   - POST /thy/trace/<idx>/get_and_append/<name>        LIVE — returns {alert}
//!   - GET  /thy/trace/<idx>/verify/lemma/<x>             LIVE — returns {html,title}
//!   - GET  /thy/trace/<idx>/verify/proof/<x>             LIVE — returns {redirect}
//!   - GET  /thy/equiv/<idx>/...                          ({alert}; Haskell: 404 HTML — needs ClosedDiffTheory)

mod common;

use common::*;

// ---------------------------------------------------------------------
// Graph routes — LIVE (DOT pipeline).
//
// `graph` renders the system's SVG through `dot`.  It falls back to the DOT
// source when the binary is missing.  `routes_graph.rs` compares the other two
// routes against the oracle's bytes.  Those two routes are `intdot`'s shell
// page and `interactive-graph-def`'s DOT document.
// ---------------------------------------------------------------------
#[tokio::test]
async fn test_graph_returns_image_or_dot() {
    // A proof node — the paths `thyPathSystem` draws.  A lemma / help / rules
    // path is its catch-all `error` instead (see `routes_graph.rs`).
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/graph/proof/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    let body = res.text().await.expect("text");
    // The presence of `dot` decides which of the two answers the server sends.
    // The content type and the body must therefore agree.  `image/svg+xml`
    // carries dot's SVG.  The fallback carries the DOT document that
    // `interactive-graph-def` also serves.
    if ct.starts_with("image/svg+xml") {
        assert!(
            body.contains("<svg") && body.contains("</svg>"),
            "svg content type must carry dot's rendered image; got {}",
            &body[..body.len().min(200)],
        );
    } else {
        assert!(
            ct.starts_with("text/plain"),
            "the only other answer is the DOT fallback; got CT={ct}",
        );
        assert!(
            body.starts_with("digraph \"G\" {\n"),
            "the fallback must be the DOT document itself; got {}",
            &body[..body.len().min(200)],
        );
    }
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
// Haskell `getDeleteStepR` (`src/Web/Handler.hs:1681-1698`) uses
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
    let idx = redir
        .split('/')
        .nth(3)
        .and_then(|value| value.parse::<usize>().ok())
        .expect("redirect idx");
    assert!(
        s.state
            .store
            .get(idx)
            .and_then(|entry| entry.proof_state)
            .is_some(),
        "direct deletion must preserve proofs from the old theory"
    );
    let source = s
        .client
        .get(s.url(&format!("/thy/trace/{idx}/source")))
        .send()
        .await
        .expect("deleted theory source")
        .text()
        .await
        .expect("source body");
    assert!(!source.contains("lemma debug"), "lemma must be removed");
}

#[tokio::test]
async fn deleting_a_lemma_preserves_other_live_proofs() {
    let s = start_server_with_theory("hide_reuse_lemma.spthy").await;
    let removed_step: serde_json::Value = s
        .client
        .get(s.url("/thy/trace/1/del/path/proof/keeps_helper"))
        .send()
        .await
        .expect("mark proof removed")
        .json()
        .await
        .expect("proof redirect");
    let edited_idx = removed_step["redirect"]
        .as_str()
        .and_then(|path| path.split('/').nth(3))
        .and_then(|value| value.parse::<usize>().ok())
        .expect("edited idx");

    let deleted: serde_json::Value = s
        .client
        .get(s.url(&format!("/thy/trace/{edited_idx}/del/path/lemma/helper")))
        .send()
        .await
        .expect("delete lemma")
        .json()
        .await
        .expect("lemma redirect");
    let final_idx = deleted["redirect"]
        .as_str()
        .and_then(|path| path.split('/').nth(3))
        .and_then(|value| value.parse::<usize>().ok())
        .expect("deleted idx");
    let source = s
        .client
        .get(s.url(&format!("/thy/trace/{final_idx}/source")))
        .send()
        .await
        .expect("updated source")
        .text()
        .await
        .expect("source body");
    assert!(!source.contains("lemma helper [reuse]"));
    assert!(source.contains("sorry /* removed */"));
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
    // This is the oracle's body, byte for byte.  The alert allocates no
    // theory, so its bytes do not depend on the capture session's history.
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("del_path_bad.json")
    );

    let missing = s
        .client
        .get(s.url("/thy/trace/999/del/path/rules"))
        .send()
        .await
        .expect("missing theory");
    assert_eq!(missing.status(), 404);
}

#[tokio::test]
async fn test_del_path_missing_targets_return_canonical_alerts() {
    let s = start_server_with_theory("issue193.spthy").await;
    let missing_lemma = s
        .client
        .get(s.url("/thy/trace/1/del/path/lemma/notALemma"))
        .send()
        .await
        .expect("missing lemma");
    assert_eq!(missing_lemma.status(), 200);
    assert_eq!(
        missing_lemma.json::<serde_json::Value>().await.unwrap(),
        serde_json::json!({"alert": "Sorry, but removing the selected lemma failed!"})
    );

    let missing_step = s
        .client
        .get(s.url("/thy/trace/1/del/path/proof/debug/_missing"))
        .send()
        .await
        .expect("missing proof path");
    assert_eq!(missing_step.status(), 200);
    assert_eq!(
        missing_step.json::<serde_json::Value>().await.unwrap(),
        serde_json::json!({"alert": "Sorry, but removing the selected proof step failed!"})
    );
}

#[tokio::test]
async fn test_del_path_proof_marks_removed() {
    let s = start_server_with_theory("issue193.spthy").await;
    let response: serde_json::Value = s
        .client
        .get(s.url("/thy/trace/1/del/path/proof/debug"))
        .send()
        .await
        .expect("delete proof root")
        .json()
        .await
        .expect("redirect JSON");
    let idx = response["redirect"]
        .as_str()
        .and_then(|path| path.split('/').nth(3))
        .and_then(|value| value.parse::<usize>().ok())
        .expect("redirect idx");
    let source = s
        .client
        .get(s.url(&format!("/thy/trace/{idx}/source")))
        .send()
        .await
        .expect("updated source")
        .text()
        .await
        .expect("source body");
    assert!(source.contains("sorry /* removed */"));
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

    assert_eq!(body, haskell_capture("next.txt"));
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
    assert_eq!(body, haskell_capture("prev.txt"));
}

#[tokio::test]
async fn test_next_normal_help_to_message_matches_haskell() {
    // Haskell `next "normal" = nextThyPath` walks Help → Message.
    // Other section strings (like `main`) are no-ops per
    // `next _ = const id` (`src/Web/Handler.hs:1546-1549`).  This
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
async fn nonproof_navigation_does_not_start_the_prover() {
    let s = start_server_with_theory_and("issue193.spthy", |cfg| {
        cfg.maude_path = "/definitely/missing/maude".to_string();
    })
    .await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/next/normal/help"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    assert_eq!(res.text().await.expect("read"), "/thy/trace/1/main/message");
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
    assert_eq!(body, haskell_capture("next_help.txt"));
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
    // `verify/lemma` falls through to the help view.  The envelope is
    // therefore the oracle's `main/help` envelope.  The test compares the
    // complete envelope, except for the header's load stamp.
    assert_page_matches_capture(
        &res.text().await.expect("text"),
        "verify.json",
        "issue193.spthy",
    );
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
    // This is the oracle's body, byte for byte.  `editProof` uses
    // `replaceTheory` at the same idx, so the redirect names theory 1.  There
    // is no fresh allocation, and these bytes are therefore independent of the
    // capture session's history.
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("verify_proof.json")
    );
}

#[tokio::test]
async fn malformed_verify_path_is_not_found_before_theory_lookup() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/999/verify/not-a-path"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 404);
}

#[tokio::test]
async fn test_equiv_overview_stub_returns_alert() {
    // The port does not support diff theories, because that needs
    // `ClosedDiffTheory`.  Haskell answers its Not Found page.  The capture of
    // that page is `haskell-responses/equiv_overview.json`, and it is the one
    // capture that no assertion can consume.  This port answers `{alert}`
    // instead.  That is a documented divergence, to align when diff support
    // lands.
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
