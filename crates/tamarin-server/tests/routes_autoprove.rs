//! Integration tests that exercise the autoprove endpoint.
//!
//! These tests run the actual Rust solver via `prove_lemma` and so
//! need a working `maude` binary on PATH (any common location detected
//! by `start_server_with_theory`).  They are tagged with the small
//! `issue193.spthy` fixture because it has only one trivial
//! exists-trace lemma (`debug`) that the solver dispatches in well
//! under a second.

mod common;

use common::*;

// ---------------------------------------------------------------------
// /thy/trace/<idx>/autoprove/<extractor>/<bound>/<quit>/proof/<lemma>
// ---------------------------------------------------------------------
//
// Haskell URL shape: /autoprove/idfs/0/False/proof/debug  (Bool is
// capitalised — Yesod `PathPiece Bool` accepts ONLY `True`/`False`).
//
// The Rust port matches that exactly:
//   - capital `True`/`False` → handler runs
//   - anything else → 404 HTML (Haskell's behaviour)
// See `parse_bool_path_piece` in `src/handlers/theory.rs`.

#[tokio::test]
async fn test_autoprove_returns_redirect_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;

    // The `debug` lemma is exists-trace + trivial; Rust autoprove
    // should redirect to the proof view on success.
    let url = s.url("/thy/trace/1/autoprove/idfs/0/False/proof/debug");
    let res = s.client.get(&url).send().await.expect("send autoprove");
    assert_eq!(res.status(), 200, "autoprove should return 200");

    let ct = content_type(&res);
    assert!(
        ct.starts_with("application/json"),
        "autoprove must reply JSON, got {}",
        ct
    );

    let v: serde_json::Value = res.json().await.expect("decode json");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("autoprove.json");
    assert_eq!(
        rust_keys, haskell_keys,
        "autoprove envelope keys must match Haskell; rust={:?}, haskell={:?}",
        rust_keys, haskell_keys
    );

    let redir = v.get("redirect").and_then(|t| t.as_str()).unwrap_or("");

    // SHAPE assertions (not byte equality — Haskell's
    // `nextSmartThyPath` produces e.g.
    // `/thy/trace/2/overview/proof/debug/_/ONE/ONE` for issue193
    // because the solver's tree has a `ONE` case after autoprove.
    // Our Rust solver returns only a status, so we land at the root
    // (`/_`), but both share the same prefix and the same
    // "NEW idx" semantics.  The frontend dispatcher works on both.
    assert!(
        redir.starts_with("/thy/trace/"),
        "redirect should start at /thy/trace/...; got {:?}",
        redir
    );
    assert!(
        redir.contains("/overview/proof/debug"),
        "redirect should point at the new-idx proof view for lemma `debug`; got {:?}",
        redir
    );
    // Most importantly: Haskell's behaviour is to allocate a NEW idx
    // for the post-autoprove snapshot — the URL must NOT reuse idx 1
    // (the pre-autoprove theory).  Same property holds in our port.
    assert!(
        !redir.starts_with("/thy/trace/1/"),
        "autoprove should allocate a fresh idx (not reuse 1); got {:?}",
        redir
    );
}

#[tokio::test]
async fn test_autoprove_url_with_lowercase_quit_returns_404() {
    // Haskell's Yesod `PathPiece Bool` parser rejects lowercase
    // `true`/`false`.  We MUST mirror that — if our router accepted
    // lowercase silently the same frontend URL builder would emit URLs
    // that don't work against Haskell.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/autoprove/idfs/0/false/proof/debug"))
        .send()
        .await
        .expect("send autoprove with lowercase quit");
    assert_eq!(
        res.status(),
        404,
        "lowercase quit must 404 (matches Haskell PathPiece Bool)"
    );
}

#[tokio::test]
async fn test_autoprove_on_bad_path_returns_alert() {
    let s = start_server_with_theory("issue193.spthy").await;
    // `rules` is not a valid path target for autoprove (it's not a
    // lemma / proof / method); Haskell returns alert, ours does too.
    let url = s.url("/thy/trace/1/autoprove/idfs/0/False/rules");
    let res = s.client.get(&url).send().await.expect("send autoprove-rules");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    let keys = json_top_keys(&v);
    let one: std::collections::BTreeSet<String> =
        std::iter::once("alert".to_string()).collect();
    assert_eq!(keys, one, "autoprove on non-lemma path should be {{alert}}");

    // The captured Haskell alert is exactly
    // "Can't run the autoprover () on the given theory path!" — we
    // emit the same string for byte-equal comparison.
    let captured = haskell_capture("autoprove_on_rules.json");
    let captured_v: serde_json::Value =
        serde_json::from_str(&captured).expect("parse captured");
    assert_eq!(
        v.get("alert").and_then(|x| x.as_str()),
        captured_v.get("alert").and_then(|x| x.as_str()),
        "alert text must match Haskell verbatim",
    );
}

#[tokio::test]
async fn test_autoprove_with_missing_idx_returns_404_html() {
    // Match Haskell: bad theory idx returns 404 HTML (see
    // `withTheory` / `notFound` in `src/Web/Handler.hs:660-666`).
    let s = start_server_with_theory("issue193.spthy").await;
    let url = s.url("/thy/trace/99/autoprove/idfs/0/False/proof/debug");
    let res = s.client.get(&url).send().await.expect("send");
    assert_eq!(res.status(), 404);
    let ct = content_type(&res);
    assert!(
        ct.starts_with("text/html"),
        "missing-idx 404 must be text/html (matches Haskell); got {}",
        ct
    );
}

#[tokio::test]
async fn test_autoprove_on_unknown_lemma_returns_alert() {
    // Probed Haskell behaviour: unknown lemma returns the canonical
    // alert "Sorry, but the autoprover () failed!" via
    // `modifyTheory`'s `Right Nothing` arm — the prover-name part is
    // empty for the default `getProverR` instantiation.  We mirror.
    let s = start_server_with_theory("issue193.spthy").await;
    let url = s.url("/thy/trace/1/autoprove/idfs/0/False/proof/notALemma");
    let res = s.client.get(&url).send().await.expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    let keys = json_top_keys(&v);
    let one: std::collections::BTreeSet<String> =
        std::iter::once("alert".to_string()).collect();
    assert_eq!(keys, one, "unknown-lemma autoprove must be {{alert}}");
    let alert = v.get("alert").and_then(|x| x.as_str()).unwrap_or("");
    assert!(
        alert.contains("Sorry") && alert.contains("autoprover"),
        "alert text should match the Haskell shape; got {:?}",
        alert
    );
}
// Web-parity regression: after autoprove, `main/proof/<lemma>` must render
// the "Applicable Proof Methods" + sequent snippet from the grown tree's
// retained per-node systems — not an empty "Constraint System is Solved".
// Guards the `set_keep_sys(true)` the interactive server enables at
// startup (see `tamarin_server::serve`).
#[tokio::test]
async fn test_autoprove_proof_view_retains_systems() {
    tamarin_theory::constraint::solver::search::set_keep_sys(true);
    let s = start_server_with_theory("Tutorial.spthy").await;
    let v: serde_json::Value = s.client
        .get(s.url("/thy/trace/1/autoprove/idfs/0/False/proof/Client_auth"))
        .send().await.expect("send").json().await.expect("decode");
    let redir = v.get("redirect").and_then(|x| x.as_str()).expect("redirect");
    let idx: usize = redir.split('/').nth(3).and_then(|x| x.parse().ok()).expect("idx");
    let pv: serde_json::Value = s.client
        .get(s.url(&format!("/thy/trace/{}/main/proof/Client_auth", idx)))
        .send().await.expect("send").json().await.expect("decode");
    let html = pv.get("html").and_then(|x| x.as_str()).unwrap_or("");
    assert!(html.contains("Applicable Proof Methods"),
        "proof view must render applicable methods from retained systems; got: {}",
        &html[..html.len().min(200)]);
    assert!(!html.contains("Constraint System is Solved"),
        "root must not render as an empty solved system");
}
