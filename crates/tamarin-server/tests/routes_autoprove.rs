// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Integration tests that exercise the prover-driving endpoints: the
//! autoprove routes and `main/method`'s single-step apply.
//!
//! These tests drive the real Rust solver through the handlers, so they
//! need a working `maude` binary: `MAUDE_PATH` if set, else a common
//! location probed by `start_server_with_theory`, else `maude` on PATH.
//! Most use the small `issue193.spthy` fixture, whose single trivial
//! exists-trace lemma (`debug`) the solver dispatches in well under a
//! second.

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

    // SHAPE assertions, not byte equality: both sides walk
    // `nextSmartThyPath` over the freshly autoproved tree (the port's
    // `next_thy_path_inner`), so the tail of the URL depends on the shape
    // that search produced.  What is pinned here is the prefix and the
    // "NEW idx" semantics, which the frontend dispatcher relies on.
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
    let res = s
        .client
        .get(&url)
        .send()
        .await
        .expect("send autoprove-rules");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(
        json_top_keys(&v),
        one_key_set("alert"),
        "autoprove on non-lemma path should be {{alert}}"
    );

    // The captured Haskell alert is exactly
    // "Can't run the autoprover () on the given theory path!" — we
    // emit the same string for byte-equal comparison.
    let captured = haskell_capture("autoprove_on_rules.json");
    let captured_v: serde_json::Value = serde_json::from_str(&captured).expect("parse captured");
    assert_eq!(
        v.get("alert").and_then(|x| x.as_str()),
        captured_v.get("alert").and_then(|x| x.as_str()),
        "alert text must match Haskell verbatim",
    );
}

// ---------------------------------------------------------------------
// /thy/trace/<idx>/main/method/<lemma>/<nr>
// ---------------------------------------------------------------------

/// An out-of-range method number has ONE answer: the 200 JSON alert
/// `getTheoryPathMR` replies to a `Nothing` apply with
/// (`src/Web/Handler.hs:1081`), byte-compared against the capture.
///
/// Upstream splits it three ways instead: `applyMethodAtPath` guards with
/// `length methods >= i` alone and then evaluates `methods !! (i-1)`
/// (`src/Web/Theory.hs:99`), so only an `i` past the end reaches that alert
/// while `i <= 0` passes the guard and raises `!!`'s `negIndex` — and `Int`
/// minBound passes it too, `i-1` wrapping to maxBound so `!!` raises
/// `tooLarge`.  Both exceptions come back as 200 alerts quoting the GHC
/// CallStack, because `modifyTheory` runs the apply under `evalInThread`
/// (`src/Web/Handler.hs:743,753`).  RS deliberately corrects that: one
/// out-of-range index, one alert.
#[tokio::test]
async fn test_method_out_of_range_index_alerts_match_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;
    // Only two methods are ranked at the `debug` root, so `3` is the first
    // index past the end; `9999` is the same answer, as are the non-positive
    // ones and `Int` minBound.
    for nr in ["0", "-1", "-9223372036854775808", "3", "9999"] {
        let url = s.url(&format!("/thy/trace/1/main/method/debug/{nr}"));
        let res = s.client.get(&url).send().await.expect("send method");
        assert_eq!(res.status(), 200, "method/{nr} must be a 200");
        assert_eq!(
            res.text().await.expect("text"),
            haskell_capture("method_out_of_range.json"),
            "method/{nr}"
        );
    }

    // The accept side of the very same guard: method `1` applies and redirects.
    let res = s
        .client
        .get(s.url("/thy/trace/1/main/method/debug/1"))
        .send()
        .await
        .expect("send method/1");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(
        json_top_keys(&v),
        one_key_set("redirect"),
        "an in-range method must be {{redirect}}"
    );
}

#[tokio::test]
async fn test_autoprove_with_missing_idx_returns_404_html() {
    // Match Haskell: bad theory idx returns 404 HTML (see
    // `withTheory` / `notFound` in `src/Web/Handler.hs:662-672`).
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
    assert_eq!(
        json_top_keys(&v),
        one_key_set("alert"),
        "unknown-lemma autoprove must be {{alert}}"
    );
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
// Guards the `SysRetention::KeepAll` that `tamarin_server::init_process_globals`
// applies for every server, the harness's included.
#[tokio::test]
async fn test_autoprove_proof_view_retains_systems() {
    let s = start_server_with_theory("Tutorial.spthy").await;
    let v: serde_json::Value = s
        .client
        .get(s.url("/thy/trace/1/autoprove/idfs/0/False/proof/Client_auth"))
        .send()
        .await
        .expect("send")
        .json()
        .await
        .expect("decode");
    let redir = v
        .get("redirect")
        .and_then(|x| x.as_str())
        .expect("redirect");
    let idx: usize = redir
        .split('/')
        .nth(3)
        .and_then(|x| x.parse().ok())
        .expect("idx");
    let pv: serde_json::Value = s
        .client
        .get(s.url(&format!("/thy/trace/{}/main/proof/Client_auth", idx)))
        .send()
        .await
        .expect("send")
        .json()
        .await
        .expect("decode");
    let html = pv.get("html").and_then(|x| x.as_str()).unwrap_or("");
    assert!(
        html.contains("Applicable Proof Methods"),
        "proof view must render applicable methods from retained systems; got: {}",
        &html[..html.len().min(200)]
    );
    assert!(
        !html.contains("Constraint System is Solved"),
        "root must not render as an empty solved system"
    );
}

// Regression: an oracle exec failure must be confined to the request
// that forced the ranking, exactly as HS's `readProcess` exception is
// caught by the Warp request thread — the server process must survive.
// The fixture's `heuristic=o` execs `./oracle` relative to the theory
// dir and no such script exists, so the first ranking call fails
// (`ORACLE_ERROR_UNWINDS` panics instead of `exit(1)`); the autoprove
// handler's spawn_blocking boundary absorbs the unwind.
#[tokio::test]
async fn test_autoprove_missing_oracle_keeps_server_alive() {
    let s = start_server_with_theory("oracle_missing.spthy").await;
    let auto = s.url("/thy/trace/1/autoprove/idfs/0/False/proof/test");
    let res = s.client.get(&auto).send().await.expect("request completes");
    assert_eq!(
        res.status(),
        200,
        "failure surfaces as an alert, not a dead socket"
    );
    let root = s
        .client
        .get(s.url("/"))
        .send()
        .await
        .expect("server still serving");
    assert_eq!(root.status(), 200, "server must survive the oracle failure");
}
