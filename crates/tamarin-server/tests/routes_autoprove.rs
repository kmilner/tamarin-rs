// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

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

/// The three autoprove routes.  The test replays the capture script's own
/// sequence (`tests/capture_haskell_fixtures.sh`) on the same fixture.  That
/// sequence is: autoprove theory 1, then autoprove the proved snapshot that
/// the first call allocated, then autoproveAll on theory 1 again.  Each
/// response is the oracle's body, byte for byte.  The comparison includes the
/// allocated index, because `modifyTheory` assigns the next free index on
/// both sides.  It also includes the proof path, which both sides reach when
/// they walk `nextSmartThyPath` over the freshly autoproved tree.
///
/// The middle call autoproves a theory that is already proved.  It still
/// answers a redirect to a fresh index, and never an alert.  Upstream runs the
/// prover again over a tree that has nothing left to do.
#[tokio::test]
async fn test_autoprove_redirect_bodies_match_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;

    // The `debug` lemma is exists-trace and trivial.
    let res = s
        .get("/thy/trace/1/autoprove/idfs/0/False/proof/debug")
        .await;
    assert_eq!(res.status(), 200, "autoprove should return 200");
    let ct = content_type(&res);
    assert!(
        ct.starts_with("application/json"),
        "autoprove must reply JSON, got {}",
        ct
    );
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("autoprove.json"),
    );

    let method = s.get("/thy/trace/2/main/proof/debug/_").await;
    assert_eq!(method.status(), 200);
    let body: serde_json::Value = method.json().await.expect("JSON response");
    let title = body["title"].as_str().expect("method title");
    assert!(
        title.starts_with("Method: <span class=\"hl_keyword\">"),
        "method titles must retain syntax highlighting: {title}"
    );
    assert!(title.ends_with("<br/>\n"));

    let overview = s.get("/thy/trace/2/overview/proof/debug").await;
    let html = overview.text().await.expect("overview HTML");
    assert!(html.contains("<span class=\"hl_good\"><span class=\"hl_keyword\">lemma</span> debug"));

    for (url, capture) in [
        (
            "/thy/trace/2/autoprove/idfs/0/False/proof/debug",
            "autoprove_on_proven.json",
        ),
        (
            "/thy/trace/1/autoproveAll/idfs/0/proof/debug",
            "autoprove_all.json",
        ),
    ] {
        let res = s.get(url).await;
        assert_eq!(res.status(), 200, "{url}");
        assert_eq!(
            res.text().await.expect("text"),
            haskell_capture(capture),
            "{url}"
        );
    }
}

#[tokio::test]
async fn test_autoprove_route_path_pieces_match_haskell() {
    // Haskell's Yesod `PathPiece Bool` parser rejects lowercase
    // `true`/`false`.  We MUST mirror that — if our router accepted
    // lowercase silently the same frontend URL builder would emit URLs
    // that don't work against Haskell.  The same table pins integer-bound
    // parsing, autoproveAll's theory-path decoder, and the accepted negative
    // bound that means "unbounded".
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, expected, case) in [
        (
            "/thy/trace/1/autoprove/idfs/0/false/proof/debug",
            404,
            "lowercase Bool",
        ),
        (
            "/thy/trace/1/autoprove/idfs/nope/False/proof/debug",
            404,
            "malformed bound",
        ),
        (
            "/thy/trace/1/autoproveAll/idfs/0/not-a-path",
            404,
            "malformed autoproveAll path",
        ),
        (
            "/thy/trace/1/autoprove/idfs/-1/False/proof/debug",
            200,
            "negative bound means unbounded",
        ),
    ] {
        assert_eq!(s.get(path).await.status(), expected, "{case}: {path}");
    }
}

#[tokio::test]
async fn test_autoprove_on_bad_path_returns_alert() {
    let s = start_server_with_theory("issue193.spthy").await;
    // `rules` is not a valid path target for autoprove (it's not a
    // lemma / proof / method); Haskell returns alert, ours does too.
    let res = s.get("/thy/trace/1/autoprove/idfs/0/False/rules").await;
    assert_eq!(res.status(), 200);
    // This is the oracle's body, byte for byte.  The alert allocates no
    // theory, so its bytes do not depend on the capture session's history.
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("autoprove_on_rules.json"),
    );

    let missing = s.get("/thy/trace/99/autoprove/idfs/0/False/rules").await;
    assert_eq!(missing.status(), 404);
}

// ---------------------------------------------------------------------
// /thy/trace/<idx>/main/method/<lemma>/<nr>
// ---------------------------------------------------------------------

/// An out-of-range method number has ONE answer: the 200 JSON alert
/// `getTheoryPathMR` replies to a `Nothing` apply with
/// (`src/Web/Handler.hs`), byte-compared against the capture.
///
/// Upstream splits it three ways instead: `applyMethodAtPath` guards with
/// `length methods >= i` alone and then evaluates `methods !! (i-1)`
/// (`src/Web/Theory.hs`), so only an `i` past the end reaches that alert
/// while `i <= 0` passes the guard and raises `!!`'s `negIndex` — and `Int`
/// minBound passes it too, `i-1` wrapping to maxBound so `!!` raises
/// `tooLarge`.  Both exceptions come back as 200 alerts quoting the GHC
/// CallStack, because `modifyTheory` runs the apply under `evalInThread`
/// (`src/Web/Handler.hs`).  RS deliberately corrects that: one
/// out-of-range index, one alert.
#[tokio::test]
async fn test_method_out_of_range_index_alerts_match_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;
    // Only two methods are ranked at the `debug` root, so `3` is the first
    // index past the end; `9999` is the same answer, as are the non-positive
    // ones and `Int` minBound.
    for nr in ["0", "-1", "-9223372036854775808", "3", "9999"] {
        let path = format!("/thy/trace/1/main/method/debug/{nr}");
        let res = s.get(&path).await;
        assert_eq!(res.status(), 200, "method/{nr} must be a 200");
        assert_eq!(
            res.text().await.expect("text"),
            haskell_capture("method_out_of_range.json"),
            "method/{nr}"
        );
    }

    // The accept side of the very same guard: method `1` applies and redirects.
    let res = s.get("/thy/trace/1/main/method/debug/1").await;
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
    // `withTheory` / `notFound` in `src/Web/Handler.hs`).
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .get("/thy/trace/99/autoprove/idfs/0/False/proof/debug")
        .await;
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
    let res = s
        .get("/thy/trace/1/autoprove/idfs/0/False/proof/notALemma")
        .await;
    assert_eq!(res.status(), 200);
    // These bytes come from a probe against the oracle.  No capture holds
    // them, because the capture script never asks for a lemma that does not
    // exist.  This test therefore pins the bytes here.
    assert_eq!(
        res.text().await.expect("text"),
        "{\"alert\":\"Sorry, but the autoprover () failed!\"}",
    );
}
// Web-parity regression: after autoprove, `main/proof/<lemma>` must render
// the "Applicable Proof Methods" + sequent snippet from the grown tree's
// retained per-node systems — not an empty "Constraint System is Solved".
// Guards the `SysRetention::KeepAll` applied to every web prover session,
// including the harness's.
#[tokio::test]
async fn test_autoprove_proof_view_retains_systems() {
    let s = start_server_with_theory("Tutorial.spthy").await;
    let v: serde_json::Value = s
        .get("/thy/trace/1/autoprove/idfs/0/False/proof/Client_auth")
        .await
        .json()
        .await
        .expect("decode");
    let idx = redirect_idx(&v, "overview/proof/Client_auth_injective");
    let pv: serde_json::Value = s
        .get(&format!("/thy/trace/{idx}/main/proof/Client_auth"))
        .await
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
// dir and no such script exists, so the interactive search API returns a
// typed ranking failure to the route.
#[tokio::test]
async fn test_autoprove_missing_oracle_keeps_server_alive() {
    let s = start_server_with_theory("oracle_missing.spthy").await;
    let res = s
        .get("/thy/trace/1/autoprove/idfs/0/False/proof/test")
        .await;
    assert_eq!(
        res.status(),
        200,
        "failure surfaces as an alert, not a dead socket"
    );
    let unpublished = s.get("/thy/trace/2/main/help").await;
    assert_eq!(
        unpublished.status(),
        404,
        "a failed search must not publish a new theory version"
    );
}

#[tokio::test]
async fn terminal_proof_view_does_not_force_its_heuristic() {
    let s = start_server_with_theory("terminal_bad_heuristic.spthy").await;
    let res = s.get("/thy/trace/1/main/proof/done").await;
    assert_eq!(res.status(), 200);
    let body: serde_json::Value = res.json().await.expect("JSON response");
    let html = body["html"].as_str().expect("HTML body");
    assert!(
        html.contains("contradiction") && html.contains("Constraint system"),
        "terminal node should render without resolving the unused missing tactic: {html}"
    );
    assert!(
        html.contains("the tactic written in the theory file: missing"),
        "the view should retain the selected, lazily-invalid ranking: {html}"
    );
    assert!(!html.contains("No such lemma or proof path"));
}

/// Issue #50: acknowledging /kill must stop the blocking worker, and must
/// not publish its partial proof. Repeating the request also checks cleanup.
#[tokio::test]
async fn cancel_autoprove_stops_loop_without_publishing() {
    use std::time::Duration;

    let s = start_server_with_theory("loop.spthy").await;
    for path in [
        "/thy/trace/1/autoprove/idfs/0/False/proof/exec",
        "/thy/trace/1/autoproveAll/idfs/0/proof/exec",
        "/thy/trace/1/autoprove/idfs/0/False/proof/exec",
    ] {
        let client = s.client.clone();
        // jQuery adds a cache-busting query, absent from the UI cancel key.
        let url = format!("{}?_=123456789", s.url(path));
        let mut proof = tokio::spawn(async move {
            client
                .get(url)
                .send()
                .await
                .unwrap()
                .json::<serde_json::Value>()
                .await
                .unwrap()
        });
        // Let the worker enter the nonterminating search before cancelling.
        tokio::time::sleep(Duration::from_millis(250)).await;
        assert!(!proof.is_finished(), "loop unexpectedly finished");
        let response = s
            .client
            .get(s.url(&format!(
                "/kill?path={}",
                percent_encoding::utf8_percent_encode(path, percent_encoding::NON_ALPHANUMERIC)
            )))
            .send()
            .await
            .unwrap();
        assert_eq!(response.text().await.unwrap(), "Canceled request!");
        // The handler awaits spawn_blocking: this response proves the worker
        // exited, rather than just abandoning its JoinHandle.
        let result = tokio::time::timeout(Duration::from_secs(10), &mut proof).await;
        if result.is_err() {
            proof.abort();
        }
        assert_eq!(
            result.expect("cancelled worker exits promptly").unwrap()["alert"],
            "Canceled request!"
        );
        assert_eq!(s.get("/thy/trace/2/overview/help").await.status(), 404);
    }
    // A subsequent bounded search on the original theory still works.
    let response: serde_json::Value = s
        .get("/thy/trace/1/autoprove/idfs/1/False/proof/exec")
        .await
        .json()
        .await
        .unwrap();
    assert_eq!(redirect_idx(&response, "overview/proof/exec"), 2);
}

/// A blocked oracle must be terminated, and subsequent requests on the same
/// retained session must produce the same proof as a clean session.
#[cfg(unix)]
#[tokio::test]
async fn cancel_oracle_then_restart_preserves_proofs() {
    use std::os::unix::fs::PermissionsExt;
    use std::time::Duration;
    let dir = tempfile::tempdir().unwrap();
    let theory = dir.path().join("theory.spthy");
    std::fs::write(
        &theory,
        std::fs::read(fixture_path("oracle_missing.spthy")).unwrap(),
    )
    .unwrap();
    let oracle = dir.path().join("oracle");
    std::fs::write(&oracle, "#!/bin/sh\ncd \"$(dirname \"$0\")\"\nif mkdir blocked 2>/dev/null; then\n  touch ready\n  sleep 60\nfi\ncat >/dev/null\nprintf '0\\n'\n").unwrap();
    std::fs::set_permissions(&oracle, std::fs::Permissions::from_mode(0o755)).unwrap();
    let s = start_server_with_theory(theory.to_str().unwrap()).await;
    for path in [
        "/thy/trace/1/autoprove/idfs/0/False/proof/test",
        "/thy/trace/1/main/method/test/1",
        "/thy/trace/1/main/proof/test",
    ] {
        let client = s.client.clone();
        let url = s.url(path);
        let pending = tokio::spawn(async move {
            client
                .get(url)
                .send()
                .await
                .unwrap()
                .json::<serde_json::Value>()
                .await
                .unwrap()
        });
        let entered = tokio::time::timeout(Duration::from_secs(5), async {
            while !dir.path().join("ready").exists() {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await;
        let kill = format!(
            "/kill?path={}",
            percent_encoding::utf8_percent_encode(path, percent_encoding::NON_ALPHANUMERIC)
        );
        let killed = tokio::time::timeout(Duration::from_secs(5), s.get(&kill)).await;
        assert!(entered.is_ok(), "oracle never entered");
        assert_eq!(
            killed
                .expect("cancel waits for prompt worker exit")
                .text()
                .await
                .unwrap(),
            "Canceled request!"
        );
        // Start again before even consuming the old request's response.
        let retried: serde_json::Value = s
            .get("/thy/trace/1/autoprove/idfs/0/False/proof/test")
            .await
            .json()
            .await
            .unwrap();
        let idx = redirect_idx(&retried, "overview/proof/test");
        assert_eq!(pending.await.unwrap()["alert"], "Canceled request!");
        let clean = start_server_with_theory(theory.to_str().unwrap()).await;
        let baseline: serde_json::Value = clean
            .get("/thy/trace/1/autoprove/idfs/0/False/proof/test")
            .await
            .json()
            .await
            .unwrap();
        let baseline_idx = redirect_idx(&baseline, "overview/proof/test");
        assert_eq!(
            s.get(&format!("/thy/trace/{idx}/source"))
                .await
                .text()
                .await
                .unwrap(),
            clean
                .get(&format!("/thy/trace/{baseline_idx}/source"))
                .await
                .text()
                .await
                .unwrap()
        );
        std::fs::remove_file(dir.path().join("ready")).unwrap();
        std::fs::remove_dir(dir.path().join("blocked")).unwrap();
    }
}

/// Navigation also offers Cancel while lazily starting the proof session.
#[cfg(unix)]
#[tokio::test]
async fn cancel_navigation_during_session_start_then_retry() {
    use std::os::unix::fs::PermissionsExt;
    use std::time::Duration;
    for path in [
        "/thy/trace/1/overview/help",
        "/thy/trace/1/next/normal/proof/debug",
        "/thy/trace/1/prev/normal/proof/debug",
    ] {
        let dir = tempfile::tempdir().unwrap();
        let wrapper = dir.path().join("maude");
        let s = start_server_with_theory_and("issue193.spthy", |cfg| {
            let maude = cfg.maude_path.replace("'", "'\"'\"'");
            let cwd = dir.path().to_str().unwrap().replace("'", "'\"'\"'");
            std::fs::write(&wrapper, format!(
                "#!/bin/sh\ncd '{cwd}'\nif [ -f block ]; then\n touch ready\n sleep 60 &\n wait\n exit 1\nfi\nexec '{maude}' \"$@\"\n"
            )).unwrap();
            std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
            cfg.maude_path = wrapper.to_str().unwrap().to_owned();
        }).await;
        std::fs::write(dir.path().join("block"), "").unwrap();
        let client = s.client.clone();
        let url = format!("{}?_=123456789", s.url(path));
        let pending = tokio::spawn(async move { client.get(url).send().await.unwrap() });
        tokio::time::timeout(Duration::from_secs(5), async {
            while !dir.path().join("ready").exists() {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .expect("navigation entered Maude startup");
        let kill = format!(
            "/kill?path={}",
            percent_encoding::utf8_percent_encode(path, percent_encoding::NON_ALPHANUMERIC)
        );
        let response = tokio::time::timeout(Duration::from_secs(5), s.get(&kill))
            .await
            .expect("navigation stops promptly");
        assert_eq!(response.text().await.unwrap(), "Canceled request!");
        assert_eq!(pending.await.unwrap().status(), 204);
        std::fs::remove_file(dir.path().join("block")).unwrap();
        let retry = s.get(path).await;
        assert_eq!(retry.status(), 200);
        let clean = start_server_with_theory("issue193.spthy").await;
        assert_eq!(
            blank_times(&retry.text().await.unwrap()),
            blank_times(&clean.get(path).await.text().await.unwrap())
        );
    }
}
