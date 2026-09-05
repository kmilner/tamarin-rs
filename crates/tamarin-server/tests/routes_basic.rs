// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Integration tests for the LIVE routes that don't run the solver.
//!
//! These tests start a real `axum` server on an ephemeral port with
//! `tests/fixtures/issue193.spthy` pre-loaded.  They then make HTTP requests
//! with `reqwest`.  They check the status, the `Content-Type` and the body.
//!
//! The test compares each body byte for byte with the captured Haskell
//! responses under `tests/fixtures/haskell-responses/`.  It blanks two parts
//! of the body first.  The first part is the theory's load stamp, on the
//! pages that print it.  The load stamp is the theory's load time and its
//! origin path.  A capture run and a test run cannot share those two values.
//! The second part is the `Generated from:` banner's build values on the
//! `prettyClosedTheory` routes.  The port emits those values empty.  See
//! `common::VERSION_BANNER_PREFIXES` for the divergence that the blanking
//! masks.
//!
//! Coverage matrix (LIVE routes):
//!   - GET  /
//!       [test_get_index_returns_html_with_theory_listed]
//!   - GET  /favicon.ico
//!       [test_favicon_redirects_to_static_image]
//!   - GET  /robots.txt
//!       [test_robots_txt]
//!   - GET  /kill  and  /kill?path=
//!       [test_kill_without_path_returns_400]
//!       [test_kill_with_path_returns_canceled_request]
//!   - GET  /thy/trace/1/overview/help
//!       [test_overview_help_html_structure]
//!   - GET  /thy/trace/1/main/help
//!       [test_main_help_envelope_matches_haskell]
//!   - GET  /thy/trace/1/main/rules
//!       [test_main_rules_envelope]
//!   - GET  /thy/trace/1/main/message
//!       [test_main_message_envelope]
//!   - GET  /thy/trace/1/main/lemma/debug
//!       [test_main_lemma_envelope]
//!   - GET  /thy/trace/1/source
//!       [test_source_returns_plain_text]
//!   - GET  /thy/trace/1/message
//!       [test_message_deduction_returns_plain_text]
//!   - GET  /thy/trace/1/download/x.spthy
//!       [test_download_for_local_theory_returns_source_file]
//!   - GET  /thy/trace/1/unload
//!       [test_unload_redirects_to_root]
//!   - POST /thy/trace/1/reload
//!       [test_reload_returns_redirect_json_same_idx]
//!
//! Coverage matrix (Not Found, i.e. the `notFound` page and wai-app-static's
//! own miss).  Status + content type only where the body is not captured:
//!   - GET  /thy/trace/99/main/help
//!       [test_main_with_missing_idx_returns_404_html]
//!   - GET  /thy/trace/99/download/x.spthy
//!       [test_download_for_missing_idx_returns_404_html]
//!   - GET  /thy/trace/99/overview/help, /thy/trace/1/json/main, /nonexistent
//!       [test_not_found_page_matches_haskell]
//!   - GET  /a&b'c%3Cd, /caf%C3%A9?q=1
//!       [test_not_found_page_escapes_the_request_path]
//!   - GET  /thy/trace/{-1,1x,99999999999999999999}/overview/help
//!       [test_unusable_theory_index_is_not_found]
//!   - GET  /thy/trace/{%31,%30%31,%2B1,1%2F2,%FF}/overview/help
//!       [test_percent_encoded_theory_index_resolves]
//!   - GET  /static/js/does-not-exist.js
//!       [test_missing_static_asset_matches_haskell]

mod common;

use common::*;

// ---------------------------------------------------------------------
// GET /
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_get_index_returns_html_with_theory_listed() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/").await;
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(
        ct.starts_with("text/html"),
        "expected text/html content-type, got {}",
        ct
    );
    let body = res.text().await.expect("read body");

    // The test compares the complete page with the oracle's page, byte for
    // byte.  The page is `rootTpl` plus `introTpl` plus the one-row
    // `theoriesTpl` table inside `defaultLayout` (Web/Hamlet.hs).  The load
    // time and the origin path are the only exceptions.  The capture run
    // cannot share those two fields with this run.
    assert_page_matches_capture(&body, "index.html", "issue193.spthy");
}

// ---------------------------------------------------------------------
// GET /favicon.ico
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_favicon_redirects_to_static_image() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/favicon.ico").await;
    let status = res.status();
    let loc = header(&res, reqwest::header::LOCATION);

    // Haskell returns 303 + Location: /static/img/favicon.ico
    // Rust returns 308 (permanent redirect) + same Location.
    // Both are valid redirects to the same target.
    assert!(status.is_redirection(), "expected redirect, got {}", status);
    assert!(
        loc.ends_with("/static/img/favicon.ico"),
        "expected redirect to favicon.ico, got {:?}",
        loc
    );
}

// ---------------------------------------------------------------------
// GET /robots.txt
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_robots_txt() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/robots.txt").await;
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
    let body = res.text().await.expect("read body");

    // The test compares the body with the oracle's body exactly.  The body is
    // `User-agent: *` with no trailing newline (`getRobotsR`,
    // src/Web/Handler.hs).
    assert_eq!(body, haskell_capture("robots.txt"));
}

// ---------------------------------------------------------------------
// GET /kill
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_kill_without_path_returns_400() {
    // Haskell: `/kill` without `?path=...` returns 400 with HTML body
    // "Invalid Arguments / No path to kill specified!".
    // See `getKillThreadR` in `src/Web/Handler.hs:1517-1525`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/kill").await;
    assert_eq!(
        res.status(),
        400,
        "/kill without ?path= must be 400 (matches Haskell invalidArgs)",
    );
    assert_eq!(content_type(&res), "text/html; charset=utf-8");
    let body = res.text().await.expect("read");
    // This is the widget that `invalidArgs` renders.  The test takes it from
    // the oracle's own page, so a re-capture that changes the widget also
    // changes this assertion.  The port emits the widget without the
    // surrounding `defaultLayout` frame that the capture carries.  For that
    // reason the test compares the lines and not the complete bytes.
    let widget = "<h1>Invalid Arguments</h1>\n<ul><li>No path to kill specified!</li>\n</ul>";
    let captured = haskell_capture("kill.txt");
    assert!(
        captured.contains(widget),
        "the capture must still carry the widget this route is pinned to; got {captured}",
    );
    for line in widget.lines() {
        assert!(
            body.contains(line),
            "400 body must carry the oracle's {line:?}; got {body}",
        );
    }
}

#[tokio::test]
async fn test_kill_with_path_returns_canceled_request() {
    // Haskell: `/kill?path=foo` returns 200 + "Canceled request!".
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/kill?path=some-key").await;
    assert_eq!(res.status(), 200);
    assert!(content_type(&res).starts_with("text/plain"));
    // The test compares the body with the oracle's body exactly.
    assert_eq!(
        res.text().await.expect("read"),
        haskell_capture("kill_path.txt")
    );
}

// ---------------------------------------------------------------------
// GET /thy/trace/<idx>/overview/help
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_overview_help_html_structure() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/overview/help").await;
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/html"), "got CT={}", ct);
    let body = res.text().await.expect("read body");

    // The test compares the complete framed page with the oracle's page, byte
    // for byte.  The load time and the origin path are the only exceptions.
    // The page holds `overviewTpl`'s four panes, the proof-script pane's
    // rendered theory and the help snippet in the centre pane.
    //
    // The comparison also covers where the panes sit.
    // `data/js/jquery-layout.js` finds them with
    // `$Container.children(".ui-layout-center")` over `<body>`.  An extra
    // `<div>` around them, for example the `ui-layout-container` that the
    // index page uses, triggers the runtime `errCenterPaneMissing` alert, and
    // the page never renders.  HS's `overviewTpl` emits the four panes at the
    // top level of `defaultLayout`'s widget.  Any wrapper that the port adds
    // shows up here as a difference.
    assert_page_matches_capture(&body, "overview_help.html", "issue193.spthy");
}

// ---------------------------------------------------------------------
// GET /thy/trace/<idx>/main/*path — JsonHtml AJAX envelope
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_main_help_envelope_matches_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/main/help").await;
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(
        ct.starts_with("application/json"),
        "expected application/json, got {}",
        ct
    );

    // The test compares the complete `JsonHtml` envelope with the oracle's
    // envelope.  The envelope holds the theory header line and the help
    // widget.  The load stamp in the header is the only exception.
    assert_page_matches_capture(
        &res.text().await.expect("text"),
        "main_help.json",
        "issue193.spthy",
    );
}

#[tokio::test]
async fn test_main_rules_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/main/rules").await;
    assert_eq!(res.status(), 200);
    // The rules view carries no load stamp.  The test therefore compares the
    // complete envelope with the oracle's, byte for byte.  The envelope holds
    // every rule of the theory, rendered by `htmlThyPath`.
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("main_rules.json")
    );
}

#[tokio::test]
async fn test_main_message_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/main/message").await;
    assert_eq!(res.status(), 200);
    // HS `messageSnippet` (Web/Theory.hs:926-937) emits the Signature section
    // and the Construction/Deconstruction rule sections.  It does not emit the
    // restrictions, which appear on the rules page.  There is no load stamp,
    // so the test compares the complete envelope.
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("main_message.json")
    );
}

#[tokio::test]
async fn test_main_lemma_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/main/lemma/debug").await;
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    // HS `htmlThyPath` renders `TheoryLemma _ -> text "this is a mistake"`
    // (Web/Theory.hs:1011-1152, see line 1074) — a deliberate upstream quirk; the bare
    // `main/lemma/<name>` path is one that the frontend never uses.  The
    // frontend always links to `main/proof/<name>` instead.
    //
    // The test compares the body with the oracle's envelope exactly, with one
    // exception.  The oracle's `renderHtmlDoc` appends a `<br/>` and a newline
    // to the line (`postprocessHtmlDoc`, Text/PrettyPrint/Html.hs:157-162).
    // The port does not emit them here.  The test removes them from the
    // capture, so the test fails on the day the port emits them.
    assert_eq!(
        body,
        haskell_capture("main_lemma.json").replace("<br/>\\n", "")
    );
}

// ---------------------------------------------------------------------
// 404 for unknown idx
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_main_with_missing_idx_returns_404_html() {
    // Haskell `withTheory` returns 404 HTML for an unknown idx
    // (see `src/Web/Handler.hs:662-672`).  We mirror that exactly —
    // the frontend's loading-dialog dismiss / global error handler
    // distinguishes 404 from a JSON envelope.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/99/main/help").await;
    assert_eq!(
        res.status(),
        404,
        "missing idx must be 404 (matches Haskell)"
    );
    let ct = content_type(&res);
    assert!(
        ct.starts_with("text/html"),
        "404 must be text/html; got {}",
        ct
    );
}

// ---------------------------------------------------------------------
// Yesod's Not Found page
// ---------------------------------------------------------------------

/// Every `notFound` carries the same page — the `defaultLayout` frame around
/// `<h1>Not Found</h1>` and the request's raw path — whatever raised it:
/// an unknown theory index, a theory path `parseTheoryPath` rejects, or a URL
/// matching no route at all.  Byte-for-byte the captured Haskell responses.
/// The framed HTML route's missing-index 404 is the first of these.
#[tokio::test]
async fn test_not_found_page_matches_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        ("/thy/trace/99/overview/help", "missing_idx_overview.html"),
        ("/thy/trace/1/json/main", "not_found_theory_path.html"),
        ("/nonexistent", "not_found_unknown_route.html"),
    ] {
        assert_not_found_capture(&s, path, capture).await;
    }
}

/// The path is spliced in by hamlet's `#{}`, so its HTML metacharacters are
/// escaped; it is the RAW path — percent-encoding intact (a `%3C` stays a
/// `%3C`, it is not decoded and then escaped), query string dropped.
#[tokio::test]
async fn test_not_found_page_escapes_the_request_path() {
    let s = start_server_with_theory("issue193.spthy").await;
    assert_not_found_capture(&s, "/a&b'c%3Cd", "not_found_escaped_path.html").await;

    // Percent-encoded bytes stay encoded, and `?…` is not part of the path.
    let res = s.get("/caf%C3%A9?q=1").await;
    assert_eq!(res.status(), 404);
    assert!(
        res.text()
            .await
            .expect("text")
            .contains("<p>/caf%C3%A9</p>"),
        "the raw path is echoed undecoded, without the query string"
    );
}

/// The theory-index route piece is `#Int` (`src/Web/Types.hs:580-616`): a
/// piece Yesod's `PathPiece Int` cannot read — trailing junk, an over-long
/// literal — makes the route not match, and a piece that reads but names no
/// live theory (a negative one, say) is the handlers' own miss.  All of them
/// carry the same Not Found page; none is a path-extractor 400.
#[tokio::test]
async fn test_unusable_theory_index_is_not_found() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        ("/thy/trace/-1/overview/help", "not_found_negative_idx.html"),
        ("/thy/trace/1x/overview/help", "not_found_unparsed_idx.html"),
        (
            "/thy/trace/99999999999999999999/overview/help",
            "not_found_huge_idx.html",
        ),
    ] {
        assert_not_found_capture(&s, path, capture).await;
    }
    // `01` and `+1` are theory 1 — `PathPiece Int` reads both.
    for path in ["/thy/trace/01/overview/help", "/thy/trace/+1/overview/help"] {
        let res = s.get(path).await;
        assert_eq!(res.status(), 200, "{path} must resolve to theory 1");
    }
}

/// Yesod dispatches on WAI's `pathInfo`, whose segments are percent-decoded,
/// so an escaped index piece names the theory it decodes to: `%31` is theory 1
/// and serves the very page the unescaped URL does (only the Not Found page's
/// echoed path is the raw one).
#[tokio::test]
async fn test_percent_encoded_theory_index_resolves() {
    let s = start_server_with_theory("issue193.spthy").await;
    let plain = s.get("/thy/trace/1/overview/help").await;
    assert_eq!(plain.status(), 200);
    let plain = plain.text().await.expect("text");
    for path in [
        "/thy/trace/%31/overview/help",
        "/thy/trace/%30%31/overview/help",
        "/thy/trace/%2B1/overview/help",
    ] {
        let res = s.get(path).await;
        assert_eq!(res.status(), 200, "{path} must resolve to theory 1");
        assert_eq!(res.text().await.expect("text"), plain, "{path}");
    }
    // An escaped separator belongs to the piece rather than ending it, and
    // escapes that are not valid UTF-8 read as no index at all: both are the
    // Not Found page, never a path-extractor 400.
    for path in [
        "/thy/trace/1%2F2/overview/help",
        "/thy/trace/%FF/overview/help",
    ] {
        assert_not_found_page(&s, path).await;
    }
}

/// `/static` is wai-app-static in HS, a separate WAI app whose miss never
/// reaches Yesod's error handler: a bare `File not found`, `text/plain` with
/// no charset.
#[tokio::test]
async fn test_missing_static_asset_matches_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/static/js/does-not-exist.js").await;
    assert_eq!(res.status(), 404);
    assert_eq!(content_type(&res), "text/plain");
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("static_not_found.txt")
    );
}

// ---------------------------------------------------------------------
// /source, /message, /download
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_source_returns_plain_text() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/source").await;
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
    // The route renders the complete `prettyClosedTheory` (`getTheorySourceR`,
    // src/Web/Handler.hs:1015-1022).  The test compares it with the oracle's
    // rendering.  The `Generated from:` banner's build-specific values are the
    // only exception.
    assert_theory_source_matches_capture(&res.text().await.expect("read"), "source.txt");
}

#[tokio::test]
async fn test_message_deduction_returns_plain_text() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/message").await;
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
    // `getTheoryMessageDeductionR` (src/Web/Handler.hs:1050-1055) renders the
    // same `prettyClosedTheory` that `/source` renders.  The oracle's two
    // captures hold the same bytes.  The test compares this route with its own
    // capture.
    assert_theory_source_matches_capture(&res.text().await.expect("read"), "message.json");
}

#[tokio::test]
async fn test_download_for_local_theory_returns_source_file() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/download/x.spthy").await;
    assert_eq!(res.status(), 200);

    // Haskell uses `application/octet-stream` (see
    // `getDownloadTheoryR` in `src/Web/Handler.hs:1763-1766` — it
    // returns `(typeOctet, source)`).  We mirror that exactly so the
    // frontend's "Save As" UX is bit-for-bit identical.
    let ct = content_type(&res);
    assert_eq!(
        ct, "application/octet-stream",
        "download must use application/octet-stream (matches Haskell)",
    );

    let cd = header(&res, reqwest::header::CONTENT_DISPOSITION);
    assert!(
        cd.contains("attachment"),
        "download must use Content-Disposition: attachment; got {:?}",
        cd,
    );
    assert!(
        cd.contains("x.spthy"),
        "Content-Disposition should preserve filename {:?}",
        cd,
    );

    // `getDownloadTheoryR` returns `getTheorySourceR`'s body under the octet
    // content type (src/Web/Handler.hs:1763-1766).  The test therefore
    // compares this payload with the oracle's in the same way as `/source`.
    assert_theory_source_matches_capture(&res.text().await.expect("read"), "download.txt");
}

#[tokio::test]
async fn test_download_for_missing_idx_returns_404_html() {
    // Haskell `withTheory` notFound for `/download/...` too.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/99/download/x.spthy").await;
    assert_eq!(res.status(), 404);
}

// ---------------------------------------------------------------------
// /unload  (GET → redirect to /)
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_unload_redirects_to_root() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/unload").await;
    assert!(
        res.status().is_redirection(),
        "expected redirect, got {}",
        res.status()
    );
    let loc = header(&res, reqwest::header::LOCATION);
    assert!(
        loc == "/" || loc.ends_with("/"),
        "unload should redirect to / (got {:?})",
        loc
    );
}

// ---------------------------------------------------------------------
// /reload (POST → JSON redirect)
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_reload_returns_redirect_json_same_idx() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.post("/thy/trace/1/reload").await;
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("reload.json");
    assert_eq!(rust_keys, haskell_keys);
    let redir = v.get("redirect").and_then(|t| t.as_str()).unwrap_or("");
    // Haskell `postReloadTheoryR` uses `replaceTheory` at the SAME idx
    // (see `src/Web/Handler.hs:443-460`).  Match exactly — preserves
    // URLs bookmarked by the user.
    assert!(
        redir.starts_with("/thy/trace/1/overview/help"),
        "reload must redirect to the SAME idx (replaceTheory semantics); got {:?}",
        redir,
    );
}
