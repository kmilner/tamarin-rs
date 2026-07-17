// Currently GPL 3.0 until granted permission by the following authors:
//   Artur Cygan, Simon Meier, Jannik Dreier, Felix Linker, "Jackie" (github
//   kanakanajm), Cas Cremers, Ralf Sasse, Yann Colomb, Benedikt Schmidt,
//   Adrian Dapprich, "Tom" (github BTom-GH), Philip Lukert, Mathias Aurand,
//   Alexander Dax, "Pops" (github racoucho1u), Dominik Schoop, Kevin Morio,
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   src/Web/Handler.hs, src/Web/Theory.hs

//! Integration tests for the LIVE routes that don't run the solver.
//!
//! These tests start a real `axum` server on an ephemeral port with
//! `tests/fixtures/issue193.spthy` pre-loaded, then make HTTP
//! requests via `reqwest` and check:
//!   - HTTP status code
//!   - Content-Type
//!   - JSON envelope key set (for `/main/*` routes)
//!
//! Comparison with Haskell is done against captured responses under
//! `tests/fixtures/haskell-responses/`.  The criterion is "same JSON
//! envelope shape" or "same HTML structural markers" — NOT byte
//! equality.
//!
//! Coverage matrix (LIVE routes):
//!   - GET /                          [test_get_index]
//!   - GET /favicon.ico               [test_favicon]
//!   - GET /robots.txt                [test_robots]
//!   - GET /kill                      [test_kill]
//!   - GET /thy/trace/1/overview/...  [test_overview_help]
//!   - GET /thy/trace/1/main/help     [test_main_help_envelope]
//!   - GET /thy/trace/1/main/rules    [test_main_rules_envelope]
//!   - GET /thy/trace/1/main/message  [test_main_message_envelope]
//!   - GET /thy/trace/1/main/lemma/X  [test_main_lemma_envelope]
//!   - GET /thy/trace/1/source        [test_source]
//!   - GET /thy/trace/1/message       [test_message_deduction]
//!   - GET /thy/trace/1/download/...  [test_download]
//!   - GET /thy/trace/1/unload        [test_unload_redirect]
//!   - GET /thy/trace/99/main/help    [test_404_for_missing_idx]

mod common;

use common::*;

// ---------------------------------------------------------------------
// GET /
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_get_index_returns_html_with_theory_listed() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.client.get(s.url("/")).send().await.expect("send /");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(
        ct.starts_with("text/html"),
        "expected text/html content-type, got {}",
        ct
    );
    let body = res.text().await.expect("read body");

    // Structural markers that should appear, matching Haskell's
    // root template (Web.Hamlet.rootTpl):
    //   - The fixture theory's name must appear (it's loaded).
    //   - A link to the overview must appear.
    //   - The upload form must appear.
    assert!(
        body.contains("RevealingSignatures"),
        "index should list the loaded theory by name; got body:\n{}",
        body
    );
    assert!(
        body.contains("/thy/trace/1/overview/help"),
        "index should link to overview/help",
    );
    assert!(
        body.contains("uploadedTheory"),
        "index should contain the upload form (name=uploadedTheory)",
    );
}

// ---------------------------------------------------------------------
// GET /favicon.ico
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_favicon_redirects_to_static_image() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/favicon.ico"))
        .send()
        .await
        .expect("send favicon");
    let status = res.status();
    let loc = header(&res, reqwest::header::LOCATION);

    // Haskell returns 303 + Location: /static/img/favicon.ico
    // Rust returns 308 (permanent redirect) + same Location.
    // Both are valid redirects to the same target.
    assert!(
        status.is_redirection(),
        "expected redirect, got {}",
        status
    );
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
    let res = s
        .client
        .get(s.url("/robots.txt"))
        .send()
        .await
        .expect("send robots");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
    let body = res.text().await.expect("read body");

    // Haskell capture is exactly "User-agent: *\n".  We match that
    // exactly here.
    assert!(
        body.starts_with("User-agent:"),
        "robots.txt should start with User-agent:, got {:?}",
        body
    );

    // Haskell-shape comparison — byte-loose, content-equal modulo
    // trailing whitespace.
    let captured = haskell_capture("robots.txt");
    assert_eq!(
        body.trim_end(),
        captured.trim_end(),
        "Rust robots.txt body must match Haskell"
    );
}

// ---------------------------------------------------------------------
// GET /kill
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_kill_without_path_returns_400() {
    // Haskell: `/kill` without `?path=...` returns 400 with HTML body
    // "Invalid Arguments / No path to kill specified!".
    // See `getKillThreadR` in `src/Web/Handler.hs:1422-1440`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/kill"))
        .send()
        .await
        .expect("send /kill");
    assert_eq!(
        res.status(),
        400,
        "/kill without ?path= must be 400 (matches Haskell invalidArgs)",
    );
    let body = res.text().await.expect("read");
    // Haskell's HTML body includes the "No path to kill specified!"
    // text — we match that key string.
    assert!(
        body.contains("No path to kill specified!"),
        "400 body must include the Haskell error text; got {}",
        body,
    );
}

#[tokio::test]
async fn test_kill_with_path_returns_canceled_request() {
    // Haskell: `/kill?path=foo` returns 200 + "Canceled request!".
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/kill?path=some-key"))
        .send()
        .await
        .expect("send /kill with path");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read");
    // Match Haskell's body verbatim.
    assert_eq!(body, "Canceled request!");
}

// ---------------------------------------------------------------------
// GET /thy/trace/<idx>/overview/help
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_overview_help_html_structure() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/overview/help"))
        .send()
        .await
        .expect("send overview");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/html"), "got CT={}", ct);
    let body = res.text().await.expect("read body");

    // Structural markers shared with Haskell overview_help.html:
    //   - "RevealingSignatures" appears (theory name)
    //   - "Proof scripts" appears (left pane heading)
    //   - "Visualization display" appears (right pane heading)
    //   - "Autoprove" appears (context menu item)
    //   - References to /static/css/* and /static/js/*
    for needle in [
        "RevealingSignatures",
        "Proof scripts",
        "Visualization display",
        "Autoprove",
        "/static/css/",
        "/static/js/",
    ] {
        assert!(
            body.contains(needle),
            "overview page missing structural marker {:?}; body=\n{}",
            needle,
            body
        );
    }
}

/// The jQuery-layout JS (`data/js/jquery-layout.js`) calls
/// `$('body').layout(...)` and resolves panes with
/// `$Container.children(".ui-layout-center")`, i.e. they MUST be direct
/// children of `<body>` — wrapping them in any extra `<div>` triggers
/// the runtime `errCenterPaneMissing` alert ("UI Layout Initialization
/// Error — The center-pane element does not exist") and the page never
/// renders.  Haskell's `overviewTpl` emits the four panes at the top
/// level of `defaultLayout`'s widget so they land directly under
/// `<body>` (see `tests/fixtures/haskell-responses/overview_help.html`).
///
/// This test guards the framed overview page (and every page produced
/// by `theory_html::overview_page`) against re-introducing a wrapper.
#[tokio::test]
async fn test_overview_help_panes_are_direct_body_children() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/overview/help"))
        .send()
        .await
        .expect("send overview");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read body");

    // The four panes MUST appear.
    for needle in [
        "ui-layout-north",
        "ui-layout-west",
        "ui-layout-east",
        "ui-layout-center",
    ] {
        assert!(
            body.contains(needle),
            "overview page is missing {} (jQuery-layout would alert errCenterPaneMissing); body=\n{}",
            needle,
            body
        );
    }

    // And they must be DIRECT children of <body>.  We extract the
    // body's first-level structure and confirm each pane's opening tag
    // appears as a top-level sibling, not nested inside any wrapper
    // div that itself sits under <body>.
    let body_open = body.find("<body>").expect("body open tag");
    let body_close = body.find("</body>").expect("body close tag");
    let body_inner = &body[body_open + "<body>".len()..body_close];

    // Reject the legacy wrapper that jQuery-layout chokes on.
    assert!(
        !body_inner.contains("ui-layout-container"),
        "ui-layout-container wrapper around the panes triggers \
         errCenterPaneMissing in jquery-layout.js (it does \
         $Container.children(...) on <body>); body=\n{}",
        body_inner
    );

    // Top-level depth tracker: count tag depth as we walk, and
    // confirm each pane opens at depth 0 (i.e., as a direct child of
    // <body>).  This is a coarse but correct check for the HTML we
    // emit (no comments / CDATA / script-with-tags-in-strings inside
    // <body>).
    fn pane_appears_at_top_level(inner: &str, class: &str) -> bool {
        let needle = format!("<div class=\"{}\"", class);
        // Walk the inner body looking for the pane opening at depth 0.
        let mut depth: i32 = 0;
        let bytes = inner.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'<' {
                // Check this position against the needle BEFORE we
                // bump depth for this tag.
                if depth == 0 && inner[i..].starts_with(&needle) {
                    return true;
                }
                // Is this a closing tag?
                if i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                    depth -= 1;
                    i += 2;
                } else {
                    // Opening tag.  Need to look at the rest of the
                    // tag to determine if it's a self-closing void
                    // element — for our limited template, `<br>`,
                    // `<img>`, `<input>`, `<meta>`, `<link>`, `<hr>`
                    // are the only voids that appear; bumping depth
                    // and then ignoring close-tag missing is benign
                    // because we only need top-level pane positions
                    // and those are followed by close tags.
                    // For correctness, we DO recognise self-closing
                    // tags via "/>".  Otherwise: increment depth.
                    // Skip to end of tag.
                    let end = inner[i..].find('>').unwrap_or(0);
                    let tag = &inner[i..i + end];
                    // A trailing `/` is only a self-close marker when it is a
                    // standalone token (` />` / `"/>` / `'/>`).  Hamlet emits
                    // unquoted URL attributes like `<a href=/>` (RootR), whose
                    // trailing `/` is part of the value `/` — NOT a self-close.
                    let is_self_close = tag.ends_with('/')
                        && tag[..tag.len() - 1]
                            .ends_with([' ', '"', '\'']);
                    let starts = i + 1;
                    let name_end = tag[1..]
                        .find([' ', '>', '/'])
                        .map(|x| x + 1)
                        .unwrap_or(tag.len());
                    let name = &inner[starts..starts + (name_end - 1)];
                    let is_void = matches!(
                        name.to_ascii_lowercase().as_str(),
                        "br" | "img" | "input" | "meta" | "link" | "hr"
                    );
                    if !is_self_close && !is_void {
                        depth += 1;
                    }
                    i += end + 1;
                }
            } else {
                i += 1;
            }
        }
        false
    }
    for class in [
        "ui-layout-north",
        "ui-layout-west",
        "ui-layout-east",
        "ui-layout-center",
    ] {
        assert!(
            pane_appears_at_top_level(body_inner, class),
            ".{} must be a direct child of <body> (jquery-layout \
             requires this — see test rationale).  body inner:\n{}",
            class,
            body_inner,
        );
    }
}

// ---------------------------------------------------------------------
// GET /thy/trace/<idx>/main/*path — JsonHtml AJAX envelope
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_main_help_envelope_matches_haskell_keys() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/main/help"))
        .send()
        .await
        .expect("send main/help");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(
        ct.starts_with("application/json"),
        "expected application/json, got {}",
        ct
    );

    let v: serde_json::Value = res.json().await.expect("decode json");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("main_help.json");

    assert_eq!(
        rust_keys, haskell_keys,
        "main/help JSON keys diverge: rust={:?}, haskell={:?}",
        rust_keys, haskell_keys
    );

    // The envelope must have both keys per Haskell's JsonHtml.
    let title = v.get("title").and_then(|t| t.as_str()).unwrap_or("");
    let html = v.get("html").and_then(|t| t.as_str()).unwrap_or("");
    assert!(!title.is_empty(), "title must be non-empty");
    assert!(!html.is_empty(), "html must be non-empty");
}

#[tokio::test]
async fn test_main_rules_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/main/rules"))
        .send()
        .await
        .expect("send main/rules");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode json");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("main_rules.json");
    assert_eq!(rust_keys, haskell_keys);

    // The Rust rules view names the rules.  issue193 has ONE and TWO.
    let html = v.get("html").and_then(|t| t.as_str()).unwrap_or("");
    assert!(html.contains("ONE"), "rules html should mention rule ONE");
    assert!(html.contains("TWO"), "rules html should mention rule TWO");
}

#[tokio::test]
async fn test_main_message_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/main/message"))
        .send()
        .await
        .expect("send main/message");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode json");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("main_message.json");
    assert_eq!(rust_keys, haskell_keys);

    // HS `messageSnippet` (Web/Theory.hs:920-931): Signature +
    // Construction/Deconstruction rule sections (NOT restrictions — those
    // live on the rules page).
    let html = v.get("html").and_then(|t| t.as_str()).unwrap_or("");
    assert!(
        html.contains("Signature")
            && html.contains("Construction Rules")
            && html.contains("Deconstruction Rules"),
        "message html should have Signature + Construction/Deconstruction sections; html={}",
        html
    );
}

#[tokio::test]
async fn test_main_lemma_envelope() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/main/lemma/debug"))
        .send()
        .await
        .expect("send main/lemma");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("main_lemma.json");
    assert_eq!(rust_keys, haskell_keys);

    let title = v.get("title").and_then(|t| t.as_str()).unwrap_or("");
    let html = v.get("html").and_then(|t| t.as_str()).unwrap_or("");
    assert!(
        title.contains("debug"),
        "title should mention the lemma name; got {:?}",
        title
    );
    // HS `htmlThyPath` renders `TheoryLemma _ -> text "this is a mistake"`
    // (Web/Theory.hs:1068) — a deliberate upstream quirk; the bare
    // `main/lemma/<name>` path is never used by the frontend (it always
    // links to `main/proof/<name>`).  We match the oracle verbatim; the
    // HS capture is `{"html":"this is a mistake<br/>\n",...}`.
    assert!(
        html.contains("this is a mistake"),
        "html must match HS's `this is a mistake` quirk; got {}",
        html
    );
}

// ---------------------------------------------------------------------
// 404 for unknown idx
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_main_with_missing_idx_returns_404_html() {
    // Haskell `withTheory` returns 404 HTML for an unknown idx
    // (see `src/Web/Handler.hs:660-666`).  We mirror that exactly —
    // the frontend's loading-dialog dismiss / global error handler
    // distinguishes 404 from a JSON envelope.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/99/main/help"))
        .send()
        .await
        .expect("send main with bad idx");
    assert_eq!(res.status(), 404, "missing idx must be 404 (matches Haskell)");
    let ct = content_type(&res);
    assert!(
        ct.starts_with("text/html"),
        "404 must be text/html; got {}",
        ct
    );
}

#[tokio::test]
async fn test_overview_with_missing_idx_returns_404_html() {
    // Same property for the framed HTML route.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/99/overview/help"))
        .send()
        .await
        .expect("send overview with bad idx");
    assert_eq!(res.status(), 404);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/html"));
}

// ---------------------------------------------------------------------
// /source, /message, /download
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_source_returns_plain_text() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/source"))
        .send()
        .await
        .expect("send source");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
    let body = res.text().await.expect("read");
    // The source route renders the full `prettyClosedTheory` (see
    // theory.rs `render_theory_source`).  This test keeps a loose
    // structural check — the theory name must appear — since exact
    // byte parity with Haskell is covered by the web-parity gate.
    assert!(
        body.contains("RevealingSignatures"),
        "source should contain the theory name; got {}",
        body,
    );
}

#[tokio::test]
async fn test_message_deduction_returns_plain_text() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/message"))
        .send()
        .await
        .expect("send message");
    assert_eq!(res.status(), 200);
    let ct = content_type(&res);
    assert!(ct.starts_with("text/plain"), "got CT={}", ct);
}

#[tokio::test]
async fn test_download_for_local_theory_returns_source_file() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/download/x.spthy"))
        .send()
        .await
        .expect("send download");
    assert_eq!(res.status(), 200);

    // Haskell uses `application/octet-stream` (see
    // `getDownloadTheoryR` in `src/Web/Handler.hs:1669-1672` — it
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

    let body = res.text().await.expect("read");
    // Body must be the .spthy source we loaded.
    assert!(
        body.contains("theory RevealingSignatures"),
        "download body should contain the original .spthy source; got {}",
        &body[..body.len().min(200)]
    );
}

#[tokio::test]
async fn test_download_for_missing_idx_returns_404_html() {
    // Haskell `withTheory` notFound for `/download/...` too.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/99/download/x.spthy"))
        .send()
        .await
        .expect("send download with bad idx");
    assert_eq!(res.status(), 404);
}

// ---------------------------------------------------------------------
// /unload  (GET → redirect to /)
// ---------------------------------------------------------------------

#[tokio::test]
async fn test_unload_redirects_to_root() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/unload"))
        .send()
        .await
        .expect("send unload");
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
    let res = s
        .client
        .post(s.url("/thy/trace/1/reload"))
        .send()
        .await
        .expect("send reload");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    let rust_keys = json_top_keys(&v);
    let haskell_keys = haskell_capture_keys("reload.json");
    assert_eq!(rust_keys, haskell_keys);
    let redir = v.get("redirect").and_then(|t| t.as_str()).unwrap_or("");
    // Haskell `postReloadTheoryR` uses `replaceTheory` at the SAME idx
    // (see `src/Web/Handler.hs:437-447`).  Match exactly — preserves
    // URLs bookmarked by the user.
    assert!(
        redir.starts_with("/thy/trace/1/overview/help"),
        "reload must redirect to the SAME idx (replaceTheory semantics); got {:?}",
        redir,
    );
}
