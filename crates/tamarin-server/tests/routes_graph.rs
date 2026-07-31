// Currently GPL 3.0 until granted permission by the following authors:
//   arcz, meiersi, felixlinker, cascremers, Kanakanajm, jdreier,
//   rsasse, BTom-GH, beschmi, YannColomb, symphorien, xaDxelA, addap,
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   src/Web/Handler.hs, src/Web/Types.hs

//! Integration tests for the DOT-pipeline routes.
//!
//! Coverage:
//!   - DOT output via the in-process `system_to_dot` against a
//!     simple known-shape proof system.
//!   - HTTP endpoints `/intdot` and `/interactive-graph-def` return
//!     well-formed DOT text.
//!   - `/graph` returns either SVG or DOT fallback.

mod common;

use common::*;

#[tokio::test]
async fn intdot_returns_html_shell() {
    // HS `getInteractiveDotGraphR` (`src/Web/Handler.hs:903-911`) returns the
    // `intdotLayout True` HTML shell page (`src/Web/Types.hs:795-825`) — a
    // `<dot-graph-viz>` custom element whose `dotsrc` points at the JSON graph
    // route (which the bundled client-side viz fetches and draws), wrapped in
    // the `.graph-page` container with the floating Options bar.  It is NOT
    // the graph data itself.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/intdot/proof/debug/_"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    assert!(
        body.contains("<dot-graph-viz"),
        "intdot must be the HTML shell with a <dot-graph-viz>, got: {}",
        &body[..body.len().min(200)]
    );
    assert!(
        body.contains("dotsrc=\"/thy/trace/1/json/proof/debug/_\""),
        "the shell's dotsrc must point at the json route; got: {}",
        &body[..body.len().min(300)]
    );
    assert!(
        body.contains("<div class=\"graph-page\">") && body.contains("id=\"popout-options\""),
        "the shell must carry the .graph-page wrapper and the options bar; got: {}",
        &body[..body.len().min(600)]
    );
}

/// Both dot routes dispatch through a `thyPathSystem` that handles only
/// `TheorySource` and `TheoryProof`; help / message / rules / lemma hit its
/// catch-all `error "Unhandled theory path. This is a bug."` — a 500, not a
/// 404 — and each route's copy of the clause is named in the CallStack
/// (`imgThyPath` at `src/Web/Theory.hs:1414`, `dotGraphString` at `:2321`).
#[tokio::test]
async fn dot_routes_unhandled_path_is_internal_error() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        ("/thy/trace/1/graph/help", "graph_unhandled_path.html"),
        ("/thy/trace/1/graph/rules", "graph_unhandled_path.html"),
        ("/thy/trace/1/graph/lemma/debug", "graph_unhandled_path.html"),
        (
            "/thy/trace/1/interactive-graph-def/rules",
            "igd_unhandled_path.html",
        ),
        (
            "/thy/trace/1/interactive-graph-def/lemma/debug",
            "igd_unhandled_path.html",
        ),
    ] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 500, "{path} must be a 500");
        assert_eq!(
            res.text().await.expect("text"),
            haskell_capture(capture),
            "{path}"
        );
    }
}

#[tokio::test]
async fn interactive_graph_def_returns_dot() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/interactive-graph-def/proof/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    assert!(body.contains("digraph"));

    // A proof path that does not resolve is `dotGraphString`'s `Nothing`,
    // which `getTheoryInteractiveGraphR` (`src/Web/Handler.hs:1464-1470`)
    // answers with `notFound`.
    let res = s
        .client
        .get(s.url("/thy/trace/1/interactive-graph-def/proof/debug/_"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 404);
}

/// The dot labels of a graph, port anchors and whitespace dropped.
///
/// The two dot emitters serialise the same graph differently — `D.showDot`
/// quotes every attribute value, names nodes `n<k>` and gives every record
/// field a port, while the port's emitter writes bare values, names nodes after
/// the node id and ports only the premise/conclusion fields — which is what the
/// web-parity gate's dot canonicalisation (`scripts/web_normalize.py`, graph
/// compared by label rather than by serialisation) exists to see past.  What
/// must agree is the graph drawn: the labels, in order.
fn dot_label_texts(dot: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = dot;
    while let Some(pos) = rest.find("label=") {
        rest = &rest[pos + "label=".len()..];
        let value = match rest.strip_prefix('"') {
            Some(inner) => {
                let end = inner.find('"').unwrap_or(inner.len());
                let (value, tail) = inner.split_at(end);
                rest = tail;
                value
            }
            None => {
                let end = rest.find([',', ']', ';', '\n']).unwrap_or(rest.len());
                let (value, tail) = rest.split_at(end);
                rest = tail;
                value
            }
        };
        let mut cleaned = String::new();
        let mut in_port = false;
        for ch in value.chars() {
            match ch {
                '<' => in_port = true,
                '>' => in_port = false,
                _ if in_port || ch.is_whitespace() => {}
                _ => cleaned.push(ch),
            }
        }
        out.push(cleaned);
    }
    out
}

/// `thyPathSystem`'s `TheorySource` arm draws the `(i-1, j-1)` case, so both
/// dot routes serve a source case as readily as a proof node: the same graph
/// the oracle draws, for both source kinds.
#[tokio::test]
async fn interactive_graph_def_renders_source_cases() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        (
            "/thy/trace/1/interactive-graph-def/cases/refined/1/1",
            "igd_cases_refined.dot",
        ),
        (
            "/thy/trace/1/interactive-graph-def/cases/raw/1/1",
            "igd_cases_raw.dot",
        ),
    ] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 200, "{path} must be a 200");
        let body = res.text().await.expect("text");
        let expected = haskell_capture(capture);
        assert_eq!(
            dot_label_texts(&body),
            dot_label_texts(&expected),
            "{path} must draw the oracle's graph; got:\n{body}"
        );
        assert!(
            !dot_label_texts(&body).is_empty(),
            "{path} must draw a non-empty graph"
        );
    }
}

/// The `!!` on the source cases raises through the dot routes too, from each
/// route's own call site (`src/Web/Theory.hs:1420` for `/graph`, `:2327` for
/// `/interactive-graph-def`), source index first.
#[tokio::test]
async fn dot_routes_out_of_range_case_is_internal_error() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        (
            "/thy/trace/1/graph/cases/refined/0/0",
            "graph_cases_neg_index.html",
        ),
        (
            "/thy/trace/1/graph/cases/refined/-1/1",
            "graph_cases_neg_index.html",
        ),
        (
            "/thy/trace/1/graph/cases/refined/1/9",
            "graph_cases_too_large.html",
        ),
        (
            "/thy/trace/1/interactive-graph-def/cases/refined/0/0",
            "igd_cases_neg_index.html",
        ),
        (
            "/thy/trace/1/interactive-graph-def/cases/refined/-1/1",
            "igd_cases_neg_index.html",
        ),
        (
            "/thy/trace/1/interactive-graph-def/cases/refined/1/9",
            "igd_cases_too_large.html",
        ),
    ] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 500, "{path} must be a 500");
        assert_eq!(
            res.text().await.expect("text"),
            haskell_capture(capture),
            "{path}"
        );
    }
}

#[tokio::test]
async fn graph_json_returns_json_graph_with_dot_json_content_type() {
    // HS `getTheoryGraphJsonR` (`src/Web/Handler.hs:1435-1444`) hands the
    // rendered file to `sendFile (fromString ".json")`, so the response
    // `Content-Type` is the literal string `.json`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/json/proof/debug"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    assert_eq!(
        res.headers()
            .get("content-type")
            .and_then(|v| v.to_str().ok()),
        Some(".json")
    );
    let body = res.text().await.expect("text");
    assert!(
        body.starts_with("{\n    \"graphs\": ["),
        "aeson-pretty 4-space layout expected; got: {}",
        &body[..body.len().min(80)]
    );
    assert!(
        body.contains("\"jgLabel\": \"Theory: RevealingSignatures Lemma: debug\""),
        "graph label must be `Theory: <thy> Lemma: <lemma>`; got: {}",
        &body[..body.len().min(400)]
    );
    assert!(!body.ends_with('\n'), "no trailing newline");
}

#[tokio::test]
async fn graph_json_unresolvable_proof_path_is_empty_body() {
    // HS `proofPathCode` is `fromMaybe ""` over `resolveProofPath`, so an
    // unknown case name still answers 200 with an EMPTY body.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/json/proof/debug/_/no_such_case"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    assert_eq!(res.text().await.expect("text"), "");
}

#[tokio::test]
async fn graph_json_unhandled_path_is_internal_error() {
    // `graphJsonThyPath` handles only `TheorySource` / `TheoryProof`;
    // everything else hits `error "Unhandled theory path. This is a bug."`
    // (`src/Web/Theory.hs:1316`), which Yesod renders as its 500 page — the
    // `defaultLayout` frame around `<h1>Internal Server Error</h1>` and the
    // exception text, byte-for-byte the captured Haskell response.
    let s = start_server_with_theory("issue193.spthy").await;
    let expected = haskell_capture("json_rules.html");
    for path in ["/thy/trace/1/json/rules", "/thy/trace/1/json/lemma/debug"] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 500, "{path} must be a 500");
        assert_eq!(
            res.headers()
                .get("content-type")
                .and_then(|v| v.to_str().ok()),
            Some("text/html; charset=utf-8"),
            "{path} must carry the error page's content type"
        );
        assert_eq!(res.text().await.expect("text"), expected, "{path}");
    }
}

#[tokio::test]
async fn graph_json_out_of_range_source_index_is_internal_error() {
    // `casesCode`'s `cases !! (i-1) !! (j-1)` (`src/Web/Theory.hs:1320`): a
    // path index of 0 makes HS's `i-1` negative (`!!`'s `negIndex`), a
    // past-the-end one raises its `tooLarge`, and the CallStack in the error
    // page names the failing `!!`.
    //
    // `parseCases` reads both indices with `safeRead` at `ReadS Int`
    // (`src/Web/Types.hs:443`), so a NEGATIVE index parses too and lands on
    // the same `negIndex` — the message names the `!!`, never the index, so
    // `-1/1` and `0/0` carry the very same page.
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        (
            "/thy/trace/1/json/cases/refined/0/0",
            "json_cases_neg_index.html",
        ),
        (
            "/thy/trace/1/json/cases/refined/-1/1",
            "json_cases_neg_index.html",
        ),
        (
            "/thy/trace/1/json/cases/refined/-1/-1",
            "json_cases_neg_index.html",
        ),
        (
            // The source index resolves, so this is the SECOND `!!` failing —
            // a different call site, hence a different CallStack.
            "/thy/trace/1/json/cases/refined/1/-1",
            "json_cases_neg_case_index.html",
        ),
        (
            "/thy/trace/1/json/cases/refined/9/9",
            "json_cases_too_large.html",
        ),
    ] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 500, "{path} must be a 500");
        assert_eq!(
            res.headers()
                .get("content-type")
                .and_then(|v| v.to_str().ok()),
            Some("text/html; charset=utf-8"),
            "{path} must carry the error page's content type"
        );
        assert_eq!(
            res.text().await.expect("text"),
            haskell_capture(capture),
            "{path}"
        );
    }
}

#[tokio::test]
async fn graph_json_source_case_returns_json_graph() {
    // `graphJsonThyPath`'s `TheorySource` branch (`src/Web/Theory.hs:1316`)
    // serialises the `(i-1, j-1)` case system under the label
    // `Theory: <thy> Case: <i>:<j>` — the 1-based indices straight from the
    // path.  Covers the branch the out-of-range 500 above cannot reach.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/json/cases/refined/1/1"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    assert_eq!(
        res.headers()
            .get("content-type")
            .and_then(|v| v.to_str().ok()),
        Some(".json")
    );
    let body = res.text().await.expect("text");
    let v: serde_json::Value = serde_json::from_str(&body).expect("body must be valid JSON");
    assert_eq!(
        v["graphs"][0]["jgLabel"],
        serde_json::Value::String("Theory: RevealingSignatures Case: 1:1".to_string()),
        "source-case label must be `Theory: <thy> Case: <i>:<j>`; got: {}",
        &body[..body.len().min(400)]
    );
    assert_eq!(
        v["graphs"][0]["jgType"],
        serde_json::Value::String("Tamarin prover constraint system".to_string())
    );
}

#[test]
fn dot_output_for_a_simple_system() {
    // In-process test against a known-shape proof system.  We build
    // a System with a single rule node + an Out edge and confirm
    // the DOT output contains the expected structural pieces.
    use tamarin_server::handlers::dot::system_to_dot;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::constraint::system::System;
    use tamarin_theory::fact::{fresh_fact, out_fact};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };

    let mut sys = System::empty();
    let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let info: RuleInfo<ProtoRuleACInstInfo, tamarin_theory::rule::IntrRuleACInfo> =
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Setup"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
    let rule = Rule::new(
        info,
        vec![fresh_fact(kvar.clone())],
        vec![out_fact(kvar.clone())],
        Vec::new(),
    );
    let nid = LVar::new("i", LSort::Node, 0);
    sys.add_node(nid, rule);
    let dot = system_to_dot(&sys);
    assert!(dot.starts_with("digraph G {"), "header: {}", &dot[..40]);
    assert!(dot.contains("Setup"), "rule name should appear");
    assert!(dot.contains("Fr"), "Fresh-fact tag should appear");
    assert!(dot.contains("Out"), "Out-fact tag should appear");
    // Each rule's prems / concs should be DOT record ports.
    assert!(dot.contains("<p0>"));
    assert!(dot.contains("<c0>"));
    assert!(dot.trim_end().ends_with('}'));
}
