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

#[tokio::test]
async fn graph_for_help_returns_not_found() {
    // For paths without an associated system (help / message / rules),
    // the graph route returns 404 — matching Haskell `getTheoryGraphR`,
    // which returns `notFound` when `imgThyPath` yields `Nothing`
    // (`src/Web/Handler.hs`).  There is no placeholder SVG.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/graph/help"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 404);
}

#[tokio::test]
async fn interactive_graph_def_returns_dot() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/interactive-graph-def/proof/debug/_"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    assert!(body.contains("digraph"));
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
    // (`src/Web/Theory.hs:1316`), which Yesod reports as 500.
    let s = start_server_with_theory("issue193.spthy").await;
    for path in ["/thy/trace/1/json/rules", "/thy/trace/1/json/lemma/debug"] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 500, "{path} must be a 500");
    }
    // An out-of-range case index is HS `!!` raising `index too large`.
    let res = s
        .client
        .get(s.url("/thy/trace/1/json/cases/refined/9/9"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 500);
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
