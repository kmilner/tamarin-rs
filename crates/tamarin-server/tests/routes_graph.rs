// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Integration tests for the graph routes.
//!
//! Coverage:
//!   - DOT output via the in-process `system_to_dot` against a
//!     simple known-shape proof system.
//!   - `/intdot` returns the HTML shell whose `dotsrc` points at `/json`.
//!   - `/interactive-graph-def` draws proof nodes and source cases, the
//!     latter byte-for-byte against the oracle's own document (the route
//!     serialises through `showDot`, exactly as upstream's does); for it and
//!     `/graph`, every other theory path is Yesod's 500 page.
//!   - `/json` returns the aeson-pretty JSON graph, with and without
//!     `abbrevInBackend`; after an autoprove its nodes and edges are the
//!     searched node's own system (the `SysRetention::KeepAll` guard).
//!   - On all three, a source/case index naming no case is the Not Found
//!     page — the port's deliberate divergence from upstream's unchecked
//!     `!!`, whose 500 pages leak the GHC CallStack.

mod common;

use common::*;

#[tokio::test]
async fn intdot_returns_html_shell() {
    // HS `getInteractiveDotGraphR` (`src/Web/Handler.hs:903-911`) returns the
    // `intdotLayout True` HTML shell page (`src/Web/Types.hs:795-824`) — a
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
/// (`imgThyPath` at `src/Web/Theory.hs:1416`, `dotGraphString` at `:2323`).
#[tokio::test]
async fn dot_routes_unhandled_path_is_internal_error() {
    let s = start_server_with_theory("issue193.spthy").await;
    for (path, capture) in [
        ("/thy/trace/1/graph/help", "graph_unhandled_path.html"),
        ("/thy/trace/1/graph/rules", "graph_unhandled_path.html"),
        (
            "/thy/trace/1/graph/lemma/debug",
            "graph_unhandled_path.html",
        ),
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
    // The route answers `D.showDot "G"`'s container verbatim (`dotGraphString`,
    // `src/Web/Theory.hs:2312-2318`): the QUOTED digraph id, and the blank line
    // `"\n}\n"` leaves before the closing brace
    // (`lib/utils/src/Text/Dot.hs:246-248`).
    // The document between them is pinned byte for byte against the oracle by
    // `interactive_graph_def_renders_source_cases`.
    assert!(body.starts_with("digraph \"G\" {\n"), "header: {body:.40}");
    assert!(body.ends_with("\n\n}\n"), "trailer: {body:?}");

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
        assert_eq!(
            body,
            haskell_capture(capture),
            "{path} must be the oracle's document byte for byte"
        );
    }
}

/// A case index naming no case is a plain `notFound` on the dot routes: the
/// Not Found page, 404, whichever end of the list the index falls off.
///
/// Upstream feeds the index into `cases !! (i-1) !! (j-1)` unchecked
/// (`src/Web/Theory.hs:1422` for `/graph`, `:2329` for
/// `/interactive-graph-def`), so these URLs answer 500 with the raw
/// `Prelude.!!` text and its GHC CallStack; RS deliberately corrects that,
/// which is why these are the only cases-route responses the port does not
/// byte-compare against a capture.
#[tokio::test]
async fn dot_routes_out_of_range_case_is_not_found() {
    let s = start_server_with_theory("issue193.spthy").await;
    for path in [
        "/thy/trace/1/graph/cases/refined/0/0",
        "/thy/trace/1/graph/cases/refined/-1/1",
        "/thy/trace/1/graph/cases/refined/1/9",
        "/thy/trace/1/graph/cases/refined/-9223372036854775808/1",
        "/thy/trace/1/interactive-graph-def/cases/refined/0/0",
        "/thy/trace/1/interactive-graph-def/cases/refined/-1/1",
        "/thy/trace/1/interactive-graph-def/cases/refined/-1/-1",
        "/thy/trace/1/interactive-graph-def/cases/refined/9/9",
    ] {
        assert_not_found_page(&s, path).await;
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
    assert_eq!(content_type(&res), ".json");
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

/// `graph_json_returns_json_graph_with_dot_json_content_type` reads the lemma
/// root, which carries no rule instances, so its assertions hold over an EMPTY
/// graph and cannot see whether the solved systems survive.  Autoprove `debug`
/// and re-read the witness node: its system must actually be there.  This is
/// the regression guard for `init_process_globals`' `SysRetention::KeepAll` —
/// without it every searched proof node drops its `System` and every
/// post-autoprove graph renders empty.
#[tokio::test]
async fn graph_json_after_autoprove_carries_the_system() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/autoprove/idfs/0/False/proof/debug"))
        .send()
        .await
        .expect("send autoprove");
    assert_eq!(res.status(), 200);
    let redirect: serde_json::Value = res.json().await.expect("autoprove replies JSON");
    // `{"redirect": "/thy/trace/2/overview/proof/debug/<path>"}` — the graph
    // route for the same node is that path with `overview` swapped for `json`.
    let target = redirect["redirect"]
        .as_str()
        .expect("autoprove must redirect to the proved node")
        .replace("/overview/", "/json/");
    let body = s
        .client
        .get(s.url(&target))
        .send()
        .await
        .expect("send")
        .text()
        .await
        .expect("text");
    let v: serde_json::Value = serde_json::from_str(&body).expect("body must be valid JSON");
    let graph = &v["graphs"][0];
    assert!(
        !graph["jgNodes"].as_array().expect("jgNodes").is_empty(),
        "the autoproved node's graph must carry its system's rule instances, \
         not an empty node list; got: {}",
        body
    );
    assert!(
        !graph["jgEdges"].as_array().expect("jgEdges").is_empty(),
        "the autoproved node's graph must carry its system's edges; got: {}",
        body
    );
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
    // (`src/Web/Theory.hs:1318`), which Yesod renders as its 500 page — the
    // `defaultLayout` frame around `<h1>Internal Server Error</h1>` and the
    // exception text, byte-for-byte the captured Haskell response.
    let s = start_server_with_theory("issue193.spthy").await;
    let expected = haskell_capture("json_rules.html");
    for path in ["/thy/trace/1/json/rules", "/thy/trace/1/json/lemma/debug"] {
        let res = s.client.get(s.url(path)).send().await.expect("send");
        assert_eq!(res.status(), 500, "{path} must be a 500");
        assert_eq!(
            content_type(&res),
            "text/html; charset=utf-8",
            "{path} must carry the error page's content type"
        );
        assert_eq!(res.text().await.expect("text"), expected, "{path}");
    }
}

#[tokio::test]
async fn graph_json_out_of_range_source_index_is_not_found() {
    // `parseCases` reads both indices with `safeRead` at `ReadS Int`
    // (`src/Web/Types.hs:443`), so 0, a negative one and `Int` minBound all
    // parse and reach the handler alongside a past-the-end one.  Upstream
    // hands every one of them to `casesCode`'s unchecked
    // `cases !! (i-1) !! (j-1)` (`src/Web/Theory.hs:1322`), which raises: the
    // response is a 500 whose body is `Prelude.!!: negative index` or
    // `index too large` plus a CallStack naming the failing `!!` (minBound
    // wraps `i-1` to maxBound, so even that one reports "too large").  RS
    // deliberately corrects it — an index naming no case is a miss, and every
    // one of these answers the ordinary Not Found page.
    let s = start_server_with_theory("issue193.spthy").await;
    for path in [
        "/thy/trace/1/json/cases/refined/0/0",
        "/thy/trace/1/json/cases/refined/-1/1",
        "/thy/trace/1/json/cases/refined/-1/-1",
        // The source index resolves; only the case index is out of range.
        "/thy/trace/1/json/cases/refined/1/-1",
        "/thy/trace/1/json/cases/refined/1/0",
        "/thy/trace/1/json/cases/refined/9/9",
        "/thy/trace/1/json/cases/refined/-9223372036854775808/1",
    ] {
        assert_not_found_page(&s, path).await;
    }
}

#[tokio::test]
async fn graph_json_source_case_returns_json_graph() {
    // `graphJsonThyPath`'s `TheorySource` branch (`src/Web/Theory.hs:1316`)
    // serialises the `(i-1, j-1)` case system under the label
    // `Theory: <thy> Case: <i>:<j>` — the 1-based indices straight from the
    // path.  Covers the branch the out-of-range 404 above cannot reach.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/json/cases/refined/1/1"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    assert_eq!(content_type(&res), ".json");
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

#[tokio::test]
async fn graph_json_abbrev_in_backend_shortens_long_terms() {
    // `getTheoryGraphJsonR` runs the sub-proof's system through
    // `Web.Utils.abbrev` when `abbrevInBackend` is present
    // (`src/Web/Handler.hs:1440`, `src/Web/Theory.hs:1330-1333`): every
    // premise/conclusion term of `size >= 30` is replaced by a
    // `Name AbbrevName` constant named after the term's head symbol, with an
    // occurrence counter from that symbol's SECOND abbreviation on.  The body
    // is byte-compared against the Haskell capture.
    let s = start_server_with_theory("BigTermProved.spthy").await;
    let path = "/thy/trace/1/json/proof/done/_/Init/Init";
    let abbreviated = s
        .client
        .get(s.url(&format!("{path}?abbrevInBackend=1")))
        .send()
        .await
        .expect("send");
    assert_eq!(abbreviated.status(), 200);
    let abbreviated = abbreviated.text().await.expect("text");
    assert_eq!(abbreviated, haskell_capture("json_proof_abbrev.json"));

    // The abbreviation constants render as their bare ids — no quotes, no
    // sigil (`show (Name AbbrevName n) = show n`, LTerm.hs:240).
    assert!(
        abbreviated.contains(r#""jgnFactShow": "A( g3 )""#),
        "abbreviated fact must show the bare constant"
    );

    // Without the parameter the same node keeps its full terms, so the two
    // bodies differ.
    let plain = s.client.get(s.url(path)).send().await.expect("send");
    assert_eq!(plain.status(), 200);
    let plain = plain.text().await.expect("text");
    assert!(
        plain.contains(r#""jgnFactShow": "A( g(f(~x, f(~x,"#),
        "unabbreviated fact must keep the nested term"
    );
    assert!(plain.len() > abbreviated.len());
}

#[test]
fn dot_output_for_a_simple_system() {
    // The whole document `system_to_dot` produces for a one-rule system, which
    // is the only exercise that entry point gets: it pairs the batch writer's
    // options (`Batch.hs:254-255`) with the web routes' label, a combination no
    // upstream call site makes.  Every byte here is `Text.Dot`'s, anchored on
    // the oracle by
    // `constraint::system::dot::showdot::tests::single_rule_matches_the_oracle_bytes`:
    // unindented statements, quoted numeric attribute values, `node[…]`
    // abutting its id, the three record PORTS (`n0`/`n1`/`n2`) allocated off
    // the graph-global counter before the node itself (`n3`), and the blank
    // line `showDot` leaves before the closing brace.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::constraint::system::dot::system_to_dot;
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
    assert_eq!(
        dot,
        concat!(
            "digraph \"G\" {\n",
            "nodesep=\"0.3\";\n",
            "ranksep=\"0.3\";\n",
            "node[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\"];\n",
            "edge[fontsize=\"8\",fontname=\"Helvetica\"];\n",
            "n3[shape=\"record\",label=\"{{<n0> Fr( ~k )}|{<n1> #i : Setup}|{<n2> Out( ~k )}}\"\
             ,fillcolor=\"#d5d897\",style=\"filled\",fontcolor=\"black\",role=\"Undefined\"];\n",
            "\n",
            "}\n",
        )
    );
}
