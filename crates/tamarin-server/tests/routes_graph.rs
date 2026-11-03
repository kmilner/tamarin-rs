// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Integration tests for the graph routes.
//!
//! Coverage:
//!   - DOT output via the in-process `system_to_dot` against a
//!     simple known-shape proof system.
//!   - `/intdot` returns the oracle's HTML shell byte for byte.  Its
//!     `dotsrc` points at `/json` under the requested theory path.
//!   - `/interactive-graph-def` draws proof nodes and source cases, the
//!     latter byte-for-byte against the oracle's own document (the route
//!     serialises through `showDot`, exactly as upstream's does); for it and
//!     `/graph`, every other theory path is Yesod's 500 page.
//!   - `/json` returns the aeson-pretty JSON graph, with and without
//!     `abbrevInBackend`; after an autoprove its nodes and edges are the
//!     searched node's own system (the `SysRetention::KeepAll` guard).
//!   - On all three, an invalid source/case index reproduces upstream's
//!     500 page from its unchecked
//!     `!!`, whose 500 pages leak the GHC CallStack.

mod common;

use common::*;

#[tokio::test]
async fn intdot_returns_html_shell() {
    // HS `getInteractiveDotGraphR` (`src/Web/Handler.hs`) returns the
    // `intdotLayout True` HTML shell page (`src/Web/Types.hs`) — a
    // `<dot-graph-viz>` custom element whose `dotsrc` points at the JSON graph
    // route (which the bundled client-side viz fetches and draws), wrapped in
    // the `.graph-page` container with the floating Options bar.  It is NOT
    // the graph data itself.
    let s = start_server_with_theory("issue193.spthy").await;
    // `intdotLayout` does not depend on the system, because the handler only
    // does `withTheory`.  It therefore answers the shell for any theory path,
    // and a lemma path is one of them.  The oracle capture comes from a lemma
    // path.  The test compares the response byte for byte.
    let res = s.get("/thy/trace/1/intdot/lemma/debug").await;
    assert_eq!(res.status(), 200);
    assert_eq!(
        res.text().await.expect("text"),
        haskell_capture("intdot.html")
    );

    // The shell's `dotsrc` is the same theory path, rendered again against the
    // json route.  An empty proof-tree case name therefore comes back as `_`.
    let res = s.get("/thy/trace/1/intdot/proof/debug/_").await;
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    assert!(
        body.contains("dotsrc=\"/thy/trace/1/json/proof/debug/_\""),
        "the shell's dotsrc must point at the json route; got: {}",
        &body[..body.len().min(300)]
    );
}

/// Both dot routes dispatch through a `thyPathSystem` that handles only
/// `TheorySource` and `TheoryProof`; help / message / rules / lemma hit its
/// catch-all `error "Unhandled theory path. This is a bug."` — a 500, not a
/// 404 — and each route's copy of the clause is named in the CallStack
/// (`imgThyPath` and `dotGraphString` in `src/Web/Theory.hs`).
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
        let res = s.get(path).await;
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
        .get("/thy/trace/1/interactive-graph-def/proof/debug")
        .await;
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    // The route answers `D.showDot "G"`'s container verbatim (`dotGraphString`,
    // `src/Web/Theory.hs`): the QUOTED digraph id, and the blank line
    // `"\n}\n"` leaves before the closing brace
    // (`lib/utils/src/Text/Dot.hs`).
    // The document between them is pinned byte for byte against the oracle by
    // `interactive_graph_def_renders_source_cases`.
    assert!(body.starts_with("digraph \"G\" {\n"), "header: {body:.40}");
    assert!(body.ends_with("\n\n}\n"), "trailer: {body:?}");

    // A proof path that does not resolve is `dotGraphString`'s `Nothing`,
    // which `getTheoryInteractiveGraphR` (`src/Web/Handler.hs`)
    // answers with `notFound`.
    let res = s
        .get("/thy/trace/1/interactive-graph-def/proof/debug/_")
        .await;
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
        let res = s.get(path).await;
        assert_eq!(res.status(), 200, "{path} must be a 200");
        let body = res.text().await.expect("text");
        assert_eq!(
            body,
            haskell_capture(capture),
            "{path} must be the oracle's document byte for byte"
        );
    }
}

/// Match both failing (!!) sites, including negative-index precedence and
/// wrapping Int subtraction, without crashing the server. Each callstack is
/// captured from the pinned Haskell oracle, not assembled by the test.
#[tokio::test]
async fn graph_routes_invalid_case_indices_match_haskell() {
    let s = start_server_with_theory("issue193.spthy").await;
    for route in ["json", "graph", "interactive-graph-def"] {
        for kind in ["raw", "refined"] {
            for (indices, failure) in [
                ("0/1", "source_negative"),
                ("-1/1", "source_negative"),
                ("9999/1", "source_large"),
                ("9999/9999", "source_large"),
                ("-9223372036854775808/1", "source_large"),
                ("1/0", "case_negative"),
                ("1/-1", "case_negative"),
                ("0/0", "case_negative"),
                ("-1/-1", "case_negative"),
                ("9999/0", "case_negative"),
                ("-9223372036854775808/-1", "case_negative"),
                ("1/9999", "case_large"),
                ("1/-9223372036854775808", "case_large"),
            ] {
                let path = format!("/thy/trace/1/{route}/cases/{kind}/{indices}");
                let res = s.get(&path).await;
                assert_eq!(res.status(), 500, "{path}");
                assert_eq!(content_type(&res), "text/html; charset=utf-8", "{path}");
                assert_eq!(
                    res.text().await.expect("text"),
                    haskell_capture(&format!("{route}_{failure}.html")),
                    "{path}"
                );
            }
        }
    }
    assert_eq!(
        s.get("/thy/trace/1/json/cases/refined/1/1").await.status(),
        200
    );
}

#[tokio::test]
async fn graph_json_returns_json_graph_with_dot_json_content_type() {
    // HS `getTheoryGraphJsonR` (`src/Web/Handler.hs`) hands the
    // rendered file to `sendFile (fromString ".json")`, so the response
    // `Content-Type` is the literal string `.json`.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/json/proof/debug").await;
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
/// the regression guard for the web session's `SysRetention::KeepAll` —
/// without it every searched proof node drops its `System` and every
/// post-autoprove graph renders empty.
#[tokio::test]
async fn graph_json_after_autoprove_carries_the_system() {
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .get("/thy/trace/1/autoprove/idfs/0/False/proof/debug")
        .await;
    assert_eq!(res.status(), 200);
    let redirect: serde_json::Value = res.json().await.expect("autoprove replies JSON");
    // `{"redirect": "/thy/trace/2/overview/proof/debug/<path>"}` — the graph
    // route for the same node is that path with `overview` swapped for `json`.
    let target = redirect["redirect"]
        .as_str()
        .expect("autoprove must redirect to the proved node")
        .replace("/overview/", "/json/");
    let body = s.get(&target).await.text().await.expect("text");
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
    let res = s.get("/thy/trace/1/json/proof/debug/_/no_such_case").await;
    assert_eq!(res.status(), 200);
    assert_eq!(res.text().await.expect("text"), "");
}

#[tokio::test]
async fn unknown_lemma_is_an_unresolvable_graph_path() {
    let s = start_server_with_theory("issue193.spthy").await;

    let json = s.get("/thy/trace/1/json/proof/notALemma").await;
    assert_eq!(json.status(), 200);
    assert_eq!(json.text().await.expect("JSON body"), "");

    for route in ["graph", "interactive-graph-def"] {
        let response = s
            .get(&format!("/thy/trace/1/{route}/proof/notALemma"))
            .await;
        assert_eq!(response.status(), 404, "{route}");
    }
}

#[tokio::test]
async fn graph_json_unhandled_path_is_internal_error() {
    // `graphJsonThyPath` handles only `TheorySource` / `TheoryProof`;
    // everything else hits `error "Unhandled theory path. This is a bug."`
    // (`src/Web/Theory.hs`), which Yesod renders as its 500 page — the
    // `defaultLayout` frame around `<h1>Internal Server Error</h1>` and the
    // exception text, byte-for-byte the captured Haskell response.
    let s = start_server_with_theory("issue193.spthy").await;
    let expected = haskell_capture("json_rules.html");
    for path in ["/thy/trace/1/json/rules", "/thy/trace/1/json/lemma/debug"] {
        let res = s.get(path).await;
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
async fn graph_json_source_case_returns_json_graph() {
    // `graphJsonThyPath`'s `TheorySource` branch (`src/Web/Theory.hs`)
    // serialises the `(i-1, j-1)` case system under the label
    // `Theory: <thy> Case: <i>:<j>` — the 1-based indices straight from the
    // path. Covers the successful branch alongside the bounds-error tests.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s.get("/thy/trace/1/json/cases/refined/1/1").await;
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
    // (`src/Web/Handler.hs`, `src/Web/Theory.hs`): every
    // premise/conclusion term of `size >= 30` is replaced by a
    // `Name AbbrevName` constant named after the term's head symbol, with an
    // occurrence counter from that symbol's SECOND abbreviation on.  The body
    // is byte-compared against the Haskell capture.
    let s = start_server_with_theory("BigTermProved.spthy").await;
    let path = "/thy/trace/1/json/proof/done/_/Init/Init";
    let abbreviated = s.get(&format!("{path}?abbrevInBackend=1")).await;
    assert_eq!(abbreviated.status(), 200);
    let abbreviated = abbreviated.text().await.expect("text");
    assert_eq!(abbreviated, haskell_capture("json_proof_abbrev.json"));

    // The abbreviation constants render as their bare ids — no quotes, no
    // sigil (`show (Name AbbrevName n) = show n`, LTerm.hs).
    assert!(
        abbreviated.contains(r#""jgnFactShow": "A( g3 )""#),
        "abbreviated fact must show the bare constant"
    );

    // Without the parameter the same node keeps its full terms, so the two
    // bodies differ.
    let plain = s.get(path).await;
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
    // options (`Batch.hs`) with the web routes' label, a combination no
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

/// `--with-json` switches `/graph` to HS's `OutJSON` branch: the system's
/// JSON graph is written to a file and `<json-cmd> <img> <json>` renders
/// the image (`jsonToImg`, Web/Theory.hs).  A stub renderer
/// stands in for the tool: it checks it was handed a non-empty JSON file
/// and writes a recognisable SVG.  A failing renderer is HS's
/// `imgGenerated False` → the generic Not Found page.
#[tokio::test]
async fn graph_renders_via_json_cmd_when_with_json_is_set() {
    use std::io::Write;
    use std::os::unix::fs::PermissionsExt;

    let dir = std::env::temp_dir().join(format!("tam-json-stub-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mkdir stub dir");
    let ok_stub = dir.join("json-ok.sh");
    {
        let mut f = std::fs::File::create(&ok_stub).expect("create stub");
        // $1 = img path, $2 = json path — the HS argument order.
        writeln!(f, "#!/bin/sh\n[ -s \"$2\" ] || exit 3\ngrep -q graphs \"$2\" || exit 4\nprintf '<svg><!--json-stub--></svg>' > \"$1\"").unwrap();
    }
    std::fs::set_permissions(&ok_stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    let fail_stub = dir.join("json-fail.sh");
    {
        let mut f = std::fs::File::create(&fail_stub).expect("create stub");
        writeln!(f, "#!/bin/sh\nexit 7").unwrap();
    }
    std::fs::set_permissions(&fail_stub, std::fs::Permissions::from_mode(0o755)).unwrap();

    let stub = ok_stub.to_string_lossy().to_string();
    let s = start_server_with_theory_and("issue193.spthy", |cfg| {
        cfg.json_path = Some(stub);
    })
    .await;
    let res = s.get("/thy/trace/1/graph/proof/debug").await;
    assert_eq!(res.status(), 200);
    assert_eq!(
        res.headers()
            .get("content-type")
            .and_then(|v| v.to_str().ok()),
        Some("image/svg+xml")
    );
    let body = res.text().await.expect("text");
    assert_eq!(body, "<svg><!--json-stub--></svg>");

    // The failing renderer: HS reports on stdout/stderr and the route
    // answers the generic Not Found page.
    let stub = fail_stub.to_string_lossy().to_string();
    let s = start_server_with_theory_and("issue193.spthy", |cfg| {
        cfg.json_path = Some(stub);
    })
    .await;
    let res = s.get("/thy/trace/1/graph/proof/debug").await;
    assert_eq!(res.status(), 404);

    let _ = std::fs::remove_dir_all(&dir);
}
