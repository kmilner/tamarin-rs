// Currently GPL 3.0 until granted permission by the following authors:
//   Artur Cygan, Simon Meier, Jannik Dreier, Felix Linker, Cas Cremers,
//   "Jackie" (github kanakanajm), Ralf Sasse, Yann Colomb, Benedikt Schmidt,
//   "Tom" (github BTom-GH), Adrian Dapprich, Alexander Dax, symphorien,
//   Jérôme (github Azurios-git), and other minor contributors (see upstream
//   git history)
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
    // HS `getInteractiveDotGraphR` (`src/Web/Handler.hs:897`) returns the
    // `intdotLayout` HTML shell page (`src/Web/Types.hs:727`) — a
    // `<dot-graph-viz>` custom element whose `dotsrc` points at the
    // `interactive-graph-def` route (which serves the raw DOT the bundled
    // client-side viz renders).  It is NOT the raw DOT itself.
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/intdot/proof/debug/_"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("text");
    assert!(body.contains("<dot-graph-viz"),
        "intdot must be the HTML shell with a <dot-graph-viz>, got: {}",
        &body[..body.len().min(200)]);
    assert!(body.contains("/interactive-graph-def/proof/debug/_"),
        "the shell's dotsrc must point at interactive-graph-def; got: {}",
        &body[..body.len().min(300)]);
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

#[test]
fn dot_output_for_a_simple_system() {
    // In-process test against a known-shape proof system.  We build
    // a System with a single rule node + an Out edge and confirm
    // the DOT output contains the expected structural pieces.
    use tamarin_server::handlers::dot::system_to_dot;
    use tamarin_theory::constraint::system::System;
    use tamarin_theory::fact::{fresh_fact, out_fact};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    let mut sys = System::empty();
    let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let info: RuleInfo<
        ProtoRuleACInstInfo,
        tamarin_theory::rule::IntrRuleACInfo,
    > = RuleInfo::Proto(ProtoRuleACInstInfo {
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
