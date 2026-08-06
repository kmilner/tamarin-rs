use super::*;
use tamarin_theory::constraint::system::System;

#[test]
fn dot_for_empty_system() {
    let sys = System::empty();
    let s = system_to_dot(&sys);
    assert!(s.starts_with("digraph G {"));
    assert!(s.contains("nodesep"));
    assert!(s.trim_end().ends_with('}'));
}

#[test]
fn dot_for_node_with_rule() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
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
    let s = system_to_dot(&sys);
    assert!(s.contains("Setup"));
    assert!(s.contains("Fr"));
    assert!(s.contains("Out"));
}

/// Build a two-node system plus the edge between them, and a second copy of
/// it with one endpoint's node dropped from `sNodes` (`hidden` = 0 for the
/// source, 1 for the target) — the shape `compressSystem`'s `hideRule`
/// (Simplification.hs:125-152) leaves behind: the node is gone from the
/// drawn system while an edge still names it, so `systemMissingNodes`
/// (Graph.hs:116-122) draws it as a trapezium.
fn hidden_endpoint_graph(
    src_conc: LNFact,
    tgt_prem: LNFact,
    hidden: usize,
) -> (System, System, GEdge) {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_theory::rule::{
        ConcIdx, PremIdx, ProtoRuleACInstInfo, Rule, RuleAttributes, RuleInfo,
    };
    let mk = |name: &'static str, prems: Vec<LNFact>, concs: Vec<LNFact>| {
        let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(name),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        Rule::new(info, prems, concs, Vec::new())
    };
    let n1 = LVar::new("vr", LSort::Node, 1);
    let n2 = LVar::new("vr", LSort::Node, 2);
    let mut sys = System::empty();
    sys.add_node(n1, mk("Producer", Vec::new(), vec![src_conc]));
    sys.add_node(n2, mk("Consumer", vec![tgt_prem], Vec::new()));
    let src = (n1, ConcIdx(0));
    let tgt = (n2, PremIdx(0));
    sys.add_edge(tamarin_theory::constraint::constraints::Edge { src, tgt });
    let mut drawn = sys.clone();
    let gone = if hidden == 0 { n1 } else { n2 };
    drawn.nodes_mut().retain(|(id, _)| id != &gone);
    (sys, drawn, GEdge::System(src, tgt))
}

/// Render `drawn`'s repr while resolving edge facts as HS does.
fn dot_of(orig: &System, drawn: System) -> String {
    use crate::graph::render_system::RenderSystem;
    use crate::graph::repr::compute_basic_graph_repr;
    let simplified = RenderSystem::from_prover(drawn);
    let repr = compute_basic_graph_repr(&simplified);
    let graph = Graph {
        system: orig,
        simplified,
        repr,
        abbreviations: Abbreviations::new(),
    };
    let color_map = build_node_color_map(&orig.nodes);
    dot_graph_compact(&GraphOptions::default(), &color_map, &graph)
}

fn edge_line(dot: &str) -> String {
    dot.lines()
        .find(|l| l.contains("->"))
        .unwrap_or_else(|| panic!("no edge in\n{dot}"))
        .to_string()
}

/// `dotEdge`'s `check p` (Dot.hs:391-392) resolves an edge's endpoints with
/// the Graph-level `resolveNodePremFact`/`resolveNodeConcFact`
/// (Graph.hs:87-96), which read `_gSystem` — the ORIGINAL system
/// `systemToGraph` stores (Graph.hs:164) — while the nodes on screen come
/// from the compressed/simplified copy.  So a conclusion whose node the
/// compression hid still types the edge, even though that endpoint renders
/// as a portless `MissingNode` trapezium (Dot.hs:277).
///
/// The two endpoints carry deliberately different fact tags: every edge a
/// real system holds joins two copies of the SAME fact, so only an
/// asymmetric pair can tell the two systems apart.  Resolving against the
/// drawn system instead would find only `Fr( ~k )` — neither proto nor K —
/// and emit `color="gray30"`.
///
/// HS spells the surviving attribute list `[style="bold",weight="10.0",
/// color="gray50"]`, as captured for the missing-node edge in
/// `tests/fixtures/haskell-responses/igd_cases_raw.dot`.
#[test]
fn edge_style_resolves_hidden_source_conc_from_original_system() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{fresh_fact, proto_fact, Multiplicity};
    let a = Term::Lit(Lit::Var(LVar::new("A", LSort::Pub, 0)));
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let (orig, drawn, _) = hidden_endpoint_graph(
        proto_fact(Multiplicity::Persistent, "Reg", vec![a]),
        fresh_fact(k),
        0,
    );
    let dot = dot_of(&orig, drawn);
    assert!(
        dot.contains("trapezium"),
        "the hidden conclusion's node must draw as a MissingNode: {dot}"
    );
    let edge = edge_line(&dot);
    assert!(edge.contains("style=\"bold\""), "{edge}");
    assert!(edge.contains("color=\"gray50\""), "{edge}");
    assert!(!edge.contains("gray30"), "{edge}");
}

/// The premise half of the same rule: `check` tests the TARGET premise
/// first (Dot.hs:391), also through the original system, so a hidden target
/// node types the edge even when the visible source conclusion (`Out`) is
/// neither a proto nor a K fact and would yield `color="gray30"` on its own.
#[test]
fn edge_style_resolves_hidden_target_prem_from_original_system() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{out_fact, proto_fact, Multiplicity};
    let a = Term::Lit(Lit::Var(LVar::new("A", LSort::Pub, 0)));
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let (orig, drawn, _) = hidden_endpoint_graph(
        out_fact(k),
        proto_fact(Multiplicity::Persistent, "Reg", vec![a]),
        1,
    );
    let dot = dot_of(&orig, drawn);
    assert!(
        dot.contains("trapezium"),
        "the hidden premise's node must draw as a MissingNode: {dot}"
    );
    let edge = edge_line(&dot);
    assert!(edge.contains("style=\"bold\""), "{edge}");
    assert!(edge.contains("color=\"gray50\""), "{edge}");
    assert!(!edge.contains("gray30"), "{edge}");
}

/// `edge_style`'s persistence test is HS `isPersistentFact`
/// (Fact.hs:379-380), i.e. HS `factTagMultiplicity` (Fact.hs:383-388),
/// which maps `KUFact` and `KDFact` to `Persistent` alongside `ProtoFact
/// Persistent _ _`.  An edge with a LINEAR proto fact at one end and a
/// KU/KD fact at the other therefore takes the bold proto branch
/// (Dot.hs:393-395) AND its `gray50` colour, because `check` tests BOTH
/// endpoints for each predicate independently (Dot.hs:391-392).
///
/// The mixed endpoint pair is not reachable from a solver-built system:
/// HS `insertEdges` (Reduction.hs:281-284) unifies an edge's two facts with
/// `solveFactEqs`, which is `contradictoryIf` their tags differ
/// (Reduction.hs:766-769), and the two raw `sEdges` writers pair an `In`/`Fr`
/// premise with the matching conclusion of the `ISend`/`Fresh` rule they mint
/// (HS `exploitPrem`, Reduction.hs:243-260).  So this pins the predicate on a
/// hand-built system rather than on oracle bytes, using a persistent-proto
/// edge as the reference attribute string.
#[test]
fn edge_style_treats_k_facts_as_persistent() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{kd_fact, ku_fact, proto_fact, Multiplicity};
    let a = Term::Lit(Lit::Var(LVar::new("A", LSort::Pub, 0)));
    let m = Term::Lit(Lit::Var(LVar::new("m", LSort::Msg, 0)));
    // `hidden_endpoint_graph`'s drawn copy is irrelevant here: `edge_style`
    // reads only the original system.
    let style_of = |conc: LNFact, prem: LNFact| -> String {
        let (orig, _, edge) = hidden_endpoint_graph(conc, prem, 1);
        let GEdge::System(src, tgt) = edge else {
            unreachable!("hidden_endpoint_graph builds a SystemEdge")
        };
        edge_style(&orig.node_rule_map(), &src, &tgt)
    };
    let linear = || proto_fact(Multiplicity::Linear, "Use", vec![a.clone()]);
    let persistent = style_of(
        proto_fact(Multiplicity::Persistent, "Reg", vec![a.clone()]),
        linear(),
    );
    assert!(persistent.contains("style=\"bold\""), "{persistent}");
    assert!(persistent.contains("color=\"gray50\""), "{persistent}");
    // Two linear proto facts stay bold but uncoloured.
    let both_linear = style_of(linear(), linear());
    assert!(both_linear.contains("style=\"bold\""), "{both_linear}");
    assert!(!both_linear.contains("gray50"), "{both_linear}");
    // A KU/KD endpoint is persistent, at either end of the edge.
    for k in [ku_fact(m.clone()), kd_fact(m.clone())] {
        let conc_side = style_of(k.clone(), linear());
        assert_eq!(conc_side, persistent, "KU/KD conclusion: {k:?}");
        let prem_side = style_of(linear(), k.clone());
        assert_eq!(prem_side, persistent, "KU/KD premise: {k:?}");
    }
}

// Minimized web-parity repro (dot shape): the premise /
// conclusion rows of OIDC_Implicit's `Browser_Redirects_To_URI` record
// node must be laid out by HS `renderRow`/`renderBalanced`
// (Dot.hs:357-379) — each field at width `max 30 (round (1.3 * 100 *
// oneLineLen/sumLens))`, ribbon `round (w/1.5)` — NOT at the page width.
// Expected bytes extracted verbatim from the cached HS response for
// `/thy/trace/…/interactive-graph-def/proof/Nonce_Sources/…` on
// `examples/asiaccs20-POIDC/OIDC_Implicit.spthy` (`\l`→`\n`,
// `&nbsp;`→space, record escapes undone).
#[test]
fn render_balanced_matches_hs_oidc_rows() {
    use tamarin_term::builtin::pair;
    use tamarin_term::lterm::{pub_term, LSort, LVar};
    use tamarin_term::vterm::var_term;
    use tamarin_theory::fact::{proto_fact, Multiplicity};

    let mv = |n: &str| var_term(LVar::new(n, LSort::Msg, 0));
    let pv = |n: &str| var_term(LVar::new(n, LSort::Pub, 0));
    // <'id_token', <'iss', iss>, <'sub', sub>, <'aud', aud>, 'nonce', nonce>
    let inner = || {
        pair(
            pub_term("id_token"),
            pair(
                pair(pub_term("iss"), mv("iss")),
                pair(
                    pair(pub_term("sub"), mv("sub")),
                    pair(
                        pair(pub_term("aud"), mv("aud")),
                        pair(pub_term("nonce"), mv("nonce")),
                    ),
                ),
            ),
        )
    };
    // <RE1, $uri, AU1, <inner>, sig>
    let big = pair(
        mv("RE1"),
        pair(pv("uri"), pair(mv("AU1"), pair(inner(), mv("sig")))),
    );
    let f1 = proto_fact(
        Multiplicity::Persistent,
        "Server_to_Client_TLS",
        vec![pv("Server1"), mv("BR1"), big],
    );
    let f2 = proto_fact(
        Multiplicity::Persistent,
        "St_Browser_Session",
        vec![mv("BR2"), pv("Server1"), mv("BR1")],
    );
    let f3 = proto_fact(
        Multiplicity::Persistent,
        "St_Browser_Session",
        vec![mv("BR2"), pv("Server"), mv("BR3")],
    );
    let f4 = proto_fact(
        Multiplicity::Persistent,
        "Uri_belongs_to",
        vec![pv("uri"), pv("Server")],
    );

    // The 4-premise row: widths proportional to one-line lengths.
    let sp = |n: usize| " ".repeat(n);
    let rows = render_balanced(
        [&f1, &f2, &f3, &f4]
            .iter()
            .map(|f| fact_doc_of(f))
            .collect(),
    );
    assert_eq!(rows[0], format!(
            "!Server_to_Client_TLS( $Server1, BR1,\n{}<RE1, $uri, AU1, \n{}<'id_token', <'iss', iss>, <'sub', sub>, \n{}<'aud', aud>, 'nonce', nonce>, \n{}sig>\n)",
            sp(23), sp(24), sp(25), sp(24)), "row 0:\n{}", rows[0]);
    assert_eq!(
        rows[1],
        format!(
            "!St_Browser_Session( BR2,\n{}$Server1,\n{}BR1\n)",
            sp(21),
            sp(21)
        ),
        "row 1:\n{}",
        rows[1]
    );
    assert_eq!(
        rows[2],
        format!(
            "!St_Browser_Session( BR2,\n{}$Server,\n{}BR3\n)",
            sp(21),
            sp(21)
        ),
        "row 2:\n{}",
        rows[2]
    );
    assert_eq!(
        rows[3],
        format!("!Uri_belongs_to( $uri,\n{}$Server\n)", sp(17)),
        "row 3:\n{}",
        rows[3]
    );

    // The single-fact conclusion row: w = max 30 (round 130) = 130,
    // ribbon = round(130/1.5) = 87 — the 82-col pair fits ONE line
    // (at the page width 100/67 it would split like the premise row).
    let conc = proto_fact(
        Multiplicity::Persistent,
        "Client_to_Server_TLS",
        vec![
            mv("BR3"),
            pv("Server"),
            pair(mv("AU1"), pair(inner(), mv("sig"))),
        ],
    );
    let crow = render_balanced(vec![fact_doc_of(&conc)]);
    assert_eq!(crow[0], format!(
            "!Client_to_Server_TLS( BR3, $Server,\n{}<AU1, <'id_token', <'iss', iss>, <'sub', sub>, <'aud', aud>, 'nonce', nonce>, sig>\n)",
            sp(23)), "conc row:\n{}", crow[0]);
}

#[test]
fn dot_uses_pretty_printing_for_terms() {
    // Two pub var literals should render as $a, $b not as cryptic
    // M:0 placeholders.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{fresh_fact, out_fact};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    let mut sys = System::empty();
    let a = Term::Lit(Lit::Var(LVar::new("a", LSort::Pub, 0)));
    let info: RuleInfo<ProtoRuleACInstInfo, tamarin_theory::rule::IntrRuleACInfo> =
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Setup"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
    let rule = Rule::new(
        info,
        vec![fresh_fact(a.clone())],
        vec![out_fact(a.clone())],
        Vec::new(),
    );
    let nid = LVar::new("i", LSort::Node, 0);
    sys.add_node(nid, rule);
    let s = system_to_dot(&sys);
    assert!(s.contains("$a"), "expected $a in DOT output: {}", s);
}

#[test]
fn dot_emits_cluster_for_role() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    let mut sys = System::empty();
    let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let mk = |name: &str, role: Option<&str>| -> RuleACInst {
        let attrs = RuleAttributes {
            role: role.map(|r| r.to_string()),
            ..Default::default()
        };
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
                attributes: attrs,
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            vec![out_fact(kvar.clone())],
            // Action to prevent compression from hiding it.
            vec![out_fact(kvar.clone())],
        )
    };
    sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", Some("Alice")));
    sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", Some("Bob")));
    let s = system_to_dot(&sys);
    // Each role yields a cluster subgraph.
    assert!(s.contains("subgraph cluster_"), "missing cluster: {}", s);
    assert!(s.contains("Alice"), "missing Alice cluster label: {}", s);
    assert!(s.contains("Bob"), "missing Bob cluster label: {}", s);
}

#[test]
fn dot_with_sl0_does_not_collapse_less() {
    // Construct a system with a transitive less-chain; verify SL2/SL3
    // drops the redundant edge and SL0 keeps it.
    use tamarin_theory::constraint::constraints::LessAtom;
    let mut sys = System::empty();
    let a = LVar::new("a", tamarin_term::lterm::LSort::Node, 0);
    let b = LVar::new("b", tamarin_term::lterm::LSort::Node, 0);
    let c = LVar::new("c", tamarin_term::lterm::LSort::Node, 0);
    sys.content_mut()
        .less_atoms
        .push(LessAtom::new(a, b, Reason::Fresh));
    sys.content_mut()
        .less_atoms
        .push(LessAtom::new(b, c, Reason::Fresh));
    sys.content_mut()
        .less_atoms
        .push(LessAtom::new(a, c, Reason::Fresh));
    let opts_sl0 = crate::graph::GraphOptions {
        simplification_level: crate::graph::SimplificationLevel::SL0,
        compress: false,
        ..crate::graph::GraphOptions::default()
    };
    let s0 = system_to_dot_with(&sys, &opts_sl0);
    // Count dashed less-edges by `style=\"dashed\"` occurrences.
    let dashed_sl0 = s0.matches("style=\"dashed\"").count();
    let opts_sl3 = crate::graph::GraphOptions {
        simplification_level: crate::graph::SimplificationLevel::SL3,
        compress: false,
        ..crate::graph::GraphOptions::default()
    };
    let s3 = system_to_dot_with(&sys, &opts_sl3);
    let dashed_sl3 = s3.matches("style=\"dashed\"").count();
    assert!(
        dashed_sl3 < dashed_sl0,
        "SL3 should drop the redundant transitive edge: SL0={} SL3={}",
        dashed_sl0,
        dashed_sl3
    );
}

#[test]
fn dot_query_params_select_simplification() {
    // Smoke test for graph_options_from_query, matching HS `getOptions`
    // (Handler.hs): the `simplification` param reads `SL0..SL3` via the
    // derived `Read`, and `uncompress` presence turns compression off.
    let opts = crate::graph::graph_options_from_query("simplification=SL3&uncompress=");
    assert_eq!(
        opts.simplification_level,
        crate::graph::SimplificationLevel::SL3
    );
    assert!(!opts.compress);
}

#[test]
fn dot_with_cluster_passes_graphviz_lint() {
    // Render a small system with a cluster and (if `dot` is on
    // PATH) verify the output parses without errors.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    let mut sys = System::empty();
    let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let mk = |name: &str, role: Option<&str>| -> RuleACInst {
        let attrs = RuleAttributes {
            role: role.map(|r| r.to_string()),
            ..Default::default()
        };
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
                attributes: attrs,
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            vec![out_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],
        )
    };
    sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", Some("Alice")));
    sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", Some("Bob")));
    let s = system_to_dot(&sys);
    // Try piping through `dot` if it's available; otherwise skip.
    use std::io::Write;
    use std::process::{Command, Stdio};
    let child = Command::new("dot")
        .args(["-Tplain", "/dev/null"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();
    let Ok(mut child) = child else {
        return;
    };
    if let Some(mut sin) = child.stdin.take() {
        let _ = sin.write_all(s.as_bytes());
    }
    let out = child.wait_with_output().expect("dot wait");
    // If dot complains, the stderr would be non-empty.
    if !out.status.success() {
        panic!(
            "graphviz `dot` rejected our output:\nstderr=\n{}\nDOT was:\n{}",
            String::from_utf8_lossy(&out.stderr),
            s
        );
    }
}

#[test]
fn dot_abbreviations_and_legend_appear_only_when_abbreviate_is_set() {
    // Build a System whose nodes carry a long, frequently-repeated
    // compound term -- the abbreviation algorithm should emit a legend.
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_no_eq, Term};
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{Fact, FactTag};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    let mut sys = System::empty();
    let a = Term::Lit(Lit::Var(LVar::new("argument", LSort::Msg, 0)));
    let b = Term::Lit(Lit::Var(LVar::new("payload", LSort::Msg, 0)));
    let k = Term::Lit(Lit::Var(LVar::new("session_key", LSort::Msg, 0)));
    let senc = NoEqSym::new(
        b"senc".to_vec(),
        2,
        Privacy::Public,
        Constructability::Constructor,
    );
    // A long-ish term to abbreviate.
    let big = f_app_no_eq(senc, vec![f_app_no_eq(senc, vec![a, b]), k]);
    let mk = |name: &str| -> RuleACInst {
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            vec![Fact::new(FactTag::Out, vec![big.clone()])],
            vec![Fact::new(FactTag::Out, vec![big.clone()])],
        )
    };
    sys.add_node(LVar::new("a", LSort::Node, 1), mk("R1"));
    sys.add_node(LVar::new("b", LSort::Node, 2), mk("R2"));
    sys.add_node(LVar::new("c", LSort::Node, 3), mk("R3"));
    let s = system_to_dot(&sys);
    // The legend is emitted as a `plain`-shaped node with a TABLE
    // label (Haskell `generateLegend` emits no heading row).
    assert!(s.contains("legend ["), "no legend node: {}", s);
    assert!(s.contains("<TABLE"), "no abbreviations table: {}", s);
    assert!(s.contains("Out( SE1 )"), "facts not abbreviated: {}", s);

    // `goAbbreviate` gates only the APPLICATION of the abbreviations
    // (`renderLNFact`, Dot.hs:228-236, and `when abbreviate
    // generateLegend`, Dot.hs:538) — `systemToGraph` computes them either
    // way.  With the flag clear, the same system renders every term
    // spelled out, carries no legend, and mentions no generated name.
    let opts = GraphOptions {
        abbreviate: false,
        ..GraphOptions::default()
    };
    let plain = system_to_dot_with(&sys, &opts);
    assert!(
        plain.contains("Out( senc(senc(argument, payload), session_key) )"),
        "terms should be spelled out: {}",
        plain
    );
    assert!(!plain.contains("legend ["), "unexpected legend: {}", plain);
    assert!(!plain.contains("<TABLE"), "unexpected table: {}", plain);
    assert!(
        !plain.contains("SE1"),
        "abbreviation name leaked: {}",
        plain
    );
}

// Build a simple proto rule node with the given premises/actions/concs.
#[cfg(test)]
fn proto_node(name: &str, prems: Vec<LNFact>, acts: Vec<LNFact>, concs: Vec<LNFact>) -> RuleACInst {
    use tamarin_theory::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};
    Rule::new(
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        prems,
        concs,
        acts,
    )
}

#[test]
fn dot_persistent_fact_keeps_bang_prefix_and_zero_arity_parens() {
    // HS `prettyLNFact`: a persistent proto fact gets the `!` prefix
    // (showFactTag, Fact.hs:519-523), and a zero-arity fact renders
    // `Name( )` — `nestShort'` = `sep [text (n++"("), text ")"]`, whose
    // `sep` space-joins the two when they fit on one line (Class.hs:221-223 /
    // Fact.hs:539-546, see line 544).
    //
    // Authenticated against the repo's HS prover (v1.13.0) on a minimal
    // theory: `--prove` shows `[ Fr( ~k ) ] --> [ !Reg( ~k ), Started( ) ]`
    // — i.e. the `!` prefix on `!Reg` and the spaced empty parens on `Started`.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{fresh_fact, proto_fact, Multiplicity};
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let reg = proto_fact(Multiplicity::Persistent, "Reg", vec![k.clone()]);
    let started = proto_fact(Multiplicity::Linear, "Started", vec![]);
    let ru = proto_node("Setup", vec![fresh_fact(k)], vec![started], vec![reg]);
    sys.add_node(LVar::new("i", LSort::Node, 0), ru);
    // Disable compression so the action node / facts are not collapsed.
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let s = system_to_dot_with(&sys, &opts);
    assert!(s.contains("!Reg("), "persistent `!` prefix missing: {}", s);
    assert!(
        s.contains("Started( )"),
        "zero-arity fact should render `Started( )`: {}",
        s
    );
}

#[test]
fn dot_node_id_uses_show_lvar_format() {
    // HS `prettyNodeId = text . show`: a node id renders `#i` when idx==0
    // and `#i.2` when idx==2 (`instance Show LVar`, LTerm.hs:525-532;
    // sortPrefix LSortNode = "#", LTerm.hs:190-195, see line 194). The rule-node header is
    // `prettyNodeId v <-> colon <-> showDotRuleCaseName` (Dot.hs:236-379, see line 336).
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let mk = || {
        let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        proto_node("R", vec![], vec![out_fact(k.clone())], vec![out_fact(k)])
    };
    let mut sys0 = System::empty();
    sys0.add_node(LVar::new("i", LSort::Node, 0), mk());
    let s0 = system_to_dot_with(&sys0, &opts);
    assert!(s0.contains("#i : R"), "idx==0 should render `#i`: {}", s0);
    assert!(
        !s0.contains("#i0"),
        "idx==0 must not append the index: {}",
        s0
    );

    let mut sys2 = System::empty();
    sys2.add_node(LVar::new("i", LSort::Node, 2), mk());
    let s2 = system_to_dot_with(&sys2, &opts);
    assert!(
        s2.contains("#i.2 : R"),
        "idx==2 should render `#i.2`: {}",
        s2
    );
}

#[test]
fn dot_drops_diff_annotation_action_fact() {
    // HS `ruleLabelM.isNotDiffAnnotation` (Dot.hs:236-379, see line 341) drops the synthetic
    // `Diff<getRuleNameDiff ru>` linear proto fact from the action row.
    // For a standard proto rule `R`, getRuleNameDiff = "ProtoR", so the
    // dropped fact is `ProtoFact Linear "DiffProtoR" 0`.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{out_fact, proto_fact, Multiplicity};
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let diff = proto_fact(Multiplicity::Linear, "DiffProtoR", vec![]);
    let real = proto_fact(Multiplicity::Linear, "Visible", vec![]);
    let ru = proto_node("R", vec![], vec![diff, real], vec![out_fact(k)]);
    sys.add_node(LVar::new("i", LSort::Node, 0), ru);
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let s = system_to_dot_with(&sys, &opts);
    assert!(
        s.contains("Visible( )"),
        "non-diff action fact must remain: {}",
        s
    );
    assert!(
        !s.contains("DiffProtoR"),
        "Diff annotation fact must be filtered out: {}",
        s
    );
}

#[test]
fn dot_compact_intruder_node_is_plain_ellipse() {
    // HS `mkNode` CompactBoringNodes (Dot.hs:294-304): an intruder rule
    // collapses to a plain `mkSimpleNode` ellipse with NO fill/role attrs.
    // With an outgoing edge the label is `#id : name` (actions dropped);
    // without one it is the full `#id : name[acts]`. Compact endpoints also
    // carry no record ports (Dot.hs:303-304).
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::constraint::constraints::Edge;
    use tamarin_theory::fact::{in_fact, out_fact, proto_fact, Multiplicity};
    use tamarin_theory::rule::{ConcIdx, IntrRuleACInfo, PremIdx, Rule};
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, 0)));

    // (1) coerce with an outgoing edge -> compact `#j : coerce`, no actions.
    let mut sys = System::empty();
    let coerce = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![in_fact(x.clone())],
        vec![out_fact(x.clone())],
        vec![proto_fact(Multiplicity::Linear, "Act", vec![x.clone()])],
    );
    let isend = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::ISend),
        vec![in_fact(x.clone())],
        vec![out_fact(x.clone())],
        Vec::new(),
    );
    let j = LVar::new("j", LSort::Node, 0);
    let v = LVar::new("v", LSort::Node, 0);
    sys.add_node(j, coerce);
    sys.add_node(v, isend);
    sys.content_mut().edges.push(Edge {
        src: (j, ConcIdx(0)),
        tgt: (v, PremIdx(0)),
    });
    let out = system_to_dot_with(&sys, &opts);
    // Outgoing coerce: `#j : coerce` (its `Act(..)` action is dropped).
    assert!(
        out.contains("label=\"#j : coerce\",shape=ellipse"),
        "outgoing intruder node must be a plain ellipse `#j : coerce`: {out}"
    );
    assert!(
        !out.contains("coerce[Act"),
        "outgoing compact label must drop the action row: {out}"
    );
    // Compact nodes carry no record ports and no fill/role attrs.
    assert!(
        !out.contains("<p0>") && !out.contains("<c0>"),
        "compact intruder nodes must not emit record ports: {out}"
    );
    assert!(
        !out.contains("fillcolor"),
        "compact intruder nodes carry no fill: {out}"
    );
    // The compact->compact edge is emitted portless.
    assert!(
        out.contains("j_0 -> v_0"),
        "edge between two compact nodes must be portless: {out}"
    );

    // (2) coerce with NO outgoing edge keeps the bracketed action row.
    let mut sys2 = System::empty();
    let coerce2 = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![in_fact(x.clone())],
        vec![out_fact(x.clone())],
        vec![proto_fact(Multiplicity::Linear, "Act", vec![x.clone()])],
    );
    sys2.add_node(LVar::new("k", LSort::Node, 0), coerce2);
    let out2 = system_to_dot_with(&sys2, &opts);
    assert!(
        out2.contains("#k : coerce[Act( ~x )]"),
        "non-outgoing compact label keeps the `[..]` action row: {out2}"
    );
}

#[test]
fn dot_explicit_rule_color_attribute_sets_fillcolor() {
    // HS `dotNodeCompact` prefers `ruleColor'` (the explicit `color:`
    // attribute) over the colormap (Dot.hs:248-256). The hex is
    // `rgbToHex` of the attribute's Rgb.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    use tamarin_theory::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};
    use tamarin_utils::color::Rgb;
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let rgb = Rgb::new(1.0, 0.5, 0.0);
    let expected = tamarin_utils::color::rgb_to_hex(rgb); // "#ff7f00"
    let attrs = RuleAttributes {
        color: Some(rgb),
        ..Default::default()
    };
    let ru = Rule::new(
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Coloured"),
            attributes: attrs,
            loop_breakers: Vec::new(),
        }),
        Vec::new(),
        vec![out_fact(k.clone())],
        vec![out_fact(k)],
    );
    sys.add_node(LVar::new("i", LSort::Node, 0), ru);
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let s = system_to_dot_with(&sys, &opts);
    assert!(
        s.contains(&format!("fillcolor=\"{}\"", expected)),
        "explicit rule colour {} must be used as fillcolor: {}",
        expected,
        s
    );
}

#[test]
fn dot_no_cluster_preamble_sets_node_size_and_less_edge_color_first() {
    // No-cluster preamble mirrors HS setDefaultAttributes (Dot.hs:130-135)
    // — including `width=0.3,height=0.2` on the node defaults. The less
    // edge emits `color` before `style` (HS dotLessEdge, Dot.hs:406-410, see line 410).
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_theory::constraint::constraints::LessAtom;
    let mut sys = System::empty();
    let a = LVar::new("a", LSort::Node, 0);
    let b = LVar::new("b", LSort::Node, 0);
    sys.content_mut()
        .less_atoms
        .push(LessAtom::new(a, b, Reason::Fresh));
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        simplification_level: crate::graph::SimplificationLevel::SL0,
        ..GraphOptions::default()
    };
    let s = system_to_dot_with(&sys, &opts);
    assert!(
        s.contains("width=0.3,height=0.2"),
        "no-cluster preamble must set node width/height: {}",
        s
    );
    // `Reason::Fresh` -> "blue3"; color must precede style.
    assert!(
        s.contains("[color=\"blue3\",style=\"dashed\"]"),
        "less edge must emit color before style: {}",
        s
    );
}

#[test]
fn dot_cluster_preamble_uses_cluster_attributes() {
    // When clusters exist HS switches to setDefaultAttributesIfCluster
    // (Dot.hs:140-161), which sets `packmode`/`pack`/etc.
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    use tamarin_theory::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let mk = |name: &str, role: &str| -> RuleACInst {
        let attrs = RuleAttributes {
            role: Some(role.to_string()),
            ..Default::default()
        };
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
                attributes: attrs,
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            vec![out_fact(k.clone())],
            vec![out_fact(k.clone())],
        )
    };
    sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", "Alice"));
    sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", "Bob"));
    let s = system_to_dot(&sys);
    assert!(
        s.contains("packmode=cluster"),
        "cluster preamble must set packmode: {}",
        s
    );
    // Cluster subgraph styling: filled with the roleColor.
    assert!(
        s.contains("style=\"filled\";"),
        "cluster must be style=filled: {}",
        s
    );
}

// ---- palette-driven node attributes (HS Dot.hs:236-379) ------------------
// The `nodeColorMap` palette itself is exercised in `graph::color`.

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::constraint::constraints::{NodeId, Reason};
use tamarin_theory::rule::{
    ProtoRuleACInstInfo, ProtoRuleName as PRN, Rule as TRule, RuleAttributes, RuleInfo as TRuleInfo,
};

/// A bare protocol-rule node (no facts) with the given name.
fn named_proto_node(name: PRN) -> RuleACInst {
    TRule::new(
        TRuleInfo::Proto(ProtoRuleACInstInfo {
            name,
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )
}
fn nid(i: u64) -> NodeId {
    LVar::new("i", LSort::Node, i)
}
#[test]
fn rule_fillcolor_priority_matches_hs() {
    use tamarin_utils::color::Rgb;
    // Palette-only map for a single otherwise-group proto rule "R":
    // sizes = [0,1,0,0] -> (1,0) = #d5d897.
    let nodes: Vec<(NodeId, RuleACInst)> = vec![(nid(0), named_proto_node(PRN::Stand("R")))];
    let cm = build_node_color_map(&nodes);
    let r = &nodes[0].1;

    // (3) palette fallback: no explicit colour, no manual colour.
    assert_eq!(rule_fillcolor(r, &nid(0), None, &cm), "#d5d897");
    // (2) cluster manualNodeColor beats the palette.
    assert_eq!(rule_fillcolor(r, &nid(0), Some("#123456"), &cm), "#123456");
    // (1) explicit `color:` attribute beats both manual and palette.
    let mut colored = named_proto_node(PRN::Stand("R"));
    if let TRuleInfo::Proto(p) = &mut colored.info {
        p.attributes.color = Some(Rgb::new(1.0, 0.5, 0.0));
    }
    let expect = tamarin_utils::color::rgb_to_hex(Rgb::new(1.0, 0.5, 0.0));
    assert_eq!(
        rule_fillcolor(&colored, &nid(0), Some("#123456"), &cm),
        expect
    );

    // Node absent from the map -> HS `maybe "white" ...` = "white".
    let absent = named_proto_node(PRN::Stand("NotInMap"));
    assert_eq!(rule_fillcolor(&absent, &nid(9), None, &cm), "white");
}

#[test]
fn dot_rule_node_uses_faithful_palette_fillcolor() {
    // End-to-end through system_to_dot_with: a lone protocol rule is the
    // sole member of group 1, so its fill colour is the (1,0) palette hex #d5d897.
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    sys.add_node(
        nid(0),
        named_proto_node_with_out(PRN::Stand("R"), out_fact(k)),
    );
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let s = system_to_dot_with(&sys, &opts);
    assert!(
        s.contains("fillcolor=\"#d5d897\""),
        "rule node must use the faithful nodeColorMap palette hex: {}",
        s
    );
    // HS record attrs: the light palette colour is bright, so a black font
    // (Dot.hs:236-379, see line 258/284-287); no `role` attribute -> "Undefined" (Dot.hs:236-379, see line 259).
    assert!(
        s.contains("fontcolor=\"black\""),
        "bright palette colour must use a black font: {}",
        s
    );
    assert!(
        s.contains("role=\"Undefined\""),
        "role-less rule must render role=\"Undefined\": {}",
        s
    );
}

#[test]
fn color_uses_white_font_matches_hs_luminance() {
    use tamarin_utils::color::Rgb;
    // HS colorUsesWhiteFont: 0.2126r + 0.7152g + 0.0722b < 0.5 (and Just).
    assert!(!color_uses_white_font(None)); // absent -> black
    assert!(!color_uses_white_font(Some(Rgb::new(1.0, 1.0, 1.0)))); // white bg -> black font
    assert!(color_uses_white_font(Some(Rgb::new(0.0, 0.0, 0.0)))); // black bg -> white font
                                                                   // A dark blue (low luminance) uses a white font.
    assert!(color_uses_white_font(Some(Rgb::new(0.0, 0.0, 1.0)))); // 0.0722 < 0.5
                                                                   // A pure green is bright enough for a black font (0.7152 >= 0.5).
    assert!(!color_uses_white_font(Some(Rgb::new(0.0, 1.0, 0.0))));
}

#[test]
fn rule_node_emits_role_attribute() {
    // HS `role = fromMaybe "Undefined" (getNodeRole node)` (Dot.hs:236-379, see line 243,259):
    // a rule carrying a `role` attribute renders it verbatim.
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::out_fact;
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    let mut ru = named_proto_node_with_out(PRN::Stand("R"), out_fact(k));
    if let TRuleInfo::Proto(p) = &mut ru.info {
        p.attributes.role = Some("Alice".to_string());
    }
    sys.add_node(nid(0), ru);
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        ..GraphOptions::default()
    };
    let s = system_to_dot_with(&sys, &opts);
    assert!(
        s.contains("role=\"Alice\""),
        "rule node must render its role attribute: {}",
        s
    );
}

/// Like [`named_proto_node`] but with a single conclusion so the node is
/// not compressed away.
fn named_proto_node_with_out(name: PRN, conc: LNFact) -> RuleACInst {
    TRule::new(
        TRuleInfo::Proto(ProtoRuleACInstInfo {
            name,
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        Vec::new(),
        vec![conc.clone()],
        vec![conc],
    )
}
