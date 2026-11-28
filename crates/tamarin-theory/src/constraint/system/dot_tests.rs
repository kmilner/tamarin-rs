// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::constraint::system::System;

#[test]
fn sapic_suffix_trimming_preserves_haskell_edge_cases() {
    assert_eq!(trim_sapic_name("role_step_12_3"), "role_step");
    assert_eq!(trim_sapic_name("role_step_x_3"), "role_step_x_3");
    assert_eq!(trim_sapic_name("role__"), "role");
    assert_eq!(trim_sapic_name("plain"), "plain");
}

/// An empty system renders as the bare container with no clusters.  It holds
/// the `setDefaultAttributes` preamble (System/Dot.hs) and `showDot`'s
/// blank line before the closing brace.  It holds nothing else.  There is no
/// legend scope, because there is nothing to abbreviate.  There is no stray
/// node statement and no rank statement.  The test compares the complete
/// document, because every substring check here also holds for output that
/// lost its body.
#[test]
fn dot_for_empty_system() {
    let sys = System::empty();
    assert_eq!(
        system_to_dot_with(&sys, &GraphOptions::default()),
        concat!(
            "digraph \"G\" {\n",
            "nodesep=\"0.3\";\n",
            "ranksep=\"0.3\";\n",
            "node[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\"];\n",
            "edge[fontsize=\"8\",fontname=\"Helvetica\"];\n",
            "\n",
            "}\n",
        )
    );
}

/// Build a two-node system plus the edge between them, and a second copy of
/// it with one endpoint's node dropped from `sNodes` (`hidden` = 0 for the
/// source, 1 for the target) — the shape `compressSystem`'s `hideRule`
/// (Simplification.hs) leaves behind: the node is gone from the
/// drawn system while an edge still names it, so `systemMissingNodes`
/// (Graph.hs) draws it as a trapezium.
fn hidden_endpoint_graph(src_conc: LNFact, tgt_prem: LNFact, hidden: usize) -> (System, System) {
    use crate::rule::{
        ConcIdx, IntrRuleACInfo, PremIdx, ProtoRuleACInstInfo, Rule, RuleAttributes, RuleInfo,
    };
    use tamarin_term::lterm::{LSort, LVar};
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
    sys.add_edge(crate::constraint::constraints::Edge { src, tgt });
    let mut drawn = sys.clone();
    let gone = if hidden == 0 { n1 } else { n2 };
    drawn.nodes_mut().retain(|(id, _)| id != &gone);
    (sys, drawn)
}

/// [`hidden_endpoint_graph`] rendered: the two-node graph with `hidden`'s
/// endpoint dropped from the drawn system.
fn dot_of_hidden(src_conc: LNFact, tgt_prem: LNFact, hidden: usize) -> String {
    let (orig, drawn) = hidden_endpoint_graph(src_conc, tgt_prem, hidden);
    dot_of(&orig, drawn)
}

/// Render `drawn`'s repr while resolving edge facts as HS does.
fn dot_of(orig: &System, drawn: System) -> String {
    use crate::constraint::system::graph::render_system::RenderSystem;
    use crate::constraint::system::graph::repr::compute_basic_graph_repr;
    let simplified = RenderSystem::from_prover(drawn);
    let repr = compute_basic_graph_repr(&simplified);
    let graph = Graph {
        system: orig,
        repr,
        abbreviations: Abbreviations::new(),
    };
    let color_map = build_node_color_map(&orig.nodes);
    let mut g = tamarin_utils::dot::DotGraph::new();
    showdot::dot_graph_compact(&mut g, &GraphOptions::default(), &color_map, &graph);
    tamarin_utils::dot::show_dot("G", &g)
}

fn edge_line(dot: &str) -> String {
    dot.lines()
        .find(|l| l.contains("->"))
        .unwrap_or_else(|| panic!("no edge in\n{dot}"))
        .to_string()
}

/// The attribute list of the graph's single edge — `edge_line` without the
/// endpoint ids, which `Text.Dot`'s graph-global counter assigns and which
/// therefore say nothing about the styling under test.
fn edge_attrs(dot: &str) -> String {
    let line = edge_line(dot);
    let open = line
        .find('[')
        .unwrap_or_else(|| panic!("edge carries no attribute list: {line}"));
    line[open..].to_string()
}

/// [`classify_edge`]'s persistence test is HS `isPersistentFact`
/// (Theory/Model/Fact.hs), i.e. HS `factTagMultiplicity`
/// (Theory/Model/Fact.hs),
/// which maps `KUFact` and `KDFact` to `Persistent` alongside `ProtoFact
/// Persistent _ _`.  An edge with a LINEAR proto fact at one end and a
/// KU/KD fact at the other therefore takes the bold proto branch
/// (System/Dot.hs) AND its `gray50` colour, because `check` tests BOTH
/// endpoints for each predicate independently (System/Dot.hs).
///
/// The mixed endpoint pair is not reachable from a solver-built system:
/// HS `insertEdges` (Reduction.hs) unifies an edge's two facts with
/// `solveFactEqs`, which is `contradictoryIf` their tags differ
/// (Reduction.hs), and the two raw `sEdges` writers pair an `In`/`Fr`
/// premise with the matching conclusion of the `ISend`/`Fresh` rule they mint
/// (HS `exploitPrem`, Reduction.hs).  So this
/// pins the predicate on a hand-built system rather than on oracle bytes,
/// using a persistent-proto edge as the reference attribute string.
#[test]
fn classify_edge_treats_k_facts_as_persistent() {
    use crate::fact::{kd_fact, ku_fact, proto_fact, Multiplicity};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let a = Term::Lit(Lit::Var(LVar::new("A", LSort::Pub, 0)));
    let m = Term::Lit(Lit::Var(LVar::new("m", LSort::Msg, 0)));
    // The endpoint facts are resolved through the ORIGINAL system, so which
    // node `hidden_endpoint_graph` drops from the drawn copy cannot move these
    // attributes; every variant below hides the same one.
    let style_of =
        |conc: LNFact, prem: LNFact| -> String { edge_attrs(&dot_of_hidden(conc, prem, 1)) };
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

#[test]
fn dot_abbreviations_and_legend_appear_only_when_abbreviate_is_set() {
    // Build a System whose nodes carry a long, frequently-repeated
    // compound term -- the abbreviation algorithm should emit a legend.
    use crate::fact::{Fact, FactTag};
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo};
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_no_eq, Term};
    use tamarin_term::vterm::Lit;
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
    let s = system_to_dot_with(&sys, &GraphOptions::default());
    // With `goAbbreviate` set, `renderLNFact` (System/Dot.hs) substitutes the
    // generated name into the fact rows themselves, not just into the legend.
    assert!(s.contains("Out( SE1 )"), "facts not abbreviated: {}", s);

    // The whole legend, byte for byte from the `rank="sink"` scope on.  Three
    // things live here and nowhere else in the suite:
    //
    //  * the `D.scope` wrapper carrying `rank="sink"` around a single
    //    `shape=plain` HTML-label node (System/Dot.hs);
    //  * graphviz's HTML printer `align`ing the rows under the opening
    //    `<TABLE …>` tag, so every row after the first is preceded by a
    //    newline and a run of spaces as wide as that tag (65);
    //  * the invisible edge from every graph sink to the legend node
    //    (System/Dot.hs over `getGraphSinks`, Graph.hs) — resolved
    //    through `dsNodes`, i.e. each record's rule-label PORT, not its bare
    //    id.
    //
    // The rows are `topoSortAbbrevs` order (System/Dot.hs): the inner
    // `senc(argument, payload)` and `session_key` before the `senc(SE2, SE3)`
    // whose expansion mentions them.
    let pad = " ".repeat(65);
    let row = |name: &str, exp: &str| {
        format!(
            "<TR><TD ALIGN=\"LEFT\" VALIGN=\"TOP\"><FONT COLOR=\"#000000\">{name}</FONT></TD> \
             <TD ALIGN=\"LEFT\" VALIGN=\"TOP\">=</TD> \
             <TD ALIGN=\"LEFT\" VALIGN=\"TOP\">{exp}</TD></TR>"
        )
    };
    let expected_legend = format!(
        "{{\nrank=\"sink\";\n\
         n9[shape=\"plain\",label=<<TABLE BORDER=\"1\" CELLBORDER=\"0\" \
         CELLSPACING=\"3\" CELLPADDING=\"1\">{r2}\n{pad}{r3}\n{pad}{r1}</TABLE>>];\n\
         \n}}\n\
         n2:n0 -> n9[style=\"invis\"];\n\
         n5:n3 -> n9[style=\"invis\"];\n\
         n8:n6 -> n9[style=\"invis\"];\n\
         \n}}\n",
        r2 = row("SE2", "senc(argument, payload)"),
        r3 = row("SE3", "session_key"),
        r1 = row("SE1", "senc(SE2, SE3)"),
    );
    let tail = s
        .find("{\nrank=\"sink\";")
        .map(|i| &s[i..])
        .unwrap_or_else(|| panic!("no rank=sink legend scope in:\n{s}"));
    assert_eq!(tail, expected_legend, "legend block:\n{s}");

    // `goAbbreviate` gates only the APPLICATION of the abbreviations
    // (`renderLNFact`, System/Dot.hs, and `when abbreviate
    // generateLegend`, System/Dot.hs) — `systemToGraph` computes them either
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
    assert!(
        !plain.contains("shape=\"plain\""),
        "unexpected legend: {}",
        plain
    );
    assert!(!plain.contains("<TABLE"), "unexpected table: {}", plain);
    assert!(
        !plain.contains("SE1"),
        "abbreviation name leaked: {}",
        plain
    );
}

// Build a simple proto rule node with the given premises/actions/concs.
// `pub(super)` so `dot_showdot_tests.rs` shares it.
pub(super) fn proto_node(
    name: &str,
    prems: Vec<LNFact>,
    acts: Vec<LNFact>,
    concs: Vec<LNFact>,
) -> RuleACInst {
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};
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
fn dot_compact_intruder_node_is_plain_ellipse() {
    // HS `mkNode` CompactBoringNodes (System/Dot.hs): an intruder rule
    // collapses to a plain `mkSimpleNode` ellipse with NO fill/role attrs.
    // With an outgoing edge the label is `#id : name` (actions dropped);
    // without one it is the full `#id : name[acts]` (System/Dot.hs).  Compact
    // endpoints also carry no record ports: every prem/act/conc key maps to
    // the one bare id (System/Dot.hs).
    use crate::constraint::constraints::Edge;
    use crate::fact::{in_fact, out_fact, proto_fact, Multiplicity};
    use crate::rule::{ConcIdx, IntrRuleACInfo, PremIdx, Rule};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
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
        out.contains("label=\"#j : coerce\",shape=\"ellipse\""),
        "outgoing intruder node must be a plain ellipse `#j : coerce`: {out}"
    );
    assert!(
        !out.contains("coerce[Act"),
        "outgoing compact label must drop the action row: {out}"
    );
    // Compact nodes are `mkSimpleNode` ellipses: no record fields, so no
    // `Text.Dot` ports, and no fill/role attrs.
    assert!(
        !out.contains('<'),
        "compact intruder nodes must not emit record ports: {out}"
    );
    assert!(
        !out.contains("fillcolor"),
        "compact intruder nodes carry no fill: {out}"
    );
    // The compact->compact edge is emitted portless (bare ids, no `:port`).
    assert!(
        out.contains("n0 -> n1["),
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
fn dot_cluster_preamble_uses_cluster_attributes() {
    // When clusters exist HS switches to setDefaultAttributesIfCluster
    // (System/Dot.hs), and `dotCluster` (System/Dot.hs) opens each subgraph
    // with nine attributes of its own (System/Dot.hs).  Both blocks are
    // pinned byte-for-byte: a check on one or two attributes is blind to a
    // dropped `label`, a flipped `pack`, or a `roleColor` whose alpha or
    // channel scale moved.
    //
    // Oracle bytes: `--prove --output-dot` of the pinned v1.13.0 binary on
    // `examples/sapic/fast/basic/channels1.spthy`, whose roles are `P`,
    // `Process` and `Q`.  The preamble carries no theory-specific text, and
    // the two hexes below are that capture's own `cluster_P_Session_1` and
    // `cluster_Q_Session_1` colours — `roleColor` keys on the base name
    // alone (System/Dot.hs), so the session index does not move them.
    use crate::fact::out_fact;
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
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
    sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", "P"));
    sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", "Q"));
    let s = system_to_dot_with(&sys, &GraphOptions::default());
    const PREAMBLE: &str = concat!(
        "digraph \"G\" {\n",
        "nodesep=\"0.8\";\n",
        "ranksep=\"0.8\";\n",
        "sep=\"4\";\n",
        "splines=\"true\";\n",
        "overlap=\"false\";\n",
        "pack=\"true\";\n",
        "packmode=\"cluster\";\n",
        "concentrate=\"true\";\n",
        "compound=\"true\";\n",
        "remincross=\"true\";\n",
        "mclimit=\"10\";\n",
        "nslimit=\"20\";\n",
        "nslimit1=\"20\";\n",
        "ordering=\"out\";\n",
        "rankdir=\"TB\";\n",
        "showboxes=\"false\";\n",
        "clusterrank=\"local\";\n",
        "node[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\",\
         margin=\"0.05,0.05\",shape=\"ellipse\"];\n",
        "edge[fontsize=\"8\",fontname=\"Helvetica\",penwidth=\"1.5\",arrowsize=\"0.5\",\
         color=\"black\",style=\"solid\",weight=\"8\"];\n",
    );
    assert!(
        s.starts_with(PREAMBLE),
        "cluster preamble must be the oracle's, byte for byte:\n{s}"
    );
    // `dotCluster`'s own nine attributes, in HS's order, with `roleColor`
    // (System/Dot.hs) resolved from the base name.
    let cluster_block = |name: &str, hex: &str| {
        format!(
            "subgraph \"cluster_{name}\" {{\n\
             nodesep=\"0.6\";\n\
             ranksep=\"0.6\";\n\
             label=\"{name}\";\n\
             style=\"filled\";\n\
             color=\"{hex}\";\n\
             penwidth=\"2\";\n\
             fillcolor=\"{hex}\";\n\
             overlap=\"false\";\n\
             sep=\"4\";\n"
        )
    };
    assert!(
        s.contains(&cluster_block("P_Session_1", "#D8364B4C")),
        "P cluster block:\n{s}"
    );
    assert!(
        s.contains(&cluster_block("Q_Session_1", "#3649D84C")),
        "Q cluster block:\n{s}"
    );
}

// ---- palette-driven node attributes (HS `dotNodeCompact`, System/Dot.hs) --
// The `nodeColorMap` palette itself is exercised in `graph::color`.

use crate::constraint::constraints::NodeId;
use crate::rule::{
    ProtoRuleACInstInfo, ProtoRuleName as PRN, Rule as TRule, RuleAttributes, RuleInfo as TRuleInfo,
};
use tamarin_term::lterm::{LSort, LVar};

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
fn color_uses_white_font_matches_hs_luminance() {
    use tamarin_utils::color::Rgb;
    // HS colorUsesWhiteFont: 0.2126r + 0.7152g + 0.0722b < 0.5 (and Just).
    // Absent -> black; a white background -> black; a black one -> white.
    assert!(!color_uses_white_font(None));
    assert!(!color_uses_white_font(Some(Rgb::new(1.0, 1.0, 1.0))));
    assert!(color_uses_white_font(Some(Rgb::new(0.0, 0.0, 0.0))));
    // A dark blue (low luminance) uses a white font: 0.0722 < 0.5.
    assert!(color_uses_white_font(Some(Rgb::new(0.0, 0.0, 1.0))));
    // A pure green is bright enough for a black font (0.7152 >= 0.5).
    assert!(!color_uses_white_font(Some(Rgb::new(0.0, 1.0, 0.0))));
}
