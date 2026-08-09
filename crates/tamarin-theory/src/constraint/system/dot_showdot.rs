// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The batch `--output-dot` serializer: HS
//! `D.showDot label $ dotSystemCompact graphOptions dotOptions system`
//! (Batch.hs:256).
//!
//! Same graph CONTENT as the interactive renderer in [`super`] — whose label,
//! colour, filtering and ordering helpers this module reuses wholesale — but
//! built as a `Text.Dot` element tree ([`tamarin_utils::dot`]) and rendered by
//! `showDot`, which is what makes the bytes HS's:
//!
//!   * NODE IDS come from `Text.Dot`'s single monotonic counter
//!     (`rawNode`, Text/Dot.hs:156-162): `n0`, `n1`, … in ALLOCATION order,
//!     which for a record is every field's PORT first (left-to-right) and the
//!     node itself last (`genRecord`, Text/Dot.hs:284-288).
//!   * EVERY record field carries a port `<n<k>>` (Text/Dot.hs:258-262),
//!     including the middle rule-label row — HS's port type is
//!     `Maybe (Either PremIdx ConcIdx)` and the rule label is the `Nothing`
//!     port (Dot.hs:309-315).  The node's own dot id, as recorded in
//!     `dsNodes`, is therefore the PORTED `n<node>:n<label-port>`, which is
//!     what less-edges attach to.
//!   * ATTRIBUTE VALUES are always quoted, including numbers
//!     (`showAttr`, Text/Dot.hs:346-353) — `nodesep="0.3"`, `weight="10.0"`.
//!   * STATEMENTS are unindented, one per line, and a node's attribute list
//!     abuts its id (`n3[…];`, `node[…];`).
//!
//! Reference: `lib/utils/src/Text/Dot.hs`,
//! `lib/theory/src/Theory/Constraint/System/Dot.hs`.

use std::collections::BTreeMap;

use tamarin_utils::dot::{
    hcat_records, port_field, record, show_dot, vcat_records, DotGraph, NodeId as DotNodeId, Record,
};

use super::*;
use crate::constraint::constraints::{NodeConc, NodeId, NodePrem, Reason};
use crate::constraint::system::graph::repr::{Cluster, GraphRepr};
use crate::rule::{ConcIdx, PremIdx};

/// HS's record port type `Maybe (Either PremIdx ConcIdx)` (Dot.hs:295-296):
/// the key each record field is tagged with, and thus the key `dotNodeCompact`
/// sorts the returned association list by (Dot.hs:264-269).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RowKey {
    /// `Just (Left i)` — a premise field, cached into `dsPrems`.
    Prem(usize),
    /// `Nothing` — the rule-label row, whose node id becomes `dsNodes[v]`.
    Act,
    /// `Just (Right i)` — a conclusion field, cached into `dsConcs`.
    Conc(usize),
}

/// HS `DotState` (Dot.hs:94-101): the dot id of every emitted component,
/// keyed the way the edge writers look them up.
#[derive(Default)]
struct DotState {
    /// `_dsNodes`: the LAST node emitted at a system node id — `dotLessEdge`'s
    /// (Dot.hs:409-413) and `generateLegend`'s (Dot.hs:455-458) lookup.
    ds_nodes: BTreeMap<NodeId, DotNodeId>,
    /// `_dsPrems`: `dotGenEdge`'s target endpoint (Dot.hs:405).
    ds_prems: BTreeMap<NodePrem, DotNodeId>,
    /// `_dsConcs`: `dotGenEdge`'s source endpoint (Dot.hs:404).
    ds_concs: BTreeMap<NodeConc, DotNodeId>,
}

/// The `ReaderT (Graph, NodeColorMap, DotOptions)` environment (Dot.hs:92)
/// plus the two derived lookups `dotGraphCompact` computes once.
struct Env<'a> {
    opts: &'a GraphOptions,
    color_map: &'a NodeColorMap,
    graph: &'a Graph<'a>,
    /// `resolveNodePremFact`/`resolveNodeConcFact`'s system (Graph.hs:87-96) —
    /// the ORIGINAL one, not the simplified copy the repr was built from.
    orig_node_map: OrigNodeRules<'a>,
    /// `hasOutgoingEdge graph v` (Dot.hs:280-283), over the TOP-LEVEL edges.
    has_outgoing: tamarin_utils::FastSet<NodeId>,
}

impl Env<'_> {
    /// HS `renderLNFact`'s abbreviation step (Dot.hs:228-236): `goAbbreviate`
    /// gates the substitution, so an always-`None` lookup is the `else` arm.
    fn abbrev(&self, t: &LNTerm) -> Option<LNTerm> {
        if !self.opts.abbreviate {
            return None;
        }
        self.graph.abbreviations.get(t).map(|(a, _)| a.clone())
    }
}

/// HS `D.showDot label $ dotSystemCompact graphOptions dotOptions system`
/// (Batch.hs:256) — the batch `--output-dot` entry point.
pub fn system_to_dot_labeled(sys: &System, opts: &GraphOptions, label: &str) -> String {
    let graph = system_to_graph(sys, opts);
    // `dotSystemCompact` (Dot.hs:506-512) keys the palette off the RAW
    // system's nodes, not the compressed/simplified copy.
    let color_map = build_node_color_map(&sys.nodes);
    let mut g = DotGraph::new();
    dot_graph_compact(&mut g, opts, &color_map, &graph);
    show_dot(label, &g)
}

/// Port of `dotGraphCompact` (Dot.hs:514-538).
fn dot_graph_compact(
    g: &mut DotGraph,
    opts: &GraphOptions,
    color_map: &NodeColorMap,
    graph: &Graph<'_>,
) {
    let repr = &graph.repr;
    let env = Env {
        opts,
        color_map,
        graph,
        orig_node_map: graph.system.node_rule_map(),
        has_outgoing: repr
            .edges
            .iter()
            .filter_map(|e| match e {
                GEdge::System(src, _) => Some(src.0),
                _ => None,
            })
            .collect(),
    };
    let mut st = DotState::default();

    if repr.clusters.is_empty() {
        set_default_attributes(g);
    } else {
        set_default_attributes_if_cluster(g);
    }

    for node in &repr.nodes {
        dot_node_compact(g, &mut st, &env, node, None);
    }
    for cluster in &repr.clusters {
        dot_cluster(g, &mut st, &env, cluster);
    }
    let (less_edges, rest_edges) = merge_less_edges(repr.edges.iter());
    for e in rest_edges {
        dot_edge(g, &st, &env, e);
    }
    for l in &less_edges {
        dot_less_edge(g, &st, l);
    }
    // `dotClustersEdges` (Dot.hs:542-547) re-runs `mergeLessEdges` over the
    // CONCATENATION of every cluster's edges, after all nodes and clusters.
    let (cl_less, cl_rest) = merge_less_edges(repr.clusters.iter().flat_map(|c| c.edges.iter()));
    for e in cl_rest {
        dot_edge(g, &st, &env, e);
    }
    for l in &cl_less {
        dot_less_edge(g, &st, l);
    }

    if opts.abbreviate {
        generate_legend(g, &st, &env);
    }
}

/// HS `setDefaultAttributes` (Dot.hs:132-138).
fn set_default_attributes(g: &mut DotGraph) {
    g.attribute("nodesep", "0.3");
    g.attribute("ranksep", "0.3");
    g.node_attributes(attrs(&[
        ("fontsize", "8"),
        ("fontname", "Helvetica"),
        ("width", "0.3"),
        ("height", "0.2"),
    ]));
    g.edge_attributes(attrs(&[("fontsize", "8"), ("fontname", "Helvetica")]));
}

/// HS `setDefaultAttributesIfCluster` (Dot.hs:142-164).
fn set_default_attributes_if_cluster(g: &mut DotGraph) {
    for (k, v) in [
        ("nodesep", "0.8"),
        ("ranksep", "0.8"),
        ("sep", "4"),
        ("splines", "true"),
        ("overlap", "false"),
        ("pack", "true"),
        ("packmode", "cluster"),
        ("concentrate", "true"),
        ("compound", "true"),
        ("remincross", "true"),
        ("mclimit", "10"),
        ("nslimit", "20"),
        ("nslimit1", "20"),
        ("ordering", "out"),
        ("rankdir", "TB"),
        ("showboxes", "false"),
        ("clusterrank", "local"),
    ] {
        g.attribute(k, v);
    }
    g.node_attributes(attrs(&[
        ("fontsize", "8"),
        ("fontname", "Helvetica"),
        ("width", "0.3"),
        ("height", "0.2"),
        ("margin", "0.05,0.05"),
        ("shape", "ellipse"),
    ]));
    g.edge_attributes(attrs(&[
        ("fontsize", "8"),
        ("fontname", "Helvetica"),
        ("penwidth", "1.5"),
        ("arrowsize", "0.5"),
        ("color", "black"),
        ("style", "solid"),
        ("weight", "8"),
    ]));
}

fn attrs(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
        .collect()
}

/// Port of `dotCluster` (Dot.hs:572-587) and the dot half of `roleCluster`
/// (Dot.hs:178-188): the subgraph id is `createClusterNodeId name`, i.e. the
/// QUOTED `"cluster_<name>"`, and the cluster's `roleColor` is threaded to its
/// child nodes as `manualNodeColor`.
fn dot_cluster(g: &mut DotGraph, st: &mut DotState, env: &Env<'_>, cluster: &Cluster) {
    let base = extract_base_name(&cluster.name).unwrap_or_else(|| "Undefined".to_string());
    let color = role_color(&base);
    g.scope_named(DotNodeId::cluster(&cluster.name), |sub| {
        for (k, v) in [
            ("nodesep", "0.6"),
            ("ranksep", "0.6"),
            ("label", cluster.name.as_str()),
            ("style", "filled"),
            ("color", color.as_str()),
            ("penwidth", "2"),
            ("fillcolor", color.as_str()),
            ("overlap", "false"),
            ("sep", "4"),
        ] {
            sub.attribute(k, v);
        }
        for node in &cluster.nodes {
            dot_node_compact(sub, st, env, node, Some(&color));
        }
    });
}

/// HS `mkSimpleNode` (Dot.hs:292-293): a plain ellipse whose attribute list
/// starts with the label.
fn mk_simple_node(g: &mut DotGraph, lbl: &str, extra: Vec<(String, String)>) -> DotNodeId {
    let mut a = attrs(&[("label", lbl), ("shape", "ellipse")]);
    a.extend(extra);
    g.node(a)
}

/// Port of `dotNodeCompact` (Dot.hs:238-293).
fn dot_node_compact(
    g: &mut DotGraph,
    st: &mut DotState,
    env: &Env<'_>,
    node: &GNode,
    manual_color: Option<&str>,
) {
    let v = node.id;
    match &node.ty {
        NodeType::System(ru) => {
            let ru_ab = abbreviate_rule(ru, &|t: &LNTerm| env.abbrev(t));
            // `attrs` (Dot.hs:260-262): fill, style, fontcolor, role — in that
            // order, appended AFTER `genRecord`'s shape/label.
            let node_attrs = vec![
                (
                    "fillcolor".to_string(),
                    rule_fillcolor(ru, &v, manual_color, env.color_map),
                ),
                ("style".to_string(), "filled".to_string()),
                (
                    "fontcolor".to_string(),
                    if color_uses_white_font(env.color_map.lookup_node(&v)) {
                        "white"
                    } else {
                        "black"
                    }
                    .to_string(),
                ),
                (
                    "role".to_string(),
                    extract_role(ru).unwrap_or("Undefined").to_string(),
                ),
            ];
            let ids = mk_node(g, env, &v, &ru_ab, node_attrs);
            // `modM dsPrems $ M.union $ M.fromList prems` — `M.union` is
            // left-biased, so the NEW entries win.
            for (key, nid) in &ids {
                match key {
                    RowKey::Prem(i) => st.ds_prems.insert((v, PremIdx(*i)), nid.clone()),
                    RowKey::Conc(i) => st.ds_concs.insert((v, ConcIdx(*i)), nid.clone()),
                    RowKey::Act => None,
                };
            }
            // `fromJust $ lookup Nothing ids` — for a record that is the
            // rule-label field's PORTED id, for a compact node the bare id.
            if let Some((_, nid)) = ids.iter().find(|(k, _)| *k == RowKey::Act) {
                st.ds_nodes.insert(v, nid.clone());
            }
        }
        NodeType::UnsolvedAction(facts) => {
            // `fsep (punctuate comma facts) <-> opAction <-> text (show v)`,
            // rendered as ONE doc by the default HughesPJ style.
            let docs: Vec<Doc> = facts
                .iter()
                .map(|fa| fact_doc_of(&apply_abbreviations_fact(&|t| env.abbrev(t), fa)))
                .collect();
            let lbl = pretty_hpj::fsep(pretty_hpj::punctuate(Doc::text(","), docs))
                .beside_sp(Doc::text("@"))
                .beside_sp(Doc::text(v.to_string()))
                .render_with(WEB_LINE_LENGTH, WEB_RIBBON);
            let color = if facts.iter().any(|f| matches!(f.tag, FactTag::Ku)) {
                "gray"
            } else {
                "darkblue"
            };
            let nid = mk_simple_node(g, &lbl, attrs(&[("color", color)]));
            st.ds_nodes.insert(v, nid);
        }
        NodeType::LastAction => {
            let nid = mk_simple_node(g, &v.to_string(), Vec::new());
            st.ds_nodes.insert(v, nid);
        }
        // `missingNode shape label = D.node [("label", render label),("shape",shape)]`
        // (Dot.hs:283-285); both labels are `(<show v>, <i>)`
        // (`prettyNodeConc`/`prettyNodePrem`, Constraints.hs:248-255).  Note
        // the caches: a missing node lands in `dsConcs`/`dsPrems`, NOT in
        // `dsNodes`.
        NodeType::Missing(MissingHint::Conc(ci)) => {
            let nid = g.node(attrs(&[
                ("label", &format!("({}, {})", v, ci.0)),
                ("shape", "trapezium"),
            ]));
            st.ds_concs.insert((v, *ci), nid);
        }
        NodeType::Missing(MissingHint::Prem(pi)) => {
            let nid = g.node(attrs(&[
                ("label", &format!("({}, {})", v, pi.0)),
                ("shape", "invtrapezium"),
            ]));
            st.ds_prems.insert((v, *pi), nid);
        }
    }
}

/// Port of `mkNode` (Dot.hs:295-314) — the compact-ellipse / full-record
/// split, returning HS's `[(Maybe (Either PremIdx ConcIdx), D.NodeId)]`.
fn mk_node(
    g: &mut DotGraph,
    env: &Env<'_>,
    v: &NodeId,
    ru: &RuleACInst,
    node_attrs: Vec<(String, String)>,
) -> Vec<(RowKey, DotNodeId)> {
    let ps = render_row(
        ru.premises
            .iter()
            .enumerate()
            .map(|(i, fa)| (RowKey::Prem(i), fact_doc_of(fa)))
            .collect(),
    );
    let as_ = render_row(vec![(RowKey::Act, rule_label_doc(v, ru, env.opts))]);
    let cs = render_row(
        ru.conclusions
            .iter()
            .enumerate()
            .map(|(i, fa)| (RowKey::Conc(i), fact_doc_of(fa)))
            .collect(),
    );
    if is_intruder_or_fresh(ru) {
        // `CompactBoringNodes`: one ellipse, and EVERY prem/act/conc key maps
        // to its bare id (no ports).
        let lbl = if env.has_outgoing.contains(v) {
            format!("{} : {}", v, rule_case_name(ru))
        } else {
            as_.iter().map(|(_, s)| s.as_str()).collect::<String>()
        };
        let nid = mk_simple_node(g, &lbl, Vec::new());
        ps.iter()
            .chain(as_.iter())
            .chain(cs.iter())
            .map(|(k, _)| (*k, nid.clone()))
            .collect()
    } else {
        // `D.vcat $ map D.hcat $ map (map (uncurry D.portField)) $
        //  filter (not . null) [ps, as, cs]`.
        let rows: Vec<Record<RowKey>> = [ps, as_, cs]
            .into_iter()
            .filter(|r| !r.is_empty())
            .map(|row| {
                hcat_records(
                    row.into_iter()
                        .map(|(k, lbl)| port_field(k, &lbl))
                        .collect(),
                )
            })
            .collect();
        record(g, &vcat_records(rows), node_attrs).1
    }
}

/// HS `renderRow` (Dot.hs:360-364): lay a row's docs out with `renderBalanced`
/// while keeping each field's port key.
fn render_row(row: Vec<(RowKey, Doc)>) -> Vec<(RowKey, String)> {
    let (keys, docs): (Vec<RowKey>, Vec<Doc>) = row.into_iter().unzip();
    keys.into_iter().zip(render_balanced(docs)).collect()
}

/// Port of `mergeLessEdges` (Dot.hs:592-622): split a scope's edges into the
/// per-`(smaller, larger)` merged less-edges and everything else.
///
/// `eqClasses` (Extension/Prelude.hs:124-131) is a STABLE sort by the key
/// followed by `groupBy`, so the merged list is ordered by `(smaller, larger)`
/// and each class keeps its edges in encounter order.
fn merge_less_edges<'a, I: Iterator<Item = &'a GEdge>>(
    edges: I,
) -> (Vec<(NodeId, NodeId, String)>, Vec<&'a GEdge>) {
    let mut rest: Vec<&GEdge> = Vec::new();
    let mut lesses: Vec<&LessAtom> = Vec::new();
    for e in edges {
        match e {
            GEdge::Less(la) => lesses.push(la),
            _ => rest.push(e),
        }
    }
    lesses.sort_by(|a, b| (&a.smaller, &a.larger).cmp(&(&b.smaller, &b.larger)));
    let mut classes: Vec<(NodeId, NodeId, Vec<Reason>)> = Vec::new();
    for la in lesses {
        match classes.last_mut() {
            // `getAllRToC` keys the class on the FIRST member's endpoints.
            Some((s, l, reasons)) if *s == la.smaller && *l == la.larger => reasons.push(la.reason),
            _ => classes.push((la.smaller, la.larger, vec![la.reason])),
        }
    }
    let merged = classes
        .into_iter()
        .map(|(s, l, reasons)| (s, l, all_rto_colors(reasons)))
        .collect();
    (merged, rest)
}

/// HS `allRtoColors` (Dot.hs:616-622): a class's reasons, most important
/// first, as one graphviz weighted colour list.  A class of several reasons
/// splits the edge into equal-width bands (`":c;1/n"` per colour); the
/// singleton case — the only one a `System` can produce, since `LessAtom`
/// equality ignores the reason — is just the colour.
fn all_rto_colors(mut reasons: Vec<Reason>) -> String {
    // `sortBy (comparing Data.Ord.Down)` — descending, so the "most important
    // reason" (the largest `Reason`) comes first.
    reasons.sort_by(|a, b| b.cmp(a));
    let per = if reasons.len() > 1 {
        format!(";{}", 1.0 / reasons.len() as f64)
    } else {
        String::new()
    };
    reasons
        .iter()
        .map(|r| format!("{}{}", reason_color(*r), per))
        .collect::<Vec<_>>()
        .join(":")
}

/// Port of `dotEdge`'s non-less arms (Dot.hs:386-406).
fn dot_edge(g: &mut DotGraph, st: &DotState, env: &Env<'_>, edge: &GEdge) {
    let (src, tgt, style) = match edge {
        GEdge::System(src, tgt) => {
            // `[("style","bold"),("weight","10.0")]` — HS spells the weight as
            // a Double, so `showAttr` quotes `"10.0"`.
            let style = match classify_edge(&env.orig_node_map, src, tgt) {
                EdgeKind::Proto { persistent: true } => {
                    attrs(&[("style", "bold"), ("weight", "10.0"), ("color", "gray50")])
                }
                EdgeKind::Proto { persistent: false } => {
                    attrs(&[("style", "bold"), ("weight", "10.0")])
                }
                EdgeKind::K => attrs(&[("color", "orangered2")]),
                EdgeKind::Other => attrs(&[("color", "gray30")]),
            };
            (src, tgt, style)
        }
        GEdge::UnsolvedChain(src, tgt) => {
            (src, tgt, attrs(&[("style", "dotted"), ("color", "green")]))
        }
        // `mergeLessEdges` has already peeled these off.
        GEdge::Less(_) => return,
    };
    // HS `getState` `error`s on an endpoint that was never emitted, killing the
    // run; drop the edge instead so a repr divergence shows up as a missing
    // line rather than a crash.
    let (Some(s), Some(t)) = (st.ds_concs.get(src), st.ds_prems.get(tgt)) else {
        return;
    };
    g.edge(s.clone(), t.clone(), style);
}

/// Port of `dotLessEdge` (Dot.hs:409-413): colour FIRST, then style.
fn dot_less_edge(g: &mut DotGraph, st: &DotState, less: &(NodeId, NodeId, String)) {
    let (smaller, larger, color) = less;
    let (Some(s), Some(t)) = (st.ds_nodes.get(smaller), st.ds_nodes.get(larger)) else {
        return;
    };
    g.edge(
        s.clone(),
        t.clone(),
        attrs(&[("color", color), ("style", "dashed")]),
    );
}

/// Port of `generateLegend` (Dot.hs:438-458): a `rank=sink` scope holding one
/// `shape=plain` node with the HTML-table label, plus an invisible edge from
/// every graph sink to it.
fn generate_legend(g: &mut DotGraph, st: &DotState, env: &Env<'_>) {
    let abbrevs = &env.graph.abbreviations;
    if abbrevs.is_empty() {
        return;
    }
    let html = hs_legend_html_label(abbrevs);
    let n_legend = g.scope(|sub| {
        sub.attribute("rank", "sink");
        // `html_label` is `showAttr`'s one unquoted, unescaped attribute
        // (Text/Dot.hs:348).
        sub.node(vec![
            ("shape".to_string(), "plain".to_string()),
            ("html_label".to_string(), html),
        ])
    });
    for sink in graph_sinks(&env.graph.repr) {
        if let Some(nid) = st.ds_nodes.get(&sink) {
            g.edge(nid.clone(), n_legend.clone(), attrs(&[("style", "invis")]));
        }
    }
}

/// The `<TABLE …>` opening tag `abbrevLabel`'s `tableAttributes`
/// (`[Border 1, CellBorder 0, CellSpacing 3, CellPadding 1]`, Dot.hs:462)
/// print as.  Its WIDTH is also the continuation indent of the rows below
/// (see [`hs_legend_html_label`]).
const LEGEND_TABLE_OPEN: &str =
    "<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"3\" CELLPADDING=\"1\">";

/// HS `htmlLabel $ abbrevLabel sortedAbbrevs labelColor` (Dot.hs:437-479) as
/// graphviz's HTML-label printer renders it (`renderDot . unqtDot`,
/// Text/Dot.hs:414-419), wrapped in the `<`…`>` that makes it a `html_label`.
///
/// Three things the printer does that a naive concatenation does not:
///   * the rows are `align`ed under the opening tag, so every row after the
///     first is preceded by a newline and [`LEGEND_TABLE_OPEN`]-wide indent;
///   * an abbreviation's expansion is `render`ed at the default HughesPJ style
///     (100 columns, ribbon 67) and can therefore be MULTI-LINE; HS splits it
///     back into `Str` items separated by `Newline [Align HLeft]`
///     (`joinLinesWith`, Dot.hs:478-479), i.e. `<BR ALIGN="LEFT"/>`;
///   * text is escaped by [`escape_html_text`], which is not plain
///     entity-escaping.
///
/// [`super::legend_html_label`] is the interactive route's counterpart and
/// renders a flatter dialect.
fn hs_legend_html_label(abbrevs: &Abbreviations) -> String {
    let row_sep = format!("\n{}", " ".repeat(LEGEND_TABLE_OPEN.chars().count()));
    let rows: Vec<String> = order_abbreviations_for_json(abbrevs)
        .into_iter()
        .map(|(_term, name, exp)| {
            // `font txt = Text [Font [Color labelColor] txt]` with
            // `labelColor = doAbbrevColor = RGB 0 0 0` (Dot.hs:85-87/469).
            let name_cell = format!(
                "<TD ALIGN=\"LEFT\" VALIGN=\"TOP\"><FONT COLOR=\"#000000\">{}</FONT></TD>",
                escape_html_text(&render_lnterm(name))
            );
            let eq_cell = "<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">=</TD>";
            let expansion = render_lnterm(exp)
                .lines()
                .map(escape_html_text)
                .collect::<Vec<_>>()
                .join("<BR ALIGN=\"LEFT\"/>");
            let exp_cell = format!("<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">{expansion}</TD>");
            format!("<TR>{name_cell} {eq_cell} {exp_cell}</TR>")
        })
        .collect();
    format!("<{}{}</TABLE>>", LEGEND_TABLE_OPEN, rows.join(&row_sep))
}

/// HS `render $ Sys.prettyLNTerm t` (Dot.hs:470-472) — the Doc-based term
/// printer at the default style, so a wide term WRAPS.
fn render_lnterm(t: &LNTerm) -> String {
    crate::pretty_formula::term_doc(&crate::pretty_theory::lnterm_to_parser(t))
        .render_with(WEB_LINE_LENGTH, WEB_RIBBON)
}

/// graphviz's HTML-text escape (`escapeValue`, Data.GraphViz.Attributes.HTML).
///
/// Beyond the four entity substitutions, a RUN of spaces keeps its first space
/// literal and encodes the rest as `&#32;` — the numeric entity, because a
/// plain space run would be collapsed by the HTML-like label parser.  Every
/// single space (the common case) is therefore untouched.
fn escape_html_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut run = 0usize;
    for c in s.chars() {
        if c == ' ' {
            run += 1;
            if run == 1 {
                out.push(' ');
            } else {
                out.push_str("&#32;");
            }
            continue;
        }
        run = 0;
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

/// Port of `getGraphSinks` (Graph.hs:168-172) over `toEdgeList`
/// (GraphRepr.hs:92-109): the ids of the nodes — free ones then each cluster's,
/// duplicates included — that source no edge of ANY kind.
fn graph_sinks(repr: &GraphRepr) -> Vec<NodeId> {
    let sources: tamarin_utils::FastSet<NodeId> = repr
        .edges
        .iter()
        .chain(repr.clusters.iter().flat_map(|c| c.edges.iter()))
        .map(|e| match e {
            GEdge::System(src, _) | GEdge::UnsolvedChain(src, _) => src.0,
            GEdge::Less(la) => la.smaller,
        })
        .collect();
    repr.nodes
        .iter()
        .chain(repr.clusters.iter().flat_map(|c| c.nodes.iter()))
        .map(|n| n.id)
        .filter(|id| !sources.contains(id))
        .collect()
}

#[cfg(test)]
#[path = "dot_showdot_tests.rs"]
mod tests;
