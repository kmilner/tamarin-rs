// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, arcz, addap, Mathias-AURAND, racoucho1u,
//   felixlinker, cascremers, rkunnema, rsasse, Kanakanajm, beschmi,
//   Divya19gupta, PhilipLukertWork, yavivanov, BTom-GH, kevinmorio,
//   YannColomb, Nick Moore, sans-sucre, symphorien, katrielalex,
//   xaDxelA, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Constraints.hs,
//   lib/theory/src/Theory/Constraint/System/Dot.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Graph.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Simplification.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Fact.hs,
//   lib/utils/src/Control/Monad/Disj/Class.hs,
//   lib/utils/src/Text/Dot.hs, lib/utils/src/Text/PrettyPrint/Class.hs,
//   src/Web/Handler.hs

//! Port of Haskell's `Theory.Constraint.System.Dot` +
//! `Theory.Constraint.System.Graph.*` — convert a `System` into a
//! Graphviz DOT representation suitable for `dot -Tsvg`.
//!
//! We render the same kinds of nodes / edges / clusters as a single
//! self-contained DOT document, including an HTML-table legend for the
//! chosen abbreviations and similar-name / role clustering. Node ids,
//! fact rendering (`prettyLNFact`), action-row filtering (Diff /
//! auto-source), the cluster/preamble attribute blocks, the `roleColor`
//! cluster styling and the less-edge rendering all match HS byte-for-
//! byte.
//!
//! Per-rule node FILL colours are a faithful port of HS `nodeColorMap`
//! (Dot.hs:190-218): the size-dependent light-HSV palette keyed by
//! `(groupIdx, memberIdx)` — see `build_node_color_map` / `NodeColorMap` in
//! `crate::graph::color`. An explicit per-rule `color:` attribute and a
//! cluster's `manualNodeColor` still take priority (HS `dotNodeCompact`,
//! Dot.hs:248-256).
//! Each rule record also carries HS's `fontcolor` (`colorUsesWhiteFont` of the
//! palette colour, Dot.hs:236-379, see line 258/284-287) and `role` (Dot.hs:236-379, see line 259) attributes.
//!
//! KNOWN DIVERGENCES:
//!   * (serialization form only — normalised away by the parse-and-compare
//!     gate) the cluster subgraph identifier uses the Rust `cluster_<n>` form
//!     rather than HS `createClusterNodeId roleName`. The cluster's label /
//!     colour / membership are all faithful.
//!   * HS `mkNode`'s `CompactBoringNodes` branch (Dot.hs:294-304) — PORTED
//!     (see `rule_node`): under the default node style, intruder rules and the
//!     `Fresh` rule collapse to a PLAIN `mkSimpleNode` ellipse (Dot.hs:289-290)
//!     with no fill/font/role attrs. The label is `show v : showDotRuleCaseName
//!     ru` when the node has an outgoing edge (`hasOutgoingEdge`, Dot.hs:280-283,
//!     over the TOP-LEVEL `grEdges` only), else the full rule label incl. the
//!     bracketed action row. The `uncompact`/`FullBoringNodes` toggle is not
//!     plumbed through the RS handler (see `graph/options.rs`), so this route is
//!     always compact — matching the HS default (`defaultDotOptions`, Dot.hs:81-84, see line 82).
//!   * SERIALIZATION form only (normalised away by the parse-and-compare gate):
//!     protocol-rule RECORD labels use RS port ids `<p0>`/`<c0>` and spaced
//!     `{ .. } | .. | { .. }` bracketing, where HS's `Text.Dot.renderRecord`
//!     (Dot.hs:254-280) uses a graph-global port counter `<n0>`, `<n1>`, … and
//!     `{{..|..}|{..}|{..|..}}` bracketing. The gate ignores the node-id scheme
//!     and record bracketing; the field CONTENT (facts, `id : name[acts]`) is
//!     rendered identically.
//!
//! Reference:
//!   - `lib/theory/src/Theory/Constraint/System/Dot.hs`
//!   - `lib/theory/src/Theory/Constraint/System/Graph/Graph.hs`
//!   - `lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs`
//!
//! The shape mirrors `systemToGraph` + `dotSystemCompact`:
//!   1. Collect nodes from `sNodes`, plus "missing" nodes referenced
//!      by edges but absent from `sNodes`.
//!   2. Add unsolved-action-atom nodes (KU goals at fresh ids).
//!   3. Add the `LastAtom` node, if any.
//!   4. Emit edges from `sEdges` (conclusion → premise) styled by
//!      fact tag.
//!   5. Emit less-edges from `sLessAtoms` (dashed, coloured by
//!      reason).
//!   6. Emit chain edges from unsolved Chain goals (dotted green).
//!
//! Each rule node is rendered as a Graphviz record:
//!
//! ```text
//!     +------------+------------+
//!     |  prem_0    |  prem_1    |
//!     +------------+------------+
//!     |     <#i> : RuleName     |
//!     +------------+------------+
//!     |  conc_0    |  conc_1    |
//!     +------------+------------+
//! ```
//!
//! with port names `p0`, `p1`, ..., `c0`, `c1`, ... so that edges from
//! the `sEdges` set can target the correct slots.

// every `HashMap`/`HashSet` in this DOT renderer is a
// keyed-lookup / membership helper — `node_map` (node id -> rule, `.get`),
// `has_outgoing` / `port_owner_ids` / `used_dot_ids` (`.contains` / `.insert`
// dedup).  DOT output ORDER is driven by iterating the ordered
// `repr.nodes` / `repr.edges` Vecs; these maps/sets are never iterated into
// output.  Also off the batch `--prove` byte-parity surface (server graph UI).
// std kept (byte-inert).
#![allow(clippy::disallowed_types)]

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use tamarin_term::lterm::{LNTerm, LVar};
use tamarin_term::pretty::pretty_lnterm;
use tamarin_theory::constraint::constraints::LessAtom;
use tamarin_theory::constraint::system::System;
use tamarin_theory::fact::{FactTag, LNFact};
use tamarin_theory::pretty_hpj::{self, Doc, WEB_LINE_LENGTH, WEB_RIBBON};
use tamarin_theory::rule::{rule_name_string, IntrRuleACInfo, ProtoRuleName, RuleACInst, RuleInfo};
// `fix_multi_line_label` is HS `fixMultiLineLabel` (Text/Dot.hs:355-363),
// applied to every record FIELD by the `mkField` smart constructor
// (Text/Dot.hs:378-381): a multi-line label has each line's leading spaces
// replaced 1:1 by `&nbsp;` and is re-joined with `unlines` — which appends a
// TRAILING newline (→ a trailing `\l` after `showAttr`).  Single-line labels
// pass through untouched.
use tamarin_utils::dot::fix_multi_line_label;

use crate::graph::abbreviation::{
    apply_abbreviations_fact, order_abbreviations_for_json, Abbreviations,
};
use crate::graph::color::{build_node_color_map, fact_doc_of, reason_color, NodeColorMap};
use crate::graph::options::GraphOptions;
use crate::graph::repr::{extract_base_name, extract_role, GEdge, GNode, MissingHint, NodeType};
use crate::graph::{system_to_graph, Graph};

/// `NodeId -> &RuleACInst` index over the ORIGINAL system: the `_gSystem` that
/// `resolveNodePremFact`/`resolveNodeConcFact` (Graph.hs:87-96) look an edge
/// endpoint up in, reducing HS's `M.lookup v sNodes` (System.hs:927/931) to one
/// hash lookup per endpoint.
type OrigNodeRules<'a> = tamarin_utils::FastMap<&'a LVar, &'a RuleACInst>;

// ---------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------

/// Render a [`System`] into a Graphviz DOT document with default
/// graph options (Haskell `defaultGraphOptions`: SL2 + compress).
/// Returns a self-contained `digraph G { ... }` block.
pub fn system_to_dot(sys: &System) -> String {
    system_to_dot_with(sys, &GraphOptions::default())
}

/// Render a [`System`] into a Graphviz DOT document under the given
/// options.  Applies compression, simplification, role-clustering, and
/// abbreviation discovery before emitting DOT, mirroring Haskell's
/// `systemToGraph` + `dotSystemCompact`.
pub fn system_to_dot_with(sys: &System, opts: &GraphOptions) -> String {
    // 1. HS `systemToGraph se graphOptions` (Dot.hs:508): simplify, cluster and
    //    compute abbreviations.  The abbreviations come back whatever
    //    `opts.abbreviate` says; that flag gates only their APPLICATION, below.
    let graph = system_to_graph(sys, opts);
    // HS `dotSystemCompact` (Dot.hs:506-512, see line 510) computes the node
    // colour map from the RAW system's nodes (`nodeColorMap (M.elems $ get
    // sNodes se)`), NOT the compressed/simplified copy the repr was built from.
    // Mirror that: the palette is sized by the whole rule set, so it must see
    // every original node.
    let color_map = build_node_color_map(&sys.nodes);
    // 2. Emit DOT.
    dot_graph_compact(opts, &color_map, &graph)
}

/// Port of `dotGraphCompact` (Dot.hs:514-538): emit a [`Graph`]'s repr as DOT
/// under a precomputed [`NodeColorMap`].
///
/// Kept separate from [`system_to_dot_with`] because the two halves read
/// DIFFERENT systems, exactly as HS does: the colour map and `dotEdge`'s fact
/// resolution go through the ORIGINAL system, while the nodes, clusters and
/// edges laid out here come from the compressed/simplified copy in
/// [`Graph::repr`].
fn dot_graph_compact(opts: &GraphOptions, color_map: &NodeColorMap, graph: &Graph<'_>) -> String {
    let repr = &graph.repr;
    let abbrevs = &graph.abbreviations;
    let mut g = DotBuilder::new();
    // HS `dotGraphCompact` (Dot.hs:515-538, see line 528) switches the graph-level defaults to
    // `setDefaultAttributesIfCluster` when the repr has any clusters.
    g.preamble(!repr.clusters.is_empty());
    // HS `renderLNFact` (Dot.hs:228-236) asks for the abbreviated fact only
    // when `goAbbreviate` is set and renders the original otherwise; an
    // always-`None` lookup leaves every fact untouched, which is that `else`
    // arm.
    let abbrev_lookup = |t: &LNTerm| -> Option<LNTerm> {
        if !opts.abbreviate {
            return None;
        }
        abbrevs.get(t).map(|(a, _)| a.clone())
    };
    // Precompute a node-id -> rule map so the record-port decision is O(1) per
    // edge endpoint instead of scanning the simplified system's nodes per edge.
    // This is the SIMPLIFIED system, which is what backs HS's `dsConcs`/`dsPrems`
    // (Dot.hs:265-268 — filled while `dotNodeCompact` walks the repr's nodes),
    // the maps `dotGenEdge` (Dot.hs:403-406) resolves an edge's endpoints
    // through.
    let node_map: HashMap<&LVar, &RuleACInst> = graph
        .simplified
        .nodes
        .iter()
        .map(|(id, ru)| (id, ru))
        .collect();
    // Fact resolution for the edge STYLE reads a different system: `dotEdge`'s
    // `check` (Dot.hs:391-392) calls `resolveNodePremFact`/`resolveNodeConcFact`
    // from Graph.hs (:87-96), which look the endpoint up in `_gSystem` — the
    // ORIGINAL system `systemToGraph` stores alongside the repr (`Graph se
    // options repr abbrevs`, Graph.hs:164), not the compressed/simplified copy
    // the repr's nodes come from.  A node the compression hid is therefore still
    // resolvable here even though it is drawn as a `MissingNode` trapezium.
    let orig_node_map = graph.system.node_rule_map();
    // HS `hasOutgoingEdge graph v` (Dot.hs:280-283): a node has an outgoing edge
    // iff it is the conclusion-side source of some `SystemEdge` in the graph's
    // TOP-LEVEL edge set (`get grEdges repr`). Clustering removes a cluster's
    // internal edges from `grEdges` (GraphRepr.hs:126-129), so we mirror HS and
    // consult ONLY `repr.edges` (post-clustering), never a cluster's own edges.
    // Drives the compact-node label choice in `rule_node`.
    let has_outgoing: HashSet<&LVar> = repr
        .edges
        .iter()
        .filter_map(|e| match e {
            GEdge::System(src, _) => Some(&src.0),
            _ => None,
        })
        .collect();
    // HS gives every node a globally-fresh dot id via `cacheState dsNodes`
    // (Dot.hs:108-110), so a single system-node id `v` that is ALSO an
    // unsolved-action atom and/or the last-action atom is drawn as SEVERAL
    // distinct dot nodes (`n5` record + `n7` ellipse …). RS's semantic dot-id
    // scheme derives one id per `v` (`dot_node_id`), so those extra ellipses
    // would collide with the record on a single id — graphviz merges them (the
    // ellipse overwrites the record) and the parity gate's label-keyed node map
    // drops the record. Mirror HS: the SystemNode / MissingNode own the base id
    // (their record ports / bare id are what `sEdges` reference via
    // `conc_port_ref`/`prem_port_ref` = HS `dsConcs`/`dsPrems`), and a colliding
    // UnsolvedAction / LastAction ellipse (which HS never references by an
    // sEdge) gets a distinct suffixed id.
    //
    // `dsNodes[v]` (which HS `dotLessEdge` resolves each less-edge endpoint
    // through, Dot.hs:408-409) is the LAST dot node emitted at `v`. Emission
    // order is the free `repr.nodes` (System, UnsolvedAction, LastAction,
    // Missing per `compute_basic_graph_repr`) then each cluster's nodes — so we
    // walk that exact order, assigning ids and overwriting `ds_nodes` as we go.
    //
    // `port_owner_ids` = the `v`s whose base id backs an sEdge port ref
    // (SystemNode records + MissingNodes). An UnsolvedAction/LastAction at such
    // a `v` MUST yield the base to that owner regardless of emission order (a
    // SystemNode can be clustered and thus emitted AFTER a free action ellipse).
    let port_owner_ids: HashSet<&LVar> = repr
        .nodes
        .iter()
        .chain(repr.clusters.iter().flat_map(|c| c.nodes.iter()))
        .filter(|n| matches!(n.ty, NodeType::System(_) | NodeType::Missing(_)))
        .map(|n| &n.id)
        .collect();
    let mut used_dot_ids: HashSet<String> = HashSet::new();
    // Assigned id for each UnsolvedAction (tag 0) / LastAction (tag 1) node,
    // keyed by (node id, tag) — at most one of each kind per `v`.
    let mut ellipse_dot_ids: std::collections::BTreeMap<(LVar, u8), String> =
        std::collections::BTreeMap::new();
    // `dsNodes`: v -> dot id of the LAST node emitted at v (less-edge target).
    let mut ds_nodes: std::collections::BTreeMap<LVar, String> = std::collections::BTreeMap::new();
    for node in repr
        .nodes
        .iter()
        .chain(repr.clusters.iter().flat_map(|c| c.nodes.iter()))
    {
        let base = DotBuilder::dot_node_id(&node.id);
        let id = match &node.ty {
            // Base-id owners: their id is referenced by sEdge port refs.
            NodeType::System(_) | NodeType::Missing(_) => {
                used_dot_ids.insert(base.clone());
                base
            }
            NodeType::UnsolvedAction(_) | NodeType::LastAction => {
                let tag: u8 = if matches!(node.ty, NodeType::LastAction) {
                    1
                } else {
                    0
                };
                let suffix = if tag == 1 {
                    "__lastatom"
                } else {
                    "__actionatom"
                };
                let id = if port_owner_ids.contains(&node.id) || used_dot_ids.contains(&base) {
                    let mut cand = format!("{base}{suffix}");
                    let mut n = 2u32;
                    while used_dot_ids.contains(&cand) {
                        cand = format!("{base}{suffix}{n}");
                        n += 1;
                    }
                    cand
                } else {
                    base
                };
                used_dot_ids.insert(id.clone());
                ellipse_dot_ids.insert((node.id, tag), id.clone());
                id
            }
        };
        ds_nodes.insert(node.id, id);
    }
    // 2a. Top-level (ungrouped) nodes.
    //
    // HS `dotGraphCompact` (Dot.hs:530-535) emits, in order: the FREE
    // (ungrouped) nodes (`mapM_ dotNodeCompact nodes`), THEN the clusters
    // (`mapM_ dotCluster clusters`), THEN the edges.  The free nodes — e.g. an
    // unsolved-action-atom ellipse like `Unlock_0(..) @ #t2.1` — therefore
    // appear BEFORE any `subgraph cluster_*` block.  Emit them first to match
    // (a free node emitted after the cluster's closing `}` lands in the wrong
    // scope order vs HS).
    for node in &repr.nodes {
        emit_node(
            &mut g,
            node,
            &abbrev_lookup,
            opts,
            color_map,
            &has_outgoing,
            &ellipse_dot_ids,
        );
    }
    // 2b. Clusters as subgraphs.
    //
    // HS `dotCluster` (Dot.hs:572-587): each cluster gets a `roleColor`
    // derived from `extractBaseName name`, the subgraph is `style=filled`
    // with that colour, and the colour is threaded to the child nodes as
    // their `manualNodeColor` (Dot.hs:572-587, see line 587). HS also defers ALL of a
    // cluster's edges to `dotClustersEdges` (Dot.hs:507-510/517-522), which
    // runs `mergeLessEdges` over the concatenation of every cluster's edges
    // and emits them AFTER every node/cluster — so we collect them here.
    let mut cluster_edges: Vec<GEdge> = Vec::new();
    for (i, cluster) in repr.clusters.iter().enumerate() {
        // `baseName = fromMaybe "Undefined" (extractBaseName name)`.
        let base = extract_base_name(&cluster.name).unwrap_or_else(|| "Undefined".to_string());
        let color = role_color(&base);
        g.open_subgraph(i, &cluster.name, &color);
        for node in &cluster.nodes {
            emit_node_colored(
                &mut g,
                node,
                &abbrev_lookup,
                opts,
                Some(&color),
                color_map,
                &has_outgoing,
                &ellipse_dot_ids,
            );
        }
        g.close_subgraph();
        cluster_edges.extend(cluster.edges.iter().cloned());
    }
    // 2c. Edges. HS emits `restEdges` (non-less) before the merged
    // `lessEdges` within each scope (`dotGraphCompact`, Dot.hs:533-534),
    // then the cluster edges last (`dotClustersEdges`).
    emit_edges_merged(&mut g, &repr.edges, &node_map, &orig_node_map, &ds_nodes);
    emit_edges_merged(&mut g, &cluster_edges, &node_map, &orig_node_map, &ds_nodes);
    // 2d. Legend.  HS `when abbreviate generateLegend` (Dot.hs:538) gates the
    // whole legend on the option, and `generateLegend` itself skips an empty
    // abbreviation map (`unless (null abbrevs)`, Dot.hs:443).
    if opts.abbreviate && !abbrevs.is_empty() {
        g.legend(abbrevs);
    }
    g.close();
    g.into_string()
}

fn emit_node(
    g: &mut DotBuilder,
    node: &GNode,
    abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    opts: &GraphOptions,
    color_map: &NodeColorMap,
    has_outgoing: &HashSet<&LVar>,
    ellipse_dot_ids: &std::collections::BTreeMap<(LVar, u8), String>,
) {
    emit_node_colored(
        g,
        node,
        abbrev,
        opts,
        None,
        color_map,
        has_outgoing,
        ellipse_dot_ids,
    );
}

/// `emit_node` with an optional `manual_color` — the cluster `roleColor`
/// that HS `dotCluster` threads to its child nodes as `manualNodeColor`
/// (Dot.hs:572-587, see line 587). Only the `SystemNode` branch consults it (HS
/// `dotNodeCompact`, Dot.hs:248-256); the other node kinds ignore it.
fn emit_node_colored(
    g: &mut DotBuilder,
    node: &GNode,
    abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    opts: &GraphOptions,
    manual_color: Option<&str>,
    color_map: &NodeColorMap,
    has_outgoing: &HashSet<&LVar>,
    ellipse_dot_ids: &std::collections::BTreeMap<(LVar, u8), String>,
) {
    // Look up the (possibly collision-disambiguated) dot id assigned to a
    // non-record ellipse node (UnsolvedAction tag 0 / LastAction tag 1).
    let ellipse_id = |tag: u8| -> String {
        ellipse_dot_ids
            .get(&(node.id, tag))
            .cloned()
            .unwrap_or_else(|| DotBuilder::dot_node_id(&node.id))
    };
    match &node.ty {
        NodeType::System(ru) => {
            let ru_abbreviated = abbreviate_rule(ru, abbrev);
            let outgoing = has_outgoing.contains(&node.id);
            g.rule_node(
                &node.id,
                &ru_abbreviated,
                opts,
                manual_color,
                color_map,
                outgoing,
            );
        }
        NodeType::UnsolvedAction(facts) => {
            let new_facts: Vec<LNFact> = facts
                .iter()
                .map(|fa| apply_abbreviations_fact(abbrev, fa))
                .collect();
            // A colliding action ellipse (same `v` as a system record) gets a
            // distinct dot id so both nodes survive (see `ds_nodes`).
            g.action_node(&ellipse_id(0), &node.id, &new_facts);
        }
        // The last-atom uses its (possibly collision-disambiguated) dot id so
        // it does not clash with a same-id system node.
        NodeType::LastAction => {
            g.last_node(&ellipse_id(1), &node.id);
        }
        NodeType::Missing(hint) => g.missing_node(&node.id, hint),
    }
}

/// Emit a scope's edges in HS `dotGraphCompact` order: every non-less edge
/// first (`restEdges`), then the merged less-edges (`mergeLessEdges`,
/// Dot.hs:567-597). Because `LessAtom` equality ignores the reason, the
/// system holds at most one less-atom per `(smaller, larger)` pair, so the
/// `eqClasses` grouping is a no-op (singleton groups) — we only need to
/// reproduce its SORT (by `(smaller, larger)`, via `Ord LVar`) and the
/// single-reason colour. The gradient/`;weight` share code only fires for
/// multi-reason groups, which cannot arise here.
fn emit_edges_merged(
    g: &mut DotBuilder,
    edges: &[GEdge],
    node_map: &HashMap<&LVar, &RuleACInst>,
    orig_node_map: &OrigNodeRules<'_>,
    ds_nodes: &std::collections::BTreeMap<LVar, String>,
) {
    // restEdges: keep original order, drop less-edges.
    for edge in edges {
        match edge {
            GEdge::System(src, tgt) => {
                g.edge(node_map, orig_node_map, src, tgt);
            }
            GEdge::UnsolvedChain(src, tgt) => g.chain_edge(node_map, src, tgt),
            GEdge::Less(_) => {}
        }
    }
    // lessEdges: collect, sort by (smaller, larger) like `eqClasses`, emit one
    // merged edge per pair.
    let mut lesses: Vec<&LessAtom> = edges
        .iter()
        .filter_map(|e| match e {
            GEdge::Less(la) => Some(la),
            _ => None,
        })
        .collect();
    lesses.sort_by(|a, b| (&a.smaller, &a.larger).cmp(&(&b.smaller, &b.larger)));
    for la in lesses {
        g.less_edge(la, ds_nodes);
    }
}

fn abbreviate_rule(ru: &RuleACInst, abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>) -> RuleACInst {
    let mut new_ru = ru.clone();
    new_ru.premises = ru
        .premises
        .iter()
        .map(|fa| apply_abbreviations_fact(abbrev, fa))
        .collect();
    new_ru.actions = ru
        .actions
        .iter()
        .map(|fa| apply_abbreviations_fact(abbrev, fa))
        .collect();
    new_ru.conclusions = ru
        .conclusions
        .iter()
        .map(|fa| apply_abbreviations_fact(abbrev, fa))
        .collect();
    new_ru
}

/// Helper used by handlers to render the [`System`] as DOT and pipe it
/// through `/usr/bin/dot -Tsvg` (or whatever's on `$PATH`) under the given
/// graph options.  Returns the SVG bytes on success.  When `dot` is
/// missing or fails, returns the DOT source instead (the frontend's
/// `intdot-staticgraph` can render DOT client-side via viz.js, so this
/// stays a useful response).
pub fn render_svg_or_dot_with(sys: &System, opts: &GraphOptions) -> RenderResult {
    let dot = system_to_dot_with(sys, opts);
    match try_render_dot_to_svg(&dot) {
        Ok(svg) => RenderResult::Svg(svg),
        Err(_) => RenderResult::Dot(dot),
    }
}

/// What we got back from `dot`.
pub enum RenderResult {
    /// SVG bytes produced by `dot -Tsvg`.
    Svg(Vec<u8>),
    /// Raw DOT source, returned when the `dot` binary is unavailable or failed.
    Dot(String),
}

fn try_render_dot_to_svg(dot: &str) -> std::io::Result<Vec<u8>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("dot")
        .args(["-Tsvg"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    // Write the full DOT to `dot`'s stdin on a separate thread while the
    // main thread drains stdout/stderr via `wait_with_output`.  Doing the
    // (blocking) `write_all` inline before reading stdout can deadlock on
    // large graphs: `dot` fills its stdout pipe and blocks, and so does our
    // `write_all` on a full stdin pipe.
    let writer = child.stdin.take().map(|mut sin| {
        let bytes = dot.as_bytes().to_vec();
        std::thread::spawn(move || sin.write_all(&bytes))
    });
    let out = child.wait_with_output()?;
    if let Some(handle) = writer {
        // Propagate any write error (ignore a panicked thread).
        if let Ok(res) = handle.join() {
            res?;
        }
    }
    if !out.status.success() {
        return Err(std::io::Error::other(format!(
            "dot exited with status {:?}",
            out.status
        )));
    }
    Ok(out.stdout)
}

// ---------------------------------------------------------------------
// DOT construction
// ---------------------------------------------------------------------

struct DotBuilder {
    buf: String,
}

impl DotBuilder {
    fn new() -> Self {
        DotBuilder { buf: String::new() }
    }
    fn into_string(self) -> String {
        self.buf
    }
    fn preamble(&mut self, has_clusters: bool) {
        let _ = writeln!(self.buf, "digraph G {{");
        if has_clusters {
            // HS `setDefaultAttributesIfCluster` (Dot.hs:140-161): a richer
            // attribute block for clustered graphs.
            let _ = writeln!(self.buf, "  nodesep=0.8; ranksep=0.8;");
            let _ = writeln!(self.buf, "  sep=4;");
            let _ = writeln!(self.buf, "  splines=true;");
            let _ = writeln!(self.buf, "  overlap=false;");
            let _ = writeln!(self.buf, "  pack=true;");
            let _ = writeln!(self.buf, "  packmode=cluster;");
            let _ = writeln!(self.buf, "  concentrate=true;");
            let _ = writeln!(self.buf, "  compound=true;");
            let _ = writeln!(self.buf, "  remincross=true;");
            let _ = writeln!(self.buf, "  mclimit=10;");
            let _ = writeln!(self.buf, "  nslimit=20;");
            let _ = writeln!(self.buf, "  nslimit1=20;");
            let _ = writeln!(self.buf, "  ordering=out;");
            let _ = writeln!(self.buf, "  rankdir=TB;");
            let _ = writeln!(self.buf, "  showboxes=false;");
            let _ = writeln!(self.buf, "  clusterrank=local;");
            // HS `setDefaultAttributesIfCluster` sets the graph-level node
            // default shape to `ellipse` (Dot.hs:140-161, see line 160); each compact rule node
            // overrides it with its own per-node `shape=record` (emitted in
            // `rule_node`, mirroring HS `genRecord "record"`), so record rules
            // still render as records inside clusters.
            let _ = writeln!(self.buf,
                "  node [fontsize=8,fontname=\"Helvetica\",width=0.3,height=0.2,margin=\"0.05,0.05\",shape=ellipse];");
            let _ = writeln!(self.buf,
                "  edge [fontsize=8,fontname=\"Helvetica\",penwidth=1.5,arrowsize=0.5,color=black,style=solid,weight=8];");
        } else {
            // HS `setDefaultAttributes` (Dot.hs:130-135). Note the node
            // `width=0.3,height=0.2` defaults HS emits; we additionally keep
            // `shape=record` because each rule node is rendered as a record
            // label (HS sets the record shape per-node via `D.record`).
            let _ = writeln!(self.buf, "  nodesep=0.3; ranksep=0.3;");
            let _ = writeln!(
                self.buf,
                "  node [fontsize=8,fontname=\"Helvetica\",width=0.3,height=0.2,shape=record];"
            );
            let _ = writeln!(self.buf, "  edge [fontsize=8,fontname=\"Helvetica\"];");
        }
    }
    fn close(&mut self) {
        let _ = writeln!(self.buf, "}}");
    }
    fn dot_node_id(nid: &LVar) -> String {
        // Sanitise to a valid DOT identifier.
        let raw = format!("{}_{}", nid.name, nid.idx);
        raw.chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect()
    }
    fn rule_node(
        &mut self,
        nid: &LVar,
        ru: &RuleACInst,
        opts: &GraphOptions,
        manual_color: Option<&str>,
        color_map: &NodeColorMap,
        outgoing: bool,
    ) {
        let id = Self::dot_node_id(nid);
        // HS `mkNode`'s `CompactBoringNodes` branch (Dot.hs:294-304): under the
        // default node style (`defaultDotOptions = DotOptions CompactBoringNodes`,
        // Dot.hs:81-84, see line 82; the interactive route builds its `DotOptions` from
        // `getOptions`, Handler.hs:1331-1349, see line 1334/1348, defaulting to `CompactBoringNodes`
        // when the `uncompact` query param is absent), an intruder rule or the
        // `Fresh` rule collapses to a plain `mkSimpleNode` ellipse (Dot.hs:289-290)
        // with NO fill/font/role attrs. Its label is `show v : showDotRuleCaseName
        // ru` when the node has an outgoing edge, else the full rule label incl.
        // the bracketed action row (`concatMap snd as` = `ruleLabelM`,
        // Dot.hs:301-302/330-338). The ellipse label is a PLAIN string, so it is
        // escaped with `escape_dot_label` (HS `showAttr`, Dot.hs:346-353), NOT the
        // record-field `escape_dot`.
        if is_intruder_or_fresh(ru) {
            let lbl = if outgoing {
                format!("{} : {}", nid, rule_case_name(ru))
            } else {
                // HS `concatMap snd as` (Dot.hs:236-379, see line 302) — `as` is the
                // `renderRow`-rendered rule label, i.e. the SAME
                // `renderBalanced` single-doc row (width 130) the record
                // mid row uses.  No `fixMultiLineLabel` here: this label
                // goes through plain `mkSimpleNode` → `D.node` → `showAttr`
                // (spaces stay spaces; `\n` → `\l` via `escape_dot_label`).
                render_balanced(vec![rule_label_doc(nid, ru, opts)])
                    .pop()
                    .unwrap_or_default()
            };
            let _ = writeln!(
                self.buf,
                "  {} [label=\"{}\",shape=ellipse];",
                id,
                escape_dot_label(&lbl)
            );
            return;
        }
        // Build prems / acts / concs rows as Docs, then lay each row out with
        // HS `renderRow`/`renderBalanced` (Dot.hs:357-379): every field of a
        // row is rendered at a width proportional to its one-line length
        // (total 100, `max 30 . round . (*1.3)`), NOT at the page width.
        let prem_docs: Vec<Doc> = ru.premises.iter().map(fact_doc_of).collect();
        let conc_docs: Vec<Doc> = ru.conclusions.iter().map(fact_doc_of).collect();
        let ps = render_balanced(prem_docs);
        let mid = render_balanced(vec![rule_label_doc(nid, ru, opts)])
            .pop()
            .unwrap_or_default();
        let cs = render_balanced(conc_docs);
        // Record label — HS `D.vcat $ map D.hcat $ … $ filter (not . null)
        // [ps, as, cs]` (Dot.hs:310-312) rendered by `Text.Dot.renderRecord`
        // (Text/Dot.hs:254-280): the outer VCat renders as `{row|row|row}`,
        // each row (HCat) as `{field|field}`, each ported field as
        // `<port> text`.  Field text goes through `fixMultiLineLabel`
        // (mkField, Text/Dot.hs:378-381: leading spaces → `&nbsp;`, plus a
        // trailing newline via `unlines` when multi-line) and the
        // record-metachar escape (`| { } < >`, Text/Dot.hs:273-280).  The
        // remaining newlines become `\l` at the attribute level
        // (`showAttr`, Text/Dot.hs:346-353) via `escape_dot_label`.
        let mut rows: Vec<String> = Vec::new();
        if !ps.is_empty() {
            rows.push(format!(
                "{{{}}}",
                ps.iter()
                    .enumerate()
                    .map(|(i, s)| format!(
                        "<p{}> {}",
                        i,
                        escape_record_field(&fix_multi_line_label(s))
                    ))
                    .collect::<Vec<_>>()
                    .join("|")
            ));
        }
        rows.push(format!(
            "{{{}}}",
            escape_record_field(&fix_multi_line_label(&mid))
        ));
        if !cs.is_empty() {
            rows.push(format!(
                "{{{}}}",
                cs.iter()
                    .enumerate()
                    .map(|(i, s)| format!(
                        "<c{}> {}",
                        i,
                        escape_record_field(&fix_multi_line_label(s))
                    ))
                    .collect::<Vec<_>>()
                    .join("|")
            ));
        }
        let lbl = escape_dot_label(&format!("{{{}}}", rows.join("|")));
        let color = rule_fillcolor(ru, nid, manual_color, color_map);
        // HS `dotNodeCompact` record `attrs` (Dot.hs:257-259) also carry a
        // `fontcolor` and a `role`. The `fontcolor` keys off the PALETTE colour
        // (`M.lookup rInfoVal colorMap`), i.e. the raw map value — NOT the
        // resolved `fillcolor` — so an explicit/cluster override does not change
        // the font choice. `role = fromMaybe "Undefined" (getNodeRole node)`
        // (Dot.hs:236-379, see line 243).
        let palette_color = color_map.lookup_node(nid);
        let fontcolor = if color_uses_white_font(palette_color) {
            "white"
        } else {
            "black"
        };
        let role = extract_role(ru).unwrap_or("Undefined");
        // HS `genRecord "record"` (Text/Dot.hs:284-288) prepends an explicit
        // `("shape","record")` to every compact record node, then the label and
        // the `dotNodeCompact` `attrs`.  The per-node `shape=record` OVERRIDES the
        // graph-level default node shape — which is `record` in the flat
        // `setDefaultAttributes` case but `ellipse` in the clustered
        // `setDefaultAttributesIfCluster` case (Dot.hs:140-161, see line 160).  Emit it explicitly
        // so clustered SAPIC graphs keep `shape=record` (not the ellipse default).
        let _ = writeln!(self.buf,
            "  {} [shape=record,label=\"{}\",style=\"filled\",fillcolor=\"{}\",fontcolor=\"{}\",role=\"{}\"];",
            id, lbl, color, fontcolor, escape_dot_label(role));
    }
    fn action_node(&mut self, id: &str, nid: &LVar, facts: &[LNFact]) {
        // HS `lblPre <- fsep <$> punctuate comma <$> mapM renderLNFact facts;
        // lbl = lblPre <-> opAction <-> text (show v); mkSimpleNode (render
        // lbl) attrs` (Dot.hs:267-272): the WHOLE label is ONE Doc — the
        // facts fill-wrap as a paragraph — rendered by the default-style
        // `render` (HughesPJ `style`: lineLength 100, ribbon 67), NOT one
        // fact at a time.  `opAction = operator_ "@"`, `<->` is space-joined,
        // and `show v` renders via `Display for LVar` (e.g. `#i` / `#i.2`).
        let fact_docs: Vec<Doc> = facts.iter().map(fact_doc_of).collect();
        let s = pretty_hpj::fsep(pretty_hpj::punctuate(Doc::text(","), fact_docs))
            .beside_sp(Doc::text("@"))
            .beside_sp(Doc::text(nid.to_string()))
            .render_with(WEB_LINE_LENGTH, WEB_RIBBON);
        let color = if facts.iter().any(|f| matches!(f.tag, FactTag::Ku)) {
            "gray"
        } else {
            "darkblue"
        };
        // HS renders a loose action node via `mkSimpleNode (render lbl) attrs`
        // (Dot.hs:270-275) — plain `D.node [("label", …), ("shape","ellipse")]`
        // (Dot.hs:292-293), NOT `D.record`.  A plain node label is a quoted
        // string whose only metacharacters are `"` and newline (`escape_dot_label` =
        // `showAttr`, Text/Dot.hs:346-353); the record metacharacters
        // `{ } | < >` are LITERAL, so a tuple `<A, B, …>` in a goal fact must
        // stay `<…>` and NOT be `\<…\>`-escaped (only the `SystemNode`/
        // `D.record` path escapes them).
        let _ = writeln!(
            self.buf,
            "  {} [shape=ellipse,label=\"{}\",color=\"{}\"];",
            id,
            escape_dot_label(&s),
            color
        );
    }
    fn last_node(&mut self, dot_id: &str, nid: &LVar) {
        // HS `LastActionAtom -> mkSimpleNode (show v) []` (Dot.hs:236-379, see line 273): the
        // label is `show v`, rendered via `Display for LVar` (`#i` / `#i.2`),
        // via plain `D.node` (see `action_node`), so use the plain-label escaper.
        // `dot_id` is the collision-disambiguated id (see `ellipse_dot_ids`).
        let _ = writeln!(
            self.buf,
            "  {} [shape=ellipse,label=\"{}\"];",
            dot_id,
            escape_dot_label(&nid.to_string())
        );
    }
    fn missing_node(&mut self, nid: &LVar, hint: &MissingHint) {
        let id = Self::dot_node_id(nid);
        // Mirror Haskell `dotNodeCompact` (Dot.hs:274-282): a
        // missing-conclusion node is a `trapezium` labelled `prettyNodeConc`,
        // a missing-premise node is an `invtrapezium` labelled `prettyNodePrem`.
        // Both labels are `parens (prettyNodeId v <> comma <-> int i)`
        // (Constraints.hs:248-249, see line 251/255), i.e. `(<show v>, <i>)` — the conclusion /
        // premise index is part of the label, not dropped.
        let (shape, idx) = match hint {
            MissingHint::Conc(ci) => ("trapezium", ci.0),
            MissingHint::Prem(pi) => ("invtrapezium", pi.0),
        };
        let label = format!("({}, {})", nid, idx);
        // HS `dotConcC`/`dotPremC` = `missingNode shape (render label)` = plain
        // `D.node` (Dot.hs:280-282), so use the plain-label escaper (matching
        // `action_node`/`last_node`).  This label (`(#i, 0)`) never contains
        // record metacharacters, so the choice is inert here, but keeping all
        // three plain (ellipse/trapezium) nodes on `escape_dot_label` mirrors HS.
        let _ = writeln!(
            self.buf,
            "  {} [shape={},label=\"{}\"];",
            id,
            shape,
            escape_dot_label(&label)
        );
    }
    fn edge(
        &mut self,
        node_map: &HashMap<&LVar, &RuleACInst>,
        orig_node_map: &OrigNodeRules<'_>,
        src: &tamarin_theory::constraint::constraints::NodeConc,
        tgt: &tamarin_theory::constraint::constraints::NodePrem,
    ) {
        // The endpoint FACTS that colour the edge come from the original system
        // (`dotEdge`'s `check`, Dot.hs:391-392); the endpoint PORTS come from the
        // simplified one (`dotGenEdge`'s `dsConcs`/`dsPrems`, Dot.hs:403-406).
        let style = edge_style(orig_node_map, src, tgt);
        let src_ref = conc_port_ref(node_map, src);
        let tgt_ref = prem_port_ref(node_map, tgt);
        let _ = writeln!(self.buf, "  {} -> {} [{}];", src_ref, tgt_ref, style);
    }
    fn chain_edge(
        &mut self,
        node_map: &HashMap<&LVar, &RuleACInst>,
        src: &tamarin_theory::constraint::constraints::NodeConc,
        tgt: &tamarin_theory::constraint::constraints::NodePrem,
    ) {
        let src_ref = conc_port_ref(node_map, src);
        let tgt_ref = prem_port_ref(node_map, tgt);
        let _ = writeln!(
            self.buf,
            "  {} -> {} [style=\"dotted\",color=\"green\"];",
            src_ref, tgt_ref
        );
    }
    /// Open a subgraph (Graphviz `subgraph cluster_<n> { ... }`).
    /// `idx` is a numeric disambiguator; `name` is shown as the label and
    /// `color` is the cluster's `roleColor` (HS `dotCluster`, Dot.hs:572-587).
    ///
    /// The attribute block mirrors HS `dotCluster`'s sequence exactly:
    /// `nodesep=0.6`, `ranksep=0.6`, `label`, `style=filled`, `color`,
    /// `penwidth=2`, `fillcolor`, `overlap=false`, `sep=4`. (The subgraph id
    /// `cluster_<n>` is the Rust convention — HS uses
    /// `createClusterNodeId roleName` — but the styling attributes are
    /// byte-faithful.)
    fn open_subgraph(&mut self, idx: usize, name: &str, color: &str) {
        let _ = writeln!(self.buf, "  subgraph cluster_{} {{", idx);
        let _ = writeln!(self.buf, "    nodesep=\"0.6\";");
        let _ = writeln!(self.buf, "    ranksep=\"0.6\";");
        let _ = writeln!(self.buf, "    label=\"{}\";", escape_dot_label(name));
        let _ = writeln!(self.buf, "    style=\"filled\";");
        let _ = writeln!(self.buf, "    color=\"{}\";", color);
        let _ = writeln!(self.buf, "    penwidth=\"2\";");
        let _ = writeln!(self.buf, "    fillcolor=\"{}\";", color);
        let _ = writeln!(self.buf, "    overlap=\"false\";");
        let _ = writeln!(self.buf, "    sep=\"4\";");
    }
    fn close_subgraph(&mut self) {
        let _ = writeln!(self.buf, "  }}");
    }
    /// Emit a single merged less-edge. HS `dotLessEdge` (Dot.hs:406-410)
    /// emits the attributes `[("color",color),("style","dashed")]` — colour
    /// FIRST, then style. The colour is `allRtoColors` of the group's
    /// reasons; since at most one less-atom survives per node pair (LessAtom
    /// equality ignores the reason), the group is a singleton and the colour
    /// reduces to the single reason's `toColor` (`reason_color`).
    fn less_edge(&mut self, la: &LessAtom, ds_nodes: &std::collections::BTreeMap<LVar, String>) {
        // HS `dotLessEdge` resolves each endpoint through `dsNodes` (Dot.hs:408-409),
        // which holds the LAST dot node emitted at that id — the action / last
        // ellipse when it shadows a same-id system record. Mirror that by
        // resolving through the precomputed `ds_nodes` map (falling back to the
        // bare id for any endpoint that was never emitted as a node).
        let resolve = |nid: &LVar| -> String {
            ds_nodes
                .get(nid)
                .cloned()
                .unwrap_or_else(|| Self::dot_node_id(nid))
        };
        let s = resolve(&la.smaller);
        let t = resolve(&la.larger);
        let _ = writeln!(
            self.buf,
            "  {} -> {} [color=\"{}\",style=\"dashed\"];",
            s,
            t,
            reason_color(la.reason)
        );
    }
    /// Emit a legend node listing the chosen abbreviations.
    /// Mirror of Haskell's `generateLegend` (Dot.hs:415-474) — produces a
    /// single DOT node with an HTML-table label of `name = expansion` rows.
    /// Rows are ordered by `topoSortAbbrevs` applied to a descending sort
    /// of the rendered abbreviation names, so that an abbreviation used
    /// inside another's expansion is printed first.
    fn legend(&mut self, abbrevs: &Abbreviations) {
        // `topoSortAbbrevs (sortOn (Down . render . prettyLNTerm . fst) (M.toList
        // abbrevs))` — [`order_abbreviations_for_json`] runs exactly that
        // pipeline and additionally carries each entry's original term, which
        // the legend rows do not use.
        let ordered = order_abbreviations_for_json(abbrevs);
        // Mirror Haskell `abbrevLabel`: tableAttributes =
        //   [Border 1, CellBorder 0, CellSpacing 3, CellPadding 1].
        let mut html = String::new();
        html.push_str("<<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"3\" CELLPADDING=\"1\">");
        // Mirror Haskell `renderLine` (Dot.hs:441-450): each row is three
        // `LabelCell`s with `cellAttributes = [Align HLeft, VAlign HTop]`.
        // The NAME cell wraps its text in `<FONT COLOR="labelColor">`
        // (`font txt = Text [Font [Color labelColor] txt]`), while the `=`
        // and expansion cells are bare `Text`.  `labelColor = doAbbrevColor`
        // (`defaultDotOptions = DotOptions CompactBoringNodes black`,
        // Dot.hs:81-84, see line 82; the web route never overrides `_doAbbrevColor`), which
        // renders as `#000000`.  The graphviz HTML-table printer emits the
        // cells of a `Cells` row separated by a single space and each `<TR>`
        // on its own line, so we join the three cells with `" "` and the rows
        // with `"\n"`.
        let rows: Vec<String> = ordered
            .into_iter()
            .map(|(_term, name, exp)| {
                let name_cell = format!(
                    "<TD ALIGN=\"LEFT\" VALIGN=\"TOP\"><FONT COLOR=\"#000000\">{}</FONT></TD>",
                    dot_html_escape(&pretty_lnterm(name))
                );
                let eq_cell = "<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">=</TD>".to_string();
                let exp_cell = format!(
                    "<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">{}</TD>",
                    dot_html_escape(&pretty_lnterm(exp))
                );
                format!("<TR>{}</TR>", [name_cell, eq_cell, exp_cell].join(" "))
            })
            .collect();
        html.push_str(&rows.join("\n"));
        html.push_str("</TABLE>>");
        // HS `generateLegend` (Dot.hs:419-425) emits the legend inside a
        // `D.scope` carrying `rank="sink"` — i.e. `{ rank="sink"; <node>; }` —
        // then adds invisible sink→legend edges purely for layout (which we
        // omit, matching the parity comparator that drops `style=invis`
        // edges).  Reproduce the scope: besides mirroring HS's structure, the
        // leading `rank="sink";` statement keeps the legend a self-contained
        // statement.  A bare top-level `legend [...]` node emitted right after
        // a cluster's brace-terminated (`}`, no `;`) close would otherwise be
        // glued to that `}` by a naive statement splitter and lost.  Haskell
        // emits shape "plain".
        let _ = writeln!(self.buf, "  {{");
        let _ = writeln!(self.buf, "  rank=\"sink\";");
        let _ = writeln!(self.buf, "  legend [shape=plain,label={}];", html);
        let _ = writeln!(self.buf, "  }}");
    }
}

/// HTML-escape a string for use in a Graphviz HTML-like label.
/// Distinct from `crate::handlers::root::html_escape` (which also escapes
/// `'`) because it targets a different context (DOT HTML-like label vs a
/// general HTML page); do NOT merge the two char sets.
fn dot_html_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

/// Haskell `round :: Double -> Int` — IEEE round-half-to-EVEN (banker's
/// rounding), unlike Rust's `f64::round` (half-away-from-zero).  The
/// balanced widths (`conv = max 30 . round . (*1.3)`), the ribbon
/// (`round (w / 1.5)` in `fullRender`) and `scaleIndent`'s space count all
/// go through HS `round`, and half cases DO occur (e.g. `130/1.5 =
/// 86.66→87`, `1.5*23 = 34.5→34`).
fn round_half_even(x: f64) -> i64 {
    let f = x.floor();
    let diff = x - f;
    if diff > 0.5 {
        f as i64 + 1
    } else if diff < 0.5 {
        f as i64
    } else {
        let fi = f as i64;
        if fi % 2 == 0 {
            fi
        } else {
            fi + 1
        }
    }
}

/// HS `renderBalanced 100 (max 30 . round . (*1.3))` + `scaleIndent`
/// (Dot.hs:357-379), the layout engine for record-row fields: each doc of
/// a row is rendered at a line length PROPORTIONAL to its one-line length
/// (`renderStyle (defaultStyle { lineLength = w })`, i.e. PageMode with
/// ribbon `round (w / 1.5)`), so a lone fact in a row gets width
/// `max 30 (round 130) = 130` (ribbon 87) while four facts share the
/// 100-column budget.  `usedWidths` measure the OneLineMode render
/// (`Doc::one_line_render`), which turns every fill/sep break point into
/// one space.
///
/// `scaleIndent` is applied to the WHOLE rendered string (HS's `line`
/// binding spans the full render): `span isSpace` therefore only rescales
/// whitespace at the very START of the FIRST line — a no-op for every
/// label whose first char is text, exactly as in HS.
fn render_balanced(docs: Vec<Doc>) -> Vec<String> {
    if docs.is_empty() {
        return Vec::new();
    }
    let used: Vec<f64> = docs
        .iter()
        .map(|d| d.one_line_render().chars().count() as f64)
        .collect();
    let total: f64 = used.iter().sum();
    let ratio = 100.0 / total;
    docs.into_iter()
        .zip(used)
        .map(|(d, u)| {
            // conv (ratio * w) with conv = max 30 . round . (*1.3).
            let w = std::cmp::max(30, round_half_even((ratio * u) * 1.3));
            // `renderStyle (defaultStyle { lineLength = w })` keeps
            // ribbonsPerLine = 1.5 → ribbon = round (w / 1.5)
            // (pretty-1.1.3.6 `fullRender`).
            let ribbon = round_half_even(w as f64 / 1.5);
            scale_indent(d.render_with(w as usize, ribbon as usize))
        })
        .collect()
}

/// HS `scaleIndent` (Dot.hs:375-379) — see `render_balanced`.
fn scale_indent(s: String) -> String {
    let leading = s.chars().take_while(|c| c.is_whitespace()).count();
    if leading == 0 {
        return s;
    }
    let rest: String = s.chars().skip(leading).collect();
    let n = round_half_even(1.5 * leading as f64);
    let mut out = String::with_capacity(n as usize + rest.len());
    for _ in 0..n {
        out.push(' ');
    }
    out.push_str(&rest);
    out
}

/// Mirror Haskell `ruleLabelM.isNotDiffAnnotation` (Dot.hs:236-379, see line 341): the action
/// fact equal to the synthetic diff annotation
/// `Fact (ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0) S.empty []`
/// is dropped before rendering. `getRuleNameDiff` (Rule.hs:784-798) prefixes
/// the rule's `getRuleName` with `"Intr"`/`"Proto"` depending on the rule
/// kind. Returns `true` when the fact should be KEPT.
fn is_not_diff_annotation(ru: &RuleACInst, fa: &LNFact) -> bool {
    // `getRuleNameDiff` (Rule.hs:784-798) = `getRuleName` prefixed with
    // `"Intr"`/`"Proto"`; the synthetic fact name is `"Diff" ++` that.
    let rule_name_diff = match &ru.info {
        RuleInfo::Intr(_) => format!("Intr{}", rule_name_string(ru)),
        RuleInfo::Proto(_) => format!("Proto{}", rule_name_string(ru)),
    };
    let diff_fact_name = format!("Diff{}", rule_name_diff);
    let is_diff = matches!(&fa.tag,
        FactTag::Proto(tamarin_theory::fact::Multiplicity::Linear, n, 0)
            if **n == *diff_fact_name)
        && fa.terms.is_empty();
    !is_diff
}

/// Mirror Haskell `ruleLabelM.isAutoSource`/`hasAutoLabel` (Dot.hs:343-354):
/// a fact whose `showFactTag` begins with one of the auto-source label
/// prefixes is an auto-source fact. These labels are linear proto facts, so
/// `showFactTag` reduces to the bare proto name here (no `!` prefix), which
/// `fact_tag_name` returns.
fn is_auto_source(fa: &LNFact) -> bool {
    use tamarin_theory::fact::fact_tag_name;
    let name = fact_tag_name(&fa.tag);
    name.starts_with("AUTO_IN_TERM_")
        || name.starts_with("AUTO_IN_FACT_")
        || name.starts_with("AUTO_OUT_TERM_")
        || name.starts_with("AUTO_OUT_FACT_")
}

/// HS `isIntruderRule ru || isFreshRule ru` (Rule.hs:761-763 / 716-717): the
/// predicate gating `mkNode`'s `CompactBoringNodes` branch (Dot.hs:296-297).
/// True for any intruder rule and for the reserved proto `Fresh` rule.
fn is_intruder_or_fresh(ru: &RuleACInst) -> bool {
    match &ru.info {
        RuleInfo::Intr(_) => true,
        RuleInfo::Proto(p) => p.name == ProtoRuleName::Fresh,
    }
}

/// Build the rule-node label Doc — HS `ruleLabelM` (Dot.hs:330-338):
/// `prettyNodeId v <-> colon <-> text (showDotRuleCaseName ru) <> (if null lbl
/// then mempty else brackets (vcat (punctuate comma lbl)))`. `<->` is
/// space-separated (`#i : name`) but the action bracket is joined with `<>`
/// (NO space before `[`), and the actions stack VERTICALLY (`vcat`,
/// comma-punctuated) when there are several. Actions are filtered exactly
/// as HS (`is_not_diff_annotation`; drop `AUTO_*` only when
/// `goShowAutoSource`).  The caller lays this Doc out via
/// `render_balanced` (HS `asM = renderRow [(Nothing, ruleLabel)]`,
/// Dot.hs:320-322 — a single-doc row, i.e. width 130 / ribbon 87).
fn rule_label_doc(nid: &LVar, ru: &RuleACInst, opts: &GraphOptions) -> Doc {
    let act_docs: Vec<Doc> = ru
        .actions
        .iter()
        .filter(|fa| is_not_diff_annotation(ru, fa))
        .filter(|fa| !opts.show_auto_source || !is_auto_source(fa))
        .map(fact_doc_of)
        .collect();
    // `prettyNodeId v <-> colon <-> text name` — three same-line text
    // tokens joined by single spaces; layout-equivalent to one fused text
    // run of the same width (no break points inside a `<>`/`<+>` chain).
    let header = Doc::text(format!("{} : {}", nid, rule_case_name(ru)));
    if act_docs.is_empty() {
        header
    } else {
        // `brackets (vcat $ punctuate comma lbl)` (Dot.hs:236-379, see line 338).
        header
            .beside(Doc::text("["))
            .beside(pretty_hpj::vcat(pretty_hpj::punctuate(
                Doc::text(","),
                act_docs,
            )))
            .beside(Doc::text("]"))
    }
}

/// Mirror Haskell's `showDotRuleCaseName` for `RuleACInst`
/// (Theory/Model/Rule.hs:1220-1222 via `prettyDotProtoRuleName`,
/// Rule.hs:1169-1185).
fn rule_case_name(ru: &RuleACInst) -> String {
    match &ru.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => {
                if p.attributes.is_sapic_rule {
                    if s.starts_with("new") {
                        // chr 957 (ν) : ' ' : drop 3 (trimSapicName s)
                        let trimmed = trim_sapic_name(s);
                        let dropped: String = trimmed.chars().skip(3).collect();
                        format!("\u{3bd} {}", dropped)
                    } else {
                        trim_sapic_name(s)
                    }
                } else {
                    prefix_if_reserved(s)
                }
            }
            ProtoRuleName::Fresh => "Fresh".to_string(),
        },
        RuleInfo::Intr(i) => intr_case_name(i),
    }
}

/// Mirror Haskell `trimSapicName` (Theory/Model/Rule.hs:1175-1185): strips a
/// trailing `_<digits>_<digits>` suffix from a SAPiC rule name.
fn trim_sapic_name(name: &str) -> String {
    // splitString: reverse (splitOn "_" name); if >= 3 parts, the prefix is
    // intercalate "_" (reverse (drop 2 parts)), and the last two parts are
    // parts[1] (n) and parts[0] (m).
    let parts: Vec<&str> = name.split('_').collect();
    if parts.len() >= 3 {
        let m = parts[parts.len() - 1];
        let n = parts[parts.len() - 2];
        // Haskell `all isDigit s` is True for the empty string too.
        let all_digits = |s: &str| s.chars().all(|c| c.is_ascii_digit());
        if all_digits(n) && all_digits(m) {
            return parts[..parts.len() - 2].join("_");
        }
    }
    name.to_string()
}

fn intr_case_name(i: &IntrRuleACInfo) -> String {
    // Mirror Haskell `prettyIntrRuleACInfo` (Theory/Model/Rule.hs:1225-1234).
    // Note: ConstrRule/DestrRule names already carry a leading `_` (e.g.
    // `_exp`), so the Haskell `'c' : name` yields e.g. `c_exp` (a single
    // underscore), then `prefixIfReserved` is applied.
    match i {
        IntrRuleACInfo::IRecv => "irecv".into(),
        IntrRuleACInfo::ISend => "isend".into(),
        IntrRuleACInfo::Coerce => "coerce".into(),
        IntrRuleACInfo::FreshConstr => "fresh".into(),
        IntrRuleACInfo::PubConstr => "pub".into(),
        IntrRuleACInfo::NatConstr => "nat".into(),
        IntrRuleACInfo::IEquality => "iequality".into(),
        IntrRuleACInfo::ConstrRule { name, .. } => {
            prefix_if_reserved(&format!("c{}", String::from_utf8_lossy(name)))
        }
        IntrRuleACInfo::DestrRule { name, .. } => {
            prefix_if_reserved(&format!("d{}", String::from_utf8_lossy(name)))
        }
    }
}

/// Mirror Haskell `prefixIfReserved` (Theory/Model/Rule.hs:1154-1162):
/// prefixes with `_` if the name is reserved or already starts with `_`.
fn prefix_if_reserved(n: &str) -> String {
    use tamarin_theory::rule::reserved_rule_names;
    if reserved_rule_names().contains(n) || n.starts_with('_') {
        format!("_{}", n)
    } else {
        n.to_string()
    }
}

/// HS `ruleColor'` (Dot.hs:248-253): `rgbToHex` of the proto rule's explicit
/// `color:` attribute, if any. `None` for intruder rules / no attribute.
fn explicit_rule_color(ru: &RuleACInst) -> Option<String> {
    if let RuleInfo::Proto(p) = &ru.info {
        if let Some(rgb) = p.attributes.color {
            return Some(tamarin_utils::color::rgb_to_hex(rgb));
        }
    }
    None
}

/// Pick a rule node's fill colour with HS `dotNodeCompact`'s priority
/// (Dot.hs:248-256): `fromMaybe (maybe "white" rgbToHex color)
/// (ruleColor' <|> manualNodeColor)` — the explicit `color:` attribute wins,
/// then the cluster's `manualNodeColor`, then the `nodeColorMap` palette
/// fallback (`maybe "white" rgbToHex (M.lookup rInfo colorMap)`): a node
/// present in the map yields its palette hex, an absent one yields `"white"`.
fn rule_fillcolor(
    ru: &RuleACInst,
    nid: &LVar,
    manual_color: Option<&str>,
    color_map: &NodeColorMap,
) -> String {
    explicit_rule_color(ru)
        .or_else(|| manual_color.map(|c| c.to_string()))
        .unwrap_or_else(|| match color_map.lookup_node(nid) {
            Some(rgb) => tamarin_utils::color::rgb_to_hex(rgb),
            None => "white".to_string(),
        })
}

/// HS `dotNodeCompact.colorUsesWhiteFont` (Dot.hs:284-287): a node uses a white
/// font iff it HAS a palette colour and that colour is "dark" in apparent
/// (linear) luminance, `0.2126 r + 0.7152 g + 0.0722 b < 0.5`. An absent colour
/// (`None`) ⇒ black font. Keyed off the palette colour (`M.lookup rInfo
/// colorMap`), not the resolved fill.
fn color_uses_white_font(color: Option<tamarin_utils::color::Rgb>) -> bool {
    match color {
        Some(c) => 0.2126 * c.r + 0.7152 * c.g + 0.0722 * c.b < 0.5,
        None => false,
    }
}

/// Whether a node exposes Graphviz record ports (`:c<i>` / `:p<i>`).
/// HS `mkNode` (Dot.hs:294-312) only renders a record — with ports — for a
/// non-compact System node; a COMPACT node (intruder/`Fresh` under
/// `CompactBoringNodes`) and every non-System ellipse (missing / action / last)
/// map ALL their prem/conc keys to the bare node id (no port, Dot.hs:303-304).
/// `node_map` holds only System nodes, so an id absent from it is a non-System
/// ellipse (portless); a present intruder/`Fresh` rule is a compact ellipse.
fn node_has_ports(node_map: &HashMap<&LVar, &RuleACInst>, nid: &LVar) -> bool {
    node_map
        .get(nid)
        .is_some_and(|ru| !is_intruder_or_fresh(ru))
}

/// Render an edge's conclusion endpoint: `id:c<i>` for a record node, else the
/// bare `id` (compact/simple node — HS emits no port there).
fn conc_port_ref(
    node_map: &HashMap<&LVar, &RuleACInst>,
    nc: &tamarin_theory::constraint::constraints::NodeConc,
) -> String {
    let id = DotBuilder::dot_node_id(&nc.0);
    if node_has_ports(node_map, &nc.0) {
        format!("{}:c{}", id, nc.1 .0)
    } else {
        id
    }
}

/// Render an edge's premise endpoint: `id:p<i>` for a record node, else the
/// bare `id` (compact/simple node — HS emits no port there).
fn prem_port_ref(
    node_map: &HashMap<&LVar, &RuleACInst>,
    np: &tamarin_theory::constraint::constraints::NodePrem,
) -> String {
    let id = DotBuilder::dot_node_id(&np.0);
    if node_has_ports(node_map, &np.0) {
        format!("{}:p{}", id, np.1 .0)
    } else {
        id
    }
}

/// `dotEdge`'s `SystemEdge` arm (Dot.hs:386-399).
///
/// `orig_node_map` indexes the ORIGINAL system: `check p` resolves both
/// endpoints through `resolveNodePremFact`/`resolveNodeConcFact` **on the
/// `Graph`** (Dot.hs:391-392), and those read `_gSystem` (Graph.hs:87-96) —
/// the un-compressed, un-simplified system, not the copy the drawn nodes and
/// their record ports come from.
fn edge_style(
    orig_node_map: &OrigNodeRules<'_>,
    src: &tamarin_theory::constraint::constraints::NodeConc,
    tgt: &tamarin_theory::constraint::constraints::NodePrem,
) -> String {
    // Look up tag of the source-conclusion or target-premise.
    let conc_tag = lookup_conc_tag(orig_node_map, src);
    let prem_tag = lookup_prem_tag(orig_node_map, tgt);
    let is_proto = |t: Option<&FactTag>| -> bool { matches!(t, Some(FactTag::Proto(_, _, _))) };
    // HS `isPersistentFact` (Fact.hs:379-380) reads the tag's multiplicity, and
    // HS `factTagMultiplicity` (Fact.hs:383-388) makes `KUFact`/`KDFact`
    // persistent alongside `ProtoFact Persistent _ _`.  Only the proto arm can
    // fire below: the branch is gated on `check isProtoFact`, and both endpoints
    // of an `Edge` carry the same tag because HS `insertEdges`
    // (Reduction.hs:281-284) unifies the two facts through `solveFactEqs`, whose
    // first act is `contradictoryIf` on unequal tags (Reduction.hs:766-769).
    let is_persistent = |t: Option<&FactTag>| -> bool {
        t.is_some_and(|tag| {
            tamarin_theory::fact::fact_tag_multiplicity(tag)
                == tamarin_theory::fact::Multiplicity::Persistent
        })
    };
    let is_k = |t: Option<&FactTag>| -> bool { matches!(t, Some(FactTag::Ku) | Some(FactTag::Kd)) };
    if is_proto(conc_tag.as_ref()) || is_proto(prem_tag.as_ref()) {
        let mut s = String::from("style=\"bold\",weight=10");
        if is_persistent(conc_tag.as_ref()) || is_persistent(prem_tag.as_ref()) {
            s.push_str(",color=\"gray50\"");
        }
        s
    } else if is_k(conc_tag.as_ref()) || is_k(prem_tag.as_ref()) {
        "color=\"orangered2\"".to_string()
    } else {
        "color=\"gray30\"".to_string()
    }
}

/// HS `resolveNodeConcFact` (System.hs:930-931) reached through Graph.hs:93-96,
/// keeping only the tag `dotEdge`'s predicates test.
fn lookup_conc_tag(
    orig_node_map: &OrigNodeRules<'_>,
    nc: &tamarin_theory::constraint::constraints::NodeConc,
) -> Option<FactTag> {
    let (nid, idx) = nc;
    let ru = orig_node_map.get(nid)?;
    ru.conclusions.get(idx.0).map(|fa| fa.tag)
}

/// HS `resolveNodePremFact` (System.hs:926-927) reached through Graph.hs:87-90,
/// keeping only the tag `dotEdge`'s predicates test.
fn lookup_prem_tag(
    orig_node_map: &OrigNodeRules<'_>,
    np: &tamarin_theory::constraint::constraints::NodePrem,
) -> Option<FactTag> {
    let (nid, idx) = np;
    let ru = orig_node_map.get(nid)?;
    ru.premises.get(idx.0).map(|fa| fa.tag)
}

/// Port of Haskell `roleColor` (Dot.hs:534-544): a deterministic per-role
/// `#RRGGBBAA` colour. `simpleHash name = foldl (\acc c -> acc*31 + ord c) 7`
/// over the role's base name (Haskell `Int`, i.e. 64-bit two's-complement
/// wrapping), `generateValue = (hash `mod` 360) / 360` (Haskell `mod` is
/// non-negative for a positive divisor — `rem_euclid` here), then
/// `hsvToRGB (HSV (v*360) 0.75 0.85)` with each channel `floor(f*255)` and a
/// fixed alpha `floor(255*0.3) = 76`. Hex digits are UPPERCASE (`%02X`), and
/// the channel scale is `*255` (not `*256` as in `rgb_to_hex`), so this does
/// not reuse `rgb_to_hex`.
fn role_color(name: &str) -> String {
    // simpleHash: `Int` arithmetic, wraps on overflow.
    let hash: i64 = name
        .chars()
        .fold(7i64, |acc, c| acc.wrapping_mul(31).wrapping_add(c as i64));
    let v = (hash.rem_euclid(360)) as f64 / 360.0;
    let rgb =
        tamarin_utils::color::hsv_to_rgb(tamarin_utils::color::Hsv::new(v * 360.0, 0.75, 0.85));
    let chan = |f: f64| -> i64 { (f * 255.0).floor() as i64 };
    let alpha: i64 = (255.0 * 0.3_f64).floor() as i64; // = 76
    format!(
        "#{:02X}{:02X}{:02X}{:02X}",
        chan(rgb.r),
        chan(rgb.g),
        chan(rgb.b),
        alpha
    )
}

/// Escape a record FIELD's text, mirroring HS `Text.Dot.renderRecord`'s
/// `escape` (Text/Dot.hs:273-280): exactly the record metacharacters
/// `| { } < >` get a backslash — NOT `"` / `\` / newline, which are handled
/// once at the attribute level by `showAttr` (see `escape_dot_label`).
fn escape_record_field(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '|' => out.push_str("\\|"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            '<' => out.push_str("\\<"),
            '>' => out.push_str("\\>"),
            _ => out.push(c),
        }
    }
    out
}

/// Escape a Graphviz attribute VALUE, mirroring HS `Text.Dot.showAttr`
/// (Text/Dot.hs:346-353): only `"` (→ `\"`) and newline (→ `\l`, graphviz's
/// left-justified line break) are escaped.  This is the LAST escaping pass
/// for every label — plain ellipse labels (where record metacharacters
/// `{ } | < >` must stay literal) and record labels (whose field text was
/// already record-escaped by `escape_record_field`) alike.
fn escape_dot_label(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\l"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
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
    fn proto_node(
        name: &str,
        prems: Vec<LNFact>,
        acts: Vec<LNFact>,
        concs: Vec<LNFact>,
    ) -> RuleACInst {
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
        ProtoRuleACInstInfo, ProtoRuleName as PRN, Rule as TRule, RuleAttributes,
        RuleInfo as TRuleInfo,
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
}
