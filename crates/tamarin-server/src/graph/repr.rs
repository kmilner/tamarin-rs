// Currently GPL 3.0 until granted permission by the following authors:
//   addap, Mathias-AURAND, meiersi, rkunnema, sans-sucre, yavivanov,
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Constraint/System/Dot.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Graph.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/utils/src/Text/Dot.hs

//! Port of `Theory.Constraint.System.Graph.GraphRepr` —
//! intermediate representation of a `System` as nodes/edges/clusters
//! that can be rendered to DOT/JSON.
//!
//! See `lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs`.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_theory::constraint::constraints::{LessAtom, NodeConc, NodeId, NodePrem};
use tamarin_theory::fact::LNFact;
use tamarin_theory::rule::{ConcIdx, PremIdx, ProtoRuleName, RuleACInst, RuleInfo};

/// Mirrors Haskell `NodeType` from `GraphRepr.hs:58-63`.
#[derive(Debug, Clone, PartialEq)]
pub enum NodeType {
    /// Node corresponding to a `RuleACInst` from `sNodes`.
    System(RuleACInst),
    /// Unsolved adversary-knowledge action (KU goals at fresh ids).
    UnsolvedAction(Vec<LNFact>),
    /// Last-action atom (induction).
    LastAction,
    /// Referenced by an edge but absent from `sNodes`.
    Missing(MissingHint),
}

/// Mirror of `Either ConcIdx PremIdx` in Haskell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MissingHint {
    Conc(ConcIdx),
    Prem(PremIdx),
}

/// Mirror of `Node` from `GraphRepr.hs:51-55`.
#[derive(Debug, Clone, PartialEq)]
pub struct GNode {
    pub id: NodeId,
    pub ty: NodeType,
}

/// Mirror of `Edge` from `GraphRepr.hs:67-71`.
#[derive(Debug, Clone, PartialEq)]
pub enum GEdge {
    System(NodeConc, NodePrem),
    Less(LessAtom),
    UnsolvedChain(NodeConc, NodePrem),
}

/// Mirror of `Cluster` from `GraphRepr.hs:74-79`.
#[derive(Debug, Clone, PartialEq)]
pub struct Cluster {
    pub name: String,
    pub nodes: Vec<GNode>,
    pub edges: Vec<GEdge>,
}

/// Mirror of `GraphRepr` from `GraphRepr.hs:82-87`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct GraphRepr {
    pub clusters: Vec<Cluster>,
    pub nodes: Vec<GNode>,
    pub edges: Vec<GEdge>,
}

impl GraphRepr {
    pub fn new() -> Self {
        GraphRepr::default()
    }
}

// ---------------------------------------------------------------------
// Cluster construction
// ---------------------------------------------------------------------

/// Return the `role` attribute of a `RuleACInst`, if any.
/// Mirror of `extractRole` from `GraphRepr.hs:136-137`.
pub fn extract_role(ru: &RuleACInst) -> Option<&str> {
    match &ru.info {
        RuleInfo::Proto(p) => p.attributes.role.as_deref(),
        _ => None,
    }
}

/// Return a node's role, if it's a `SystemNode` with a `role`
/// attribute.  Mirror of `getNodeRole`.
pub fn node_role(n: &GNode) -> Option<&str> {
    match &n.ty {
        NodeType::System(ru) => extract_role(ru),
        _ => None,
    }
}

/// Group nodes by role.  Mirror of `groupNodesByRole`.
pub fn group_nodes_by_role<'a>(nodes: &'a [GNode]) -> BTreeMap<String, Vec<&'a GNode>> {
    let mut by_role: BTreeMap<String, Vec<&'a GNode>> = BTreeMap::new();
    for n in nodes {
        if let Some(r) = node_role(n) {
            by_role.entry(r.to_string()).or_default().push(n);
        }
    }
    by_role
}

/// `extractBaseName name` returns `Just base` when `name = base_<digits>`.
/// Mirror of `extractBaseName` (GraphRepr.hs:217-225).
pub fn extract_base_name(name: &str) -> Option<String> {
    let parts: Vec<&str> = name.split('_').collect();
    if parts.len() < 2 {
        return None;
    }
    let last = parts.last().unwrap();
    if !last.is_empty() && last.chars().all(|c| c.is_ascii_digit()) {
        Some(parts[..parts.len() - 1].join("_"))
    } else {
        None
    }
}

/// Return the rule's case-name (e.g. `Setup_1`) for proto-rules, else None.
/// Mirror of `getRuleNameByNode` (GraphRepr.hs:208-214) which renders
/// `showRuleCaseName` -> `prettyProtoRuleName` (Rule.hs:1164-1167):
/// `StandRule n -> prefixIfReserved n`, `FreshRule -> "Fresh"`.
/// `prefixIfReserved` (Rule.hs:1154-1162) prepends `_` when the name is a
/// reserved rule name or already starts with `_`.  This is plain
/// `showRuleCaseName`, NOT the SAPiC-trimming `showDotRuleCaseName`.
pub fn rule_name_by_node(n: &GNode) -> Option<String> {
    if let NodeType::System(ru) = &n.ty {
        if let RuleInfo::Proto(p) = &ru.info {
            return Some(match &p.name {
                ProtoRuleName::Stand(s) => {
                    let reserved = tamarin_theory::rule::reserved_rule_names();
                    if reserved.contains(s) || s.starts_with('_') {
                        format!("_{s}")
                    } else {
                        s.to_string()
                    }
                }
                ProtoRuleName::Fresh => "Fresh".to_string(),
            });
        }
    }
    None
}

/// Mirror of `groupBySimilarName` — group nodes by their rule's base name.
pub fn group_by_similar_name<'a>(nodes: &'a [GNode]) -> BTreeMap<String, Vec<&'a GNode>> {
    let mut out: BTreeMap<String, Vec<&'a GNode>> = BTreeMap::new();
    for n in nodes {
        if let Some(rn) = rule_name_by_node(n) {
            if let Some(base) = extract_base_name(&rn) {
                out.entry(base).or_default().push(n);
            }
        }
    }
    out
}

/// Filter edges keeping only those whose endpoints are both in `node_ids`.
/// Mirror of `filterEdgesForCluster`.
pub fn filter_edges_for_cluster(node_ids: &BTreeSet<NodeId>, edges: &[GEdge]) -> Vec<GEdge> {
    edges
        .iter()
        .filter(|e| match e {
            GEdge::System(s, t) | GEdge::UnsolvedChain(s, t) => {
                node_ids.contains(&s.0) && node_ids.contains(&t.0)
            }
            GEdge::Less(la) => node_ids.contains(&la.smaller) && node_ids.contains(&la.larger),
        })
        .cloned()
        .collect()
}

/// Group `nodes` into weakly-connected components under the projection
/// from `edges`.  Mirror of `findConnectedComponents`.
pub fn find_connected_components<'a>(
    nodes: &'a [&'a GNode],
    edges: &[GEdge],
) -> Vec<Vec<&'a GNode>> {
    // Build undirected adjacency.  Mirror of `expandCluster`, which walks
    // ONLY `SystemEdge`s for connectivity — `LessEdge`/`UnsolvedChain`
    // edges are not matched and so never join two nodes into one component.
    let mut adj: BTreeMap<NodeId, BTreeSet<NodeId>> = BTreeMap::new();
    for e in edges {
        if let GEdge::System(s, t) = e {
            let (a, b) = (s.0.clone(), t.0.clone());
            adj.entry(a.clone()).or_default().insert(b.clone());
            adj.entry(b).or_default().insert(a);
        }
    }
    let mut visited: BTreeSet<NodeId> = BTreeSet::new();
    let mut components: Vec<Vec<&'a GNode>> = Vec::new();
    let by_id: BTreeSet<NodeId> = nodes.iter().map(|n| n.id.clone()).collect();
    for n in nodes {
        if visited.contains(&n.id) {
            continue;
        }
        let mut stack = vec![n.id.clone()];
        let mut comp_set: BTreeSet<NodeId> = BTreeSet::new();
        while let Some(cur) = stack.pop() {
            if !visited.insert(cur.clone()) {
                continue;
            }
            comp_set.insert(cur.clone());
            if let Some(neighbors) = adj.get(&cur) {
                for nb in neighbors {
                    if !visited.contains(nb) && by_id.contains(nb) {
                        stack.push(nb.clone());
                    }
                }
            }
        }
        // HS `component = filter (\node -> get nNodeId node `elem` componentIds)
        // (n:ns)` (GraphRepr.hs:170-192, see line 190): component nodes are kept in the ORIGINAL
        // `nodes` order, not DFS discovery order.  Filtering the full `nodes`
        // slice is safe because each node belongs to exactly one component
        // (globally `visited`), so the per-component relative order matches HS.
        let comp: Vec<&'a GNode> = nodes
            .iter()
            .copied()
            .filter(|n| comp_set.contains(&n.id))
            .collect();
        if !comp.is_empty() {
            components.push(comp);
        }
    }
    // Haskell `go (n:ns) components = go remainingNodes (component : components)`
    // PREPENDS each newly-discovered component, so the returned list is in
    // reverse-discovery order.  We discover in the same node order but append,
    // so reverse here to match before downstream `zipWith [1..]` numbering.
    components.reverse();
    components
}

/// Generic `addCluster` from `GraphRepr.hs:117-130`.  Given a grouping
/// of nodes (one group per cluster), it:
///   1. computes connected components within each group,
///   2. emits one cluster per component named `<group><suffix><N>`,
///   3. removes those nodes and the intra-cluster edges from the
///      top-level `GraphRepr` fields,
///   4. leaves cross-cluster + non-clustered nodes/edges in place.
pub fn add_cluster(
    repr: &mut GraphRepr,
    nodes_by_group: BTreeMap<String, Vec<&GNode>>,
    name_suffix: &str,
) {
    let all_edges = repr.edges.clone();
    let mut sub_clusters: Vec<Cluster> = Vec::new();
    for (group_name, group_nodes) in &nodes_by_group {
        let group_node_ids: BTreeSet<NodeId> = group_nodes.iter().map(|n| n.id.clone()).collect();
        let edges_for_group = filter_edges_for_cluster(&group_node_ids, &all_edges);
        let components = find_connected_components(group_nodes, &edges_for_group);
        for (i, comp) in components.into_iter().enumerate() {
            let comp_ids: BTreeSet<NodeId> = comp.iter().map(|n| n.id.clone()).collect();
            let edges_in_comp = filter_edges_for_cluster(&comp_ids, &all_edges);
            sub_clusters.push(Cluster {
                name: format!("{}{}{}", group_name, name_suffix, i + 1),
                nodes: comp.into_iter().cloned().collect(),
                edges: edges_in_comp,
            });
        }
    }
    // Collect all the edges and nodes absorbed by sub_clusters.
    // The cloned cluster edges live at different addresses than the
    // elements of `all_edges`, so absorbed edges must be filtered by
    // structural equality (not pointer identity).
    //
    // Nodes too must be removed by STRUCTURAL equality, mirroring HS
    // `remainingNodes = filter (`notElem` clusteredNodes) grNodes`
    // (GraphRepr.hs:117-130, see line 127): a node id can appear TWICE in `grNodes` with
    // different types — e.g. the last-atom id is pushed both as a
    // `SystemNode` and as a free `LastAction` ellipse (see
    // `compute_basic_graph_repr`).  When the SystemNode is clustered,
    // an id-keyed filter would silently drop the free ellipse as well;
    // HS keeps it at top level (it is not an element of the cluster).
    let absorbed_nodes: Vec<GNode> = sub_clusters
        .iter()
        .flat_map(|c| c.nodes.iter().cloned())
        .collect();
    let absorbed_edges_struct: Vec<GEdge> = sub_clusters
        .iter()
        .flat_map(|c| c.edges.iter().cloned())
        .collect();
    let remaining_edges: Vec<GEdge> = all_edges
        .into_iter()
        .filter(|e| !absorbed_edges_struct.iter().any(|ae| ae == e))
        .collect();
    let remaining_nodes: Vec<GNode> = repr
        .nodes
        .iter()
        .filter(|n| !absorbed_nodes.iter().any(|an| an == *n))
        .cloned()
        .collect();
    repr.clusters = sub_clusters;
    repr.edges = remaining_edges;
    repr.nodes = remaining_nodes;
}

/// Mirror of `addClusterByRole` — wrap `add_cluster` over role groupings.
pub fn add_cluster_by_role(repr: &mut GraphRepr) {
    // Clone nodes from `repr` so the grouping borrows from owned data
    // and doesn't alias `repr`'s nodes field.
    let nodes_owned: Vec<GNode> = repr.nodes.clone();
    let groups: BTreeMap<String, Vec<&GNode>> = group_nodes_by_role(&nodes_owned);
    add_cluster(repr, groups, "_Session_");
}

/// Mirror of `addIntelligentClusterUsingSimilarNames`.
pub fn add_intelligent_cluster_using_similar_names(repr: &mut GraphRepr) {
    let nodes_owned: Vec<GNode> = repr.nodes.clone();
    let groups: BTreeMap<String, Vec<&GNode>> = group_by_similar_name(&nodes_owned);
    add_cluster(repr, groups, "_Session_");
}

// ---------------------------------------------------------------------
// Building a basic repr from a System
// ---------------------------------------------------------------------

use tamarin_theory::constraint::constraints::Goal;
use tamarin_theory::constraint::system::System;

/// Port of `computeBasicGraphRepr` from `Graph.hs:140-150`.
/// Collects from a `System`:
///   - rule nodes,
///   - unsolved-action atoms (KU goals etc.),
///   - the optional last-atom node,
///   - missing nodes referenced by edges.
pub fn compute_basic_graph_repr(sys: &System) -> GraphRepr {
    let mut nodes: Vec<GNode> = Vec::new();
    // 1. System rule instances.
    for (nid, ru) in sys.nodes.iter() {
        nodes.push(GNode {
            id: nid.clone(),
            ty: NodeType::System(ru.clone()),
        });
    }
    // 2. Unsolved action atoms — collect by node id.
    // HS `systemUnsolvedActionNodes se = map unsolvedActionNode
    // (collectBy $ unsolvedActionAtoms se)` (Graph.hs:105-108) does NOT filter
    // these ids against `sNodes`: if an id is both a system node and an
    // unsolved ActionG goal, HS emits BOTH a SystemNode and an
    // UnsolvedActionNode.  So there is no skip-if-already-a-system-node guard.
    let mut by_node: BTreeMap<NodeId, Vec<LNFact>> = BTreeMap::new();
    for (g, st) in sys.goals.iter() {
        if st.solved {
            continue;
        }
        if let Goal::Action(nid, fa) = g {
            by_node.entry(nid.clone()).or_default().push(fa.clone());
        }
    }
    for (nid, facts) in by_node {
        nodes.push(GNode {
            id: nid.clone(),
            ty: NodeType::UnsolvedAction(facts),
        });
    }
    // 3. Last-atom node.
    // HS `systemLastActionNode se = maybe [] (\nid -> [Node nid LastActionAtom])
    // (get Sys.sLastAtom se)` (Graph.hs:111-112) appends this UNCONDITIONALLY
    // whenever `sLastAtom` is set — it does NOT skip when the id coincides with
    // a system/unsolved node.  `cacheState` (Dot.hs:108) re-runs each node's
    // `dot` action and overwrites `dsNodes[v]`, so both the SystemNode record
    // AND the bare `#i` last-atom ellipse are emitted at the same id (the
    // ellipse ends up as `dsNodes[v]`, which drives less-edge resolution).  The
    // colliding dot-id is disambiguated in `dot.rs`.
    if let Some(la) = &sys.last_atom {
        nodes.push(GNode {
            id: la.clone(),
            ty: NodeType::LastAction,
        });
    }
    // 4. Missing nodes referenced by edges.
    // HS `systemMissingNodes se = mapMaybe missingNode (S.toList sEdges)`
    // (Graph.hs:116-122): each edge yields AT MOST ONE missing node — `missingNode`
    // checks the source first (`MissingNode (Left idx)`), and only if the source
    // is present does it check the target (`MissingNode (Right idx)`).  The
    // membership test is `nid `notElem` nodelist` where `nodelist = map fst
    // (M.toList sNodes)` — i.e. against `sNodes` ONLY, never against
    // unsolved-action / last-atom ids.  There is also NO dedup among missing
    // nodes: two edges sharing the same missing endpoint emit it twice.
    // `systemMissingNodes` never inspects `sLessAtoms`; less-atoms contribute
    // edges (below), not nodes.
    let sys_node_ids: BTreeSet<NodeId> = sys.nodes.iter().map(|(id, _)| id.clone()).collect();
    for e in &sys.edges {
        if !sys_node_ids.contains(&e.src.0) {
            nodes.push(GNode {
                id: e.src.0.clone(),
                ty: NodeType::Missing(MissingHint::Conc(e.src.1)),
            });
        } else if !sys_node_ids.contains(&e.tgt.0) {
            nodes.push(GNode {
                id: e.tgt.0.clone(),
                ty: NodeType::Missing(MissingHint::Prem(e.tgt.1)),
            });
        }
    }
    // 5. Edges.
    let mut edges: Vec<GEdge> = Vec::new();
    for e in &sys.edges {
        edges.push(GEdge::System(e.src.clone(), e.tgt.clone()));
    }
    for la in &sys.less_atoms {
        edges.push(GEdge::Less(la.clone()));
    }
    for (g, st) in sys.goals.iter() {
        if st.solved {
            continue;
        }
        if let Goal::Chain(src, tgt) = g {
            edges.push(GEdge::UnsolvedChain(src.clone(), tgt.clone()));
        }
    }
    GraphRepr {
        clusters: Vec::new(),
        nodes,
        edges,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_theory::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};

    fn proto_rule(name: &str, role: Option<&str>) -> RuleACInst {
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
            Vec::new(),
            Vec::new(),
        )
    }

    fn nid(name: &str, idx: u64) -> NodeId {
        LVar::new(name, LSort::Node, idx)
    }

    #[test]
    fn extract_base_name_drops_numeric_suffix() {
        assert_eq!(extract_base_name("Setup_1"), Some("Setup".to_string()));
        assert_eq!(
            extract_base_name("Long_Name_3"),
            Some("Long_Name".to_string())
        );
        assert_eq!(extract_base_name("NoSuffix"), None);
        assert_eq!(extract_base_name("Name_NotNumber"), None);
        assert_eq!(extract_base_name(""), None);
    }

    #[test]
    fn cluster_by_role_partitions_nodes() {
        let mut repr = GraphRepr::new();
        repr.nodes.push(GNode {
            id: nid("i", 1),
            ty: NodeType::System(proto_rule("Init", Some("Alice"))),
        });
        repr.nodes.push(GNode {
            id: nid("i", 2),
            ty: NodeType::System(proto_rule("Respond", Some("Bob"))),
        });
        repr.nodes.push(GNode {
            id: nid("i", 3),
            ty: NodeType::System(proto_rule("Init2", Some("Alice"))),
        });
        // No role -> stays at top level
        repr.nodes.push(GNode {
            id: nid("i", 4),
            ty: NodeType::System(proto_rule("Setup", None)),
        });
        add_cluster_by_role(&mut repr);
        // 2 Alice nodes with no connecting edge => 2 separate
        // Alice clusters; 1 Bob => 1 Bob cluster; the roleless node
        // stays at the top level.
        assert_eq!(repr.clusters.len(), 3);
        let cluster_names: Vec<&str> = repr.clusters.iter().map(|c| c.name.as_str()).collect();
        let alice_count = cluster_names
            .iter()
            .filter(|n| n.starts_with("Alice"))
            .count();
        assert_eq!(alice_count, 2);
        assert!(cluster_names.iter().any(|n| n.starts_with("Bob")));
        // The roleless node stays in repr.nodes.
        assert_eq!(repr.nodes.len(), 1);
    }

    #[test]
    fn cluster_by_role_keeps_connected_alice_together() {
        let mut repr = GraphRepr::new();
        repr.nodes.push(GNode {
            id: nid("i", 1),
            ty: NodeType::System(proto_rule("Init", Some("Alice"))),
        });
        repr.nodes.push(GNode {
            id: nid("i", 3),
            ty: NodeType::System(proto_rule("Init2", Some("Alice"))),
        });
        // Edge connecting the two Alice nodes via a SystemEdge
        repr.edges.push(GEdge::System(
            (nid("i", 1), ConcIdx(0)),
            (nid("i", 3), PremIdx(0)),
        ));
        add_cluster_by_role(&mut repr);
        // One Alice cluster containing both nodes.
        assert_eq!(repr.clusters.len(), 1);
        assert_eq!(repr.clusters[0].nodes.len(), 2);
        assert_eq!(repr.clusters[0].edges.len(), 1);
    }

    // HS `findConnectedComponents` keeps each component's nodes in the
    // ORIGINAL input order (`filter (∈ componentIds) (n:ns)`), not in DFS
    // discovery order.  With input [B, C, A] where A links to both B and C,
    // DFS pop-order would be [B, A, C]; HS keeps [B, C, A].
    #[test]
    fn connected_components_preserve_original_node_order() {
        let b = GNode {
            id: nid("i", 2),
            ty: NodeType::System(proto_rule("B", None)),
        };
        let c = GNode {
            id: nid("i", 3),
            ty: NodeType::System(proto_rule("C", None)),
        };
        let a = GNode {
            id: nid("i", 1),
            ty: NodeType::System(proto_rule("A", None)),
        };
        // Input order is deliberately [B, C, A].
        let input: Vec<&GNode> = vec![&b, &c, &a];
        // A links to both B and C via SystemEdges.
        let edges = vec![
            GEdge::System((nid("i", 1), ConcIdx(0)), (nid("i", 2), PremIdx(0))),
            GEdge::System((nid("i", 1), ConcIdx(0)), (nid("i", 3), PremIdx(0))),
        ];
        let comps = find_connected_components(&input, &edges);
        assert_eq!(comps.len(), 1);
        let ids: Vec<NodeId> = comps[0].iter().map(|n| n.id.clone()).collect();
        // Original order [B, C, A], NOT DFS order [B, A, C].
        assert_eq!(ids, vec![nid("i", 2), nid("i", 3), nid("i", 1)]);
    }

    // HS `getRuleNameByNode` -> `showRuleCaseName` -> `prettyProtoRuleName`
    // applies `prefixIfReserved` to StandRule names.  A name already starting
    // with `_` gets another `_` prepended, so `_Foo_1` -> `__Foo_1`, and
    // `extractBaseName "__Foo_1"` (splitOn "_" = ["","","Foo","1"]) -> `__Foo`.
    #[test]
    fn rule_name_by_node_applies_prefix_if_reserved() {
        let n = GNode {
            id: nid("i", 1),
            ty: NodeType::System(proto_rule("_Foo_1", None)),
        };
        assert_eq!(rule_name_by_node(&n), Some("__Foo_1".to_string()));
        // Reserved name `pub` -> `_pub`.
        let p = GNode {
            id: nid("i", 2),
            ty: NodeType::System(proto_rule("pub", None)),
        };
        assert_eq!(rule_name_by_node(&p), Some("_pub".to_string()));
        // Ordinary name is unchanged.
        let s = GNode {
            id: nid("i", 3),
            ty: NodeType::System(proto_rule("Setup", None)),
        };
        assert_eq!(rule_name_by_node(&s), Some("Setup".to_string()));
        // The composed base name for `_Foo_1` is `__Foo` (HS), not `_Foo`.
        assert_eq!(
            rule_name_by_node(&n).and_then(|rn| extract_base_name(&rn)),
            Some("__Foo".to_string())
        );
    }
}
