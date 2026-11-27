// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.System.Graph.GraphRepr` —
//! intermediate representation of a `System` as nodes/edges/clusters
//! that can be rendered to DOT/JSON.
//!
//! See `lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs`.

use std::collections::{BTreeMap, BTreeSet};

use crate::constraint::constraints::{LessAtom, NodeConc, NodeId, NodePrem};
use crate::fact::LNFact;
use crate::rule::{ConcIdx, PremIdx, ProtoRuleName, RuleACInst, RuleInfo};

/// Mirrors Haskell `NodeType` from `GraphRepr.hs`.
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

/// Mirror of `Node` from `GraphRepr.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct GNode {
    pub id: NodeId,
    pub ty: NodeType,
}

/// Mirror of `Edge` from `GraphRepr.hs`.
#[derive(Debug, Clone, PartialEq)]
pub enum GEdge {
    System(NodeConc, NodePrem),
    Less(LessAtom),
    UnsolvedChain(NodeConc, NodePrem),
}

/// Mirror of `Cluster` from `GraphRepr.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct Cluster {
    pub name: String,
    pub nodes: Vec<GNode>,
    pub edges: Vec<GEdge>,
}

/// Mirror of `GraphRepr` from `GraphRepr.hs`.
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
/// Mirror of `extractRole` from `GraphRepr.hs`.
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
/// Mirror of `extractBaseName` (GraphRepr.hs).
pub fn extract_base_name(name: &str) -> Option<String> {
    let parts: Vec<&str> = name.split('_').collect();
    if parts.len() < 2 {
        return None;
    }
    // Haskell `all isDigit s` is True for the EMPTY string too (and `isDigit`
    // is ASCII-only), so a trailing `_` — last part `""` — makes HS strip it:
    // `extractBaseName "Foo_" = Just "Foo"`.
    let last = parts.last().unwrap();
    if last.chars().all(|c| c.is_ascii_digit()) {
        Some(parts[..parts.len() - 1].join("_"))
    } else {
        None
    }
}

/// Return the rule's case-name (e.g. `Setup_1`) for proto-rules, else None.
/// Mirror of `getRuleNameByNode` (GraphRepr.hs) which renders
/// `showRuleCaseName` -> `prettyProtoRuleName` (Theory/Model/Rule.hs):
/// `StandRule n -> prefixIfReserved n`, `FreshRule -> "Fresh"`.
/// `prefixIfReserved` (Theory/Model/Rule.hs) prepends `_` when the name is a
/// reserved rule name or already starts with `_`.  This is plain
/// `showRuleCaseName`, NOT the SAPiC-trimming `showDotRuleCaseName`.
pub fn rule_name_by_node(n: &GNode) -> Option<String> {
    if let NodeType::System(ru) = &n.ty
        && let RuleInfo::Proto(p) = &ru.info
    {
        return Some(match &p.name {
            ProtoRuleName::Stand(s) => crate::rule::prefix_if_reserved(s),
            ProtoRuleName::Fresh => "Fresh".to_string(),
        });
    }
    None
}

impl GEdge {
    fn endpoints(&self) -> (NodeId, NodeId) {
        match self {
            Self::System(s, t) | Self::UnsolvedChain(s, t) => (s.0, t.0),
            Self::Less(la) => (la.smaller, la.larger),
        }
    }
}

/// Within a group only system edges establish connectivity. Components are
/// numbered in reverse discovery order, with nodes in their input order.
fn connected_components(
    nodes: Vec<GNode>,
    neighbors: &BTreeMap<NodeId, Vec<NodeId>>,
) -> Vec<Vec<GNode>> {
    let mut unseen: BTreeSet<_> = nodes.iter().map(|n| n.id).collect();
    let mut component_of = BTreeMap::new();
    let mut components = Vec::new();
    for node in &nodes {
        if unseen.remove(&node.id) {
            let mut stack = vec![node.id];
            while let Some(id) = stack.pop() {
                component_of.insert(id, components.len());
                if let Some(adjacent) = neighbors.get(&id) {
                    stack.extend(adjacent.iter().copied().filter(|n| unseen.remove(n)));
                }
            }
            components.push(Vec::new());
        }
    }
    for node in nodes {
        components[component_of[&node.id]].push(node);
    }
    components.reverse();
    components
}

fn add_clusters(repr: &mut GraphRepr, group_name: impl Fn(&GNode) -> Option<String>) {
    let mut groups = BTreeMap::<_, Vec<_>>::new();
    for node in std::mem::take(&mut repr.nodes) {
        if let Some(name) = group_name(&node) {
            groups.entry(name).or_default().push(node);
        } else {
            repr.nodes.push(node);
        }
    }

    repr.clusters.clear();
    if groups.is_empty() {
        return;
    }

    let mut neighbors = BTreeMap::<_, Vec<_>>::new();
    for edge in &repr.edges {
        if let GEdge::System(s, t) = edge {
            neighbors.entry(s.0).or_default().push(t.0);
            neighbors.entry(t.0).or_default().push(s.0);
        }
    }

    let mut memberships = BTreeMap::<NodeId, BTreeSet<usize>>::new();
    for (name, nodes) in groups {
        for (i, nodes) in connected_components(nodes, &neighbors)
            .into_iter()
            .enumerate()
        {
            let index = repr.clusters.len();
            for node in &nodes {
                memberships.entry(node.id).or_default().insert(index);
            }
            repr.clusters.push(Cluster {
                name: format!("{name}_Session_{}", i + 1),
                nodes,
                edges: Vec::new(),
            });
        }
    }

    repr.edges.retain(|edge| {
        let (source, target) = edge.endpoints();
        let (Some(left), Some(right)) = (memberships.get(&source), memberships.get(&target)) else {
            return true;
        };
        let mut clustered = false;
        for &index in left.intersection(right) {
            clustered = true;
            repr.clusters[index].edges.push(edge.clone());
        }
        !clustered
    });
}

/// Group connected rule instances with the same role into sessions.
pub fn add_cluster_by_role(repr: &mut GraphRepr) {
    add_clusters(repr, |node| node_role(node).map(str::to_owned));
}

/// Group connected rule instances with the same base name into sessions.
pub fn add_intelligent_cluster_using_similar_names(repr: &mut GraphRepr) {
    add_clusters(repr, |node| extract_base_name(&rule_name_by_node(node)?));
}

// ---------------------------------------------------------------------
// Building a basic repr from a System
// ---------------------------------------------------------------------

use crate::constraint::constraints::Goal;
use crate::constraint::system::System;

/// Port of `computeBasicGraphRepr` from `Graph.hs`.
/// Collects from a `System`:
///   - rule nodes,
///   - unsolved-action atoms (KU goals etc.),
///   - the optional last-atom node,
///   - missing nodes referenced by edges.
///
/// Crate-internal: `Graph.hs` keeps `computeBasicGraphRepr` out of its export
/// list, exposing only `systemToGraph`.
pub(crate) fn compute_basic_graph_repr(sys: &System) -> GraphRepr {
    let mut nodes: Vec<GNode> = Vec::new();
    // 1. System rule instances.
    // HS `systemNodes se = map systemNode (M.toList $ get Sys.sNodes se)`
    // (Graph.hs) reads `sNodes` in `M.Map` key order — materialised by
    // `System::nodes_in_map_order`, which carries the invariant.
    for (nid, ru) in sys.nodes_in_map_order() {
        nodes.push(GNode {
            id: *nid,
            ty: NodeType::System(ru.clone()),
        });
    }
    // 2. Unsolved action atoms — collect by node id.
    // HS `systemUnsolvedActionNodes se = map unsolvedActionNode
    // (collectBy $ unsolvedActionAtoms se)` (Graph.hs) does NOT filter
    // these ids against `sNodes`: if an id is both a system node and an
    // unsolved ActionG goal, HS emits BOTH a SystemNode and an
    // UnsolvedActionNode.  So there is no skip-if-already-a-system-node guard.
    //
    // `unsolvedActionAtoms` (System.hs) walks `M.toList sGoals`, so
    // its action goals arrive in ascending `Goal` order; this crate's goal
    // store is a `Vec` in insertion order, so sort by `Ord Goal` first.
    // Filtering an `Ord`-sorted list down to one constructor yields the
    // same sequence as sorting that constructor's goals among themselves, so
    // only the action goals need sorting here.
    //
    // `collectBy` (Extension/Prelude.hs) keys off `nub`'d FIRST
    // occurrences, and `ActionG`'s leading payload is the node id, so its key
    // order over that sorted list is ascending node id — what the `BTreeMap`
    // gives.  Within a node the facts then follow `LNFact` order.
    let mut action_goals: Vec<&Goal> = sys
        .goals
        .iter()
        .filter(|(g, st)| !st.solved && g.is_action())
        .map(|(g, _)| g)
        .collect();
    action_goals.sort();
    let mut by_node: BTreeMap<NodeId, Vec<LNFact>> = BTreeMap::new();
    for g in action_goals {
        if let Goal::Action(nid, fa) = g {
            by_node.entry(*nid).or_default().push(fa.clone());
        }
    }
    for (nid, facts) in by_node {
        nodes.push(GNode {
            id: nid,
            ty: NodeType::UnsolvedAction(facts),
        });
    }
    // 3. Last-atom node.
    // HS `systemLastActionNode se = maybe [] (\nid -> [Node nid LastActionAtom])
    // (get Sys.sLastAtom se)` (Graph.hs) appends this UNCONDITIONALLY
    // whenever `sLastAtom` is set — it does NOT skip when the id coincides with
    // a system/unsolved node.  `cacheState` (System/Dot.hs) re-runs each node's
    // `dot` action and overwrites `dsNodes[v]`, so both the SystemNode record
    // AND the bare `#i` last-atom ellipse are emitted at the same id (the
    // ellipse ends up as `dsNodes[v]`, which drives less-edge resolution).  The
    // colliding dot-id is disambiguated in `dot.rs`.
    if let Some(la) = &sys.last_atom {
        nodes.push(GNode {
            id: *la,
            ty: NodeType::LastAction,
        });
    }
    // HS reaches `sEdges` / `sLessAtoms` through `S.toList` (Graph.hs) — `Data.Set` element order, materialised by
    // `System::edges_in_set_order` / `System::less_atoms_in_set_order`.
    let sorted_edges = sys.edges_in_set_order();
    let sorted_less = sys.less_atoms_in_set_order();
    // 4. Missing nodes referenced by edges.
    // HS `systemMissingNodes se = mapMaybe missingNode (S.toList sEdges)`
    // (Graph.hs): each edge yields AT MOST ONE missing node — `missingNode`
    // checks the source first (`MissingNode (Left idx)`), and only if the source
    // is present does it check the target (`MissingNode (Right idx)`).  The
    // membership test is `nid `notElem` nodelist` where `nodelist = map fst
    // (M.toList sNodes)` — i.e. against `sNodes` ONLY, never against
    // unsolved-action / last-atom ids.  There is also NO dedup among missing
    // nodes: two edges sharing the same missing endpoint emit it twice.
    // `systemMissingNodes` never inspects `sLessAtoms`; less-atoms contribute
    // edges (below), not nodes.
    let sys_node_ids: BTreeSet<NodeId> = sys.nodes.iter().map(|(id, _)| *id).collect();
    for e in &sorted_edges {
        if !sys_node_ids.contains(&e.src.0) {
            nodes.push(GNode {
                id: e.src.0,
                ty: NodeType::Missing(MissingHint::Conc(e.src.1)),
            });
        } else if !sys_node_ids.contains(&e.tgt.0) {
            nodes.push(GNode {
                id: e.tgt.0,
                ty: NodeType::Missing(MissingHint::Prem(e.tgt.1)),
            });
        }
    }
    // 5. Edges.
    let mut edges: Vec<GEdge> = Vec::new();
    for e in &sorted_edges {
        edges.push(GEdge::System(e.src, e.tgt));
    }
    for la in sorted_less {
        edges.push(GEdge::Less(la.clone()));
    }
    // HS `unsolvedChains` (System.hs) walks `M.toList sGoals`, so
    // its chain goals arrive in ascending `Goal` order — see step 2 for why
    // sorting the filtered subset reproduces that.  `Ord` on the
    // `(NodeConc, NodePrem)` pair is exactly `Ord Goal`'s `Chain` arm, so
    // sorting the extracted pairs is the same order as sorting the goals.
    let mut chains: Vec<_> = sys.unsolved_chains().collect();
    chains.sort();
    for (src, tgt) in chains {
        edges.push(GEdge::UnsolvedChain(src, tgt));
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
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes};
    use tamarin_term::lterm::{LSort, LVar};

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

    // `sEdges` / `sLessAtoms` are `Data.Set`s upstream, so `computeBasicGraphRepr`
    // reads them through `S.toList` in ascending element order — system edges by
    // `(src, tgt)` and less-atoms by `(smaller, larger)` — with all system edges
    // ahead of all less-edges.  `NodeId` (`LVar`) orders idx-major, so `#vr.5`
    // sorts before `#vk.6`, and the display-only compression pass's appended
    // edges must land at their sorted position rather than at the end.
    #[test]
    fn basic_repr_materialises_edge_and_less_set_order() {
        use crate::constraint::constraints::{Edge, Reason};
        let mut sys = System::default();
        // Pushed in a deliberately unsorted order, as compression leaves them.
        for (s, si, t, ti) in [
            ("vr", 2u64, "vk", 8u64),
            ("vf", 0, "vi", 1),
            ("vr", 1, "vk", 8),
        ] {
            sys.content_mut().edges.push(Edge {
                src: (nid(s, si), ConcIdx(0)),
                tgt: (nid(t, ti), PremIdx(0)),
            });
        }
        for (s, si, t, ti) in [("vk", 6u64, "vk", 0u64), ("vr", 5, "vk", 0)] {
            sys.content_mut().less_atoms.push(LessAtom::new(
                nid(s, si),
                nid(t, ti),
                Reason::Formula,
            ));
        }
        let repr = compute_basic_graph_repr(&sys);
        let rendered: Vec<String> = repr
            .edges
            .iter()
            .map(|e| match e {
                GEdge::System(s, t) => format!("{}->{}", s.0, t.0),
                GEdge::Less(la) => format!("{}<{}", la.smaller, la.larger),
                GEdge::UnsolvedChain(s, t) => format!("{}~>{}", s.0, t.0),
            })
            .collect();
        assert_eq!(
            rendered,
            vec![
                "#vf->#vi.1",
                "#vr.1->#vk.8",
                "#vr.2->#vk.8",
                "#vr.5<#vk",
                "#vk.6<#vk",
            ]
        );
    }

    // `sNodes` is a `Map NodeId RuleACInst` upstream and `systemNodes` reads it
    // through `M.toList` (Graph.hs), so the emitted rule nodes are in
    // ascending `NodeId` order — idx-major, so `#vr.5` precedes `#vk.6` —
    // whatever order the solver stored them in.
    #[test]
    fn basic_repr_materialises_system_node_map_order() {
        let mut sys = System::default();
        // Added in a deliberately unsorted order, as a graft leaves them.
        for (n, i) in [("vr", 5u64), ("vk", 6), ("i", 1)] {
            sys.add_node(nid(n, i), proto_rule("R", None));
        }
        assert_eq!(sys.nodes[0].0, nid("vr", 5));
        let repr = compute_basic_graph_repr(&sys);
        let ids: Vec<String> = repr.nodes.iter().map(|n| n.id.to_string()).collect();
        assert_eq!(ids, vec!["#i.1", "#vr.5", "#vk.6"]);
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
        // HS `all isDigit ""` is True, so a trailing `_` is stripped like a
        // numeric suffix — `splitOn "_" "Foo_" = ["Foo",""]`, two parts.
        assert_eq!(extract_base_name("Foo_"), Some("Foo".to_string()));
        assert_eq!(extract_base_name("_"), Some(String::new()));
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
        // The 2 Alice nodes have no edge between them, so they give 2
        // separate Alice clusters.  The 1 Bob node gives 1 Bob cluster.  The
        // names are `<role>_Session_<i+1>` over the `M.toList` order of the
        // role grouping, so all of Alice's names come before Bob's.  The
        // session index counts the output of `findConnectedComponents`.  HS
        // builds that output by prepending (`go remainingNodes
        // (component : components)`, GraphRepr.hs).  The component
        // discovered last, `#i.3`, is therefore `_Session_1`.  Both the name
        // and the position are written to the output.  The name appears as
        // the DOT subgraph id and as the JSON `jgcName`.  The position
        // appears as the cluster emission order.
        let clustered: Vec<(&str, Vec<NodeId>)> = repr
            .clusters
            .iter()
            .map(|c| (c.name.as_str(), c.nodes.iter().map(|n| n.id).collect()))
            .collect();
        assert_eq!(
            clustered,
            vec![
                ("Alice_Session_1", vec![nid("i", 3)]),
                ("Alice_Session_2", vec![nid("i", 1)]),
                ("Bob_Session_1", vec![nid("i", 2)]),
            ]
        );
        // The node with no role stays at the top level.  No other node does.
        let top: Vec<NodeId> = repr.nodes.iter().map(|n| n.id).collect();
        assert_eq!(top, vec![nid("i", 4)]);
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
        // A last-action marker may share a rule id while remaining outside the cluster.
        repr.nodes.push(GNode {
            id: nid("i", 1),
            ty: NodeType::LastAction,
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
        assert!(repr.edges.is_empty());
        assert!(matches!(
            &repr.nodes[..],
            [GNode {
                ty: NodeType::LastAction,
                ..
            }]
        ));
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
        let mut repr = GraphRepr {
            nodes: vec![b, c, a],
            edges: vec![
                GEdge::System((nid("i", 1), ConcIdx(0)), (nid("i", 2), PremIdx(0))),
                GEdge::System((nid("i", 1), ConcIdx(0)), (nid("i", 3), PremIdx(0))),
            ],
            clusters: vec![],
        };
        add_clusters(&mut repr, |_| Some("session".to_owned()));
        assert_eq!(repr.clusters.len(), 1);
        let ids: Vec<_> = repr.clusters[0].nodes.iter().map(|n| n.id).collect();
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
