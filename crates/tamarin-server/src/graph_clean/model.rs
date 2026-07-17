//! Graph data model for the tamarin web-UI constraint-system graph.
//!
//! This is an independent model designed from the observed DOT payloads
//! (see workspace/BEHAVIOR.md). A [`Graph`] is an ordered list of top-level
//! [`Stmt`]s rendered under one of two header styles. The [`super::dot`]
//! serializer turns a `Graph` back into byte-exact DOT text.

/// Which top-level attribute header to emit.
///
/// Per the observed trigger rule (BEHAVIOR.md §4), [`Header::Compact`] is used
/// exactly when the graph carries a node with a non-`Undefined` role; otherwise
/// [`Header::Simple`]. [`Graph::infer_header`] applies that rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Header {
    /// Plain multiset-rewriting graph header (`nodesep="0.3"`, …).
    Simple,
    /// Clustered/process graph header (`packmode="cluster"`, `compound="true"`, …).
    Compact,
}

/// The role annotation carried by a record node.
///
/// `Undefined` is the sentinel for plain multiset-rewriting rules; any other
/// value denotes a process/agent role and triggers clustering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Role(pub String);

impl Role {
    pub const UNDEFINED: &'static str = "Undefined";
    pub fn undefined() -> Self {
        Role(Self::UNDEFINED.to_string())
    }
    pub fn is_undefined(&self) -> bool {
        self.0 == Self::UNDEFINED
    }
}

/// A whole graph: the two node/edge default lines are chosen by `header`, and
/// `body` holds every statement in emission order.
#[derive(Clone, Debug)]
pub struct Graph {
    pub header: Header,
    pub body: Vec<Stmt>,
}

impl Graph {
    pub fn new(header: Header) -> Self {
        Graph { header, body: Vec::new() }
    }

    pub fn push(&mut self, s: Stmt) -> &mut Self {
        self.body.push(s);
        self
    }

    /// Apply the observed clustering trigger (BEHAVIOR.md §4): compact iff any
    /// record node anywhere in the graph has a non-`Undefined` role.
    pub fn infer_header(&self) -> Header {
        if self.body.iter().any(stmt_has_role_node) {
            Header::Compact
        } else {
            Header::Simple
        }
    }

    /// Set `header` to the inferred value.
    pub fn set_inferred_header(&mut self) {
        self.header = self.infer_header();
    }
}

fn stmt_has_role_node(s: &Stmt) -> bool {
    match s {
        Stmt::Node(n) => n.has_defined_role(),
        Stmt::Cluster(c) => c.body.iter().any(stmt_has_role_node),
        Stmt::RankBlock(b) => b.body.iter().any(stmt_has_role_node),
        Stmt::Edge(_) => false,
    }
}

/// A top-level (or nested) statement, emitted in list order.
#[derive(Clone, Debug)]
pub enum Stmt {
    Node(Node),
    Edge(Edge),
    /// A `subgraph "cluster_…" { … }` block (compact/clustered mode).
    Cluster(Cluster),
    /// An anonymous `{ rank="sink"; … }` block (used for the legend).
    RankBlock(RankBlock),
}

/// A DOT node statement. `id` is the full graphviz identifier verbatim, e.g.
/// `"n5"`. Ports ([`Cell::port`]) and edge endpoints ([`EndPoint`]) use the same
/// full-string convention (`"n2"`), so the serializer emits ids as given.
#[derive(Clone, Debug)]
pub struct Node {
    pub id: String,
    pub kind: NodeKind,
}

impl Node {
    pub fn record(id: impl Into<String>, r: Record) -> Self {
        Node { id: id.into(), kind: NodeKind::Record(r) }
    }
    pub fn ellipse(id: impl Into<String>, e: Ellipse) -> Self {
        Node { id: id.into(), kind: NodeKind::Ellipse(e) }
    }
    pub fn plain(id: impl Into<String>, html: impl Into<String>) -> Self {
        Node { id: id.into(), kind: NodeKind::Plain { html: html.into() } }
    }
    pub fn has_defined_role(&self) -> bool {
        matches!(&self.kind, NodeKind::Record(r) if !r.role.is_undefined())
    }
}

#[derive(Clone, Debug)]
pub enum NodeKind {
    /// Rule / graph-node instance drawn as a graphviz record.
    Record(Record),
    /// Atomic knowledge / action / temporal node drawn as an ellipse.
    Ellipse(Ellipse),
    /// The abbreviation legend, an HTML-like label. `html` is the inner content
    /// between `label=<` and `>` (i.e. it starts with `<TABLE …`).
    Plain { html: String },
}

/// A record node's label and styling. `columns` are the top-level record groups
/// (`{…}|{…}|{…}`, typically premises / rule-info / conclusions); each column is
/// a list of ported cells joined by `|`.
#[derive(Clone, Debug)]
pub struct Record {
    pub columns: Vec<Vec<Cell>>,
    pub fillcolor: String,
    pub fontcolor: String,
    pub role: Role,
}

/// One ported record cell: `<n{port}> {text}`. `text` is taken pre-rendered
/// (already escaped/wrapped); see BEHAVIOR.md §3a on why wrapping is a gap.
#[derive(Clone, Debug)]
pub struct Cell {
    pub port: String,
    pub text: String,
}

impl Cell {
    pub fn new(port: impl Into<String>, text: impl Into<String>) -> Self {
        Cell { port: port.into(), text: text.into() }
    }
}

#[derive(Clone, Debug)]
pub struct Ellipse {
    pub label: String,
    pub color: Option<String>,
}

impl Ellipse {
    pub fn new(label: impl Into<String>) -> Self {
        Ellipse { label: label.into(), color: None }
    }
    pub fn colored(label: impl Into<String>, color: impl Into<String>) -> Self {
        Ellipse { label: label.into(), color: Some(color.into()) }
    }
}

/// One endpoint of an edge: node id plus optional record port.
#[derive(Clone, Debug)]
pub struct EndPoint {
    pub node: String,
    pub port: Option<String>,
}

impl EndPoint {
    pub fn node(node: impl Into<String>) -> Self {
        EndPoint { node: node.into(), port: None }
    }
    pub fn port(node: impl Into<String>, port: impl Into<String>) -> Self {
        EndPoint { node: node.into(), port: Some(port.into()) }
    }
}

/// An edge statement. `attrs` are `(key, value)` pairs emitted in list order as
/// `[k="v",…]` (see BEHAVIOR.md §3c for the observed style vocabulary).
#[derive(Clone, Debug)]
pub struct Edge {
    pub src: EndPoint,
    pub dst: EndPoint,
    pub attrs: Vec<(String, String)>,
}

impl Edge {
    pub fn new(src: EndPoint, dst: EndPoint, attrs: &[(&str, &str)]) -> Self {
        Edge {
            src,
            dst,
            attrs: attrs.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
        }
    }
}

/// A `subgraph "cluster_…" { … }` block.
#[derive(Clone, Debug)]
pub struct Cluster {
    /// The cluster label WITHOUT the `cluster_` prefix (e.g. `Initiator_Session_1`).
    pub label: String,
    /// 8-hex ARGB used for both `color` and `fillcolor` (e.g. `#4936D84C`).
    pub color: String,
    pub body: Vec<Stmt>,
}

/// An anonymous block carrying a `rank` and inner statements — used for the
/// legend's `{ rank="sink"; … }`.
#[derive(Clone, Debug)]
pub struct RankBlock {
    pub rank: String,
    pub body: Vec<Stmt>,
}
