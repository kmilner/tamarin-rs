//! Port of `Text.Dot` from `lib/utils/src/Text/Dot.hs`.
//!
//! Builder-style API for emitting Graphviz `.dot` graphs. The Haskell version
//! is a `State` monad; in Rust we expose a `DotGraph` struct with mutating
//! methods. `scope` and `cluster` take a closure for the nested graph.
//!
//! NOTE: the builder API (`DotGraph`, records) has no consumer in the tree
//! yet; retained as a reserved API for a future Rust DOT pipeline. The live
//! DOT path — `tamarin-server/src/handlers/dot.rs` — uses
//! `fix_multi_line_label` from this module directly.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeId {
    /// Auto-generated node id (e.g. `n42`).
    Generated(String),
    /// User-provided integer node id (rendered `u42`/`u_42`).
    User(i64),
}

impl NodeId {
    pub fn from_user(i: i64) -> Self { NodeId::User(i) }

    pub fn to_dot_string(&self) -> String {
        match self {
            NodeId::Generated(s) => s.clone(),
            NodeId::User(i) if *i < 0 => format!("u_{}", -i),
            NodeId::User(i) => format!("u{}", i),
        }
    }

    pub fn cluster(name: &str) -> Self {
        NodeId::Generated(quote_dot_id(&format!("cluster_{}", name)))
    }
}

#[derive(Debug, Clone)]
pub enum GraphElement {
    Attribute(String, String),
    Node(NodeId, Vec<(String, String)>),
    Edge(NodeId, NodeId, Vec<(String, String)>),
    Scope(Vec<GraphElement>),
    SubGraph(Option<NodeId>, Vec<GraphElement>),
}

/// Mutable builder for a `.dot` graph.
#[derive(Debug, Clone, Default)]
pub struct DotGraph {
    next_id: u64,
    elements: Vec<GraphElement>,
}

impl DotGraph {
    pub fn new() -> Self { DotGraph::default() }

    /// Allocate the next sequential id.
    pub fn next_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    pub fn set_id(&mut self, id: u64) { self.next_id = id; }

    /// `addElements`.
    pub fn add_elements(&mut self, mut new: Vec<GraphElement>) {
        self.elements.append(&mut new);
    }

    pub fn elements(&self) -> &[GraphElement] { &self.elements }

    /// `rawNode`: allocate a node and return its id.
    pub fn raw_node(&mut self, attrs: Vec<(String, String)>) -> NodeId {
        let id = self.next_id();
        let nid = NodeId::Generated(format!("n{}", id));
        self.elements.push(GraphElement::Node(nid.clone(), attrs));
        nid
    }

    /// `node`: like `raw_node`, but applies `fix_multi_line_label` to any
    /// `label` attribute.
    pub fn node(&mut self, attrs: Vec<(String, String)>) -> NodeId {
        let fixed = attrs
            .into_iter()
            .map(|(k, v)| if k == "label" { (k, fix_multi_line_label(&v)) } else { (k, v) })
            .collect();
        self.raw_node(fixed)
    }

    /// `userNode`: attach attributes to a user-supplied node id.
    pub fn user_node(&mut self, nid: NodeId, attrs: Vec<(String, String)>) {
        self.elements.push(GraphElement::Node(nid, attrs));
    }

    /// `edge`: from→to with attributes.
    pub fn edge(&mut self, from: NodeId, to: NodeId, attrs: Vec<(String, String)>) {
        self.elements.push(GraphElement::Edge(from, to, attrs));
    }

    /// `scope`: run `body` against a fresh sub-graph that inherits the
    /// id counter, then attach the result as an unnamed sub-graph.
    pub fn scope<R, F: FnOnce(&mut DotGraph) -> R>(&mut self, body: F) -> R {
        let mut sub = DotGraph::new();
        sub.set_id(self.next_id);
        let r = body(&mut sub);
        self.next_id = sub.next_id;
        self.elements.push(GraphElement::SubGraph(None, sub.elements));
        r
    }

    /// `cluster`: same as `scope`, but creates a named cluster.
    pub fn cluster<R, F: FnOnce(&mut DotGraph) -> R>(&mut self, body: F) -> (NodeId, R) {
        let id = self.next_id();
        let cid = NodeId::Generated(format!("cluster_{}", id));
        let mut sub = DotGraph::new();
        sub.set_id(self.next_id);
        let r = body(&mut sub);
        self.next_id = sub.next_id;
        self.elements
            .push(GraphElement::SubGraph(Some(cid.clone()), sub.elements));
        (cid, r)
    }

    pub fn share(&mut self, attrs: Vec<(String, String)>, nodes: Vec<NodeId>) {
        let mut inner: Vec<GraphElement> = attrs
            .into_iter()
            .map(|(k, v)| GraphElement::Attribute(k, v))
            .collect();
        for n in nodes {
            inner.push(GraphElement::Node(n, Vec::new()));
        }
        self.elements.push(GraphElement::Scope(inner));
    }

    pub fn same(&mut self, nodes: Vec<NodeId>) {
        self.share(vec![("rank".into(), "same".into())], nodes);
    }

    pub fn attribute(&mut self, key: &str, val: &str) {
        self.elements
            .push(GraphElement::Attribute(key.into(), val.into()));
    }

    pub fn node_attributes(&mut self, attrs: Vec<(String, String)>) {
        self.elements.push(GraphElement::Node(
            NodeId::Generated("node".into()),
            attrs,
        ));
    }

    pub fn edge_attributes(&mut self, attrs: Vec<(String, String)>) {
        self.elements.push(GraphElement::Node(
            NodeId::Generated("edge".into()),
            attrs,
        ));
    }

    pub fn graph_attributes(&mut self, attrs: Vec<(String, String)>) {
        self.elements.push(GraphElement::Node(
            NodeId::Generated("graph".into()),
            attrs,
        ));
    }
}

/// `showDot label`: render a graph with the given digraph id.
pub fn show_dot(label: &str, graph: &DotGraph) -> String {
    let mut out = String::new();
    out.push_str("digraph \"");
    // Inline label escaping (`"`→`\"`): push each char directly instead of
    // collecting a per-char Vec<char>.
    for c in label.chars() {
        if c == '"' { out.push('\\'); }
        out.push(c);
    }
    out.push_str("\" {\n");
    for e in graph.elements() {
        write_element(&mut out, e);
        out.push('\n');
    }
    out.push_str("\n}\n");
    out
}

fn write_element(out: &mut String, e: &GraphElement) {
    match e {
        GraphElement::Attribute(k, v) => { write_attr(out, k, v); out.push(';'); }
        GraphElement::Node(nid, attrs) => {
            out.push_str(&nid.to_dot_string());
            write_attrs(out, attrs);
            out.push(';');
        }
        GraphElement::Edge(from, to, attrs) => {
            out.push_str(&from.to_dot_string());
            out.push_str(" -> ");
            out.push_str(&to.to_dot_string());
            write_attrs(out, attrs);
            out.push(';');
        }
        GraphElement::Scope(inner) | GraphElement::SubGraph(None, inner) => {
            out.push_str("{\n");
            for e in inner { write_element(out, e); out.push('\n'); }
            out.push_str("\n}");
        }
        GraphElement::SubGraph(Some(nid), inner) => {
            out.push_str("subgraph ");
            out.push_str(&nid.to_dot_string());
            out.push_str(" {\n");
            for e in inner { write_element(out, e); out.push('\n'); }
            out.push_str("\n}");
        }
    }
}

fn write_attrs(out: &mut String, attrs: &[(String, String)]) {
    if attrs.is_empty() { return; }
    out.push('[');
    for (i, (k, v)) in attrs.iter().enumerate() {
        if i > 0 { out.push(','); }
        write_attr(out, k, v);
    }
    out.push(']');
}

fn write_attr(out: &mut String, name: &str, val: &str) {
    if name == "html_label" {
        out.push_str("label=");
        out.push_str(val);
    } else {
        out.push_str(name);
        out.push_str("=\"");
        // Inline escaping (`\n`→`\l`, `"`→`\"`): push chars directly instead of
        // collecting a per-char Vec<char>.
        for c in val.chars() {
            match c {
                '\n' => { out.push('\\'); out.push('l'); }
                '"' => { out.push('\\'); out.push('"'); }
                c => out.push(c),
            }
        }
        out.push('"');
    }
}

fn quote_dot_id(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => { out.push('\\'); out.push('"'); }
            '\\' => { out.push('\\'); out.push('\\'); }
            x => out.push(x),
        }
    }
    out.push('"');
    out
}

/// HS `fixMultiLineLabel` (Text/Dot.hs:355-363): replace each line's leading
/// whitespace 1:1 with `&nbsp;` (non-breaking space) HTML entities and re-join
/// with `unlines`, which appends a trailing newline (matched here by iterating
/// `lines()` and pushing `'\n'` after every line). Single-line labels (no
/// `\n`) pass through untouched.
pub fn fix_multi_line_label(s: &str) -> String {
    if !s.contains('\n') { return s.to_string(); }
    let mut out = String::new();
    for line in s.lines() {
        // Single pass: count leading whitespace chars and accumulate their byte
        // length, so we get the suffix byte offset without re-walking the line.
        let mut suffix_offset = 0;
        for c in line.chars() {
            if !c.is_whitespace() { break; }
            out.push_str("&nbsp;");
            suffix_offset += c.len_utf8();
        }
        out.push_str(&line[suffix_offset..]);
        out.push('\n');
    }
    out
}

// =============================================================================
// Records (record-shape nodes).
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Record<P> {
    Field(Option<P>, String),
    HCat(Vec<Record<P>>),
    VCat(Vec<Record<P>>),
}

pub fn field<P>(label: &str) -> Record<P> {
    Record::Field(None, fix_multi_line_label(label))
}

pub fn port_field<P>(port: P, label: &str) -> Record<P> {
    Record::Field(Some(port), fix_multi_line_label(label))
}

pub fn hcat_records<P>(rs: Vec<Record<P>>) -> Record<P> { Record::HCat(rs) }
pub fn vcat_records<P>(rs: Vec<Record<P>>) -> Record<P> { Record::VCat(rs) }

fn record_label<P: Clone>(graph: &mut DotGraph, rec: &Record<P>) -> (String, Vec<(P, String)>) {
    fn render<P: Clone>(
        graph: &mut DotGraph,
        rec: &Record<P>,
        horiz: bool,
    ) -> (String, Vec<(P, String)>) {
        match rec {
            Record::Field(None, lbl) => (escape_record(lbl), Vec::new()),
            Record::Field(Some(port), lbl) => {
                let id = graph.next_id();
                let pid = format!("n{}", id);
                let label = format!("<{}> {}", pid, escape_record(lbl));
                (label, vec![(port.clone(), pid)])
            }
            Record::HCat(rs) => {
                let mut labels = Vec::new();
                let mut ids = Vec::new();
                for r in rs {
                    let (l, mut i) = render(graph, r, true);
                    labels.push(l);
                    ids.append(&mut i);
                }
                let raw = labels.join("|");
                let label = if horiz { format!("{{{{{}}}}}", raw) } else { format!("{{{}}}", raw) };
                (label, ids)
            }
            Record::VCat(rs) => {
                let mut labels = Vec::new();
                let mut ids = Vec::new();
                for r in rs {
                    let (l, mut i) = render(graph, r, false);
                    labels.push(l);
                    ids.append(&mut i);
                }
                let raw = labels.join("|");
                let label = if horiz { format!("{{{}}}", raw) } else { format!("{{{{{}}}}}", raw) };
                (label, ids)
            }
        }
    }
    render(graph, rec, true)
}

fn escape_record(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '|' | '{' | '}' | '<' | '>' => { out.push('\\'); out.push(c); }
            x => out.push(x),
        }
    }
    out
}

/// `record`: create a `record`-shape node and return both its id and the
/// port association list.
pub fn record<P: Clone>(
    graph: &mut DotGraph,
    rec: &Record<P>,
    attrs: Vec<(String, String)>,
) -> (NodeId, Vec<(P, NodeId)>) {
    gen_record(graph, "record", rec, attrs)
}

/// `mrecord`: like [`record`] but with rounded corners.
pub fn mrecord<P: Clone>(
    graph: &mut DotGraph,
    rec: &Record<P>,
    attrs: Vec<(String, String)>,
) -> (NodeId, Vec<(P, NodeId)>) {
    gen_record(graph, "Mrecord", rec, attrs)
}

fn gen_record<P: Clone>(
    graph: &mut DotGraph,
    shape: &str,
    rec: &Record<P>,
    mut attrs: Vec<(String, String)>,
) -> (NodeId, Vec<(P, NodeId)>) {
    let (lbl, port_ids) = record_label(graph, rec);
    let mut full = vec![("shape".to_string(), shape.to_string()), ("label".to_string(), lbl)];
    full.append(&mut attrs);
    let nid = graph.raw_node(full);
    let ports = port_ids
        .into_iter()
        .map(|(p, pid)| {
            (
                p,
                NodeId::Generated(format!("{}:{}", nid.to_dot_string(), pid)),
            )
        })
        .collect();
    (nid, ports)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_graph_renders() {
        let g = DotGraph::new();
        let s = show_dot("g", &g);
        assert!(s.starts_with("digraph \"g\" {\n"));
        assert!(s.ends_with("}\n"));
    }

    #[test]
    fn simple_graph() {
        let mut g = DotGraph::new();
        let a = g.node(vec![("label".into(), "A".into())]);
        let b = g.node(vec![("label".into(), "B".into())]);
        g.edge(a.clone(), b.clone(), vec![("color".into(), "red".into())]);
        let s = show_dot("ex", &g);
        assert!(s.contains("n0[label=\"A\"];"));
        assert!(s.contains("n1[label=\"B\"];"));
        assert!(s.contains("n0 -> n1[color=\"red\"];"));
    }

    #[test]
    fn user_nodes_and_negative_ids() {
        let mut g = DotGraph::new();
        let a = NodeId::from_user(7);
        let b = NodeId::from_user(-3);
        g.user_node(a.clone(), vec![]);
        g.user_node(b.clone(), vec![]);
        g.edge(a, b, vec![]);
        let s = show_dot("u", &g);
        assert!(s.contains("u7;"));
        assert!(s.contains("u_3;"));
        assert!(s.contains("u7 -> u_3;"));
    }

    #[test]
    fn quoting_label_with_quotes() {
        let s = show_dot("with \"quotes\"", &DotGraph::new());
        assert!(s.starts_with("digraph \"with \\\"quotes\\\"\" {"));
    }

    #[test]
    fn scope_emits_sub_block() {
        let mut g = DotGraph::new();
        g.scope(|sub| {
            sub.node(vec![]);
        });
        let s = show_dot("g", &g);
        assert!(s.contains("{\nn0;"));
    }

    #[test]
    fn cluster_creates_named_subgraph() {
        let mut g = DotGraph::new();
        let (cid, _) = g.cluster(|sub| {
            sub.node(vec![]);
        });
        let s = show_dot("g", &g);
        assert!(s.contains("subgraph cluster_0 {"));
        let _ = cid;
    }

    #[test]
    fn fix_multi_line_label_replaces_leading_ws() {
        assert_eq!(fix_multi_line_label("a\n  b"), "a\n&nbsp;&nbsp;b\n");
        // Single-line label is untouched.
        assert_eq!(fix_multi_line_label("hello"), "hello");
    }

    #[test]
    fn record_node_emits_label_with_ports() {
        let mut g = DotGraph::new();
        let rec: Record<&'static str> = hcat_records(vec![
            field("a"),
            port_field("p1", "b"),
            field("c"),
        ]);
        let (nid, ports) = record(&mut g, &rec, vec![]);
        // One port and a node id; label should contain the angle-port marker.
        assert_eq!(ports.len(), 1);
        let s = show_dot("r", &g);
        assert!(s.contains("shape=\"record\""));
        assert!(s.contains("<n"));
        let _ = nid;
    }
}
