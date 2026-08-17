// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Text.Dot` from `lib/utils/src/Text/Dot.hs`.
//!
//! Builder-style API for emitting Graphviz `.dot` graphs. The Haskell version
//! is a `State` monad; in Rust we expose a `DotGraph` struct with mutating
//! methods. `scope` and `cluster` take a closure for the nested graph.
//!
//! Its one consumer is the workspace's single DOT serializer
//! (`tamarin-theory/src/constraint/system/dot_showdot.rs`), which drives the
//! full builder API and [`show_dot`], so the bytes reaching both the batch
//! `--output-dot` writer and the interactive graph routes are `Text.Dot`'s.
//!
//! What is `pub` here tracks `Text.Dot`'s own export list (Text/Dot.hs:14-69),
//! so a combinator with no RS caller yet still carries the visibility its
//! upstream counterpart has.  The escapers are the other side of that rule:
//! `escapeRecord` / `fixMultiLineLabel` / `escapeDotGraphLabel` are internal
//! to the Haskell module, so they are private here too.
//!
//! Two places are WIDER than the export list, both because Rust cannot express
//! what Haskell does there:
//!   * `NodeId` and `Record` are exported abstract upstream (the `-- abstract`
//!     notes at Text/Dot.hs:23 and :44), but a Rust enum's variants inherit the
//!     enum's visibility, so hiding the constructors would need a wrapper type.
//!     Nothing outside this module names a variant.
//!   * `GraphElement` is not exported at all upstream, yet it appears in the
//!     signatures of `addElements` (Text/Dot.hs:152) and
//!     `getDotGenStateElements` (Text/Dot.hs:135), which ARE exported; Haskell
//!     allows that, Rust does not.
//!
//! Two `pub` items answer to something other than a NAME in that list:
//! [`NodeId::to_dot_string`] is `instance Show NodeId` (Text/Dot.hs:86-90),
//! which an abstract type carries to its users anyway, and
//! [`DotGraph::scope_named`] is `createSubGraph` (Text/Dot.hs:148-149) at a
//! `Just cid`, the shape `cluster` itself uses (Text/Dot.hs:211-215).
//!
//! The combinators upstream exports that have no counterpart here are `runDot`,
//! `modifyDotGenState`, `htmlLabel` (whose `("html_label", …)` pair `write_attr`
//! special-cases directly), the `[String]` conveniences `hcat'`/`vcat'`
//! (Text/Dot.hs:399-408) and the `'`/`_` result-shape variants of
//! `record`/`mrecord`.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeId {
    /// Auto-generated node id (e.g. `n42`).
    Generated(String),
    /// User-provided integer node id (rendered `u42`/`u_42`).
    User(i64),
}

impl NodeId {
    pub fn from_user(i: i64) -> Self {
        NodeId::User(i)
    }

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
    pub fn new() -> Self {
        DotGraph::default()
    }

    /// Allocate the next sequential id.
    pub fn next_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    pub fn set_id(&mut self, id: u64) {
        self.next_id = id;
    }

    /// `addElements`.
    pub fn add_elements(&mut self, mut new: Vec<GraphElement>) {
        self.elements.append(&mut new);
    }

    pub fn elements(&self) -> &[GraphElement] {
        &self.elements
    }

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
            .map(|(k, v)| {
                if k == "label" {
                    (k, fix_multi_line_label(&v))
                } else {
                    (k, v)
                }
            })
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
        self.elements
            .push(GraphElement::SubGraph(None, sub.elements));
        r
    }

    /// `roleCluster`'s dot half (Theory/Constraint/System/Dot.hs:178-188 — the
    /// theory-side module, not the `Text/Dot.hs` every other citation here
    /// names): a [`scope`] carrying a
    /// CALLER-supplied cluster id — HS builds it with `createClusterNodeId`
    /// ([`NodeId::cluster`]) rather than from the counter.  The `nextId` HS
    /// runs first is a no-op on the numbering: the sub-state is re-seeded with
    /// the pre-increment value, so the body starts at the counter the caller
    /// was already on.
    ///
    /// [`scope`]: DotGraph::scope
    pub fn scope_named<R, F: FnOnce(&mut DotGraph) -> R>(&mut self, cid: NodeId, body: F) -> R {
        let mut sub = DotGraph::new();
        sub.set_id(self.next_id);
        let r = body(&mut sub);
        self.next_id = sub.next_id;
        self.elements
            .push(GraphElement::SubGraph(Some(cid), sub.elements));
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
        self.elements
            .push(GraphElement::Node(NodeId::Generated("node".into()), attrs));
    }

    pub fn edge_attributes(&mut self, attrs: Vec<(String, String)>) {
        self.elements
            .push(GraphElement::Node(NodeId::Generated("edge".into()), attrs));
    }

    pub fn graph_attributes(&mut self, attrs: Vec<(String, String)>) {
        self.elements
            .push(GraphElement::Node(NodeId::Generated("graph".into()), attrs));
    }
}

/// `showDot`'s `escapedLabel` (Text/Dot.hs:241): the digraph-id escape, which
/// touches `"` (→ `\"`) and NOTHING else — backslashes included.  Distinct
/// from `showAttr`'s attribute-value escape, which also maps `\n` to `\l`
/// (see `write_attr`).
fn escape_dot_graph_label(label: &str) -> String {
    let mut out = String::with_capacity(label.len());
    for c in label.chars() {
        if c == '"' {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

/// `showDot label`: render a graph with the given digraph id.
pub fn show_dot(label: &str, graph: &DotGraph) -> String {
    let mut out = String::new();
    out.push_str("digraph \"");
    out.push_str(&escape_dot_graph_label(label));
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
        GraphElement::Attribute(k, v) => {
            write_attr(out, k, v);
            out.push(';');
        }
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
            for e in inner {
                write_element(out, e);
                out.push('\n');
            }
            out.push_str("\n}");
        }
        GraphElement::SubGraph(Some(nid), inner) => {
            out.push_str("subgraph ");
            out.push_str(&nid.to_dot_string());
            out.push_str(" {\n");
            for e in inner {
                write_element(out, e);
                out.push('\n');
            }
            out.push_str("\n}");
        }
    }
}

fn write_attrs(out: &mut String, attrs: &[(String, String)]) {
    if attrs.is_empty() {
        return;
    }
    out.push('[');
    for (i, (k, v)) in attrs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
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
                '\n' => {
                    out.push('\\');
                    out.push('l');
                }
                '"' => {
                    out.push('\\');
                    out.push('"');
                }
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
            '"' => {
                out.push('\\');
                out.push('"');
            }
            '\\' => {
                out.push('\\');
                out.push('\\');
            }
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
fn fix_multi_line_label(s: &str) -> String {
    if !s.contains('\n') {
        return s.to_string();
    }
    let mut out = String::new();
    for line in s.lines() {
        // Single pass: count leading whitespace chars and accumulate their byte
        // length, so we get the suffix byte offset without re-walking the line.
        let mut suffix_offset = 0;
        for c in line.chars() {
            if !c.is_whitespace() {
                break;
            }
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

pub fn hcat_records<P>(rs: Vec<Record<P>>) -> Record<P> {
    Record::HCat(rs)
}
pub fn vcat_records<P>(rs: Vec<Record<P>>) -> Record<P> {
    Record::VCat(rs)
}

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
                let label = if horiz {
                    format!("{{{{{}}}}}", raw)
                } else {
                    format!("{{{}}}", raw)
                };
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
                let label = if horiz {
                    format!("{{{}}}", raw)
                } else {
                    format!("{{{{{}}}}}", raw)
                };
                (label, ids)
            }
        }
    }
    render(graph, rec, true)
}

/// `renderRecord`'s `escape` (Text/Dot.hs:273-280): the record
/// metacharacters `| { } < >` get a backslash and NOTHING else does —
/// `"` / `\` / newline are the attribute level's business (see
/// [`escape_dot_graph_label`] and `write_attr`).
fn escape_record(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '|' | '{' | '}' | '<' | '>' => {
                out.push('\\');
                out.push(c);
            }
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
    let mut full = vec![
        ("shape".to_string(), shape.to_string()),
        ("label".to_string(), lbl),
    ];
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
        // `" {\n" ++ unlines (map showGraphElement elems) ++ "\n}\n"`
        // (Text/Dot.hs:246-248): with no elements `unlines` contributes the
        // empty string, so an empty graph still carries the blank line the
        // trailing `"\n}\n"` puts before the closing brace.
        let g = DotGraph::new();
        assert_eq!(show_dot("g", &g), "digraph \"g\" {\n\n}\n");
    }

    #[test]
    fn simple_graph() {
        let mut g = DotGraph::new();
        let a = g.node(vec![("label".into(), "A".into())]);
        let b = g.node(vec![("label".into(), "B".into())]);
        g.edge(a.clone(), b.clone(), vec![("color".into(), "red".into())]);
        // `unlines (map showGraphElement elems)` ends every element with a
        // newline. The trailing `"\n}\n"` therefore still puts a blank line
        // before the closing brace. The ids run in allocation order from 0.
        assert_eq!(
            show_dot("ex", &g),
            "digraph \"ex\" {\nn0[label=\"A\"];\nn1[label=\"B\"];\nn0 -> n1[color=\"red\"];\n\n}\n"
        );
    }

    #[test]
    fn user_nodes_and_negative_ids() {
        let mut g = DotGraph::new();
        let a = NodeId::from_user(7);
        let b = NodeId::from_user(-3);
        g.user_node(a.clone(), vec![]);
        g.user_node(b.clone(), vec![]);
        g.edge(a, b, vec![]);
        // `instance Show NodeId` (Text/Dot.hs:86-90) prints `u<i>`. For a
        // negative id it prints `u_<-i>`. An empty attribute list emits no
        // brackets (`showAttrs []`).
        assert_eq!(
            show_dot("u", &g),
            "digraph \"u\" {\nu7;\nu_3;\nu7 -> u_3;\n\n}\n"
        );
    }

    #[test]
    fn quoting_label_with_quotes() {
        // `escapedLabel` (Text/Dot.hs:241) escapes `"` and nothing else. The
        // backslash below therefore stays unescaped. The `quoteDotId` path
        // escapes it.
        let s = show_dot("with \"quotes\" and a \\ backslash", &DotGraph::new());
        assert_eq!(
            s,
            "digraph \"with \\\"quotes\\\" and a \\ backslash\" {\n\n}\n"
        );
    }

    #[test]
    fn attribute_values_escape_newline_and_quote_except_html_label() {
        // `showAttr` (Text/Dot.hs:346-352) turns `\n` into `\l` and `"` into
        // `\"`. It copies everything else unchanged. `html_label` skips all of
        // that quoting. It emits `label=<...>` with no quotes, so graphviz
        // reads the value as HTML-like.
        let mut g = DotGraph::new();
        g.user_node(
            NodeId::from_user(1),
            vec![
                ("label".into(), "line1\nline2".into()),
                ("tooltip".into(), "say \"hi\"".into()),
            ],
        );
        g.user_node(
            NodeId::from_user(2),
            vec![("html_label".into(), "<<b>x</b>>".into())],
        );
        assert_eq!(
            show_dot("a", &g),
            "digraph \"a\" {\nu1[label=\"line1\\lline2\",tooltip=\"say \\\"hi\\\"\"];\n\
             u2[label=<<b>x</b>>];\n\n}\n"
        );
    }

    #[test]
    fn cluster_node_id_is_quoted_and_backslash_escaped() {
        // `createClusterNodeId` (Text/Dot.hs:138-146) wraps `cluster_<name>`
        // in `quoteDotId`. `quoteDotId` escapes both `"` and `\`. That escape
        // set is wider than the set of `escapedLabel`. The quotes are part of
        // the id, so they reach the `subgraph <id> {` header unchanged.
        assert_eq!(NodeId::cluster("Bob").to_dot_string(), "\"cluster_Bob\"");
        assert_eq!(
            NodeId::cluster("a\"b\\c").to_dot_string(),
            "\"cluster_a\\\"b\\\\c\""
        );
    }

    #[test]
    fn scope_emits_sub_block() {
        let mut g = DotGraph::new();
        g.scope(|sub| {
            sub.node(vec![]);
        });
        // `SubGraph Nothing` renders a `{ … }` block with no name. The
        // sub-graph inherits the id counter, so the body node is `n0`. It does
        // not get the id of a new graph.
        assert_eq!(show_dot("g", &g), "digraph \"g\" {\n{\nn0;\n\n}\n\n}\n");
    }

    #[test]
    fn cluster_creates_named_subgraph() {
        let mut g = DotGraph::new();
        let (cid, _) = g.cluster(|sub| {
            sub.node(vec![]);
        });
        // `cluster` (Text/Dot.hs:208-216) uses the current counter value for
        // the cluster id. It then starts the body at `succ uq`. The body node
        // is therefore `n1`, and never `n0`.
        assert_eq!(cid.to_dot_string(), "cluster_0");
        assert_eq!(
            show_dot("g", &g),
            "digraph \"g\" {\nsubgraph cluster_0 {\nn1;\n\n}\n\n}\n"
        );
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
            // The `escape` function of `renderRecord` (Text/Dot.hs:273-280)
            // puts a backslash in front of the record metacharacters. No other
            // code escapes them, so the attribute layer leaves them alone.
            field("c<|>{}"),
        ]);
        let (nid, ports) = record(&mut g, &rec, vec![]);
        // The port field takes id 0, so the record node itself gets `n1`. The
        // edge target of the port is the `<node>:<port>` pair.
        assert_eq!(nid.to_dot_string(), "n1");
        assert_eq!(ports.len(), 1);
        assert_eq!(ports[0].0, "p1");
        assert_eq!(ports[0].1.to_dot_string(), "n1:n0");
        // The top-level `HCat` is `horiz`. This gives the two nested braces.
        assert_eq!(
            show_dot("r", &g),
            "digraph \"r\" {\n\
             n1[shape=\"record\",label=\"{{a|<n0> b|c\\<\\|\\>\\{\\}}}\"];\n\n}\n"
        );
    }

    #[test]
    fn vcat_record_flips_the_brace_nesting() {
        // `render horiz (VCat rs)` recurses with `horiz = False`. A `VCat` of
        // `HCat`s is therefore `{ {a|b} | {c} }`. That shape is the inverse of
        // the shape above, which has the `HCat` on the outside. `mkNode` builds
        // this nesting for a rule box.
        let mut g = DotGraph::new();
        let rec: Record<&'static str> = vcat_records(vec![
            hcat_records(vec![field("a"), field("b")]),
            hcat_records(vec![field("c")]),
        ]);
        // `mrecord` is `genRecord "Mrecord"`. Only the shape differs.
        mrecord(&mut g, &rec, vec![("color".into(), "blue".into())]);
        assert_eq!(
            show_dot("r", &g),
            "digraph \"r\" {\n\
             n0[shape=\"Mrecord\",label=\"{{a|b}|{c}}\",color=\"blue\"];\n\n}\n"
        );
    }

    #[test]
    fn same_wraps_nodes_in_a_rank_scope() {
        // `same = share [("rank","same")]` (Text/Dot.hs:195-204) emits a
        // `Scope` with no name. The scope holds the attribute. One node per id
        // follows the attribute, and those nodes carry no brackets.
        let mut g = DotGraph::new();
        g.same(vec![NodeId::from_user(1), NodeId::from_user(2)]);
        assert_eq!(
            show_dot("g", &g),
            "digraph \"g\" {\n{\nrank=\"same\";\nu1;\nu2;\n\n}\n\n}\n"
        );
    }
}
