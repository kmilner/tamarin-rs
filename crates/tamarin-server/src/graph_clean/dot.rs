//! Byte-exact DOT serializer for [`Graph`].
//!
//! Reproduces the exact bytes the tamarin web UI emits at
//! `interactive-graph-def` (see workspace/BEHAVIOR.md §2, §3). The emission is
//! driven by one structural rule: every block is
//! `OPEN "\n"` + (each inner line + `"\n"`) + `"\n}"`, i.e. one blank line before
//! the closing brace; the top-level digraph then gets a final `"\n"`.

use super::model::*;

/// Serialize a graph to DOT text (byte-exact against captured payloads).
pub fn to_dot(g: &Graph) -> String {
    let mut lines: Vec<String> = header_lines(g.header);
    for s in &g.body {
        lines.push(render_stmt(s));
    }
    // Top-level digraph block, plus the trailing newline the server emits.
    let mut out = render_block("digraph \"G\" {", &lines);
    out.push('\n');
    out
}

/// `OPEN\n` + `line\n`* + `\n}`  (no trailing newline; callers add it if needed).
/// A `line` may itself be multi-line (a nested block); the per-line `\n` after it
/// supplies the separator the parent owes it.
fn render_block(open: &str, lines: &[String]) -> String {
    let mut s = String::new();
    s.push_str(open);
    s.push('\n');
    for l in lines {
        s.push_str(l);
        s.push('\n');
    }
    s.push_str("\n}");
    s
}

fn header_lines(h: Header) -> Vec<String> {
    let raw: &[&str] = match h {
        Header::Simple => &[
            "nodesep=\"0.3\";",
            "ranksep=\"0.3\";",
            "node[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\"];",
            "edge[fontsize=\"8\",fontname=\"Helvetica\"];",
        ],
        Header::Compact => &[
            "nodesep=\"0.8\";",
            "ranksep=\"0.8\";",
            "sep=\"4\";",
            "splines=\"true\";",
            "overlap=\"false\";",
            "pack=\"true\";",
            "packmode=\"cluster\";",
            "concentrate=\"true\";",
            "compound=\"true\";",
            "remincross=\"true\";",
            "mclimit=\"10\";",
            "nslimit=\"20\";",
            "nslimit1=\"20\";",
            "ordering=\"out\";",
            "rankdir=\"TB\";",
            "showboxes=\"false\";",
            "clusterrank=\"local\";",
            "node[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\",margin=\"0.05,0.05\",shape=\"ellipse\"];",
            "edge[fontsize=\"8\",fontname=\"Helvetica\",penwidth=\"1.5\",arrowsize=\"0.5\",color=\"black\",style=\"solid\",weight=\"8\"];",
        ],
    };
    raw.iter().map(|s| s.to_string()).collect()
}

fn render_stmt(s: &Stmt) -> String {
    match s {
        Stmt::Node(n) => render_node(n),
        Stmt::Edge(e) => render_edge(e),
        Stmt::Cluster(c) => render_cluster(c),
        Stmt::RankBlock(b) => render_rankblock(b),
    }
}

fn render_node(n: &Node) -> String {
    match &n.kind {
        NodeKind::Record(r) => {
            format!(
                "{}[shape=\"record\",label=\"{}\",fillcolor=\"{}\",style=\"filled\",fontcolor=\"{}\",role=\"{}\"];",
                n.id,
                render_record_label(r),
                r.fillcolor,
                r.fontcolor,
                r.role.0,
            )
        }
        NodeKind::Ellipse(e) => match &e.color {
            Some(c) => format!(
                "{}[label=\"{}\",shape=\"ellipse\",color=\"{}\"];",
                n.id, e.label, c
            ),
            None => format!("{}[label=\"{}\",shape=\"ellipse\"];", n.id, e.label),
        },
        NodeKind::Plain { html } => {
            format!("{}[shape=\"plain\",label=<{}>];", n.id, html)
        }
    }
}

/// `{{<p> t|<p> t}|{<p> t}|{<p> t|<p> t}}` — outer braces, groups joined by `|`,
/// each group `{cell|cell}`, each cell `<port> text`.
fn render_record_label(r: &Record) -> String {
    let mut s = String::from("{");
    let groups: Vec<String> = r
        .columns
        .iter()
        .map(|col| {
            let cells: Vec<String> = col
                .iter()
                .map(|c| format!("<{}> {}", c.port, c.text))
                .collect();
            format!("{{{}}}", cells.join("|"))
        })
        .collect();
    s.push_str(&groups.join("|"));
    s.push('}');
    s
}

fn render_edge(e: &Edge) -> String {
    let mut s = render_endpoint(&e.src);
    s.push_str(" -> ");
    s.push_str(&render_endpoint(&e.dst));
    if !e.attrs.is_empty() {
        let attrs: Vec<String> = e
            .attrs
            .iter()
            .map(|(k, v)| format!("{}=\"{}\"", k, v))
            .collect();
        s.push('[');
        s.push_str(&attrs.join(","));
        s.push(']');
    }
    s.push(';');
    s
}

fn render_endpoint(ep: &EndPoint) -> String {
    match &ep.port {
        Some(p) => format!("{}:{}", ep.node, p),
        None => ep.node.clone(),
    }
}

fn render_cluster(c: &Cluster) -> String {
    let mut lines = vec![
        "nodesep=\"0.6\";".to_string(),
        "ranksep=\"0.6\";".to_string(),
        format!("label=\"{}\";", c.label),
        "style=\"filled\";".to_string(),
        format!("color=\"{}\";", c.color),
        "penwidth=\"2\";".to_string(),
        format!("fillcolor=\"{}\";", c.color),
        "overlap=\"false\";".to_string(),
        "sep=\"4\";".to_string(),
    ];
    for s in &c.body {
        lines.push(render_stmt(s));
    }
    let open = format!("subgraph \"cluster_{}\" {{", c.label);
    render_block(&open, &lines)
}

fn render_rankblock(b: &RankBlock) -> String {
    let mut lines = vec![format!("rank=\"{}\";", b.rank)];
    for s in &b.body {
        lines.push(render_stmt(s));
    }
    render_block("{", &lines)
}
