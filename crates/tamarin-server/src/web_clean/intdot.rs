//! The `intdot/*` mini-page and the `interactive-graph-def/*` DOT skeleton.
//!
//! `intdot/<path>` returns a tiny standalone HTML page whose only content is a
//! `<dot-graph-viz>` custom element pointing at the matching
//! `interactive-graph-def/<path>` DOT source (same trailing path, resolved
//! numeric index). No trailing newline (ends `</html>`).
//!
//! `interactive-graph-def/<path>` returns Graphviz DOT. For a proof node with
//! no constructed graph (e.g. a freshly opened lemma) the body is the fixed
//! empty-graph skeleton below, which DOES end in a newline. Non-empty graphs
//! are prover-produced and out of scope for this template.

const INTDOT_TEMPLATE: &str = r#"<!DOCTYPE html>
<html><head><meta charset="UTF-8" /><meta name="viewport" content="width=device-width, initial-scale=1.0" /><title>Theory: §NAME§</title><style> body,html{width: 100%; height: 100%; overflow: hidden; margin: 0; padding: 0; }</style><link rel="stylesheet" href="/static/css/intdot-style.css"><script type="module" src="/static/js/intdot-graph.es.js"></script></script></head><body><dot-graph-viz dotsrc="§DOTSRC§"></dot-graph-viz>
</body></html>"#;

/// The empty-graph DOT skeleton returned for a proof node with no graph.
pub const EMPTY_GRAPH_DOT: &str = "digraph \"G\" {\nnodesep=\"0.3\";\nranksep=\"0.3\";\nnode[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\"];\nedge[fontsize=\"8\",fontname=\"Helvetica\"];\n\n}\n";

/// Render the `intdot` mini HTML page.
///
/// * `theory_name` — used only in the `<title>` (not entity-escaped here since
///   the observed value is a plain identifier; escape upstream if needed).
/// * `dotsrc` — full path to the DOT source, e.g.
///   `/thy/trace/3/interactive-graph-def/proof/exec`.
pub fn render_intdot(theory_name: &str, dotsrc: &str) -> String {
    INTDOT_TEMPLATE
        .replace("§NAME§", theory_name)
        .replace("§DOTSRC§", dotsrc)
}

/// Convenience: build the `dotsrc` path for a given index and trailing proof
/// path segments (everything after `interactive-graph-def/`).
pub fn dotsrc_path(index: u64, trailing: &str) -> String {
    format!("/thy/trace/{index}/interactive-graph-def/{trailing}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_graph_dot_shape() {
        assert!(EMPTY_GRAPH_DOT.starts_with("digraph \"G\" {\n"));
        assert!(EMPTY_GRAPH_DOT.ends_with("}\n"));
    }

    #[test]
    fn dotsrc_builder() {
        assert_eq!(
            dotsrc_path(3, "proof/exec"),
            "/thy/trace/3/interactive-graph-def/proof/exec"
        );
    }
}
