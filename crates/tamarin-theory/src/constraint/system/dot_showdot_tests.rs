// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Unit pins for the DOT serializer's `Text.Dot` bytes.

use super::*;
use crate::constraint::system::graph::SimplificationLevel;
use crate::constraint::system::System;
use crate::fact::{fresh_fact, out_fact, proto_fact, Multiplicity};
use tamarin_term::lterm::{LSort, LVar};
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

/// The `Text.Dot` container plus the whole element block for a one-rule
/// system, byte-for-byte against the pinned oracle's `--output-dot`.
///
/// Every serialization rule this module exists for is visible here: unindented
/// statements, quoted numeric attribute values, `node[…]` abutting its id,
/// counter-derived `n<k>` ids with the three record PORTS (`n0`/`n1`/`n2`)
/// allocated before the node itself (`n3`), and `showDot`'s blank line before
/// the closing brace.
#[test]
fn single_rule_matches_the_oracle_bytes() {
    let mut sys = System::empty();
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    sys.add_node(
        LVar::new("i", LSort::Node, 0),
        super::super::tests::proto_node(
            "R",
            vec![fresh_fact(k.clone())],
            vec![proto_fact(Multiplicity::Linear, "A", vec![k.clone()])],
            vec![out_fact(k)],
        ),
    );
    let got = system_to_dot_labeled(&sys, &GraphOptions::default(), "trace_Triv");
    assert_eq!(
        got,
        concat!(
            "digraph \"trace_Triv\" {\n",
            "nodesep=\"0.3\";\n",
            "ranksep=\"0.3\";\n",
            "node[fontsize=\"8\",fontname=\"Helvetica\",width=\"0.3\",height=\"0.2\"];\n",
            "edge[fontsize=\"8\",fontname=\"Helvetica\"];\n",
            "n3[shape=\"record\",label=\"{{<n0> Fr( ~k )}|{<n1> #i : R[A( ~k )]}|{<n2> Out( ~k )}}\"\
             ,fillcolor=\"#d5d897\",style=\"filled\",fontcolor=\"black\",role=\"Undefined\"];\n",
            "\n",
            "}\n",
        )
    );
}

/// `showDot`'s digraph id escapes `"` and NOTHING else (Text/Dot.hs:241).
#[test]
fn digraph_id_escapes_only_double_quotes() {
    let sys = System::empty();
    let got = system_to_dot_labeled(&sys, &GraphOptions::default(), "a \"b\" \\c");
    assert!(got.starts_with("digraph \"a \\\"b\\\" \\c\" {\n"), "{got}");
}

/// `dotLessEdge` resolves both endpoints through `dsNodes` (System/Dot.hs:409-413),
/// which for a RECORD node is the rule-label field's PORTED id — not the bare
/// node id — and emits `color` before `style`.
#[test]
fn less_edge_targets_the_record_label_port() {
    use crate::constraint::constraints::{LessAtom, Reason};
    let mut sys = System::empty();
    let a = LVar::new("a", LSort::Node, 0);
    let b = LVar::new("b", LSort::Node, 0);
    let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
    sys.add_node(
        a,
        super::super::tests::proto_node("A", vec![], vec![], vec![out_fact(k.clone())]),
    );
    sys.add_node(
        b,
        super::super::tests::proto_node("B", vec![fresh_fact(k)], vec![], vec![]),
    );
    sys.content_mut()
        .less_atoms
        .push(LessAtom::new(a, b, Reason::Fresh));
    let opts = GraphOptions {
        compress: false,
        abbreviate: false,
        simplification_level: SimplificationLevel::SL0,
        ..GraphOptions::default()
    };
    let got = system_to_dot_labeled(&sys, &opts, "l");
    let less: Vec<&str> = got.lines().filter(|l| l.contains("dashed")).collect();
    assert_eq!(
        less,
        vec!["n2:n0 -> n5:n4[color=\"blue3\",style=\"dashed\"];"],
        "{got}"
    );
}

/// graphviz's HTML-text escape keeps the first space of a run literal and
/// encodes the rest as `&#32;` (see [`escape_html_text`]) — the indentation of
/// a wrapped abbreviation expansion is the only place this is observable.
#[test]
fn html_text_escape_encodes_all_but_the_first_space_of_a_run() {
    assert_eq!(escape_html_text("a b"), "a b");
    assert_eq!(escape_html_text("    >,"), " &#32;&#32;&#32;&gt;,");
    assert_eq!(escape_html_text("<a & b>"), "&lt;a &amp; b&gt;");
}
