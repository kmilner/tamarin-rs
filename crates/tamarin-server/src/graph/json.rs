// Currently GPL 3.0 until granted permission by the following authors:
//   addap, Esslingen-Security-Privacy, Divya19gupta, arcz, meiersi,
//   kevinmorio, cascremers, gilcu3, jdreier, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/term/src/Term/VTerm.hs, lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Graph.hs,
//   lib/theory/src/Theory/Constraint/System/JSON.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs, src/Main/Mode/Batch.hs,
//   src/Web/Handler.hs, src/Web/Theory.hs

//! Port of `Theory.Constraint.System.JSON` — serialise the graph part of a
//! constraint [`System`] to the JSON graph format the interactive frontend
//! consumes (`<dot-graph-viz dotsrc=".../json/...">`).
//!
//! See `lib/theory/src/Theory/Constraint/System/JSON.hs`.
//!
//! Only the `sequentsToJSONPretty` variant (JSON.hs:553-558) is ported: it is
//! the one both the web handler (`src/Web/Handler.hs:1435-1444`) and the batch
//! trace export (`src/Main/Mode/Batch.hs`) call, so the HS `pretty` flag is
//! always `True` here — every fact carries its `prettyLNFact` rendering and
//! every outermost term its `show`n form.
//!
//! Output shape reproduces aeson-pretty's default `Config` (4-space indent,
//! no trailing newline) with the object keys in the alphabetical order
//! `Data.Aeson.Object` serialises them in.  HS post-processes the encoder's
//! `<`/`>` escapes back into literal `<`/`>` (`removePseudoUnicode`,
//! JSON.hs:225-229); `serde_json` never escapes those characters, so the
//! literal form comes out directly.

use serde_json::{Map, Value};

use tamarin_term::function_symbols::{plain_show_bytes, show_acfct_sym, AcSym, FunSym};
use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

use tamarin_theory::constraint::constraints::{NodeConc, NodeId, NodePrem, Reason};
use tamarin_theory::constraint::solver::tactic_show::show_lnterm;
use tamarin_theory::fact::{fact_tag_multiplicity, show_fact_tag, FactTag, LNFact, Multiplicity};
use tamarin_theory::pretty_hpj::{fsep, punctuate, Doc, WEB_LINE_LENGTH, WEB_RIBBON};
use tamarin_theory::rule::{
    is_coerce_rule_info, is_constr_rule_info, is_destr_rule_info, is_fresh_constr_rule_info,
    is_iequality_rule_info, is_irecv_rule_info, is_isend_rule_info, is_nat_constr_rule_info,
    is_pub_constr_rule_info, rule_name_string, ProtoRuleName, RuleACInst, RuleInfo,
};

use crate::graph::abbreviation::order_abbreviations_for_json;
use crate::graph::color::{build_node_color_map, fact_doc_of, reason_color, NodeColorMap};
use crate::graph::options::GraphOptions;
use crate::graph::render_system::RenderSystem;
use crate::graph::repr::{Cluster, GEdge, GNode, MissingHint, NodeType};
use crate::graph::{system_to_graph, Graph};

/// `NodeId → &RuleACInst` index over the ORIGINAL system, built once per
/// rendered graph.  HS's `resolveNodePremFact` / `resolveNodeConcFact`
/// (System.hs:926-931) are `M.lookup`s into `sNodes`; this crate stores the
/// nodes in a `Vec`, and every edge resolves up to two of them.
type NodeRules<'a> = tamarin_utils::FastMap<&'a NodeId, &'a RuleACInst>;

/// HS `resolveNodePremFact` (System.hs:926-927) via Graph.hs:87-90.
fn resolve_node_prem_fact<'a>(prem: &NodePrem, rules: &NodeRules<'a>) -> Option<&'a LNFact> {
    rules
        .get(&prem.0)
        .copied()
        .and_then(|ru| ru.premises.get(prem.1 .0))
}

/// HS `resolveNodeConcFact` (System.hs:930-931) via Graph.hs:93-96.
fn resolve_node_conc_fact<'a>(conc: &NodeConc, rules: &NodeRules<'a>) -> Option<&'a LNFact> {
    rules
        .get(&conc.0)
        .copied()
        .and_then(|ru| ru.conclusions.get(conc.1 .0))
}

// ---------------------------------------------------------------------
// String helpers
// ---------------------------------------------------------------------

/// Port of `cleanString` (JSON.hs:212-217) — flatten a rendered pretty-printer
/// document onto one line.
///
/// The HS equations rewrite and then RE-EXAMINE the rewritten prefix:
///
/// ```text
/// cleanString (' ':'\n':' ':xs) = cleanString (' ':xs)
/// cleanString ('\n':xs)         = cleanString xs
/// cleanString (' ':' ':xs)      = cleanString (' ':xs)
/// cleanString (c:xs)            = c : cleanString xs
/// ```
///
/// so a space is consed back onto the remaining input and matched again.  The
/// only equations a re-consed space can match are the first and the third, so
/// a space keeps absorbing `"\n "` and `" "` and is then emitted by the last
/// equation — which is what the inner loop does.
fn clean_string(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(chars.len());
    let mut i = 0usize;
    while let Some(&c) = chars.get(i) {
        i += 1;
        match c {
            '\n' => {}
            ' ' => {
                loop {
                    match (chars.get(i), chars.get(i + 1)) {
                        (Some('\n'), Some(' ')) => i += 2,
                        (Some(' '), _) => i += 1,
                        _ => break,
                    }
                }
                out.push(' ');
            }
            _ => out.push(c),
        }
    }
    out
}

/// Port of `pps` (JSON.hs:221-222) — `cleanString . render`.
///
/// HS `render` is HughesPJ's default `style` (PageMode, `lineLength = 100`,
/// `ribbonsPerLine = 1.5` ⇒ ribbon `round (100/1.5) = 67`), so a wide fact
/// wraps before `cleanString` flattens it back onto one line.
fn pps(d: Doc) -> String {
    clean_string(&d.render_with(WEB_LINE_LENGTH, WEB_RIBBON))
}

/// Derived `Show` of `ACSym` (FunctionSymbols.hs:138-139).  The `ACfct`
/// constructor's argument is a tuple, whose `showsPrec` ignores the operator
/// precedence, so no extra parentheses are added around it.
fn show_ac_sym(o: &AcSym) -> String {
    match o {
        AcSym::Union => "Union".to_string(),
        AcSym::Mult => "Mult".to_string(),
        AcSym::Xor => "Xor".to_string(),
        AcSym::NatPlus => "NatPlus".to_string(),
        AcSym::AcFct(sym) => format!("ACfct {}", show_acfct_sym(sym)),
    }
}

/// `show` of an `LNTerm` literal: `instance Show (Lit c v)` (VTerm.hs:98-100)
/// delegating to `instance Show LVar` (LTerm.hs:548-554) and `instance Show
/// Name` (LTerm.hs:235-240), both of which are the `Display` impls in
/// `tamarin_term::pretty`.
///
/// `Show Name` covers `FreshName` (`~'x'`), `PubName` (`'x'`), `NodeName`
/// (`#'x'`), `NatName` (`%'x'`) and `AbbrevName` (`x` — the bare id, see
/// [`crate::graph::web_utils_abbrev`]).
fn show_lit(l: &Lit<Name, LVar>) -> String {
    l.to_string()
}

// ---------------------------------------------------------------------
// Rule / edge classification
// ---------------------------------------------------------------------

/// Port of `getRuleType` (JSON.hs:237-250).  Guard ORDER is significant: the
/// generic `isIntruderRule` / `isProtocolRule` tests come last.
fn get_rule_type(ru: &RuleACInst) -> &'static str {
    match &ru.info {
        RuleInfo::Intr(i) => {
            // HS `isDestrRule` (Rule.hs:694-698) also covers `IEqualityRule`.
            if is_destr_rule_info(i) || is_iequality_rule_info(i) {
                "isDestrRule"
            } else if is_constr_rule_info(i)
                || is_fresh_constr_rule_info(i)
                || is_pub_constr_rule_info(i)
                || is_nat_constr_rule_info(i)
                || is_coerce_rule_info(i)
            {
                "isConstrRule"
            } else if is_irecv_rule_info(i) {
                "isIRecvRule"
            } else if is_isend_rule_info(i) {
                "isISendRule"
            } else {
                "isIntruderRule"
            }
        }
        RuleInfo::Proto(p) => {
            if p.name == ProtoRuleName::Fresh {
                "isFreshRule"
            } else {
                "isProtocolRule"
            }
        }
    }
}

/// HS `check p`, shared by `getRelationType` (JSON.hs:434-435) and `colorEdge`'s
/// `SystemEdge` arm (JSON.hs:452-453): the TARGET premise's fact is tested
/// first, then the SOURCE conclusion's.
fn edge_fact_check(prem: Option<&LNFact>, conc: Option<&LNFact>, p: fn(&LNFact) -> bool) -> bool {
    prem.is_some_and(p) || conc.is_some_and(p)
}

/// The single classification `graphEdgeToJSONGraphEdge` (JSON.hs:467-495) needs
/// per edge.
///
/// `getRelationType` (JSON.hs:432-441) and `colorEdge` (JSON.hs:444-463) walk
/// the IDENTICAL `check` cascade over a `SystemEdge`'s endpoint facts and
/// differ only in the string each arm yields, so an edge is classified once
/// and both strings are read off the result.
enum EdgeClass {
    SystemK,
    SystemPersistent,
    SystemProto,
    SystemDefault,
    UnsolvedChain,
    Less(Reason),
}

impl EdgeClass {
    /// `colorEdge` (JSON.hs:444-463).
    fn color(&self) -> &'static str {
        match self {
            EdgeClass::SystemK => "orangered2",
            EdgeClass::SystemPersistent => "gray50",
            EdgeClass::SystemProto => "black",
            EdgeClass::SystemDefault => "gray30",
            EdgeClass::UnsolvedChain => "green",
            EdgeClass::Less(r) => reason_color(*r),
        }
    }

    /// `jgeRelation` (JSON.hs:467-495): `getRelationType` for a `SystemEdge`,
    /// a literal for the other two edge kinds.
    fn relation(&self) -> &'static str {
        match self {
            EdgeClass::SystemK => "KFact",
            EdgeClass::SystemPersistent => "PersistentFact",
            EdgeClass::SystemProto => "ProtoFact",
            EdgeClass::SystemDefault => "default",
            EdgeClass::UnsolvedChain => "unsolvedChain",
            EdgeClass::Less(_) => "LessAtoms",
        }
    }
}

fn classify_edge(edge: &GEdge, rules: &NodeRules<'_>) -> EdgeClass {
    match edge {
        GEdge::System(src, tgt) => {
            let prem = resolve_node_prem_fact(tgt, rules);
            let conc = resolve_node_conc_fact(src, rules);
            if edge_fact_check(prem, conc, LNFact::is_k_fact) {
                EdgeClass::SystemK
            } else if edge_fact_check(prem, conc, LNFact::is_persistent) {
                EdgeClass::SystemPersistent
            } else if edge_fact_check(prem, conc, LNFact::is_proto) {
                EdgeClass::SystemProto
            } else {
                EdgeClass::SystemDefault
            }
        }
        GEdge::UnsolvedChain(_, _) => EdgeClass::UnsolvedChain,
        GEdge::Less(la) => EdgeClass::Less(la.reason),
    }
}

// ---------------------------------------------------------------------
// JSON construction
// ---------------------------------------------------------------------

/// Build a JSON object from `(key, value)` pairs inserted in the alphabetical
/// order `Data.Aeson` emits.
fn object<'a>(fields: impl IntoIterator<Item = (&'a str, Value)>) -> Value {
    let mut m = Map::new();
    for (k, v) in fields {
        m.insert(k.to_string(), v);
    }
    Value::Object(m)
}

/// Port of `lntermToJSONGraphNodeTerm` (JSON.hs:275-292) at `pretty = True`.
///
/// `jgnShow` is populated for the OUTERMOST term only and omitted entirely
/// when empty (JSON.hs:76-81), so nested subterms carry just `jgnFunct` /
/// `jgnParams`.  Terms that are neither a literal nor a `NoEq`/`AC`
/// application fall into HS's catch-all `Const ("unknown term type: " ++ show
/// t)`.
fn json_term(t: &LNTerm, outermost: bool) -> Value {
    let params =
        |ts: &[LNTerm]| -> Value { Value::Array(ts.iter().map(|a| json_term(a, false)).collect()) };
    let funct = |name: String, ts: &[LNTerm]| -> Value {
        let mut fields = vec![("jgnFunct", Value::String(name)), ("jgnParams", params(ts))];
        if outermost {
            fields.push(("jgnShow", Value::String(show_lnterm(t))));
        }
        object(fields)
    };
    match t {
        Term::Lit(l) => object([("jgnConst", Value::String(show_lit(l)))]),
        Term::App(FunSym::NoEq(s), ts) => funct(plain_show_bytes(s.name), ts),
        Term::App(FunSym::Ac(o), ts) => funct(show_ac_sym(o), ts),
        _ => object([(
            "jgnConst",
            Value::String(format!("unknown term type: {}", show_lnterm(t))),
        )]),
    }
}

/// Port of `itemToJSONGraphNodeFact` (JSON.hs:295-309) at `pretty = True`.
fn json_fact(id: String, f: &LNFact) -> Value {
    // `show (factTag f)` is the DERIVED Show of `FactTag`
    // (Fact.hs:137-148); the `ProtoFact` constructor never reaches it
    // because `isProtoFact` short-circuits to the literal "ProtoFact".
    let tag = match f.tag {
        FactTag::Proto(_, _, _) => "ProtoFact",
        FactTag::Fresh => "FreshFact",
        FactTag::Out => "OutFact",
        FactTag::In => "InFact",
        FactTag::Ku => "KUFact",
        FactTag::Kd => "KDFact",
        FactTag::Ded => "DedFact",
        FactTag::Term => "TermFact",
    };
    let mult = match fact_tag_multiplicity(&f.tag) {
        Multiplicity::Linear => "",
        Multiplicity::Persistent => "!",
    };
    object([
        ("jgnFactId", Value::String(id)),
        ("jgnFactMult", Value::String(mult.to_string())),
        ("jgnFactName", Value::String(show_fact_tag(&f.tag))),
        ("jgnFactShow", Value::String(pps(fact_doc_of(f)))),
        ("jgnFactTag", Value::String(tag.to_string())),
        (
            "jgnFactTerms",
            Value::Array(f.terms.iter().map(|t| json_term(t, true)).collect()),
        ),
    ])
}

/// Port of `factToJSONGraphNodeFact` (JSON.hs:315-317): premise/conclusion
/// facts are identified by `<node>:<prefix><index>`, 0-based.
fn json_indexed_fact(prefix: &str, n: &NodeId, idx: usize, f: &LNFact) -> Value {
    json_fact(format!("{}:{}{}", n, prefix, idx), f)
}

/// `jgnActs` (JSON.hs:335 and JSON.hs:365): every action fact carries the
/// constant id "action"; only premise/conclusion facts get a record port.
fn json_action_facts(facts: &[LNFact]) -> Value {
    Value::Array(
        facts
            .iter()
            .map(|f| json_fact("action".to_string(), f))
            .collect(),
    )
}

/// Port of `nodeToJSONGraphNodeMetadata` (JSON.hs:321-328).
fn json_metadata(n: &NodeId, ru: &RuleACInst) -> Value {
    object([
        ("jgnActs", json_action_facts(&ru.actions)),
        (
            "jgnConcs",
            Value::Array(
                ru.conclusions
                    .iter()
                    .enumerate()
                    .map(|(i, f)| json_indexed_fact("c", n, i, f))
                    .collect(),
            ),
        ),
        (
            "jgnPrems",
            Value::Array(
                ru.premises
                    .iter()
                    .enumerate()
                    .map(|(i, f)| json_indexed_fact("p", n, i, f))
                    .collect(),
            ),
        ),
    ])
}

/// A `JSONGraphNodeFact` with only its id set — the stub HS emits for a node
/// referenced by an edge but absent from `sNodes` (JSON.hs:385-392/405-412).
fn json_stub_fact(id: String) -> Value {
    object([
        ("jgnFactId", Value::String(id)),
        ("jgnFactMult", Value::String(String::new())),
        ("jgnFactName", Value::String(String::new())),
        ("jgnFactShow", Value::String(String::new())),
        ("jgnFactTag", Value::String(String::new())),
        ("jgnFactTerms", Value::Array(Vec::new())),
    ])
}

/// Port of `graphNodeToJSONGraphNode` (JSON.hs:331-418).  `jgnMetadata` and
/// `jgnColor` are omitted when absent (JSON.hs:200-207).
fn json_node(node: &GNode, color_map: &NodeColorMap) -> Value {
    let nid = node.id.to_string();
    match &node.ty {
        NodeType::System(ru) => {
            let mut fields: Vec<(&str, Value)> = Vec::with_capacity(5);
            if let Some(rgb) = color_map.lookup_node(&node.id) {
                fields.push((
                    "jgnColor",
                    Value::String(tamarin_utils::color::rgb_to_hex(rgb)),
                ));
            }
            fields.push(("jgnId", Value::String(nid)));
            fields.push(("jgnLabel", Value::String(rule_name_string(ru))));
            fields.push(("jgnMetadata", json_metadata(&node.id, ru)));
            fields.push(("jgnType", Value::String(get_rule_type(ru).to_string())));
            object(fields)
        }
        NodeType::UnsolvedAction(facts) => {
            // `pps $ fsep $ punctuate comma $ map prettyLNFact facts`.
            let label = pps(fsep(punctuate(
                Doc::char(','),
                facts.iter().map(fact_doc_of).collect(),
            )));
            object([
                ("jgnId", Value::String(nid)),
                ("jgnLabel", Value::String(label)),
                (
                    "jgnMetadata",
                    object([
                        ("jgnActs", json_action_facts(facts)),
                        ("jgnConcs", Value::Array(Vec::new())),
                        ("jgnPrems", Value::Array(Vec::new())),
                    ]),
                ),
                ("jgnType", Value::String("unsolvedActionAtom".to_string())),
            ])
        }
        NodeType::LastAction => object([
            ("jgnId", Value::String(nid.clone())),
            ("jgnLabel", Value::String(nid)),
            ("jgnType", Value::String("lastAtom".to_string())),
        ]),
        NodeType::Missing(hint) => {
            // HS ignores the recorded conclusion/premise index and always
            // emits `c0` / `p0` here (JSON.hs:374-375).
            let stub =
                |port: char| Value::Array(vec![json_stub_fact(format!("{}:{}0", nid, port))]);
            let (ty, concs, prems) = match hint {
                MissingHint::Conc(_) => ("missingNodeConc", stub('c'), Value::Array(Vec::new())),
                MissingHint::Prem(_) => ("missingNodePrem", Value::Array(Vec::new()), stub('p')),
            };
            object([
                ("jgnId", Value::String(nid)),
                ("jgnLabel", Value::String(String::new())),
                (
                    "jgnMetadata",
                    object([
                        ("jgnActs", Value::Array(Vec::new())),
                        ("jgnConcs", concs),
                        ("jgnPrems", prems),
                    ]),
                ),
                ("jgnType", Value::String(ty.to_string())),
            ])
        }
    }
}

/// Port of `graphEdgeToJSONGraphEdge` (JSON.hs:467-495).  Less-edges address
/// their endpoints by bare node id; the other two kinds use record ports.
fn json_edge(edge: &GEdge, rules: &NodeRules<'_>) -> Value {
    let class = classify_edge(edge, rules);
    let color = Value::String(class.color().to_string());
    let relation = Value::String(class.relation().to_string());
    match edge {
        GEdge::System(src, tgt) | GEdge::UnsolvedChain(src, tgt) => object([
            ("jgeColor", color),
            ("jgeRelation", relation),
            (
                "jgeSource",
                Value::String(format!("{}:c{}", src.0, src.1 .0)),
            ),
            (
                "jgeTarget",
                Value::String(format!("{}:p{}", tgt.0, tgt.1 .0)),
            ),
        ]),
        GEdge::Less(la) => object([
            ("jgeColor", color),
            ("jgeRelation", relation),
            ("jgeSource", Value::String(la.smaller.to_string())),
            ("jgeTarget", Value::String(la.larger.to_string())),
        ]),
    }
}

/// Port of `graphClusterToJSONGraphCluster` (JSON.hs:488-496).
fn json_cluster(cluster: &Cluster, rules: &NodeRules<'_>, color_map: &NodeColorMap) -> Value {
    object([
        (
            "jgcEdges",
            Value::Array(cluster.edges.iter().map(|e| json_edge(e, rules)).collect()),
        ),
        ("jgcName", Value::String(cluster.name.clone())),
        (
            "jgcNodes",
            Value::Array(
                cluster
                    .nodes
                    .iter()
                    .map(|n| json_node(n, color_map))
                    .collect(),
            ),
        ),
    ])
}

/// Port of `sequentToJSONGraph` (JSON.hs:510-529).
fn json_graph(label: &str, graph: &Graph<'_>, color_map: &NodeColorMap) -> Value {
    // One index over the original system's nodes for every edge of this graph.
    let rules = graph.system.node_rule_map();
    object([
        (
            "jgAbbrevs",
            Value::Array(
                order_abbreviations_for_json(&graph.abbreviations)
                    .into_iter()
                    // `graphAbbrevtoJSONGraphAbbrev` (JSON.hs:499-506).
                    .map(|(term, abbrev, expansion)| {
                        object([
                            ("jgaAbbrev", json_term(abbrev, true)),
                            ("jgaExpansion", json_term(expansion, true)),
                            ("jgaTerm", json_term(term, true)),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "jgClusters",
            Value::Array(
                graph
                    .repr
                    .clusters
                    .iter()
                    .map(|c| json_cluster(c, &rules, color_map))
                    .collect(),
            ),
        ),
        ("jgDirected", Value::Bool(true)),
        (
            "jgEdges",
            Value::Array(
                graph
                    .repr
                    .edges
                    .iter()
                    .map(|e| json_edge(e, &rules))
                    .collect(),
            ),
        ),
        ("jgLabel", Value::String(label.to_string())),
        (
            "jgNodes",
            Value::Array(
                graph
                    .repr
                    .nodes
                    .iter()
                    .map(|n| json_node(n, color_map))
                    .collect(),
            ),
        ),
        (
            "jgType",
            Value::String("Tamarin prover constraint system".to_string()),
        ),
    ])
}

/// Port of `sequentsToJSONPretty` (JSON.hs:553-558).
///
/// Renders `{"graphs": [...]}` with aeson-pretty's default 4-space indent and
/// NO trailing newline.  The node colour palette is keyed off each system's
/// RAW `sNodes` (`nodeColorMap (M.elems $ get sNodes system)`), i.e. before
/// compression/simplification.
///
/// Upstream keeps the encoder's output a `ByteString` all the way to
/// `BL.writeFile` (JSON.hs:564-569, `src/Web/Theory.hs:1335-1340`), so the
/// wire bytes are the document's own UTF-8 — which is what writing this
/// `String` out as UTF-8 produces.
///
/// The inputs are [`RenderSystem`]s: this endpoint is reached with systems
/// that `web_utils_abbrev::abbrev` may have rewritten into a display-only
/// shape, so the whole route is typed render-only from that boundary on.
pub fn sequents_to_json_pretty(
    graph_options: &GraphOptions,
    systems: &[(String, &RenderSystem)],
) -> String {
    let graphs: Vec<Value> = systems
        .iter()
        .map(|(label, system)| {
            let graph = system_to_graph(system, graph_options);
            let color_map = build_node_color_map(&system.nodes);
            json_graph(label, &graph, &color_map)
        })
        .collect();
    let root = object([("graphs", Value::Array(graphs))]);
    // `removePseudoUnicode $ encodePretty graphJSON`: the `<`/`>` unescaping
    // is a no-op against `serde_json`, whose output never contains the
    // `<`/`>` escapes it rewrites (see the module docs).
    to_pretty_string(&root)
}

/// aeson-pretty `encodePretty` layout: 4-space indent, `": "` between key and
/// value, empty arrays/objects inline, no trailing newline.
fn to_pretty_string(v: &Value) -> String {
    let mut buf: Vec<u8> = Vec::new();
    let formatter = serde_json::ser::PrettyFormatter::with_indent(b"    ");
    let mut ser = serde_json::Serializer::with_formatter(&mut buf, formatter);
    serde::Serialize::serialize(v, &mut ser).expect("serialising a serde_json::Value cannot fail");
    String::from_utf8(buf).expect("serde_json emits UTF-8")
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::{f_app_no_eq, lit};
    use tamarin_theory::constraint::system::System;
    use tamarin_theory::fact::Fact;

    fn var(name: &str, sort: LSort) -> LNTerm {
        lit(Lit::Var(LVar::new(name, sort, 0)))
    }

    fn sym(name: &str, arity: usize) -> NoEqSym {
        NoEqSym::new(
            name.as_bytes().to_vec(),
            arity,
            Privacy::Public,
            Constructability::Constructor,
        )
    }

    // `cleanString` collapses the wrapped output of the pretty-printer: a
    // `" \n "` run becomes a single space (and is re-examined, so a following
    // space collapses too), a bare newline vanishes, and doubled spaces
    // collapse.
    #[test]
    fn clean_string_flattens_wrapped_render() {
        assert_eq!(clean_string("a \n b"), "a b");
        assert_eq!(clean_string("a\nb"), "ab");
        assert_eq!(clean_string("a    b"), "a b");
        assert_eq!(clean_string("a \n    b"), "a b");
        assert_eq!(clean_string(""), "");
        // A leading `\n` is dropped, then the re-consed space collapses with
        // the indentation that follows.
        assert_eq!(clean_string("\n   x"), " x");
    }

    // `show` of a term is NOT `prettyLNTerm`: arguments are comma-separated
    // without spaces and pairs stay in `pair(a,b)` form.
    #[test]
    fn raw_show_matches_haskell_show_instance() {
        let pair = f_app_no_eq(
            tamarin_term::function_symbols::pair_sym(),
            vec![
                lit(Lit::Con(Name::new(NameTag::Pub, "3"))),
                var("nr", LSort::Fresh),
            ],
        );
        let pk = f_app_no_eq(sym("pk", 1), vec![var("ltkA", LSort::Fresh)]);
        let t = f_app_no_eq(sym("aenc", 2), vec![pair, pk]);
        assert_eq!(show_lnterm(&t), "aenc(pair('3',~nr),pk(~ltkA))");
        // A nullary NoEq symbol shows as the bare name (no parentheses).
        assert_eq!(show_lnterm(&f_app_no_eq(sym("g", 0), vec![])), "g");
    }

    // `jgnShow` is present on the OUTERMOST term only, and omitted entirely
    // (rather than emitted as "") on nested subterms and on literals.
    #[test]
    fn jgn_show_only_on_outermost_term() {
        let t = f_app_no_eq(sym("pk", 1), vec![var("ltkA", LSort::Fresh)]);
        let v = json_term(&t, true);
        assert_eq!(v["jgnShow"], Value::String("pk(~ltkA)".into()));
        assert_eq!(v["jgnParams"][0].get("jgnShow"), None);
        assert_eq!(v["jgnParams"][0]["jgnConst"], Value::String("~ltkA".into()));
        assert_eq!(json_term(&t, false).get("jgnShow"), None);
    }

    // `jgnFactShow` is `pps (prettyLNFact f)`: the fact is rendered through
    // HughesPJ at 100/67, so a wide fact WRAPS, and `cleanString` then folds
    // the wrapped output back onto one line with single spaces.  Expected
    // strings captured from the Haskell oracle for a fact whose one-line form
    // is 341 columns wide.
    #[test]
    fn wide_fact_render_is_flattened_back_to_one_line() {
        // `g(f(~x, f(~x, … f(~x, ~x)…)))` with 20 nested `f` applications.
        let nest = |x: &LNTerm| -> LNTerm {
            let mut t = x.clone();
            for _ in 0..20 {
                t = f_app_no_eq(sym("f", 2), vec![x.clone(), t]);
            }
            f_app_no_eq(sym("g", 1), vec![t])
        };
        let x0 = var("x", LSort::Fresh);
        let x1 = lit(Lit::Var(LVar::new("x", LSort::Fresh, 1)));
        let (t0, t1) = (nest(&x0), nest(&x1));
        assert_eq!(
            show_lnterm(&t0),
            "g(f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,\
             f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,f(~x,~x)))))))))))))))))))))"
        );
        let fa: LNFact = Fact::new(
            FactTag::Proto(
                Multiplicity::Linear,
                tamarin_term::intern::intern_str("Done"),
                2,
            ),
            vec![t0, t1],
        );
        assert_eq!(
            pps(fact_doc_of(&fa)),
            "Done( g(f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, \
             f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, f(~x, \
             ~x))))))))))))))))))))), g(f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, \
             f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, \
             f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, f(~x.1, \
             ~x.1))))))))))))))))))))))"
        );
    }

    // The document reaches the wire as its own UTF-8, so the `⊕` an xor term's
    // pretty form carries is the three bytes `E2 8A 95` — not the `C3 A2 C2 8A
    // C2 95` a `String` round-trip would produce.
    #[test]
    fn json_body_keeps_non_ascii_label_in_utf8() {
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[(
                "Theory: ⊕".to_string(),
                &RenderSystem::from_prover(System::default()),
            )],
        );
        assert!(
            out.as_bytes().windows(3).any(|w| w == b"\xe2\x8a\x95"),
            "label must carry the UTF-8 ⊕"
        );
        assert!(
            !out.as_bytes()
                .windows(6)
                .any(|w| w == b"\xc3\xa2\xc2\x8a\xc2\x95"),
            "the doubly-encoded form must not appear"
        );
    }

    // Derived `Show ACSym`: the plain constructors are bare names, `ACfct`
    // renders its `(name,(privacy,constructability,ndc))` tuple argument.
    #[test]
    fn ac_sym_show_matches_derived_show() {
        assert_eq!(show_ac_sym(&AcSym::Mult), "Mult");
        assert_eq!(show_ac_sym(&AcSym::NatPlus), "NatPlus");
        let f = AcFctSym::new(
            b"bar".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        assert_eq!(
            show_ac_sym(&AcSym::AcFct(f)),
            "ACfct (\"bar\",(Public,Constructor,NotNDC))"
        );
    }

    // The empty system serialises to the `root.json` fixture captured from the
    // Haskell oracle: 4-space indent, alphabetical keys, empty arrays inline,
    // and no trailing newline.
    #[test]
    fn empty_system_matches_root_fixture() {
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[(
                "Theory: NSPK3 Lemma: injective_agree".to_string(),
                &RenderSystem::from_prover(System::default()),
            )],
        );
        assert_eq!(out, include_str!("../../tests/assets/hsjson_root.json"));
    }

    // A single unsolved action atom reproduces the `simplify.json` fixture:
    // node id / label / metadata layout, `jgnFactTag` "ProtoFact", and the
    // `prettyLNFact` spacing in `jgnFactShow`.
    #[test]
    fn unsolved_action_atom_matches_simplify_fixture() {
        use tamarin_theory::constraint::constraints::Goal;
        use tamarin_theory::constraint::system::GoalStatus;
        let mut sys = System::default();
        let nid = LVar::new("i", LSort::Node, 0);
        let fa: LNFact = Fact::new(
            FactTag::Proto(
                Multiplicity::Linear,
                tamarin_term::intern::intern_str("Commit"),
                3,
            ),
            vec![
                var("actor", LSort::Msg),
                var("peer", LSort::Msg),
                var("params", LSort::Msg),
            ],
        );
        sys.goals_mut()
            .push((Goal::Action(nid, fa), GoalStatus::default()));
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[(
                "Theory: NSPK3 Lemma: injective_agree".to_string(),
                &RenderSystem::from_prover(sys),
            )],
        );
        assert_eq!(out, include_str!("../../tests/assets/hsjson_simplify.json"));
    }
}
