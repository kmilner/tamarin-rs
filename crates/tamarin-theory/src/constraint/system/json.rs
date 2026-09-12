// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Constraint.System.JSON` — serialise the graph part of a
//! constraint [`System`] to the JSON graph format the interactive frontend
//! consumes (`<dot-graph-viz dotsrc=".../json/...">`).
//!
//! See `lib/theory/src/Theory/Constraint/System/JSON.hs`.
//!
//! Only the `sequentsToJSONPretty` variant (JSON.hs:564-569) is ported: it is
//! the one both the web handler (`src/Web/Handler.hs:1435-1444`) and the batch
//! trace export (`src/Main/Mode/Batch.hs`) call, so the HS `pretty` flag is
//! always `True` here — every fact carries its `prettyLNFact` rendering and
//! every outermost term its `show`n form.
//!
//! The bytes come out of `write_value`, a port of aeson-pretty's
//! `encodePretty` at `defConfig` (4-space indent, `": "` between key and
//! value, empty containers inline, no trailing newline) over
//! `Data.Aeson.Text`'s string escaper — aeson-pretty's `fromValue` hands
//! every scalar to `Aeson.encodeToTextBuilder` — followed by
//! `removePseudoUnicode` (JSON.hs:228-239).  That escaper differs from
//! `serde_json`'s: 0x08 and 0x0c take the generic `\u00xx` form where
//! `serde_json` emits `\b` / `\f`, so the encoder cannot be delegated to
//! `serde_json`.  `<`, `>` and `&` all reach the wire literally
//! (oracle-verified: a pub name `'a&b'` arrives as a literal `&`), so
//! `removePseudoUnicode` can only bite payload text that itself spells out
//! the six characters of a `\u003c` / `\u003e` escape.  Object keys are
//! emitted in the ascending order `Data.Aeson.Object` serialises them in,
//! which is what our `BTreeMap` iteration yields.

use std::collections::BTreeMap;

use tamarin_term::function_symbols::{plain_show_bytes, show_acfct_sym, AcSym, FunSym};
use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::term::{show_term, Term};
use tamarin_term::vterm::Lit;

use crate::constraint::constraints::{NodeConc, NodeId, NodePrem, Reason};
use crate::fact::{
    fact_tag_multiplicity, is_proto_fact, show_fact_tag, FactTag, LNFact, Multiplicity,
};
use crate::pretty_hpj::{fsep, punctuate, Doc, DEFAULT_LINE_LENGTH, DEFAULT_RIBBON};
use crate::rule::{
    is_constr_rule, is_destr_rule, is_irecv_rule_info, is_isend_rule_info, rule_name_string,
    ProtoRuleName, RuleACInst, RuleInfo,
};

use crate::constraint::system::graph::abbreviation::order_abbreviations_for_json;
use crate::constraint::system::graph::color::{
    build_node_color_map, fact_doc_of, reason_color, NodeColorMap,
};
use crate::constraint::system::graph::options::GraphOptions;
use crate::constraint::system::graph::render_system::RenderSystem;
use crate::constraint::system::graph::repr::{Cluster, GEdge, GNode, MissingHint, NodeType};
use crate::constraint::system::graph::{system_to_graph, Graph};
use crate::constraint::system::NodeRuleMap;

/// Graph structure is shallow. Terms retain their existing shared ownership
/// and expand one level at a time through the same JSON writer, avoiding a
/// second deeply nested tree with recursive construction and destruction.
enum Json {
    Object(BTreeMap<String, Json>),
    Array(Vec<Json>),
    String(String),
    Bool(bool),
    Term(LNTerm, bool),
}

/// HS `resolveNodePremFact` (System.hs:928-929) via Graph.hs:87-90.
fn resolve_node_prem_fact<'a>(prem: &NodePrem, rules: &NodeRuleMap<'a>) -> Option<&'a LNFact> {
    rules
        .get(&prem.0)
        .copied()
        .and_then(|ru| ru.premises.get(prem.1 .0))
}

/// HS `resolveNodeConcFact` (System.hs:932-933) via Graph.hs:93-96.
fn resolve_node_conc_fact<'a>(conc: &NodeConc, rules: &NodeRuleMap<'a>) -> Option<&'a LNFact> {
    rules
        .get(&conc.0)
        .copied()
        .and_then(|ru| ru.conclusions.get(conc.1 .0))
}

// ---------------------------------------------------------------------
// String helpers
// ---------------------------------------------------------------------

/// Port of `cleanString` (JSON.hs:213-218) — flatten a rendered pretty-printer
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
    clean_string(&d.render_with(DEFAULT_LINE_LENGTH, DEFAULT_RIBBON))
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
/// delegating to `instance Show LVar` (LTerm.hs:550-557) and `instance Show
/// Name` (LTerm.hs:235-240), both of which are the `Display` impls in
/// `tamarin_term::pretty`.
///
/// `Show Name` covers `FreshName` (`~'x'`), `PubName` (`'x'`), `NodeName`
/// (`#'x'`), `NatName` (`%'x'`) and `AbbrevName` (`x` — the bare id, see
/// tamarin-server's `web_utils_abbrev`).
fn show_lit(l: &Lit<Name, LVar>) -> String {
    l.to_string()
}

// ---------------------------------------------------------------------
// Rule / edge classification
// ---------------------------------------------------------------------

/// Port of `getRuleType` (JSON.hs:247-260).  Guard ORDER is significant: the
/// generic `isIntruderRule` / `isProtocolRule` tests come last.
fn get_rule_type(ru: &RuleACInst) -> &'static str {
    match &ru.info {
        RuleInfo::Intr(i) => {
            if is_destr_rule(i) {
                "isDestrRule"
            } else if is_constr_rule(i) {
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

fn classify_edge(edge: &GEdge, rules: &NodeRuleMap<'_>) -> EdgeClass {
    match edge {
        GEdge::System(src, tgt) => {
            let prem = resolve_node_prem_fact(tgt, rules);
            let conc = resolve_node_conc_fact(src, rules);
            if edge_fact_check(prem, conc, LNFact::is_k_fact) {
                EdgeClass::SystemK
            } else if edge_fact_check(prem, conc, LNFact::is_persistent) {
                EdgeClass::SystemPersistent
            } else if edge_fact_check(prem, conc, is_proto_fact) {
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
fn object<'a>(fields: impl IntoIterator<Item = (&'a str, Json)>) -> Json {
    let mut m = BTreeMap::new();
    for (k, v) in fields {
        m.insert(k.to_string(), v);
    }
    Json::Object(m)
}

/// Port of `lntermToJSONGraphNodeTerm` (JSON.hs:285-302) at `pretty = True`.
///
/// `jgnShow` is populated for the OUTERMOST term only and omitted entirely
/// when empty (JSON.hs:77-82), so nested subterms carry just `jgnFunct` /
/// `jgnParams`.  Terms that are neither a literal nor a `NoEq`/`AC`
/// application fall into HS's catch-all `Const ("unknown term type: " ++ show
/// t)`.
fn json_term(t: &LNTerm, outermost: bool) -> Json {
    Json::Term(t.clone(), outermost)
}

// Expand only this node. Child terms remain shared until the writer reaches them.
fn term_object(t: &LNTerm, outermost: bool) -> Json {
    let params =
        |ts: &[LNTerm]| -> Json { Json::Array(ts.iter().map(|a| json_term(a, false)).collect()) };
    let funct = |name: String, ts: &[LNTerm]| -> Json {
        let mut fields = vec![("jgnFunct", Json::String(name)), ("jgnParams", params(ts))];
        if outermost {
            fields.push(("jgnShow", Json::String(show_term(t))));
        }
        object(fields)
    };
    match t {
        Term::Lit(l) => object([("jgnConst", Json::String(show_lit(l)))]),
        Term::App(FunSym::NoEq(s), ts) => funct(plain_show_bytes(s.name), ts),
        Term::App(FunSym::Ac(o), ts) => funct(show_ac_sym(o), ts),
        _ => object([(
            "jgnConst",
            Json::String(format!("unknown term type: {}", show_term(t))),
        )]),
    }
}

/// Port of `itemToJSONGraphNodeFact` (JSON.hs:305-319) at `pretty = True`.
fn json_fact(id: String, f: &LNFact) -> Json {
    // `show (factTag f)` is the DERIVED Show of `FactTag`
    // (Theory/Model/Fact.hs:137-148); the `ProtoFact` constructor never reaches it
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
        ("jgnFactId", Json::String(id)),
        ("jgnFactMult", Json::String(mult.to_string())),
        ("jgnFactName", Json::String(show_fact_tag(&f.tag))),
        ("jgnFactShow", Json::String(pps(fact_doc_of(f)))),
        ("jgnFactTag", Json::String(tag.to_string())),
        (
            "jgnFactTerms",
            Json::Array(f.terms.iter().map(|t| json_term(t, true)).collect()),
        ),
    ])
}

/// Port of `factToJSONGraphNodeFact` (JSON.hs:325-327): premise/conclusion
/// facts are identified by `<node>:<prefix><index>`, 0-based.
fn json_indexed_fact(prefix: &str, n: &NodeId, idx: usize, f: &LNFact) -> Json {
    json_fact(format!("{}:{}{}", n, prefix, idx), f)
}

/// `jgnActs` (JSON.hs:335 and JSON.hs:365): every action fact carries the
/// constant id "action"; only premise/conclusion facts get a record port.
fn json_action_facts(facts: &[LNFact]) -> Json {
    Json::Array(
        facts
            .iter()
            .map(|f| json_fact("action".to_string(), f))
            .collect(),
    )
}

/// Port of `nodeToJSONGraphNodeMetadata` (JSON.hs:331-338).
fn json_metadata(n: &NodeId, ru: &RuleACInst) -> Json {
    object([
        ("jgnActs", json_action_facts(&ru.actions)),
        (
            "jgnConcs",
            Json::Array(
                ru.conclusions
                    .iter()
                    .enumerate()
                    .map(|(i, f)| json_indexed_fact("c", n, i, f))
                    .collect(),
            ),
        ),
        (
            "jgnPrems",
            Json::Array(
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
/// referenced by an edge but absent from `sNodes` (JSON.hs:395-402/415-422).
fn json_stub_fact(id: String) -> Json {
    object([
        ("jgnFactId", Json::String(id)),
        ("jgnFactMult", Json::String(String::new())),
        ("jgnFactName", Json::String(String::new())),
        ("jgnFactShow", Json::String(String::new())),
        ("jgnFactTag", Json::String(String::new())),
        ("jgnFactTerms", Json::Array(Vec::new())),
    ])
}

/// Port of `graphNodeToJSONGraphNode` (JSON.hs:341-428).  `jgnMetadata` and
/// `jgnColor` are omitted when absent (JSON.hs:201-208).
fn json_node(node: &GNode, color_map: &NodeColorMap) -> Json {
    let nid = node.id.to_string();
    match &node.ty {
        NodeType::System(ru) => {
            let mut fields: Vec<(&str, Json)> = Vec::with_capacity(5);
            if let Some(rgb) = color_map.lookup_node(&node.id) {
                fields.push((
                    "jgnColor",
                    Json::String(tamarin_utils::color::rgb_to_hex(rgb)),
                ));
            }
            fields.push(("jgnId", Json::String(nid)));
            fields.push(("jgnLabel", Json::String(rule_name_string(ru))));
            fields.push(("jgnMetadata", json_metadata(&node.id, ru)));
            fields.push(("jgnType", Json::String(get_rule_type(ru).to_string())));
            object(fields)
        }
        NodeType::UnsolvedAction(facts) => {
            // `pps $ fsep $ punctuate comma $ map prettyLNFact facts`.
            let label = pps(fsep(punctuate(
                Doc::char(','),
                facts.iter().map(fact_doc_of).collect(),
            )));
            object([
                ("jgnId", Json::String(nid)),
                ("jgnLabel", Json::String(label)),
                (
                    "jgnMetadata",
                    object([
                        ("jgnActs", json_action_facts(facts)),
                        ("jgnConcs", Json::Array(Vec::new())),
                        ("jgnPrems", Json::Array(Vec::new())),
                    ]),
                ),
                ("jgnType", Json::String("unsolvedActionAtom".to_string())),
            ])
        }
        NodeType::LastAction => object([
            ("jgnId", Json::String(nid.clone())),
            ("jgnLabel", Json::String(nid)),
            ("jgnType", Json::String("lastAtom".to_string())),
        ]),
        NodeType::Missing(hint) => {
            // HS ignores the recorded conclusion/premise index and always
            // emits `c0` / `p0` here (the two `MissingNode` branches,
            // JSON.hs:384-428, and the `a.d. TODO` at line 385 that says so).
            let stub = |port: char| Json::Array(vec![json_stub_fact(format!("{}:{}0", nid, port))]);
            let (ty, concs, prems) = match hint {
                MissingHint::Conc(_) => ("missingNodeConc", stub('c'), Json::Array(Vec::new())),
                MissingHint::Prem(_) => ("missingNodePrem", Json::Array(Vec::new()), stub('p')),
            };
            object([
                ("jgnId", Json::String(nid)),
                ("jgnLabel", Json::String(String::new())),
                (
                    "jgnMetadata",
                    object([
                        ("jgnActs", Json::Array(Vec::new())),
                        ("jgnConcs", concs),
                        ("jgnPrems", prems),
                    ]),
                ),
                ("jgnType", Json::String(ty.to_string())),
            ])
        }
    }
}

/// Port of `graphEdgeToJSONGraphEdge` (JSON.hs:467-495).  Less-edges address
/// their endpoints by bare node id; the other two kinds use record ports.
fn json_edge(edge: &GEdge, rules: &NodeRuleMap<'_>) -> Json {
    let class = classify_edge(edge, rules);
    let color = Json::String(class.color().to_string());
    let relation = Json::String(class.relation().to_string());
    match edge {
        GEdge::System(src, tgt) | GEdge::UnsolvedChain(src, tgt) => object([
            ("jgeColor", color),
            ("jgeRelation", relation),
            (
                "jgeSource",
                Json::String(format!("{}:c{}", src.0, src.1 .0)),
            ),
            (
                "jgeTarget",
                Json::String(format!("{}:p{}", tgt.0, tgt.1 .0)),
            ),
        ]),
        GEdge::Less(la) => object([
            ("jgeColor", color),
            ("jgeRelation", relation),
            ("jgeSource", Json::String(la.smaller.to_string())),
            ("jgeTarget", Json::String(la.larger.to_string())),
        ]),
    }
}

/// Port of `graphClusterToJSONGraphCluster` (JSON.hs:498-506).
fn json_cluster(cluster: &Cluster, rules: &NodeRuleMap<'_>, color_map: &NodeColorMap) -> Json {
    object([
        (
            "jgcEdges",
            Json::Array(cluster.edges.iter().map(|e| json_edge(e, rules)).collect()),
        ),
        ("jgcName", Json::String(cluster.name.clone())),
        (
            "jgcNodes",
            Json::Array(
                cluster
                    .nodes
                    .iter()
                    .map(|n| json_node(n, color_map))
                    .collect(),
            ),
        ),
    ])
}

/// Port of `sequentToJSONGraph` (JSON.hs:520-539).
fn json_graph(label: &str, graph: &Graph<'_>, color_map: &NodeColorMap) -> Json {
    // One index over the original system's nodes for every edge of this graph.
    let rules = graph.system.node_rule_map();
    object([
        (
            "jgAbbrevs",
            Json::Array(
                order_abbreviations_for_json(&graph.abbreviations)
                    .into_iter()
                    // `graphAbbrevtoJSONGraphAbbrev` (JSON.hs:509-516).
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
            Json::Array(
                graph
                    .repr
                    .clusters
                    .iter()
                    .map(|c| json_cluster(c, &rules, color_map))
                    .collect(),
            ),
        ),
        ("jgDirected", Json::Bool(true)),
        (
            "jgEdges",
            Json::Array(
                graph
                    .repr
                    .edges
                    .iter()
                    .map(|e| json_edge(e, &rules))
                    .collect(),
            ),
        ),
        ("jgLabel", Json::String(label.to_string())),
        (
            "jgNodes",
            Json::Array(
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
            Json::String("Tamarin prover constraint system".to_string()),
        ),
    ])
}

/// Port of `sequentsToJSONPretty` (JSON.hs:564-569).
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
    let mut out = Vec::new();
    write_sequents_json_pretty(
        graph_options,
        systems.iter().map(|(l, s)| (l.as_str(), *s)),
        &mut out,
    )
    .expect("Vec<u8> writes are infallible");
    // The writer emits only `escape_into`-escaped strings and ASCII frame
    // bytes, so the document is valid UTF-8 by construction.
    String::from_utf8(out).expect("the JSON writer emits UTF-8")
}

/// [`sequents_to_json_pretty`] streamed into a writer, one graph at a time —
/// the batch `--output-json` path (HS `BL.writeFile`, Batch.hs:270-272),
/// where holding every graph's `Json` tree plus the finished document would
/// scale peak RSS with total output size instead of the largest graph.
///
/// Byte-identical to rendering the whole document at once: the frame bytes
/// around each graph contain no `\`, so a `removePseudoUnicode` needle
/// (see [`remove_pseudo_unicode`]) can never straddle a chunk boundary, and
/// applying the rewrite per graph chunk equals applying it to the whole
/// document.
pub fn write_sequents_json_pretty<L, R, W>(
    graph_options: &GraphOptions,
    systems: impl IntoIterator<Item = (L, R)>,
    w: &mut W,
) -> std::io::Result<()>
where
    L: AsRef<str>,
    R: std::borrow::Borrow<RenderSystem>,
    W: std::io::Write,
{
    // The frame `write_value` gives `object([("graphs", Json::Array(…))])`:
    // root object at level 0, the array's elements at level 2.
    w.write_all(b"{\n    \"graphs\": [")?;
    let mut first = true;
    for (label, system) in systems {
        let system = system.borrow();
        let graph = system_to_graph(system, graph_options);
        let color_map = build_node_color_map(&system.nodes);
        let val = json_graph(label.as_ref(), &graph, &color_map);
        let mut chunk = String::new();
        if !first {
            chunk.push(',');
        }
        chunk.push('\n');
        chunk.push_str(INDENT);
        chunk.push_str(INDENT);
        write_value(&mut chunk, &val, 2);
        w.write_all(remove_pseudo_unicode(chunk).as_bytes())?;
        first = false;
    }
    if first {
        // `write_compound` collapses an empty array to `[]`.
        w.write_all(b"]\n}")
    } else {
        w.write_all(b"\n    ]\n}")
    }
}

/// aeson-pretty's indentation unit at `defConfig` (`confIndent = Spaces 4`).
const INDENT: &str = "    ";

/// Port of `Data.Aeson.Text.string` (aeson 2.1.2.1) — the escaper
/// aeson-pretty's `fromValue` reaches for every string scalar and every
/// object key by handing them to `Aeson.encodeToTextBuilder`.
///
/// Only `"`, `\` and the C0 controls are escaped at all: `"`, `\`, `\n`,
/// `\r` and `\t` get short forms, and every other character below 0x20 —
/// including `\x08` and `\x0c`, which JSON also spells `\b` and `\f` —
/// takes the `\u00xx` form with LOWERCASE hex digits (`showHex`).
/// Everything at or above 0x20 is passed through verbatim, so `<`, `>`,
/// `&`, DEL and astral-plane characters all reach the wire as themselves;
/// `removePseudoUnicode` therefore has no encoder-produced escape to undo
/// (see [`write_value`]).
///
/// Escapes are rare enough in this schema that the pass-through characters are
/// copied a run at a time: `clean` tracks the start of the verbatim span still
/// owed to `out`, and only an escaped character flushes it.
fn escape_into(out: &mut String, s: &str) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    out.push('"');
    let mut clean = 0;
    for (i, c) in s.char_indices() {
        let short = match c {
            '"' => Some("\\\""),
            '\\' => Some("\\\\"),
            '\n' => Some("\\n"),
            '\r' => Some("\\r"),
            '\t' => Some("\\t"),
            // The remaining C0 controls take the generic `\u00xx` form.
            _ if c < '\u{20}' => None,
            // Verbatim: extend the clean run.
            _ => continue,
        };
        out.push_str(&s[clean..i]);
        match short {
            Some(esc) => out.push_str(esc),
            None => {
                let b = c as u32;
                out.push_str("\\u00");
                out.push(HEX[(b >> 4) as usize] as char);
                out.push(HEX[(b & 0xf) as usize] as char);
            }
        }
        clean = i + c.len_utf8();
    }
    out.push_str(&s[clean..]);
    out.push('"');
}

/// Port of aeson-pretty's `fromValue` / `fromCompound` at `defConfig`: an
/// item list is `pNewline`-separated and indented one level deeper than its
/// brackets, the closing bracket sits at the parent's indent, and an EMPTY
/// container collapses to `[]` / `{}` with no newline inside.
///
/// Terms expand lazily through this same writer. Guarding the term entry
/// protects depth-dependent formatting without a separate term scheduler.
fn write_value(out: &mut String, v: &Json, level: usize) {
    match v {
        Json::Object(m) => {
            write_compound(out, level, ('{', '}'), m, |out, (k, val), level| {
                escape_into(out, k);
                out.push_str(": ");
                write_value(out, val, level);
            });
        }
        Json::Array(a) => {
            write_compound(out, level, ('[', ']'), a, |out, item, level| {
                write_value(out, item, level);
            });
        }
        Json::String(s) => escape_into(out, s),
        Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Json::Term(t, outermost) => tamarin_utils::stack::ensure_sufficient_stack(|| {
            write_value(out, &term_object(t, *outermost), level);
        }),
    }
}

/// `fromCompound` (aeson-pretty): the bracket/indent frame shared by objects
/// and arrays.  `item` writes one element at the already-indented cursor, at
/// nesting depth `level + 1`.
fn write_compound<T>(
    out: &mut String,
    level: usize,
    (open, close): (char, char),
    items: impl IntoIterator<Item = T>,
    mut item: impl FnMut(&mut String, T, usize),
) {
    out.push(open);
    let mut empty = true;
    for (i, elem) in items.into_iter().enumerate() {
        empty = false;
        if i > 0 {
            out.push(',');
        }
        out.push('\n');
        for _ in 0..=level {
            out.push_str(INDENT);
        }
        item(out, elem, level + 1);
    }
    if !empty {
        out.push('\n');
        for _ in 0..level {
            out.push_str(INDENT);
        }
    }
    out.push(close);
}

/// HS `removePseudoUnicode` (JSON.hs:228-239), applied to `encodePretty`'s
/// (aeson-pretty at `defConfig`) output:
/// two literal byte-substring rewrites over the chunk, applied in the
/// order the HS composition gives them: `\u003c` → `<` first, then
/// `\u003e` → `>`.  Neither is string-aware, so a source string holding the
/// six characters `\u003c` is escaped to `\\u003c` and then rewritten to the
/// invalid-JSON `\<` — reproduced here rather than avoided.  Since the
/// encoder itself never emits a `\u003c` / `\u003e` escape, that mangling is
/// the pass's only observable effect.  Each rewrite is therefore guarded by a
/// scan for its needle, which keeps the usual whole-chunk copy off the path.
fn remove_pseudo_unicode(mut s: String) -> String {
    if s.contains("\\u003c") {
        s = s.replace("\\u003c", "<");
    }
    if s.contains("\\u003e") {
        s = s.replace("\\u003e", ">");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;
    use crate::fact::Fact;
    use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::{f_app_no_eq, lit};

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
        assert_eq!(show_term(&t), "aenc(pair('3',~nr),pk(~ltkA))");
        // A nullary NoEq symbol shows as the bare name (no parentheses).
        let nullary: LNTerm = f_app_no_eq(sym("g", 0), vec![]);
        assert_eq!(show_term(&nullary), "g");
    }

    // `jgnShow` is present on the OUTERMOST term only, and omitted entirely
    // (rather than emitted as "") on nested subterms and on literals.
    #[test]
    fn jgn_show_only_on_outermost_term() {
        let t = f_app_no_eq(sym("pk", 1), vec![var("ltkA", LSort::Fresh)]);
        let render = |outermost| {
            let mut out = String::new();
            write_value(&mut out, &json_term(&t, outermost), 0);
            serde_json::from_str::<serde_json::Value>(&out).unwrap()
        };
        let v = render(true);
        assert_eq!(v["jgnShow"], "pk(~ltkA)");
        assert_eq!(v["jgnParams"][0].get("jgnShow"), None);
        assert_eq!(v["jgnParams"][0]["jgnConst"], "~ltkA");
        assert_eq!(render(false).get("jgnShow"), None);
    }

    #[test]
    fn deep_json_export_and_write_failure_use_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                use crate::constraint::constraints::Goal;
                use crate::constraint::system::graph::simplify::SimplificationLevel;
                let mut term = var("x", LSort::Msg);
                for _ in 0..512 {
                    term = f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![term]);
                }
                let mut sys = System::default();
                sys.add_goal(Goal::Action(
                    LVar::new("i", LSort::Node, 0),
                    Fact::new(FactTag::Proto(Multiplicity::Linear, "Ev", 1), vec![term]),
                ));
                let render = RenderSystem::from_prover(sys);
                let options = GraphOptions {
                    abbreviate: false,
                    compress: false,
                    simplification_level: SimplificationLevel::SL0,
                    ..Default::default()
                };
                let mut output = Vec::new();
                write_sequents_json_pretty(&options, [("L", &render)], &mut output).unwrap();
                let output = String::from_utf8(output).unwrap();
                assert_eq!(output.matches("\"jgnFunct\": \"h\"").count(), 512);
                assert_eq!(output.matches("\"jgnConst\": \"x\"").count(), 1);
                assert!(output.ends_with("\n    ]\n}"));

                // Fail after the prefix, when the graph and its shared terms exist.
                struct FailGraph(bool);
                impl std::io::Write for FailGraph {
                    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                        if std::mem::replace(&mut self.0, true) {
                            Err(std::io::Error::other("graph write failed"))
                        } else {
                            Ok(bytes.len())
                        }
                    }
                    fn flush(&mut self) -> std::io::Result<()> {
                        Ok(())
                    }
                }
                let error =
                    write_sequents_json_pretty(&options, [("L", render)], &mut FailGraph(false))
                        .unwrap_err();
                assert_eq!(error.to_string(), "graph write failed");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn dropping_unrendered_json_uses_term_ownership() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = var("x", LSort::Msg);
                for _ in 0..8192 {
                    term = f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![term]);
                }
                let value = json_term(&term, true);
                drop(term);
                drop(value);
            })
            .unwrap()
            .join()
            .unwrap();
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
            show_term(&t0),
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
        assert_eq!(out, include_str!("../../../tests/assets/hsjson_root.json"));
    }

    // A single unsolved action atom reproduces the `simplify.json` fixture:
    // node id / label / metadata layout, `jgnFactTag` "ProtoFact", and the
    // `prettyLNFact` spacing in `jgnFactShow`.
    #[test]
    fn unsolved_action_atom_matches_simplify_fixture() {
        use crate::constraint::constraints::Goal;
        use crate::constraint::system::GoalStatus;
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
        assert_eq!(
            out,
            include_str!("../../../tests/assets/hsjson_simplify.json")
        );
    }

    // `Data.Aeson.Text.string` short-forms only `\"`, `\\`, `\n`, `\r`
    // and `\t`; `<`, `>` and `&` all reach the wire literally.  0x08 and 0x0c
    // take the generic `\u00xx` form rather than JSON's `\b` / `\f`, and the
    // hex digits are lowercase.
    #[test]
    fn escapes_match_data_aeson_text() {
        let label = "a&b<c>d\"e\\f\ng\rh\ti\u{0}j\u{8}k\u{c}l\u{1f}m";
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[(
                label.to_string(),
                &RenderSystem::from_prover(System::default()),
            )],
        );
        assert_eq!(
            out,
            concat!(
                "{\n",
                "    \"graphs\": [\n",
                "        {\n",
                "            \"jgAbbrevs\": [],\n",
                "            \"jgClusters\": [],\n",
                "            \"jgDirected\": true,\n",
                "            \"jgEdges\": [],\n",
                "            \"jgLabel\": \"a&b<c>d\\\"e\\\\f\\ng\\rh\\ti\\u0000j\\u0008k\\u000cl\\u001fm\",\n",
                "            \"jgNodes\": [],\n",
                "            \"jgType\": \"Tamarin prover constraint system\"\n",
                "        }\n",
                "    ]\n",
                "}",
            )
        );
    }

    // The escaper runs over every string in the document, not just the label.
    // A pub-name literal carrying `&`, `<` and `>` is the reachable route:
    // `singleQuotedString` (Token.hs:452-453) accepts every character but
    // `'` and newline, and the name lands in `jgnLabel`, `jgnFactShow` and
    // `jgnConst` alike — all of them literal on the wire.
    #[test]
    fn pub_name_specials_reach_the_wire_literally() {
        use crate::constraint::constraints::Goal;
        use crate::constraint::system::GoalStatus;
        let mut sys = System::default();
        let nid = LVar::new("i", LSort::Node, 0);
        let fa: LNFact = Fact::new(
            FactTag::Proto(
                Multiplicity::Linear,
                tamarin_term::intern::intern_str("Ev"),
                1,
            ),
            vec![lit(Lit::Con(Name::new(NameTag::Pub, "a&b<c>d")))],
        );
        sys.goals_mut()
            .push((Goal::Action(nid, fa), GoalStatus::default()));
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[("L".to_string(), &RenderSystem::from_prover(sys))],
        );
        assert!(
            out.contains("\"jgnConst\": \"'a&b<c>d'\""),
            "jgnConst: {out}"
        );
        assert!(
            out.contains("\"jgnLabel\": \"Ev( 'a&b<c>d' )\""),
            "jgnLabel: {out}"
        );
        assert!(
            out.contains("\"jgnFactShow\": \"Ev( 'a&b<c>d' )\""),
            "jgnFactShow: {out}"
        );
        // No `\u0026` anywhere: the writer must not have re-grown the
        // over-escaping the oracle probe disproved.
        assert!(!out.contains("\\u0026"), "{out}");
    }

    // `removePseudoUnicode` is a raw byte rewrite over the WHOLE document, not
    // a string-aware pass: a label holding the six characters `\u003c` is
    // escaped to `\\u003c` and the pass then eats the tail of that escape,
    // leaving the invalid-JSON `\<`.  HS emits exactly this.
    #[test]
    fn pseudo_unicode_pass_mangles_a_literal_escape_in_the_payload() {
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[(
                "x\\u003cy\\u003ez".to_string(),
                &RenderSystem::from_prover(System::default()),
            )],
        );
        assert!(out.contains("\"jgLabel\": \"x\\<y\\>z\","), "{out}");
        assert!(serde_json::from_str::<serde_json::Value>(&out).is_err());
    }

    // `roleCluster` groups a rule's nodes under `<role>_Session_<n>`, and
    // `sequentToJSONGraph` (JSON.hs:520-539) then serialises them through
    // `graphClusterToJSONGraphCluster` (JSON.hs:498-506) instead of the
    // top-level node list.  Every other pin in this module renders an
    // UNCLUSTERED system, so `jgClusters` is `[]` in all of them and the
    // cluster writer is unexercised.
    //
    // Oracle shape, read off `--prove --output-json` of the pinned v1.13.0
    // binary on `examples/sapic/fast/basic/channels1.spthy` (roles `P`,
    // `Process`, `Q`): top-level `jgNodes` is EMPTY while three clusters
    // carry every node, each cluster object is exactly
    // `{jgcEdges, jgcName, jgcNodes}` in that order, and `jgcName` is the
    // cluster's FULL name (`P_Session_1`) — `extractBaseName` picks the
    // colour, never the name.
    #[test]
    fn clustered_system_serialises_through_jg_clusters() {
        use crate::fact::out_fact;
        use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo};
        let k = lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let mk = |name: &'static str, role: &str| {
            Rule::new(
                RuleInfo::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name),
                    attributes: RuleAttributes {
                        role: Some(role.to_string()),
                        ..Default::default()
                    },
                    loop_breakers: Vec::new(),
                }),
                Vec::new(),
                vec![out_fact(k.clone())],
                vec![out_fact(k.clone())],
            )
        };
        let mut sys = System::empty();
        sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", "P"));
        sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", "Q"));
        let out = sequents_to_json_pretty(
            &GraphOptions::default(),
            &[("L".to_string(), &RenderSystem::from_prover(sys))],
        );
        assert!(
            out.contains("            \"jgNodes\": [],\n"),
            "clustered nodes must leave the top-level list empty:\n{out}"
        );
        for (name, node) in [("P_Session_1", "#a.1"), ("Q_Session_1", "#b.2")] {
            let block = format!(
                "                {{\n\
                 \x20                   \"jgcEdges\": [],\n\
                 \x20                   \"jgcName\": \"{name}\",\n\
                 \x20                   \"jgcNodes\": [\n\
                 \x20                       {{\n\
                 \x20                           \"jgnColor\": \""
            );
            assert!(out.contains(&block), "{name} cluster object:\n{out}");
            assert!(
                out.contains(&format!("\"jgnId\": \"{node}\",")),
                "{name} must carry its node {node}:\n{out}"
            );
        }
        // This checks the cluster order, which the `contains` checks above
        // cannot see.  HS builds the clusters from `Map.toList nodesByGroup`
        // (GraphRepr.hs:123) over the `Map String [Node]` that
        // `groupNodesByRole` (:139-144) accumulates.  Data.Map lists its keys
        // in ascending order.  The roles therefore go into the output sorted
        // by name.
        let p = out
            .find("\"jgcName\": \"P_Session_1\"")
            .expect("P_Session_1 cluster");
        let q = out
            .find("\"jgcName\": \"Q_Session_1\"")
            .expect("Q_Session_1 cluster");
        assert!(
            p < q,
            "clusters must reach the wire in ascending role order:\n{out}"
        );
    }

    // There are no traces at all.  The empty array stays inline, because
    // aeson-pretty does not break an empty list over three lines.  The
    // document also ends without a trailing newline.  These are the same 20
    // bytes that `--output-json` writes for a theory with nothing solved.
    #[test]
    fn empty_graph_list_is_twenty_bytes() {
        let out = sequents_to_json_pretty(&GraphOptions::default(), &[]);
        assert_eq!(out, "{\n    \"graphs\": []\n}");
    }
}
