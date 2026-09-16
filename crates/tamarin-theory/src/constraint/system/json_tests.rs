// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
    tamarin_test_support::on_stack(256 * 1024, || {
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
        let error = write_sequents_json_pretty(&options, [("L", render)], &mut FailGraph(false))
            .unwrap_err();
        assert_eq!(error.to_string(), "graph write failed");
    });
}

#[test]
fn dropping_unrendered_json_uses_term_ownership() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut term = var("x", LSort::Msg);
        for _ in 0..8192 {
            term = f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![term]);
        }
        let value = json_term(&term, true);
        drop(term);
        drop(value);
    });
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
