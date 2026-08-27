// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Out-of-line tests for `tools::abstract_interpretation`.  The expected
//! byte strings are the v1.13.0 oracle's observed output for the same
//! shapes (`--partial-evaluation` stderr traces and the `text{*…*}`
//! report body).  Maude-backed tests need a maude:
//! [`tamarin_test_support::require_maude_path`] resolves one from
//! `$MAUDE_PATH`, the system prefixes, `$PATH` or the package-manager
//! prefixes, and PANICS when none of those hits.  Set
//! `TAM_ALLOW_NO_MAUDE=1` to skip them silently instead.

use super::*;
use crate::fact::{proto_fact, Multiplicity};
use crate::rule::{ProtoRuleEInfo, ProtoRuleName, Rule};
use crate::signature::SignaturePure;
use tamarin_term::builtin::{fresh_var, msg_var};
use tamarin_term::lterm::pub_term;
use tamarin_term::maude_sig::{hash_maude_sig, pair_maude_sig};
use tamarin_term::term::f_app_no_eq;
use tamarin_test_support::require_maude_path;

// =============================================================================
// Doc helpers (numbered' / $--$)
// =============================================================================

/// The VERBOSE trace body indents the `numbered'` blank separator to two
/// spaces under `nest 2` — HS `nest` indents the `text ""` separator line.
#[test]
fn numbered_prime_nest_indents_blank_separator() {
    let d = hpj::numbered_prime(vec![Doc::text("St( ~k )"), Doc::text("Out( z )")]).nest(2);
    assert_eq!(
        d.render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON),
        "  1. St( ~k )\n  \n  2. Out( z )"
    );
}

/// `flushRight` left-pads the index to the widest index's width.
#[test]
fn numbered_prime_flush_right_pads_indices() {
    let docs: Vec<Doc> = (0..13).map(|_| Doc::text("x")).collect();
    let out = hpj::numbered_prime(docs).render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[0], " 1. x");
    assert_eq!(lines[1], "");
    assert_eq!(lines[18], "10. x");
    assert_eq!(lines[24], "13. x");
}

#[test]
fn numbered_empty_is_empty_doc() {
    assert!(matches!(
        hpj::numbered(Doc::text_hs(""), vec![]),
        Doc::Empty
    ));
}

#[test]
fn above_blank_case_empty_guards() {
    let a = || Doc::text("a");
    let b = || Doc::text("b");
    let r = |d: Doc| d.render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON);
    assert_eq!(r(hpj::above_blank(a(), b())), "a\n\nb");
    assert_eq!(r(hpj::above_blank(a(), Doc::Empty)), "a");
    assert_eq!(r(hpj::above_blank(Doc::Empty, b())), "b");
}

// =============================================================================
// absFact / absTerm
// =============================================================================

/// Every `Out` fact collapses to `Out( z )` with `z = LVar "z" Msg 0`.
#[test]
fn abs_fact_out_collapses_to_out_z() {
    let hashed = f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![fresh_var("k", 7)]);
    let a = abs_fact(&crate::fact::out_fact(hashed));
    assert_eq!(
        a,
        crate::fact::out_fact(var_term(LVar::new("z", LSort::Msg, 0)))
    );
}

/// Constants survive, `NoEq` applications are recursed into, and the
/// binding map is keyed by the WHOLE sub-term: identical sub-terms share
/// one imported variable, the per-fact counter runs left-to-right, name
/// hints come from the variable's own name (`"z"` for non-variables).
#[test]
fn abs_fact_bindings_constants_and_noeq() {
    let h = |t: LNTerm| f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![t]);
    let fa = proto_fact(
        Multiplicity::Linear,
        "St",
        vec![
            pub_term("a"),
            fresh_var("k", 5),
            h(fresh_var("k", 5)),
            msg_var("x", 9),
        ],
    );
    let a = abs_fact(&fa);
    let expect = proto_fact(
        Multiplicity::Linear,
        "St",
        vec![
            pub_term("a"),
            fresh_var("k", 0),
            h(fresh_var("k", 0)),
            msg_var("x", 1),
        ],
    );
    assert_eq!(a, expect);
}

/// An AC application is abstracted to a single variable with hint `"z"`
/// and the term's sort.
#[test]
fn abs_fact_ac_application_becomes_z_var() {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    let ac = tamarin_term::term::f_app(
        FunSym::Ac(AcSym::Mult),
        vec![msg_var("x", 0), msg_var("y", 0)],
    );
    let a = abs_fact(&proto_fact(Multiplicity::Linear, "F", vec![ac]));
    assert_eq!(
        a,
        proto_fact(Multiplicity::Linear, "F", vec![msg_var("z", 0)])
    );
}

/// `BTreeSet<LNFact>` reproduces HS's `S.Set LNFact` order: persistent
/// proto facts before linear ones, then name STRING order (`S1 < S10 <
/// S2`), then the builtin tags `Fr < Out < In`.
#[test]
fn abstract_state_set_order_matches_hs() {
    let mut st: BTreeSet<LNFact> = BTreeSet::new();
    st.insert(proto_fact(
        Multiplicity::Linear,
        "St",
        vec![fresh_var("k", 0)],
    ));
    st.insert(proto_fact(
        Multiplicity::Persistent,
        "Perm",
        vec![msg_var("m", 0)],
    ));
    st.insert(proto_fact(
        Multiplicity::Linear,
        "S1",
        vec![fresh_var("k", 0)],
    ));
    st.insert(proto_fact(
        Multiplicity::Linear,
        "S10",
        vec![fresh_var("k", 0)],
    ));
    st.insert(proto_fact(
        Multiplicity::Linear,
        "S2",
        vec![fresh_var("k", 0)],
    ));
    st.insert(crate::fact::in_fact(msg_var("z", 0)));
    st.insert(crate::fact::out_fact(msg_var("z", 0)));
    st.insert(crate::fact::fresh_fact(fresh_var("z", 0)));
    let names: Vec<String> = st
        .iter()
        .map(|f| crate::fact::show_fact_tag(&f.tag))
        .collect();
    assert_eq!(
        names,
        vec!["!Perm", "S1", "S10", "S2", "St", "Fr", "Out", "In"]
    );
}

// =============================================================================
// abs_state_report — §2.1 bytes (13-fact oracle capture shape)
// =============================================================================

#[test]
fn abs_state_report_bytes_flush_right_13_facts() {
    let mut st: BTreeSet<LNFact> = BTreeSet::new();
    for i in 1..=11 {
        st.insert(proto_fact(
            Multiplicity::Linear,
            &format!("S{}", i),
            vec![fresh_var("k", 0)],
        ));
    }
    st.insert(crate::fact::fresh_fact(fresh_var("z", 0)));
    st.insert(crate::fact::in_fact(msg_var("z", 0)));
    let body = abs_state_report(&st, 11, 11);
    let expect = " the abstract state after partial evaluation contains 13 facts:\n\
                  \n \
                  1. S1( ~k )\n\
                  \n \
                  2. S10( ~k )\n\
                  \n \
                  3. S11( ~k )\n\
                  \n \
                  4. S2( ~k )\n\
                  \n \
                  5. S3( ~k )\n\
                  \n \
                  6. S4( ~k )\n\
                  \n \
                  7. S5( ~k )\n\
                  \n \
                  8. S6( ~k )\n\
                  \n \
                  9. S7( ~k )\n\
                  \n\
                  10. S8( ~k )\n\
                  \n\
                  11. S9( ~k )\n\
                  \n\
                  12. Fr( ~z )\n\
                  \n\
                  13. In( z )\n\
                  \nThis abstract state results in 11 refined multiset rewriting rules.\n\
                  Note that the original number of multiset rewriting rules was 11.\n\n";
    assert_eq!(body, expect);
}

// =============================================================================
// eqModuloFreshnessNoAC / rule ordering
// =============================================================================

fn simple_rule(name: &str, prem_var: (&str, u64), conc_var: (&str, u64)) -> ProtoRuleE {
    Rule::new(
        ProtoRuleEInfo::standard(name),
        vec![crate::fact::in_fact(msg_var(prem_var.0, prem_var.1))],
        vec![crate::fact::out_fact(msg_var(conc_var.0, conc_var.1))],
        vec![],
    )
}

/// Alpha-equivalent duplicates merge (first occurrence wins); the rule
/// NAME is part of the compared `info`, so refinements of different rules
/// never merge.
#[test]
fn nub_modulo_freshness_first_occurrence_wins() {
    let a1 = simple_rule("A", ("x", 3), ("x", 3));
    let a2 = simple_rule("A", ("y", 8), ("y", 8));
    let b = simple_rule("B", ("x", 3), ("x", 3));
    let kept = nub_modulo_freshness(vec![
        (a1.clone(), Vec::new()),
        (a2, Vec::new()),
        (b.clone(), Vec::new()),
    ]);
    assert_eq!(kept, vec![a1, b]);
}

/// Same variable pattern but DIFFERENT sharing structure stays distinct.
#[test]
fn nub_modulo_freshness_distinguishes_sharing() {
    let shared = simple_rule("A", ("x", 0), ("x", 0));
    let unshared = simple_rule("A", ("x", 0), ("y", 1));
    let kept = nub_modulo_freshness(vec![(shared, Vec::new()), (unshared, Vec::new())]);
    assert_eq!(kept.len(), 2);
}

/// The Set round-trip key orders by rule name (HS derived
/// `Ord ProtoRuleEInfo` — name first).
#[test]
fn proto_rule_key_sorts_alphabetically_by_name() {
    let mut rules = [
        simple_rule("Zebra", ("x", 0), ("x", 0)),
        simple_rule("Apple", ("x", 0), ("x", 0)),
        simple_rule("Mango", ("x", 0), ("x", 0)),
    ];
    rules.sort_by(|a, b| proto_rule_key(a).cmp(&proto_rule_key(b)));
    let names: Vec<&str> = rules
        .iter()
        .map(|r| match &r.info.name {
            ProtoRuleName::Stand(s) => *s,
            ProtoRuleName::Fresh => "Fresh",
        })
        .collect();
    assert_eq!(names, vec!["Apple", "Mango", "Zebra"]);
}

// =============================================================================
// Maude-backed: partial_evaluation
// =============================================================================

/// §2.2 oracle bytes: `[ Fr(~k) ] --> [ St(~k), Out(~k) ]` traces
/// ` partial evaluation: step 0 added 2 facts` with the VERBOSE nested
/// fact list, and stdout inputs (state + refined rules) are identical
/// between styles.
#[test]
fn partial_evaluation_trace_bytes_and_style_invariance() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let init: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Init"),
        vec![crate::fact::fresh_fact(fresh_var("k", 0))],
        vec![
            proto_fact(Multiplicity::Linear, "St", vec![fresh_var("k", 0)]),
            crate::fact::out_fact(fresh_var("k", 0)),
        ],
        vec![],
    );
    let (st_s, rules_s, trace_s) =
        partial_evaluation(&h, EvaluationStyle::Summary, std::slice::from_ref(&init)).unwrap();
    assert_eq!(trace_s, " partial evaluation: step 0 added 2 facts\n");

    let (st_v, rules_v, trace_v) =
        partial_evaluation(&h, EvaluationStyle::Tracing, std::slice::from_ref(&init)).unwrap();
    assert_eq!(
        trace_v,
        " partial evaluation: step 0 added 2 facts\n\
         \n  \
         1. St( ~k )\n  \
         \n  \
         2. Out( z )\n\n"
    );

    let (st_q, rules_q, trace_q) =
        partial_evaluation(&h, EvaluationStyle::Silent, &[init]).unwrap();
    assert_eq!(trace_q, "");

    // stdout is byte-identical between styles: same state, same rules.
    assert_eq!(st_s, st_v);
    assert_eq!(st_s, st_q);
    assert_eq!(rules_s, rules_v);
    assert_eq!(rules_s, rules_q);

    assert_eq!(st_s.len(), 4); // St(~k), Fr(~z), Out(z), In(z)
    assert_eq!(rules_s.len(), 1);
}

/// `Eq`/`Ord LNFact` ignore annotations (Theory/Model/Fact.hs:170-174) but
/// `prettyLNFact` prints them (Theory/Model/Fact.hs:567-574), so which
/// annotations the
/// abstract state shows is decided by `S.insert`'s REPLACE-on-equal
/// semantics: the LAST conclusion inserted wins.  Oracle bytes for
/// `rule A: [Fr(~k)] --> [St(~k)]` + `rule B: [Fr(~k)] --> [St(~k)[+]]`
/// under `--partial-evaluation=SUMMARY` — the report's first entry is
/// `1. St( ~k )[+]`, i.e. B's annotated form, even though A sorts first.
#[test]
fn abstract_state_keeps_the_last_inserted_annotations() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let st_plain = proto_fact(Multiplicity::Linear, "St", vec![fresh_var("k", 0)]);
    let st_marked = LNFact::fresh_annotated(
        st_plain.tag,
        [crate::fact::FactAnnotation::SolveFirst]
            .into_iter()
            .collect(),
        vec![fresh_var("k", 0)],
    );
    let mk = |name: &'static str, conc: LNFact| -> ProtoRuleE {
        Rule::new(
            ProtoRuleEInfo::standard(name),
            vec![crate::fact::fresh_fact(fresh_var("k", 0))],
            vec![conc],
            vec![],
        )
    };
    // `getProtoRuleEs`' sorted order: A before B, so B's conclusion is
    // abstracted and inserted last.
    let rules = [mk("A", st_plain), mk("B", st_marked)];
    let (st, refined, _) = partial_evaluation(&h, EvaluationStyle::Summary, &rules).unwrap();
    let report = abs_state_report(&st, refined.len(), rules.len());
    assert!(
        report.contains("\n1. St( ~k )[+]\n"),
        "the annotated form must survive; got:\n{report}"
    );
}

/// The pe_multi shape (§3 rows 2, 5, 6, 7): one rule refining into two,
/// constants surviving abstraction, `freshToFree`'s name-hint rule
/// (singleton-Var image keeps the DOMAIN var's name; App image keeps the
/// range vars' names), and the final rename normalising each rule's
/// minimum index to 0.
#[test]
fn partial_evaluation_rule_multiplication_and_name_hints() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = pair_maude_sig().merge(hash_maude_sig());
    let h = MaudeHandle::start(&path, sig).unwrap();
    let hh = |t: LNTerm| f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![t]);
    let st_fact = |a: LNTerm, b: LNTerm| proto_fact(Multiplicity::Linear, "St", vec![a, b]);

    let rule_a: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("A"),
        vec![crate::fact::fresh_fact(fresh_var("k", 0))],
        vec![st_fact(pub_term("a"), fresh_var("k", 0))],
        vec![],
    );
    let rule_b: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("B"),
        vec![crate::fact::fresh_fact(fresh_var("k", 0))],
        vec![st_fact(pub_term("b"), hh(fresh_var("k", 0)))],
        vec![],
    );
    let rule_c: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("C"),
        vec![st_fact(msg_var("x", 0), msg_var("y", 0))],
        vec![crate::fact::out_fact(msg_var("y", 0))],
        vec![proto_fact(
            Multiplicity::Linear,
            "Use",
            vec![msg_var("x", 0)],
        )],
    );
    let rule_d: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("D"),
        vec![
            crate::fact::in_fact(msg_var("m", 0)),
            st_fact(msg_var("x", 0), msg_var("y", 0)),
        ],
        vec![proto_fact(
            Multiplicity::Persistent,
            "Perm",
            vec![msg_var("m", 0), msg_var("x", 0)],
        )],
        vec![],
    );

    let rules = [rule_a, rule_b, rule_c, rule_d];
    let (st, refined, trace) = partial_evaluation(&h, EvaluationStyle::Summary, &rules).unwrap();
    assert_eq!(
        trace,
        " partial evaluation: step 0 added 2 facts\n \
         partial evaluation: step 1 added 3 facts\n"
    );

    // State: !Perm×2 first (persistent), then St×2, Fr, Out, In.
    let tags: Vec<String> = st
        .iter()
        .map(|f| crate::fact::show_fact_tag(&f.tag))
        .collect();
    assert_eq!(tags, vec!["!Perm", "!Perm", "St", "St", "Fr", "Out", "In"]);
    assert!(st.contains(&st_fact(pub_term("a"), fresh_var("k", 0))));
    assert!(st.contains(&st_fact(pub_term("b"), hh(fresh_var("k", 0)))));

    // Refined: one A, one B, two C, two D — in that (already sorted) order.
    let names: Vec<&str> = refined
        .iter()
        .map(|r| match &r.info.name {
            ProtoRuleName::Stand(s) => *s,
            ProtoRuleName::Fresh => "Fresh",
        })
        .collect();
    assert_eq!(names, vec!["A", "B", "C", "C", "D", "D"]);

    // C #1: singleton-Var image keeps the DOMAIN var's name (`y`), sorted
    // state order puts the 'a' fact first; min index renamed to 0.
    assert_eq!(
        refined[2].premises,
        vec![st_fact(pub_term("a"), fresh_var("y", 0))]
    );
    assert_eq!(
        refined[2].actions,
        vec![proto_fact(Multiplicity::Linear, "Use", vec![pub_term("a")])]
    );
    // C #2: App image keeps the RANGE var's name (`k`).
    assert_eq!(
        refined[3].premises,
        vec![st_fact(pub_term("b"), hh(fresh_var("k", 0)))]
    );
    // D #1 (§3 row 7): `[ In( m ), St( 'a', ~y.1 ) ]`.
    assert_eq!(
        refined[4].premises,
        vec![
            crate::fact::in_fact(msg_var("m", 0)),
            st_fact(pub_term("a"), fresh_var("y", 1)),
        ]
    );
    assert_eq!(
        refined[5].premises,
        vec![
            crate::fact::in_fact(msg_var("m", 0)),
            st_fact(pub_term("b"), hh(fresh_var("k", 1))),
        ]
    );
}

// =============================================================================
// Maude-backed: apply_partial_evaluation splice
// =============================================================================

fn text_item(tag: &str) -> TheoryItem {
    TheoryItem::Text(("section".to_string(), tag.to_string()))
}

/// The report + refined rules land at the FIRST rule item's position;
/// earlier items stay put, later non-rule items follow; the refined rules
/// come out alphabetically (§3 rows 1, 3).
#[test]
fn apply_partial_evaluation_splices_at_first_rule_item() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();

    let zebra: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Zebra"),
        vec![],
        vec![crate::fact::out_fact(msg_var("x", 0))],
        vec![],
    );
    let apple: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Apple"),
        vec![],
        vec![proto_fact(
            Multiplicity::Linear,
            "Ap",
            vec![msg_var("y", 0)],
        )],
        vec![],
    );

    let mut elab: Theory = Theory::new("T", SignaturePure::empty(false));
    elab.items = vec![
        text_item("before"),
        TheoryItem::Rule(OpenProtoRule::new(zebra)),
        text_item("mid"),
        TheoryItem::Rule(OpenProtoRule::new(apple)),
        text_item("after"),
    ];

    let trace = apply_partial_evaluation(&mut elab, &h, EvaluationStyle::Summary).unwrap();
    // Two zero-premise rules, conclusions abstract to Ap(y) + Out(z).
    assert_eq!(trace, " partial evaluation: step 0 added 2 facts\n");

    // before | text{*report*} | Apple | Zebra | mid | after.
    assert_eq!(elab.items.len(), 6);
    assert_eq!(elab.items[0], text_item("before"));
    match &elab.items[1] {
        TheoryItem::Text((header, body)) => {
            assert_eq!(header, "text");
            assert!(
                body.starts_with(" the abstract state after partial evaluation contains 4 facts:")
            );
            assert!(body.ends_with(
                "This abstract state results in 2 refined multiset rewriting rules.\n\
                 Note that the original number of multiset rewriting rules was 2.\n\n"
            ));
        }
        other => panic!("expected report item, got {:?}", other),
    }
    let rule_name = |it: &TheoryItem| match it {
        TheoryItem::Rule(r) => r.name().to_string(),
        other => panic!("expected rule item, got {:?}", other),
    };
    assert_eq!(rule_name(&elab.items[2]), "Apple");
    assert_eq!(rule_name(&elab.items[3]), "Zebra");
    assert_eq!(elab.items[4], text_item("mid"));
    assert_eq!(elab.items[5], text_item("after"));

    // Fresh OpenProtoRules for the caller's re-close.
    assert!(elab.rules().all(|r| r.variant_substs.is_empty()
        && r.abstracted_rule.is_none()
        && r.loop_breakers.is_empty()));
}

/// A spliced refined rule carries the pre-macro rule as its `rule_e`, the
/// half HS's re-close narrows `applyMacroInRule macros ruE` from while
/// keeping `ruE` itself (lib/theory/src/Rule.hs:82-86).  `open_proto_rule`
/// then identifies the AC half with it up to terms and the rule renders
/// without a `rule (modulo AC)` block.
#[test]
fn a_refined_rule_keeps_its_pre_macro_e_half() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();

    // `macros: dup(y) = <y, y>` and a rule whose conclusion calls it.
    let y = LVar::new("y", LSort::Msg, 0);
    let dup: crate::theory::LNMacro = crate::theory::LNMacro::new(
        b"dup".to_vec(),
        vec![y],
        tamarin_term::builtin::pair(var_term(y), var_term(y)),
    );
    let dup_call: LNTerm = f_app(
        tamarin_term::macro_expand::macro_to_fun_sym(&dup),
        vec![var_term(y)],
    );
    let macroed: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Macroed"),
        vec![],
        vec![proto_fact(
            Multiplicity::Linear,
            "Ap",
            vec![dup_call.clone()],
        )],
        vec![],
    );

    let mut elab: Theory = Theory::new("T", SignaturePure::empty(false));
    elab.items = vec![
        TheoryItem::Macros(vec![dup]),
        TheoryItem::Rule(OpenProtoRule::new(macroed)),
    ];
    apply_partial_evaluation(&mut elab, &h, EvaluationStyle::Silent).unwrap();

    let refined: Vec<&OpenProtoRule> = elab.rules().collect();
    assert_eq!(refined.len(), 1);
    let opr = refined[0];
    assert_eq!(
        opr.rule_e().conclusions,
        vec![proto_fact(Multiplicity::Linear, "Ap", vec![dup_call])]
    );
    assert_eq!(
        opr.rule.conclusions,
        vec![proto_fact(
            Multiplicity::Linear,
            "Ap",
            vec![tamarin_term::builtin::pair(var_term(y), var_term(y))]
        )]
    );
    assert!(crate::theory::open_proto_rule(opr).rule_ac.is_empty());
}

/// A theory with no rule items is a no-op (HS `replaceProtoRules [] = []`).
#[test]
fn apply_partial_evaluation_no_rules_is_noop() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let mut elab: Theory = Theory::new("T", SignaturePure::empty(false));
    elab.items = vec![text_item("only")];
    let elab_before = elab.clone();
    let trace = apply_partial_evaluation(&mut elab, &h, EvaluationStyle::Tracing).unwrap();
    assert_eq!(trace, "");
    assert_eq!(elab, elab_before);
}

// =============================================================================
// `_restrict`-formula frees
// =============================================================================

/// One `_restrict` formula as the rule carries it: an atom over the given
/// free variables.
fn restr_action(timepoint: LVar, arg: LVar) -> crate::formula::SyntacticLNFormula {
    let lift = |v: LVar| {
        crate::formula::lift_free(&tamarin_term::vterm::var_term::<
            tamarin_term::lterm::Name,
            LVar,
        >(v))
    };
    crate::formula::ProtoFormula::Atom(crate::atom::ProtoAtom::Action(
        lift(timepoint),
        crate::fact::Fact::fresh(
            crate::fact::FactTag::Proto(Multiplicity::Linear, "P", 1),
            vec![lift(arg)],
        ),
    ))
}

/// `info_frees` is HS `freesList` over `preRestriction` (Term/LTerm.hs:605-608):
/// first occurrence first, NOT sorted by `Ord LVar`.  An action atom folds its
/// timepoint before the fact's arguments (Theory/Model/Atom.hs:129-136), so
/// `P( y ) @ #i` with `#i` at the higher index yields `[#i, y]` where the
/// sorted list would be `[y, #i]`.
#[test]
fn info_frees_are_in_occurrence_order() {
    let i = LVar::new("i", LSort::Node, 5);
    let y = LVar::new("y", LSort::Msg, 1);
    let mut r: ProtoRuleE = Rule::new(ProtoRuleEInfo::standard("A"), vec![], vec![], vec![]);
    r.info.restrictions = vec![restr_action(i, y)];
    assert_eq!(info_frees(&r), vec![i, y]);
}

// =============================================================================
// Maude-backed: `_restrict`-formula frees floor the final rename
// =============================================================================

/// HS rules keep their `_restrict` formulas in `preRestriction`, whose
/// frees are folded by `HasFrees (Rule i)` but never substituted (`Apply
/// ProtoRuleEInfo` is the identity) — so a refined rule whose body vars
/// were ALL substituted keeps its refined indices in the final rename
/// (the index-0 info frees floor the shift).  Oracle pin:
/// features/predicates/minimal.spthy renders `[ In( x.2 ) ] --[
/// Restr_A_1( eq(x.2, x.2) ) ]-> [ ]`, while the same rule with a
/// free-less `_restrict` formula renders `[ In( x ) ]`.
#[test]
fn info_frees_floor_the_final_rename() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = pair_maude_sig().merge(hash_maude_sig());
    let h = MaudeHandle::start(&path, sig).unwrap();
    let hh = |t: LNTerm| f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![t]);
    let rule_a = |restrictions: Vec<crate::formula::SyntacticLNFormula>| -> ProtoRuleE {
        let mut r = Rule::new(
            ProtoRuleEInfo::standard("A"),
            vec![crate::fact::in_fact(msg_var("x", 0))],
            vec![],
            vec![proto_fact(
                Multiplicity::Linear,
                "Restr_A_1",
                vec![hh(msg_var("x", 0))],
            )],
        );
        r.info.restrictions = restrictions;
        r
    };

    // Refinement: In(x.0) ≐ In(z.1) (state fact renamed above avoid=1),
    // unifier image drawn at index 2 → body var x.2.  With the formula
    // free x.0 in play the rename's minimum is 0 and x.2 SURVIVES.
    let with_free = vec![restr_action(
        LVar::new("i", LSort::Node, 0),
        LVar::new("x", LSort::Msg, 0),
    )];
    let (_, refined, _) =
        partial_evaluation(&h, EvaluationStyle::Silent, &[rule_a(with_free)]).unwrap();
    assert_eq!(refined.len(), 1);
    assert_eq!(
        refined[0].premises,
        vec![crate::fact::in_fact(msg_var("x", 2))]
    );
    assert_eq!(
        refined[0].actions,
        vec![proto_fact(
            Multiplicity::Linear,
            "Restr_A_1",
            vec![hh(msg_var("x", 2))]
        )]
    );

    // Without info frees the same rule renames its minimum down to 0.
    let (_, refined0, _) =
        partial_evaluation(&h, EvaluationStyle::Silent, &[rule_a(vec![])]).unwrap();
    assert_eq!(
        refined0[0].premises,
        vec![crate::fact::in_fact(msg_var("x", 0))]
    );
}

// =============================================================================
// Maude-backed: loop-breaker node identity over PE-refined rules
// =============================================================================

/// HS `useAutoLoopBreakersAC` keys the premise-solving relation by the
/// WHOLE closed item (`Ord`), so same-named refined rules with different
/// bodies are DISTINCT graph nodes.  Oracle pins (partial-evaluation
/// probes):
/// * `Gen/Step('1')/Step('2')/Back` — dataflow acyclic per item, cyclic
///   under a name key → the oracle renders ZERO `// loop breaker:`
///   comments (a name key would fabricate one);
/// * `Back/Gen/Step` with a REAL `Step ↔ Back` cycle → the oracle marks
///   `Back` premise 0 only.
#[test]
fn loop_breakers_key_same_named_refined_rules_apart() {
    use crate::constraint::solver::context::annotate_loop_breakers;
    use crate::rule::PremIdx;
    use crate::theory::OpenProtoRule;
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let fact = |name: &'static str, arg: LNTerm| -> LNFact {
        proto_fact(Multiplicity::Linear, name, vec![arg])
    };
    let rule = |name: &'static str, prems: Vec<LNFact>, concs: Vec<LNFact>| -> OpenProtoRule {
        OpenProtoRule::new(Rule::new(
            ProtoRuleEInfo::standard(name),
            prems,
            concs,
            vec![],
        ))
    };

    // Acyclic per item: Step('1') feeds Back, Back feeds Step('2') — no
    // node reaches itself unless the two Steps are conflated by name.
    let mut rules = [
        rule(
            "Gen",
            vec![crate::fact::fresh_fact(fresh_var("x", 0))],
            vec![fact("A", pub_term("1")), fact("A", pub_term("2"))],
        ),
        rule(
            "Step",
            vec![fact("A", pub_term("1"))],
            vec![fact("B", pub_term("1"))],
        ),
        rule(
            "Step",
            vec![fact("A", pub_term("2"))],
            vec![fact("B", pub_term("2"))],
        ),
        rule(
            "Back",
            vec![fact("B", pub_term("1"))],
            vec![fact("A", pub_term("2"))],
        ),
    ];
    annotate_loop_breakers(&mut rules.iter_mut().collect::<Vec<_>>(), &h);
    assert!(
        rules.iter().all(|r| r.loop_breakers.is_empty()),
        "acyclic per-item graph must yield no breakers; got {:?}",
        rules.iter().map(|r| &r.loop_breakers).collect::<Vec<_>>()
    );

    // Real cycle: Step('1') → B('1') → Back → A('1') → Step('1').  Rules
    // in the refined theory's (name-sorted) order; the oracle marks Back
    // premise 0.
    let mut rules = [
        rule(
            "Back",
            vec![fact("B", pub_term("1"))],
            vec![fact("A", pub_term("1"))],
        ),
        rule(
            "Gen",
            vec![crate::fact::fresh_fact(fresh_var("x", 0))],
            vec![fact("A", pub_term("1"))],
        ),
        rule(
            "Step",
            vec![fact("A", pub_term("1"))],
            vec![fact("B", pub_term("1"))],
        ),
    ];
    annotate_loop_breakers(&mut rules.iter_mut().collect::<Vec<_>>(), &h);
    let breakers: Vec<&[PremIdx]> = rules.iter().map(|r| r.loop_breakers.as_slice()).collect();
    assert_eq!(
        breakers,
        vec![&[PremIdx(0)][..], &[][..], &[][..]],
        "the cycle must still be found across distinct same-named nodes"
    );
}
