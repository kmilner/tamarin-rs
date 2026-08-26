// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::fact::{fresh_fact, in_fact, out_fact};
use tamarin_term::builtin::msg_var;

/// `Rule::new` puts each argument into its own field.  The lists have distinct
/// lengths and distinct contents.  A swap of the premises and the conclusions
/// therefore cannot hide behind two lists of the same shape.
/// `ProtoRuleEInfo::standard` interns the name into `Stand` without change,
/// and it leaves the attributes and the restrictions empty.
#[test]
fn build_simple_proto_rule_e() {
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Send"),
        vec![fresh_fact(msg_var("k", 0)), in_fact(msg_var("m", 0))],
        vec![out_fact(msg_var("k", 0))],
        vec![],
    );
    assert_eq!(
        r.premises,
        vec![fresh_fact(msg_var("k", 0)), in_fact(msg_var("m", 0))]
    );
    assert_eq!(r.conclusions, vec![out_fact(msg_var("k", 0))]);
    assert!(r.actions.is_empty());
    assert!(r.new_vars.is_empty());
    assert_eq!(r.info.name, ProtoRuleName::Stand("Send"));
    assert_eq!(r.info.attributes, RuleAttributes::empty());
    assert!(r.info.restrictions.is_empty());
}

/// `lookup_premise` and `lookup_conclusion` index their own list.  The two
/// lists have different lengths, and the test also checks the identity of each
/// fact.  A lookup that reads the wrong list therefore fails here.  Both
/// functions return `None` for an index one past the end.
#[test]
fn rule_indices_lookup() {
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Echo"),
        vec![in_fact(msg_var("m", 0)), in_fact(msg_var("n", 0))],
        vec![out_fact(msg_var("m", 0))],
        vec![],
    );
    assert_eq!(
        r.lookup_premise(PremIdx(0)),
        Some(&in_fact(msg_var("m", 0)))
    );
    assert_eq!(
        r.lookup_premise(PremIdx(1)),
        Some(&in_fact(msg_var("n", 0)))
    );
    assert_eq!(r.lookup_premise(PremIdx(2)), None);
    assert_eq!(
        r.lookup_conclusion(ConcIdx(0)),
        Some(&out_fact(msg_var("m", 0)))
    );
    assert_eq!(r.lookup_conclusion(ConcIdx(1)), None);
}

/// The enumerators pair each fact with its own 0-based index, in list order.
/// Each enumerator reads the premise list or the conclusion list that matches
/// its name.
#[test]
fn enumerate_yields_indices() {
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("X"),
        vec![in_fact(msg_var("a", 0)), in_fact(msg_var("b", 0))],
        vec![out_fact(msg_var("c", 0))],
        vec![],
    );
    let prems: Vec<(PremIdx, LNFact)> = r
        .enumerate_premises()
        .map(|(i, f)| (i, f.clone()))
        .collect();
    assert_eq!(
        prems,
        vec![
            (PremIdx(0), in_fact(msg_var("a", 0))),
            (PremIdx(1), in_fact(msg_var("b", 0))),
        ]
    );
    let concs: Vec<(ConcIdx, LNFact)> = r
        .enumerate_conclusions()
        .map(|(i, f)| (i, f.clone()))
        .collect();
    assert_eq!(concs, vec![(ConcIdx(0), out_fact(msg_var("c", 0)))]);
}

/// `RuleAttributes::merge` is the combiner that SAPIC rule compression applies
/// (`tamarin_sapic::compression`).  An `Option` field takes the right value
/// when that value is `Some`.  It keeps the left value when the right value is
/// `None`.  A `bool` field is the `||` of the two sides, so a `true` on either
/// side survives.
#[test]
fn rule_attributes_merge_prefers_right_but_keeps_left() {
    use tamarin_utils::color::Rgb;
    let a = RuleAttributes {
        color: Some(Rgb::new(1.0, 0.0, 0.0)),
        role: Some("alice".into()),
        ignore_deriv_checks: true,
        ..Default::default()
    };
    let b = RuleAttributes {
        role: Some("bob".into()),
        is_sapic_rule: true,
        ..Default::default()
    };
    let merged = a.merge(b.clone());
    // The right value wins where it is `Some`.
    assert_eq!(merged.role, Some("bob".into()));
    // The left value survives where the right value is `None`.
    assert_eq!(merged.color, Some(Rgb::new(1.0, 0.0, 0.0)));
    // Both bools are the `||` of the two sides.  The right value alone does
    // not overwrite them.
    assert!(merged.is_sapic_rule);
    assert!(merged.ignore_deriv_checks);
    // A right value with all fields empty is the identity.  The merge keeps
    // every left field.  A `merge` that took the right value alone would
    // clear those fields.
    let kept = b.clone().merge(RuleAttributes::empty());
    assert_eq!(kept.role, Some("bob".into()));
    assert!(kept.is_sapic_rule);
    // A left value with all fields empty leaves the right value unchanged.
    let kept = RuleAttributes::empty().merge(b);
    assert_eq!(kept.role, Some("bob".into()));
    assert!(kept.is_sapic_rule);
}

#[test]
fn rule_info_conversion_round_trip() {
    let intr: IntrRuleAC = Rule::new(IntrRuleACInfo::Coerce, vec![], vec![], vec![]);
    let lifted: RuleAC = rule_ac_intr_to_rule_ac(intr.clone());
    let back = rule_ac_to_intr_rule_ac(lifted).unwrap();
    assert_eq!(back, intr);
    // The down-conversion is a filter, not a cast.  A protocol rule has no
    // intruder info, so the conversion returns `None`.
    let proto: RuleAC = Rule::new(
        RuleInfo::Proto(ProtoRuleACInfo {
            name: ProtoRuleName::Stand("P"),
            attributes: RuleAttributes::empty(),
            variants: Vec::new(),
            loop_breakers: Vec::new(),
        }),
        vec![],
        vec![],
        vec![],
    );
    assert!(rule_ac_to_intr_rule_ac(proto).is_none());
}

#[test]
fn intruder_predicates() {
    let f = FunSym::NoEq(tamarin_term::function_symbols::NoEqSym::new(
        b"f".to_vec(),
        1,
        tamarin_term::function_symbols::Privacy::Public,
        tamarin_term::function_symbols::Constructability::Constructor,
    ));
    assert!(is_constr_rule_info(&IntrRuleACInfo::ConstrRule {
        name: b"f".to_vec(),
        fun: f
    }));
    assert!(is_destr_rule_info(&IntrRuleACInfo::DestrRule {
        name: b"f".to_vec(),
        remaining_applications: 0,
        rhs_is_proper_subterm: true,
        rhs_is_constant: false,
        funs: vec![f]
    }));
    assert!(is_coerce_rule_info(&IntrRuleACInfo::Coerce));
    // Each predicate accepts only its own variant.  An over-broad `matches!`
    // arm fails here.  A predicate that always returns `true` also fails here.
    assert!(!is_constr_rule_info(&IntrRuleACInfo::Coerce));
    assert!(!is_destr_rule_info(&IntrRuleACInfo::Coerce));
    assert!(!is_coerce_rule_info(&IntrRuleACInfo::ConstrRule {
        name: b"f".to_vec(),
        fun: f
    }));
}

/// `IntrRuleACInfo`'s derived `Ord`/`Hash` walk the variants in
/// declaration order and, within a variant, the fields in declaration
/// order.  Pin both against a reshuffle: the variant sequence
/// `ConstrRule < DestrRule < Coerce`, and the `DestrRule` field order of
/// HS `DestrRule BC.ByteString Int Bool Bool [FunSym]`
/// (Theory/Model/Rule.hs:541).
#[test]
fn intr_rule_ac_info_ord_follows_declaration_order() {
    let sym = |n: &[u8]| {
        FunSym::NoEq(tamarin_term::function_symbols::NoEqSym::new(
            n.to_vec(),
            1,
            tamarin_term::function_symbols::Privacy::Public,
            tamarin_term::function_symbols::Constructability::Constructor,
        ))
    };
    let destr = |name: &[u8], rem: i64, sub: bool, con: bool, funs: Vec<FunSym>| {
        IntrRuleACInfo::DestrRule {
            name: name.to_vec(),
            remaining_applications: rem,
            rhs_is_proper_subterm: sub,
            rhs_is_constant: con,
            funs,
        }
    };
    let base = destr(b"a", 0, false, false, vec![]);
    // `name` outranks every later field.
    assert!(base < destr(b"b", -1, false, false, vec![]));
    // `remaining_applications` outranks fields 3-5.
    assert!(base < destr(b"a", 1, false, false, vec![]));
    assert!(destr(b"a", -1, true, true, vec![sym(b"z")]) < base);
    // `rhs_is_proper_subterm` outranks fields 4-5.
    assert!(base < destr(b"a", 0, true, false, vec![]));
    assert!(destr(b"a", 0, false, true, vec![sym(b"z")]) < destr(b"a", 0, true, false, vec![]));
    // `rhs_is_constant` outranks `funs`.
    assert!(base < destr(b"a", 0, false, true, vec![]));
    assert!(destr(b"a", 0, false, false, vec![sym(b"z")]) < destr(b"a", 0, false, true, vec![]));
    // `funs` breaks the remaining tie.
    assert!(base < destr(b"a", 0, false, false, vec![sym(b"a")]));

    // `ConstrRule`: `name` outranks `fun`.
    let constr = |name: &[u8], fun: FunSym| IntrRuleACInfo::ConstrRule {
        name: name.to_vec(),
        fun,
    };
    assert!(constr(b"a", sym(b"z")) < constr(b"b", sym(b"a")));

    // Variant order.
    assert!(constr(b"z", sym(b"z")) < destr(b"a", 0, false, false, vec![]));
    assert!(destr(b"z", i64::MAX, true, true, vec![sym(b"z")]) < IntrRuleACInfo::Coerce);
}

#[test]
fn print_extended_position() {
    let ep: ExtendedPosition = (PremIdx(2), 1, vec![0, 1, 0]);
    assert_eq!(print_position(&ep), "2_1_0_1_0_");
    assert_eq!(print_fact_position(&ep), "2");
}

#[test]
fn reserved_names_match_hs() {
    // HS `reservedRuleNames` (Model/Rule.hs:1284-1285), in its own order.
    assert_eq!(
        RESERVED_RULE_NAMES,
        [
            "Fresh",
            "irecv",
            "isend",
            "coerce",
            "fresh",
            "pub",
            "iequality"
        ]
    );
}

use crate::test_maude::maude_path;

#[test]
fn unify_ln_fact_eqs_tag_mismatch_no_unifiers() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let f1 = out_fact(msg_var("x", 0));
    let f2 = in_fact(msg_var("y", 0));
    let res = unify_ln_fact_eqs(&h, &[Equal { lhs: f1, rhs: f2 }]).unwrap();
    assert!(res.is_empty());
}

/// Facts that constrain nothing are facts with equal 0-ary tags.  They
/// short-circuit to exactly one unifier, and that unifier is the trivial one.
/// They do not short-circuit to "no unifiers".  That result would make every
/// premise with a nullary fact unsolvable.
#[test]
fn unify_ln_fact_eqs_nullary_facts_yield_one_trivial_unifier() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let f = crate::fact::proto_fact(crate::fact::Multiplicity::Linear, "P", vec![]);
    let res = unify_ln_fact_eqs(
        &h,
        &[Equal {
            lhs: f.clone(),
            rhs: f,
        }],
    )
    .unwrap();
    assert_eq!(res.len(), 1);
    assert!(res[0].is_empty());
}

#[test]
fn unify_ln_fact_eqs_two_vars() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let f1 = out_fact(msg_var("x", 0));
    let f2 = out_fact(msg_var("y", 0));
    let res = unify_ln_fact_eqs(&h, &[Equal { lhs: f1, rhs: f2 }]).unwrap();
    // At least one unifier; mgu binds one of the two vars.
    assert!(!res.is_empty());
    assert!(res.iter().all(|s| !s.is_empty()));
}

#[test]
fn unifiable_ln_facts_yes_no() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let f1 = out_fact(msg_var("x", 0));
    let f2 = out_fact(msg_var("y", 0));
    let f3 = in_fact(msg_var("y", 0));
    assert!(unifiable_ln_facts(&h, &f1, &f2).unwrap());
    assert!(!unifiable_ln_facts(&h, &f1, &f3).unwrap());
}

#[test]
fn unifiable_rule_ac_insts_same_shape() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let r1: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![in_fact(msg_var("a", 0))],
        vec![out_fact(msg_var("a", 0))],
        vec![],
    );
    let r2: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![in_fact(msg_var("b", 0))],
        vec![out_fact(msg_var("b", 0))],
        vec![],
    );
    assert!(unifiable_rule_ac_insts(&h, &r1, &r2).unwrap());
}

#[test]
fn unifiable_rule_ac_insts_different_info_no() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
    let r1: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![in_fact(msg_var("a", 0))],
        vec![out_fact(msg_var("a", 0))],
        vec![],
    );
    let r2: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::ISend),
        vec![in_fact(msg_var("b", 0))],
        vec![out_fact(msg_var("b", 0))],
        vec![],
    );
    assert!(!unifiable_rule_ac_insts(&h, &r1, &r2).unwrap());
}

/// A rule with one distinguishable variable in each of its four
/// variable-bearing lists.  The tests assert both `HasFrees` directions
/// against this rule.  A walk that drops any single list is therefore visible.
fn rule_with_a_var_in_every_list(base: u64) -> ProtoRuleE {
    Rule::new(
        ProtoRuleEInfo::standard("X"),
        vec![in_fact(msg_var("a", base))],
        vec![out_fact(msg_var("b", base + 1))],
        vec![fresh_fact(msg_var("c", base + 2))],
    )
    .with_new_vars(vec![msg_var("d", base + 3)])
}

/// `HasFrees::for_each_free` folds the premises, then the conclusions, then
/// the actions, then `new_vars`.  The test compares the exact sequence, not
/// only the membership.  A missing list shrinks the variable set of every
/// rename.  A different fold order shifts the fresh indices that
/// `bounds_max`-style seeds produce.
#[test]
fn has_frees_for_rule_visits_every_list_in_order() {
    use tamarin_term::lterm::{HasFrees, LSort};
    let r = rule_with_a_var_in_every_list(0);
    let mut seen: Vec<(String, u64)> = Vec::new();
    r.for_each_free(&mut |v| {
        assert_eq!(v.sort, LSort::Msg);
        seen.push((v.name.to_string(), v.idx));
    });
    assert_eq!(
        seen,
        vec![
            ("a".into(), 0),
            ("b".into(), 1),
            ("c".into(), 2),
            ("d".into(), 3),
        ]
    );
}

#[test]
fn d_exp_pmult_emap_rule_classification() {
    let dexp: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            name: b"_exp".to_vec(),
            remaining_applications: 0,
            rhs_is_proper_subterm: false,
            rhs_is_constant: false,
            funs: vec![],
        }),
        vec![],
        vec![],
        vec![],
    );
    let dpmult: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            name: b"_pmult".to_vec(),
            remaining_applications: 0,
            rhs_is_proper_subterm: false,
            rhs_is_constant: false,
            funs: vec![],
        }),
        vec![],
        vec![],
        vec![],
    );
    let dem: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            name: b"_em".to_vec(),
            remaining_applications: 0,
            rhs_is_proper_subterm: false,
            rhs_is_constant: false,
            funs: vec![],
        }),
        vec![],
        vec![],
        vec![],
    );
    let coerce: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![],
        vec![],
        vec![],
    );
    assert!(is_d_exp_rule(&dexp));
    assert!(!is_d_exp_rule(&dpmult));
    assert!(is_d_pmult_rule(&dpmult));
    assert!(is_d_emap_rule(&dem));
    assert!(is_coerce_rule_inst(&coerce));
}

#[test]
fn get_remaining_rule_applications_works() {
    let with_budget: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            name: b"_x".to_vec(),
            remaining_applications: 3,
            rhs_is_proper_subterm: false,
            rhs_is_constant: false,
            funs: vec![],
        }),
        vec![],
        vec![],
        vec![],
    );
    assert_eq!(get_remaining_rule_applications(&with_budget), 3);
    let no_budget: RuleACInst = Rule::new(
        RuleInfo::Intr(IntrRuleACInfo::Coerce),
        vec![],
        vec![],
        vec![],
    );
    assert_eq!(get_remaining_rule_applications(&no_budget), 0);
}

/// `HasFrees::map_free_with` rebuilds all four lists.  Every index comes back
/// shifted.  A list that the rebuild does not map keeps its original index,
/// and that index appears here as an entry with no shift.
#[test]
fn rename_rule_shifts_indices() {
    use tamarin_term::lterm::{HasFrees, LSort};
    let r = rule_with_a_var_in_every_list(5);
    // Shift by +10.
    let renamed = r.map_free(&mut |v| LVar {
        idx: v.idx + 10,
        ..v
    });
    let mut idxs = Vec::new();
    renamed.for_each_free(&mut |v| {
        assert_eq!(v.sort, LSort::Msg);
        idxs.push(v.idx);
    });
    assert_eq!(idxs, vec![15, 16, 17, 18]);
}

// =========================================================================
// `prettyRuleRestrGen` (Theory/Model/Rule.hs:1366-1382)
// =========================================================================

/// With no actions the middle of the `sep` is the bare `-->`
/// (Theory/Model/Rule.hs:1369-1370), and each fact list is
/// `fsep ["[", ppList, "]"]`, so a body that fits on one line carries a
/// space inside each bracket.  The premise and conclusion lists are `nest
/// 1`ed (Theory/Model/Rule.hs:1368,1375), which is the leading column the
/// rule body shows when it is rendered at column zero.
#[test]
fn pretty_rule_restr_gen_uses_the_bare_arrow_without_actions() {
    use tamarin_term::builtin::fresh_var;
    let prems = vec![fresh_fact(fresh_var("k", 0))];
    let concls = vec![out_fact(fresh_var("k", 0))];
    assert_eq!(
        pretty_rule_restr_gen(&prems, &[], &concls).render(),
        " [ Fr( ~k ) ] --> [ Out( ~k ) ]"
    );
}

/// With actions the arrow becomes `fsep ["--[", ppList acts, "]->"]`
/// (Theory/Model/Rule.hs:1371-1374), and the action list is punctuated by
/// the same comma as the premise and conclusion lists.
#[test]
fn pretty_rule_restr_gen_brackets_the_actions() {
    use crate::fact::{proto_fact, Multiplicity};
    use tamarin_term::builtin::fresh_var;
    let prems = vec![fresh_fact(fresh_var("k", 0))];
    let acts = vec![
        proto_fact(Multiplicity::Linear, "A", vec![fresh_var("k", 0)]),
        proto_fact(Multiplicity::Persistent, "B", vec![fresh_var("k", 0)]),
    ];
    let concls = vec![out_fact(fresh_var("k", 0))];
    assert_eq!(
        pretty_rule_restr_gen(&prems, &acts, &concls).render(),
        " [ Fr( ~k ) ] --[ A( ~k ), !B( ~k ) ]-> [ Out( ~k ) ]"
    );
}

/// A body too wide for the ribbon breaks at the `sep`
/// (Theory/Model/Rule.hs:1368-1375): the premises, the arrow and the
/// conclusions each take a line, and only the two fact lists carry the
/// `nest 1` column.
#[test]
fn pretty_rule_restr_gen_breaks_at_the_arrows() {
    use crate::fact::{proto_fact, Multiplicity};
    use tamarin_term::builtin::fresh_var;
    let prems: Vec<_> = (0..3)
        .map(|i| {
            proto_fact(
                Multiplicity::Linear,
                "Wide",
                vec![fresh_var("keymaterial", i)],
            )
        })
        .collect();
    let concls = vec![out_fact(fresh_var("k", 0))];
    let rendered = pretty_rule_restr_gen(&prems, &[], &concls).render();
    assert_eq!(
        rendered.lines().collect::<Vec<_>>(),
        vec![
            " [ Wide( ~keymaterial ), Wide( ~keymaterial.1 ), Wide( ~keymaterial.2 ) ]",
            "-->",
            " [ Out( ~k ) ]",
        ]
    );
}

/// HS keeps a rule's `_restrict` formulas on `preRestriction`
/// (Theory/Text/Parser/Rule.hs:135) and `liftedAddProtoRule` appends the
/// generated actions without touching the field
/// (Theory/Text/Parser.hs:188), so the elaborated rule carries them —
/// closed against the theory's signature, with its predicate atoms
/// unexpanded.
#[test]
fn elaborated_rule_carries_its_restrict_formulas() {
    let src = "theory T begin\n\
               functions: eq/2\n\
               rule A:\n  [In(x)] --[ _restrict(Ex #i. Act(eq(x,x)) @ #i) ]-> []\n\
               end";
    let mut parsed = tamarin_parser::parse_theory(src, &[]).unwrap();
    crate::rule_restriction::lift_rule_restrictions(&mut parsed).unwrap();
    let elab = crate::elaborate::elaborate(&parsed).unwrap();
    let source = parsed
        .items
        .iter()
        .find_map(|it| match it {
            tamarin_parser::ast::TheoryItem::Rule(r) if r.name == "A" => Some(r),
            _ => None,
        })
        .expect("parsed rule A");
    assert_eq!(source.embedded_restrictions.len(), 1);
    let expected =
        crate::formula::from_parser(&source.embedded_restrictions[0], &elab.signature.maude_sig)
            .unwrap();
    let rule = elab.rules().find(|r| r.name() == "A").expect("rule A");
    assert_eq!(rule.rule.info.restrictions, vec![expected]);
}

/// HS `prettyRuleAttributes` returns `emptyDoc` for a record equal to `mempty`
/// (Theory/Model/Rule.hs:1330-1334), which is what an unattributed rule
/// carries.
#[test]
fn pretty_rule_attribute_omits_an_empty_record() {
    let attr = RuleAttributes::empty();
    assert_eq!(pretty_rule_attribute(&attr).render(), "");
    assert_eq!(pretty_rule_attributes(&attr).render(), "");
}

/// HS `prettyRuleAttribute` renders `catMaybes [color, process,
/// no_derivcheck, issapicrule, role]` in that order, separated by
/// `punctuate comma` and wrapped in brackets by `prettyRuleAttributes`
/// (Theory/Model/Rule.hs:1313-1334).  A record with all five fields set fixes
/// both the order and the spelling of each one, and overruns the ribbon: the
/// `fsep` then breaks the list, with the continuation hanging one column in —
/// where `hcat [text "[", …]` left it.
#[test]
fn pretty_rule_attribute_renders_all_five_fields_in_order() {
    let attr = RuleAttributes {
        color: Some(tamarin_utils::color::Rgb::new(1.0, 0.0, 0.5)),
        process: Some(std::sync::Arc::new(crate::sapic::SharedProcess::new(
            crate::sapic::Process::Null(crate::sapic::ProcessParsedAnnotation::empty()),
        ))),
        ignore_deriv_checks: true,
        is_sapic_rule: true,
        role: Some("Initiator".to_string()),
    };
    assert_eq!(
        pretty_rule_attributes(&attr).render(),
        "[color=#ff0080, process=\"0\", no_derivcheck, issapicrule,\n role='Initiator']"
    );
}

/// Each field on its own: a `Nothing` field and a `False` flag drop out of
/// `catMaybes` (Theory/Model/Rule.hs:1315-1321), so a record with one field
/// set renders exactly that field.
#[test]
fn pretty_rule_attribute_renders_each_field_alone() {
    let with = |f: fn(&mut RuleAttributes)| {
        let mut attr = RuleAttributes::empty();
        f(&mut attr);
        pretty_rule_attributes(&attr).render()
    };
    assert_eq!(
        with(|a| a.color = Some(tamarin_utils::color::Rgb::new(0.0, 0.0, 0.0))),
        "[color=#000000]"
    );
    assert_eq!(
        with(
            |a| a.process = Some(std::sync::Arc::new(crate::sapic::SharedProcess::new(
                crate::sapic::Process::Null(crate::sapic::ProcessParsedAnnotation::empty())
            )))
        ),
        "[process=\"0\"]"
    );
    assert_eq!(with(|a| a.ignore_deriv_checks = true), "[no_derivcheck]");
    assert_eq!(with(|a| a.is_sapic_rule = true), "[issapicrule]");
    assert_eq!(with(|a| a.role = Some("R".to_string())), "[role='R']");
}

/// HS `equalUpToTerms` compares the rule name, the three list lengths and the
/// fact tags (Theory/Model/Rule.hs:958-968).  Two rules whose facts carry the
/// same tags but different terms are equal; a differing name, an extra action
/// or a differing tag separates them.
#[test]
fn equal_up_to_terms_ignores_terms() {
    use crate::fact::{proto_fact, Multiplicity};
    let ac = |name: &str, acts: Vec<crate::fact::LNFact>| ProtoRuleAC {
        info: ProtoRuleACInfo {
            name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
            attributes: RuleAttributes::empty(),
            variants: vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()],
            loop_breakers: vec![],
        },
        premises: vec![in_fact(msg_var("other", 0))],
        conclusions: vec![out_fact(msg_var("other", 0))],
        actions: acts,
        new_vars: vec![],
    };
    let e: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Send"),
        vec![in_fact(msg_var("m", 0))],
        vec![out_fact(msg_var("m", 0))],
        vec![],
    );
    assert!(equal_up_to_terms(&ac("Send", vec![]), &e));
    assert!(!equal_up_to_terms(&ac("Other", vec![]), &e));
    assert!(!equal_up_to_terms(
        &ac(
            "Send",
            vec![proto_fact(Multiplicity::Linear, "Act", vec![])]
        ),
        &e
    ));
    let mut wrong_tag = ac("Send", vec![]);
    wrong_tag.premises = vec![fresh_fact(msg_var("m", 0))];
    assert!(!equal_up_to_terms(&wrong_tag, &e));
}

/// HS `mergeOpenProtoRules` (OpenTheory.hs:592-603) collapses a run of
/// consecutive rule items sharing an E rule into one item whose AC list is
/// their concatenation, in order.  A non-rule item between two such rules
/// ends the run, and every other item keeps its place.
#[test]
fn merge_open_proto_rules_groups_consecutive_equal_e_rules() {
    use crate::theory::{
        merge_open_proto_rules, OpenProtoRule, ProofSkeleton, TheoryItem, TranslationElement,
    };
    // Two rules whose E half is the same `Send` rule and whose AC halves are
    // the two Maude narrowings `unfoldRuleVariants` names `Send___VARIANT_<i>`
    // (lib/theory/src/Rule.hs:63-79).
    let e: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Send"),
        vec![in_fact(msg_var("m", 0))],
        vec![out_fact(msg_var("m", 0))],
        vec![],
    );
    let variant = |i: usize| {
        let mut r = OpenProtoRule::new(Rule::new(
            ProtoRuleEInfo::standard(format!("Send___VARIANT_{i}")),
            vec![in_fact(msg_var("m", 0))],
            vec![out_fact(msg_var("m", 0))],
            vec![],
        ));
        r.rule_e = Some(Box::new(e.clone()));
        r
    };
    let other = OpenProtoRule::new(Rule::new(
        ProtoRuleEInfo::standard("Recv"),
        vec![in_fact(msg_var("m", 0))],
        vec![],
        vec![],
    ));
    let items: Vec<TheoryItem<OpenProtoRule, ProofSkeleton, TranslationElement>> = vec![
        TheoryItem::Rule(variant(1)),
        TheoryItem::Rule(variant(2)),
        TheoryItem::Text(("".to_string(), "between".to_string())),
        TheoryItem::Rule(variant(3)),
        TheoryItem::Rule(other),
    ];
    let merged = merge_open_proto_rules(&items);
    let names = |r: &crate::theory::MergedProtoRule| {
        r.rule_ac
            .iter()
            .map(|ac| match ac.info.name {
                ProtoRuleName::Stand(n) => n.to_string(),
                ProtoRuleName::Fresh => "Fresh".to_string(),
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(merged.len(), 4);
    match &merged[0] {
        TheoryItem::Rule(r) => {
            assert_eq!(r.rule_e, e);
            assert_eq!(names(r), vec!["Send___VARIANT_1", "Send___VARIANT_2"]);
        }
        other => panic!("expected a rule item, got {other:?}"),
    }
    assert!(matches!(merged[1], TheoryItem::Text(_)));
    match &merged[2] {
        TheoryItem::Rule(r) => assert_eq!(names(r), vec!["Send___VARIANT_3"]),
        other => panic!("expected a rule item, got {other:?}"),
    }
    // `Recv`'s AC half is its own E half up to terms, so `openProtoRule` drops
    // it (lib/theory/src/Rule.hs:55-58).
    match &merged[3] {
        TheoryItem::Rule(r) => assert!(r.rule_ac.is_empty()),
        other => panic!("expected a rule item, got {other:?}"),
    }
}

/// `closeProtoRule` maps `ClosedProtoRule ruE` over the `variants (modulo AC)`
/// blocks the source writes and reaches `variantsProtoRule` only for a rule
/// that writes none (lib/theory/src/Rule.hs:82-86), so a written variant keeps
/// the disjunction its parser gave it — `Disj [emptySubstVFresh]`
/// (`protoRuleACInfo`, Theory/Text/Parser/Rule.hs:138-143, see line 142).
/// `prettyOpenProtoRuleAsClosedRule` then takes its `length disj == 1` arm and
/// annotates the rule instead of quoting a `variants (modulo AC)` block
/// (OpenTheory.hs:836-843).  The rule here also carries a narrowing
/// disjunction, which is what `populate_rule_variants` leaves on every rule
/// item whose E rule holds a reducible sub-term.
#[test]
fn manual_variant_keeps_the_trivial_disjunction() {
    let opr = crate::theory::OpenProtoRule {
        rule: Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![in_fact(msg_var("c", 0))],
            vec![out_fact(msg_var("c", 0))],
            vec![],
        ),
        variant_substs: vec![tamarin_term::subst_vfresh::LNSubstVFresh::from_list([(
            LVar::new("c", tamarin_term::lterm::LSort::Msg, 0),
            msg_var("z", 4),
        )])],
        abstracted_rule: None,
        loop_breakers: Vec::new(),
        rule_e: None,
        rule_ac: vec![Rule::new(
            ProtoRuleEInfo::standard("R___VARIANT_1"),
            vec![in_fact(msg_var("z", 0))],
            vec![out_fact(msg_var("z", 0))],
            vec![],
        )],
    };
    let merged = crate::theory::open_proto_rule(&opr);
    assert_eq!(
        merged.rule_ac[0].info.variants,
        vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()]
    );
    let out = pretty_open_proto_rule_as_closed_rule(&merged).render();
    assert!(out.contains("has exactly the trivial AC variant"), "{out}");
    assert!(!out.contains("variants (modulo AC)"), "{out}");
}

/// HS `frees` at `Rule ProtoRuleEInfo` folds the info before the four fact
/// and new-variable lists, and `HasFrees ProtoRuleEInfo` reaches the
/// `_restrict` formulas (Theory/Model/Rule.hs:291-298, :491-494).  The
/// [`HasFrees`] impl on `Rule<I>` skips the info, so a variable that occurs
/// only in a restriction is visible to `proto_rule_e_frees` and to nothing
/// else; one that occurs in both is listed once.
#[test]
fn proto_rule_e_frees_folds_the_rule_restrictions() {
    use crate::atom::ProtoAtom;
    use crate::formula::ProtoFormula;
    use tamarin_term::lterm::{frees, BVar, LSort};
    use tamarin_term::vterm::var_term;

    let a = LVar::new("a", LSort::Msg, 0);
    let t = LVar::new("t", LSort::Node, 9);
    let mut r = rule_with_a_var_in_every_list(0);
    r.info.restrictions = vec![
        ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Free(t)))).and(ProtoFormula::Atom(
            ProtoAtom::EqE(var_term(BVar::Free(a)), var_term(BVar::Free(a))),
        )),
    ];

    let listed = |names: &[(&str, LSort, u64)]| -> Vec<LVar> {
        names
            .iter()
            .map(|(n, s, i)| LVar::new(*n, *s, *i))
            .collect()
    };
    assert_eq!(
        frees(&r),
        listed(&[
            ("a", LSort::Msg, 0),
            ("b", LSort::Msg, 1),
            ("c", LSort::Msg, 2),
            ("d", LSort::Msg, 3),
        ])
    );
    assert_eq!(
        proto_rule_e_frees(&r),
        listed(&[
            ("a", LSort::Msg, 0),
            ("b", LSort::Msg, 1),
            ("c", LSort::Msg, 2),
            ("d", LSort::Msg, 3),
            ("t", LSort::Node, 9),
        ])
    );
}
