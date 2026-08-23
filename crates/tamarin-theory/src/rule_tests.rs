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
