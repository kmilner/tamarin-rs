use super::*;
use crate::fact::{fresh_fact, in_fact, out_fact};
use tamarin_term::builtin::msg_var;

#[test]
fn build_simple_proto_rule_e() {
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Send"),
        vec![fresh_fact(msg_var("k", 0))],
        vec![out_fact(msg_var("k", 0))],
        vec![],
    );
    assert_eq!(r.premises.len(), 1);
    assert_eq!(r.conclusions.len(), 1);
    assert!(matches!(r.info.name, ProtoRuleName::Stand(_)));
}

#[test]
fn rule_indices_lookup() {
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Echo"),
        vec![in_fact(msg_var("m", 0))],
        vec![out_fact(msg_var("m", 0))],
        vec![],
    );
    assert!(r.lookup_premise(PremIdx(0)).is_some());
    assert!(r.lookup_premise(PremIdx(1)).is_none());
    assert!(r.lookup_conclusion(ConcIdx(0)).is_some());
}

#[test]
fn enumerate_yields_indices() {
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("X"),
        vec![in_fact(msg_var("a", 0)), in_fact(msg_var("b", 0))],
        vec![],
        vec![],
    );
    let prems: Vec<PremIdx> = r.enumerate_premises().map(|(i, _)| i).collect();
    assert_eq!(prems, vec![PremIdx(0), PremIdx(1)]);
}

#[test]
fn rule_attributes_merge_prefers_right() {
    let a = RuleAttributes {
        role: Some("alice".into()),
        ..Default::default()
    };
    let b = RuleAttributes {
        role: Some("bob".into()),
        is_sapic_rule: true,
        ..Default::default()
    };
    let merged = a.merge(b);
    assert_eq!(merged.role, Some("bob".into()));
    assert!(merged.is_sapic_rule);
}

#[test]
fn rule_info_conversion_round_trip() {
    let intr: IntrRuleAC = Rule::new(IntrRuleACInfo::Coerce, vec![], vec![], vec![]);
    let lifted: RuleAC = rule_ac_intr_to_rule_ac(intr.clone());
    let back = rule_ac_to_intr_rule_ac(lifted).unwrap();
    assert_eq!(back, intr);
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
    assert!(!is_constr_rule_info(&IntrRuleACInfo::Coerce));
}

/// `IntrRuleACInfo`'s derived `Ord`/`Hash` walk the variants in
/// declaration order and, within a variant, the fields in declaration
/// order.  Pin both against a reshuffle: the variant sequence
/// `ConstrRule < DestrRule < Coerce`, and the `DestrRule` field order of
/// HS `DestrRule BC.ByteString Int Bool Bool [FunSym]` (Rule.hs:541).
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
fn reserved_names_include_fresh() {
    let r = reserved_rule_names();
    // Matches Haskell reservedRuleNames (Rule.hs):
    // ["Fresh", "irecv", "isend", "coerce", "fresh", "pub", "iequality"].
    assert!(r.contains("Fresh"));
    assert!(r.contains("coerce"));
    assert!(r.contains("iequality"));
    assert!(!r.contains("KU"));
}

fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return Some(p);
    }
    for c in ["/usr/local/bin/maude", "maude"] {
        if std::path::Path::new(c).exists() {
            return Some(c.to_string());
        }
    }
    None
}

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

#[test]
fn has_frees_for_rule_visits_premise_and_conclusion_vars() {
    use tamarin_term::lterm::{HasFrees, LSort};
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("X"),
        vec![in_fact(msg_var("a", 0))],
        vec![out_fact(msg_var("b", 1))],
        vec![],
    );
    let mut seen: Vec<(String, u64)> = Vec::new();
    r.for_each_free(&mut |v| {
        assert_eq!(v.sort, LSort::Msg);
        seen.push((v.name.to_string(), v.idx));
    });
    assert!(seen.contains(&("a".into(), 0)));
    assert!(seen.contains(&("b".into(), 1)));
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
    assert!(is_destr_rule(&dexp));
    assert!(!is_destr_rule(&coerce));
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

#[test]
fn rename_rule_shifts_indices() {
    use tamarin_term::lterm::{HasFrees, LSort};
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("X"),
        vec![in_fact(msg_var("a", 5))],
        vec![out_fact(msg_var("b", 7))],
        vec![],
    );
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
    assert!(idxs.contains(&15));
    assert!(idxs.contains(&17));
}
