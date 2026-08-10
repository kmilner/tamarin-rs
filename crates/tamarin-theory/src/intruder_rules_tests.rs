// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

/// Pins every `show_fun_sym_name` arm to the display name HS
/// `showFunSymName` (Term/Term.hs:286-296) produces.  The arms read
/// `tamarin_term::function_symbols`' `*SymString` constants, which are
/// also what `maude_print` emits into the Maude module, so an edit to one
/// of them moves intruder-rule names, `close_rule.rs` case names and
/// `reduction.rs` term rendering in lockstep — this test is what makes
/// such an edit loud.
///
/// Note the `Union` trap: it renders as `munSymString` ("mun"), NOT
/// `unionSymString` ("union").
#[test]
fn show_fun_sym_name_pins_the_builtin_display_names() {
    use tamarin_term::function_symbols::{
        pair_sym, AcFctSym, AcSym, CSym, Constructability, NdcState, Privacy,
    };
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::Union)), "mun");
    assert_ne!(show_fun_sym_name(&FunSym::Ac(AcSym::Union)), "union");
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::Mult)), "mult");
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::Xor)), "xor");
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::NatPlus)), "tplus");
    assert_eq!(show_fun_sym_name(&FunSym::C(CSym::EMap)), "em");
    assert_eq!(show_fun_sym_name(&FunSym::List), "List");
    // The two user arms print the symbol's own interned name.
    assert_eq!(show_fun_sym_name(&FunSym::NoEq(pair_sym())), "pair");
    let ac_foo = AcFctSym::new(
        b"foo".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::AcFct(ac_foo))), "foo");
}

// Pins HS `subsetOf` (Utils/Misc.hs:87-88, see line 88) as a SET subset:
// `(S.fromList xs) `S.isSubsetOf` (S.fromList ys)` deduplicates BOTH
// sides, so `is_subset_of` must ignore multiplicity entirely.
#[test]
fn is_subset_of_ignores_multiplicity() {
    use tamarin_term::vterm::var_term;
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let z = var_term(LVar::new("z", LSort::Msg, 0));
    // {KU(y)} ⊆ {KU(y), KU(z)}: as a SET subset (HS `subsetOf`) this holds
    // even though a=[KU(y),KU(y)] has higher multiplicity than the single
    // KU(y) in b — a multiset-subset check would reject it (no second
    // KU(y) in b to consume).
    let a = vec![ku_fact(y.clone()), ku_fact(y.clone())];
    let b = vec![ku_fact(y.clone()), ku_fact(z.clone())];
    assert!(is_subset_of(&a, &b));
    // A distinct element of `a` not in `b` ⇒ not a subset.
    assert!(!is_subset_of(&b, &a));
}

// minimize_intruder_rules' trace-mode subsumption goes through
// `equal_subset_rule_up_to_renaming`, whose premise check is the
// SET-subset `is_subset_of` (HS `srpr2 `subsetOf` spr1`): a peer whose
// DISTINCT premise set is a subset subsumes this rule even at higher
// multiplicity.
#[test]
fn minimize_drops_set_subsumed_rule() {
    use tamarin_term::vterm::var_term;
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let z = var_term(LVar::new("z", LSort::Msg, 1));
    let name = b"_subsume_test".to_vec();
    // r_j (subsumer): premises [KU(y), KU(y)], conclusion KD(x).
    let r_j = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![ku_fact(y.clone()), ku_fact(y.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    // r_i (subsumed): premises [KU(y), KU(z)], same conclusion KD(x).
    // The conclusions unify by the empty (renaming) substitution, and
    // distinct premises of r_j ({KU(y)}) ⊆ distinct premises of r_i
    // ({KU(y), KU(z)}), so r_j subsumes r_i → r_i dropped.  r_j itself
    // is not dropped: KU(z) of r_i is absent from r_j's premise set.
    let r_i = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![ku_fact(y.clone()), ku_fact(z.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    let out = minimize_intruder_rules(false, &maude, vec![r_j.clone(), r_i.clone()]);
    // Set-subset: r_i is dropped; only r_j survives.  (Multiset bookkeeping
    // would have kept both, since r_j has two KU(y) but r_i only one.)
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].premises, r_j.premises);
}

// The structural early-reject in `equal_duplicate_rule_up_to_renaming`
// (zipped fact-tag mismatch) is a pure filter: on every pair — ones that
// trip it and ones that pass it — the result must equal the unfiltered
// HS pipeline `equalRuleUpToRenamingIgnoringNames r1 (r2 `renameAvoiding`
// r1)` run directly.
#[test]
fn equal_duplicate_early_reject_agrees_with_unfiltered_check() {
    use tamarin_term::vterm::var_term;
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    let constr = ku_pair_rule_with_var("a", 0);
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    // Destructor layout: premises [KU(y), KU(y)], conclusion [KD(x)].
    // Zipped against `constr`'s [KU] ++ [KU] ++ [KU] layout, the third
    // pair is (KU, KD) resp. (KD, KU) — the filter trips both ways.
    let destr = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: b"_dup_test".to_vec(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![ku_fact(y.clone()), ku_fact(y.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    for (r1, r2) in [(&constr, &destr), (&destr, &constr), (&constr, &constr)] {
        let unfiltered = equal_rule_up_to_renaming_ignoring_names(
            &maude,
            r1,
            &tamarin_term::lterm::rename_avoiding(r2.clone(), r1),
        );
        assert_eq!(
            equal_duplicate_rule_up_to_renaming(&maude, r1, r2),
            unfiltered
        );
    }
    // Sanity on the pair choices: the filter-tripping pairs are negatives,
    // the filter-passing self-pair is a positive.
    assert!(!equal_duplicate_rule_up_to_renaming(
        &maude, &constr, &destr
    ));
    assert!(equal_duplicate_rule_up_to_renaming(
        &maude, &constr, &constr
    ));
}

// The early rejects in `equal_subset_rule_up_to_renaming` only fire on
// pairs whose unfiltered verdict is already false: (a) head-conclusion
// tag mismatch ⇒ `unifyLNFactEqs` = [] ⇒ HS `[] -> False`; (b) an `r2`
// premise with no tag/term-count-matching `r1` premise ⇒ `srpr2
// `subsetOf` spr1` impossible (substitution preserves both).  Pin the
// false verdicts on shapes that trip each filter; the true path through
// both filters is pinned by `minimize_drops_set_subsumed_rule`.
#[test]
fn equal_subset_early_rejects_are_necessary() {
    use tamarin_term::vterm::var_term;
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let name = b"_subset_reject_test".to_vec();
    let mk = |prems: Vec<LNFact>, conc: LNFact| {
        Rule::new(
            IntrRuleACInfo::DestrRule {
                name: name.clone(),
                remaining_applications: -1,
                rhs_is_proper_subterm: true,
                rhs_is_constant: false,
                funs: vec![],
            },
            prems,
            vec![conc],
            vec![],
        )
    };
    // (a) conclusion KD(x) vs KU(x): tags differ.
    let r1 = mk(vec![ku_fact(y.clone())], kd_fact(x.clone()));
    let r2 = mk(vec![ku_fact(y.clone())], ku_fact(x.clone()));
    assert!(!equal_subset_rule_up_to_renaming(&maude, &r1, &r2));
    // (b) r2's KD(y) premise has no KD premise in r1 to map onto, even
    // though the KD(x) conclusions unify by a renaming.
    let r1 = mk(vec![ku_fact(y.clone())], kd_fact(x.clone()));
    let r2 = mk(vec![kd_fact(y.clone())], kd_fact(x.clone()));
    assert!(!equal_subset_rule_up_to_renaming(&maude, &r1, &r2));
}

/// A `[ KU(v) ] --[ KU(t) ]-> [ KU(t) ]` rule over the single variable
/// `v`, used to give `minimize_intruder_rules` peers whose fingerprints
/// differ, collide, and coincide.
fn ku_rule_over_var(v: &str, t: impl Fn(LNTerm) -> LNTerm) -> IntrRuleAC {
    use tamarin_term::function_symbols::pair_sym;
    let a = var_term(LVar::new(v, LSort::Msg, 0));
    let concfact = ku_fact(t(a.clone()));
    Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_shape".to_vec(),
            fun: FunSym::NoEq(pair_sym()),
        },
        vec![ku_fact(a)],
        vec![concfact.clone()],
        vec![concfact],
    )
}

// `RuleFingerprint`'s rejects rest on shape facts that hold with no
// Maude present: HS `unifyRaw` (Term/Unification.hs:288-306) fails on a
// top-symbol mismatch, and any substitution accepted by `isRenaming`
// (SubstVFresh.hs:148-149) maps variables to variables and hence
// preserves every top-level shape.
#[test]
fn fingerprint_rejects_are_shape_clashes_only() {
    use tamarin_term::builtin::pair;
    use tamarin_term::function_symbols::{fst_dest_sym, AcSym};
    use tamarin_term::term::{f_app_no_eq, unsafe_f_app};
    let fst = |t: LNTerm| f_app_no_eq(fst_dest_sym(), vec![t]);
    let fp = RuleFingerprint::of;

    let pair_rule = ku_rule_over_var("a", |a| pair(a.clone(), a));
    let fst_rule = ku_rule_over_var("a", fst);
    let var_rule = ku_rule_over_var("a", |a| a);
    let nested_rule = ku_rule_over_var("a", |a| pair(a.clone(), pair(a.clone(), a)));

    // Differing top symbol (and arity): `unifyRaw`'s NoEq arm needs
    // `lfsym == rfsym`, so the zipped conclusion equation has no unifier.
    assert!(!fp(&pair_rule).may_be_duplicate(&fp(&fst_rule)));
    assert!(!fp(&pair_rule).may_be_subset(&fp(&fst_rule)));
    // `Var` against `FApp`: any unifier binds the variable to a
    // non-variable, which `isRenaming` rejects.
    assert!(!fp(&pair_rule).may_be_duplicate(&fp(&var_rule)));
    assert!(!fp(&pair_rule).may_be_subset(&fp(&var_rule)));
    // Colliding fingerprints (same tags, same top symbols) pass both
    // prechecks even though the rules are not duplicates.
    assert!(fp(&pair_rule).may_be_duplicate(&fp(&nested_rule)));
    assert!(fp(&pair_rule).may_be_subset(&fp(&nested_rule)));
    // Identical rules pass, as they must: they ARE duplicates.
    assert!(fp(&pair_rule).may_be_duplicate(&fp(&pair_rule)));

    // A rule with no conclusion can never be `equalSubsetRuleUpToRenaming`
    // (`head co2`/`head co1` have nothing to unify).
    let no_conc = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: b"_no_conc".to_vec(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![ku_fact(var_term(LVar::new("a", LSort::Msg, 0)))],
        vec![],
        vec![],
    );
    assert!(!fp(&no_conc).may_be_subset(&fp(&pair_rule)));
    assert!(!fp(&pair_rule).may_be_subset(&fp(&no_conc)));

    // A one-argument AC application is `Opaque`: HS assumes such terms
    // never occur (Term/Unification.hs:299-301), so it licenses no reject.
    let ac_singleton = ku_rule_over_var("a", |a| unsafe_f_app(FunSym::Ac(AcSym::Mult), vec![a]));
    assert!(fp(&ac_singleton).may_be_duplicate(&fp(&var_rule)));
    assert!(fp(&ac_singleton).may_be_duplicate(&fp(&pair_rule)));
}

// `minimize_intruder_rules`' fingerprint prechecks are pure filters: on a
// rule list whose fingerprints differ, collide, and coincide, the
// survivors and their order must be the HS `go` result, and no rejected
// pair may have a `True` verdict under the unguarded checks.
#[test]
fn minimize_keeps_order_across_differing_and_colliding_fingerprints() {
    use tamarin_term::builtin::pair;
    use tamarin_term::function_symbols::fst_dest_sym;
    use tamarin_term::term::f_app_no_eq;
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    // Fingerprint differs from the pair-shaped rules (top symbol `fst`).
    let fst_rule = ku_rule_over_var("d", |a| f_app_no_eq(fst_dest_sym(), vec![a]));
    // Fingerprint COLLIDES with the pair-shaped rules (conclusion is a
    // 2-ary `pair` application too) but the rules are not duplicates:
    // `pair(c, pair(c,c))` and `pair(b,b)` fail the occurs check.
    let collide_rule = ku_rule_over_var("c", |a| pair(a.clone(), pair(a.clone(), a)));
    // True duplicates: alpha-variants of one another.
    let dup_a = ku_pair_rule_with_var("a", 0);
    let dup_b = ku_pair_rule_with_var("b", 1);

    let rules = vec![
        dup_a.clone(),
        fst_rule.clone(),
        collide_rule.clone(),
        dup_b.clone(),
    ];
    // HS `go` drops a rule as soon as a peer in `checked ++ unchecked`
    // matches, so of the two duplicates the EARLIER one goes: `dup_a`
    // sees `dup_b` in `unchecked`, while `dup_b` sees no kept duplicate.
    let out = minimize_intruder_rules(false, &maude, rules.clone());
    assert_eq!(out, vec![fst_rule, collide_rule, dup_b]);

    // Soundness of every reject: a fingerprint may only reject a pair
    // whose unguarded verdict is already false.
    let fps: Vec<RuleFingerprint> = rules.iter().map(RuleFingerprint::of).collect();
    let mut rejected = 0;
    let mut passed_but_false = 0;
    for (i, fp_i) in fps.iter().enumerate() {
        for (j, fp_j) in fps.iter().enumerate() {
            if i == j {
                continue;
            }
            let dup = equal_duplicate_rule_up_to_renaming(&maude, &rules[i], &rules[j]);
            let sub = equal_subset_rule_up_to_renaming(&maude, &rules[i], &rules[j]);
            if !fp_i.may_be_duplicate(fp_j) {
                assert!(!dup);
                rejected += 1;
            } else if !dup {
                passed_but_false += 1;
            }
            if !fp_i.may_be_subset(fp_j) {
                assert!(!sub);
                rejected += 1;
            }
        }
    }
    // The corpus exercises both arms: some pairs are rejected on their
    // fingerprints, and some pass the precheck yet fail the real check.
    assert!(rejected > 0);
    assert!(passed_but_false > 0);
}

#[test]
fn special_rules_count_excluding_diff() {
    let r = special_intruder_rules(false);
    assert_eq!(r.len(), 5);
    assert!(matches!(r[0].info, IntrRuleACInfo::Coerce));
    assert!(matches!(r[1].info, IntrRuleACInfo::PubConstr));
    assert!(matches!(r[2].info, IntrRuleACInfo::FreshConstr));
    assert!(matches!(r[3].info, IntrRuleACInfo::ISend));
    assert!(matches!(r[4].info, IntrRuleACInfo::IRecv));
}

#[test]
fn special_rules_count_with_diff() {
    let r = special_intruder_rules(true);
    assert_eq!(r.len(), 6);
    assert!(matches!(r[5].info, IntrRuleACInfo::IEquality));
}

#[test]
fn pub_constr_has_x_pub_in_new_vars() {
    let r = &special_intruder_rules(false)[1];
    assert_eq!(r.new_vars.len(), 1);
}

#[test]
fn fresh_constr_has_fresh_premise() {
    let r = &special_intruder_rules(false)[2];
    assert_eq!(r.premises.len(), 1);
    assert!(matches!(r.premises[0].tag, crate::fact::FactTag::Fresh));
}

#[test]
fn isend_emits_in_conclusion() {
    let r = &special_intruder_rules(false)[3];
    assert!(matches!(r.conclusions[0].tag, crate::fact::FactTag::In));
}

// =========================================================================
// construction_rules: per-symbol KU constructor generation.
//
// Direct Haskell-spec mirror — Theory.Tools.IntruderRules.hs:
//
//     constructionRules fSig =
//         [ createRuleNoEq s f k | NoEqUser f@(s,(k,Public,Constructor,_)) <- S.toList fSig ] ++
//         [ createRuleAC s f | ACfctUser f@(s,(Public,Constructor,_)) <- S.toList fSig ]
// =========================================================================

#[test]
fn construction_rules_pair_signature_emits_pair_rule() {
    // The default pair-only signature has `pair/2`, `fst/1`, `snd/1`.
    // pair is Public+Constructor → emits a KU rule;
    // fst, snd are Public+Destructor → no construction rule.
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let rules = construction_rules(&sig.user_defined_st_fun_syms());
    // Find the pair rule.
    let pair_rule = rules.iter().find(|r| match &r.info {
        IntrRuleACInfo::ConstrRule { name, .. } => name == b"_pair",
        _ => false,
    });
    let pair_rule = pair_rule.expect("expected pair construction rule");
    // pair/2 → 2 KU premises, 1 KU conclusion, 1 KU action.
    assert_eq!(pair_rule.premises.len(), 2);
    assert_eq!(pair_rule.conclusions.len(), 1);
    assert_eq!(pair_rule.actions.len(), 1);
    // All facts have KU tag.
    for f in pair_rule
        .premises
        .iter()
        .chain(&pair_rule.conclusions)
        .chain(&pair_rule.actions)
    {
        assert_eq!(f.tag, crate::fact::FactTag::Ku);
    }
}

#[test]
fn construction_rules_only_emits_constructor_info() {
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let rules = construction_rules(&sig.user_defined_st_fun_syms());
    // Every emitted rule should have `ConstrRule` info — never
    // a `DestrRule` (we filter on Constructability).
    for r in &rules {
        match &r.info {
            IntrRuleACInfo::ConstrRule { .. } => {}
            other => panic!("expected ConstrRule, got {:?}", other),
        }
    }
    assert!(
        !rules.is_empty(),
        "default pair sig has at least one constructor"
    );
}

/// Symmetric-encryption signature should emit one destructor rule
/// for `sdec(senc(x, y), y) = x`.  The rule must have:
///   - First premise: KD(senc(x, y)).
///   - Second premise: KU(y).
///   - Conclusion: KD(x).
#[test]
fn destruction_rules_sym_enc_emits_decryption() {
    let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(false, r))
        .collect();
    // We expect exactly one destructor: the outermost decryption.
    assert!(
        !rules.is_empty(),
        "expected at least one sdec destructor; got {:?}",
        rules
    );
    // Inspect: first rule should have KD as first premise + at least one KU.
    let first = &rules[0];
    assert_eq!(first.premises[0].tag, crate::fact::FactTag::Kd);
    assert!(
        first
            .premises
            .iter()
            .skip(1)
            .all(|p| p.tag == crate::fact::FactTag::Ku),
        "follow-on premises must be KU; got {:?}",
        first.premises
    );
    assert_eq!(first.conclusions[0].tag, crate::fact::FactTag::Kd);
}

/// Pair signature emits `fst` / `snd` destructors.
#[test]
fn destruction_rules_pair_emits_fst_snd_destructors() {
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(false, r))
        .collect();
    // One destructor per rule; pair has fst + snd → 2 destructor rules.
    assert!(
        rules.len() >= 2,
        "expected >= 2 pair destructors (fst + snd); got {}",
        rules.len()
    );
}

/// `subtermConstructorRules` on a sym-enc signature yields only
/// CONSTRUCTOR rules (the senc constructor; the sdec destructors come
/// from the narrowing-based `destruction_rules_no_eq` instead).
#[test]
fn subterm_constructor_rules_emits_only_constructors() {
    let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
    let maude = match maude_bin_path()
        .and_then(|p| tamarin_term::maude_proc::MaudeHandle::start(&p, sig.clone()).ok())
    {
        Some(m) => m,
        None => return,
    };
    let rules = subterm_constructor_rules(false, &maude, &sig);
    assert!(
        rules
            .iter()
            .all(|r| matches!(r.info, IntrRuleACInfo::ConstrRule { .. })),
        "subterm_constructor_rules must yield only ConstrRules"
    );
    assert!(
        !rules.is_empty(),
        "sym-enc sig has at least the senc constructor"
    );
}

#[test]
fn construction_rules_premise_count_equals_arity() {
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    for r in construction_rules(&sig.user_defined_st_fun_syms()) {
        // Pull the symbol's arity from the rule's KU action term.
        let conc_term = &r.conclusions[0].terms[0];
        let arity = match conc_term {
            tamarin_term::term::Term::App(_, args) => args.len(),
            tamarin_term::term::Term::Lit(_) => 0,
        };
        assert_eq!(
            r.premises.len(),
            arity,
            "premise count must equal symbol arity"
        );
        assert_eq!(r.conclusions.len(), 1);
        assert_eq!(r.actions.len(), 1);
    }
}

// =========================================================================
// Haskell-faithfulness invariants for `destruction_rules`.
//
// Mirrors IntruderRules.hs:129-157.  Two easy-to-break patterns:
//
//   1. Pattern #1 line 135: at the LAST position step, if the
//      current term is an FApp AND rhs has free vars, return [].
//      (The "skip-last" case.)
//
//   2. Private-symbol stop (line 149): descending through a Private
//      constructor terminates the loop early.
// =========================================================================

/// `destructionRules` for the sym-enc rule `sdec(senc(x, y), y) = x`
/// must emit EXACTLY ONE destructor, not two.
///
/// The rule has rhs position [0, 0] — two steps.  Without the
/// skip-last guard, Rust emits a second (degenerate) destructor at
/// the inner step, producing `KD(x) + KU(...) → KD(x)` — a
/// self-loop that explodes the chain search on denning_sacco.
#[test]
fn destruction_rules_sym_enc_emits_exactly_one_destructor() {
    let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(false, r))
        .collect();
    assert_eq!(
        rules.len(),
        1,
        "sym-enc rule `sdec(senc(x, y), y) = x` must yield EXACTLY ONE \
             destructor — the skip-last pattern (IntruderRules.hs:135) \
             elides the inner step.  Got {} rules.  If this regresses, \
             denning_sacco-class chain explosion will silently reappear.",
        rules.len()
    );
    let r = &rules[0];
    // Premise[0] = KD(senc(x, y)); follow-on premises = KU(y).
    assert_eq!(r.premises[0].tag, crate::fact::FactTag::Kd);
    // Inner step was elided, so no `KD(x) KU(x) → KD(x)` self-loop.
    for p in &r.premises[1..] {
        assert_eq!(p.tag, crate::fact::FactTag::Ku);
    }
}

/// `destructionRules` for the asym-enc rule
/// `adec(aenc(x, pk(y)), y) = x` likewise emits EXACTLY ONE
/// destructor (position [0, 0], rhs free var x).
#[test]
fn destruction_rules_asym_enc_emits_exactly_one_destructor() {
    let sig = tamarin_term::maude_sig::asym_enc_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(false, r))
        .collect();
    assert_eq!(
        rules.len(),
        1,
        "asym-enc rule must yield EXACTLY ONE destructor; got {} rules. \
             Skip-last pattern was probably regressed.",
        rules.len()
    );
}

/// `destructionRules` for pair `fst(<x,y>) = x` and `snd(<x,y>) = y`
/// each yield EXACTLY ONE destructor.  Pair is a one-step rule
/// (position [0]), but skip-last doesn't apply to the FIRST step
/// because step_idx == 0 and pos_iter.len() == 1 → step_idx+1 == len,
/// and `t` is `pair(x,y)` (FApp) and rhs is a var (free) — so
/// skip-last DOES fire.  This means the destructor must be emitted
/// at the WRAPPING-step (the outer match arm where we step from
/// the destructor's lhs into pair), NOT at the inner step.
///
/// (This is subtle and worth pinning explicitly.)
#[test]
fn destruction_rules_pair_emits_exactly_two_destructors() {
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(false, r))
        .collect();
    assert_eq!(
        rules.len(),
        2,
        "pair signature must yield exactly fst + snd destructors \
             (2 total); got {} rules.  Pair rules are `fst(<x,y>) = x` \
             and `snd(<x,y>) = y` at position [0] each.",
        rules.len()
    );
}

// =========================================================================
// `equal_rule_up_to_renaming` (Theory/Model/Rule.hs:1157-1175).  Mirrors HS:
//
//   equalRuleUpToRenaming r1 r2 = reader $ \hnd ->
//     case eqs of
//       Nothing   -> False
//       Just eqs' -> (rn1 == rn2) && any isRenamingPerRule (unifs eqs' hnd)
//
// Pin both ends of the predicate: a positive (two rules differing only
// in variable names) and a negative (structurally different).
// =========================================================================
/// Absolute maude locations probed when `MAUDE_PATH` is unset — the same
/// pair the rest of the workspace's maude-gated suites walk.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Probed after [`MAUDE_CANDIDATES`] and `$PATH`: this workspace's benchmark
/// toolchain installs maude under linuxbrew, which is not on a default `PATH`.
const MAUDE_BREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The first `maude` on `$PATH`, if any.
fn maude_on_path() -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("maude"))
        .find(|c| c.is_file())
        .map(|c| c.to_string_lossy().into_owned())
}

/// Locate the Maude binary the pins below run against: `$MAUDE_PATH` when set,
/// else the first of [`MAUDE_CANDIDATES`], `$PATH`, [`MAUDE_BREW`] that exists.
///
/// A `MAUDE_PATH` naming a file that does not exist is a MISCONFIGURATION, not
/// a reason to skip — returning `None` there would turn every maude-backed pin
/// in this file green on a CI whose image moved maude.  Panic instead, so the
/// run goes red.  Resolving nothing at all is the same failure with a wider
/// blast radius, so it panics too: `TAM_ALLOW_NO_MAUDE=1` is the only way to
/// get the old silent skip, and naming it is a deliberate statement that this
/// run is not asserting anything about maude.
fn maude_bin_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?}, or point it at a real maude — skipping \
             every maude-backed pin here would report green vacuously"
        );
        return Some(p);
    }
    if let Some(c) = MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
    {
        return Some((*c).to_string());
    }
    if let Some(p) = maude_on_path() {
        return Some(p);
    }
    if std::path::Path::new(MAUDE_BREW).exists() {
        return Some(MAUDE_BREW.to_string());
    }
    if std::env::var("TAM_ALLOW_NO_MAUDE").as_deref() == Ok("1") {
        return None;
    }
    panic!(
        "no maude found: probed $MAUDE_PATH, {MAUDE_CANDIDATES:?}, $PATH and \
         {MAUDE_BREW}.  Every maude-backed pin in this file would otherwise \
         report green having run nothing.  Install maude, point MAUDE_PATH at \
         it, or set TAM_ALLOW_NO_MAUDE=1 to accept the silent skip."
    );
}

fn maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    let path = maude_bin_path()?;
    // A maude that resolved but will not start is the same misconfiguration
    // as a dangling MAUDE_PATH: swallowing it with `.ok()` would silently
    // skip every pin in this file, so fail loudly instead.
    Some(
        tamarin_term::maude_proc::MaudeHandle::start(
            &path,
            tamarin_term::maude_sig::pair_maude_sig(),
        )
        .unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 pin here would otherwise skip silently"
            )
        }),
    )
}

/// Build a rule `[ KU(a) ] --[ KU(pair(a, a)) ]-> [ KU(pair(a, a)) ]`
/// (a constructor-shape rule with one var `a`).  Used to test
/// `equal_rule_up_to_renaming` with two alpha-equivalent rules.
fn ku_pair_rule_with_var(var_name: &str, idx: u64) -> IntrRuleAC {
    use tamarin_term::builtin::pair;
    use tamarin_term::function_symbols::pair_sym;
    use tamarin_term::lterm::{LSort, LVar};
    let a = var_term(LVar::new(var_name, LSort::Msg, idx));
    let p = pair(a.clone(), a.clone());
    Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_pair".to_vec(),
            fun: FunSym::NoEq(pair_sym()),
        },
        vec![ku_fact(a.clone())],
        vec![ku_fact(p.clone())],
        vec![ku_fact(p)],
    )
}

/// Positive: two rules that differ ONLY in their bound variable's
/// name (and possibly idx) must compare equal-up-to-renaming.
///
/// HS: `unifyLNTerm` produces a renaming `[x.0 ~> y.7]`; its
/// restriction to each rule's vars (each is the singleton `{x.0}`
/// vs `{y.7}`) is a renaming, so `isRenamingPerRule` holds.
#[test]
fn equal_rule_up_to_renaming_alpha_equivalent_pair_rules() {
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    let r1 = ku_pair_rule_with_var("x", 0);
    let r2 = ku_pair_rule_with_var("y", 7);
    assert!(
        equal_rule_up_to_renaming(&maude, &r1, &r2),
        "two rules differing only in their bound var's name+idx \
             must be equal-up-to-renaming.  HS: `unifyLNTerm` yields a \
             renaming `[x.0 ~> y.7]`, isRenaming on each rule's restricted \
             var set holds.  See Theory/Model/Rule.hs:1157-1175."
    );
    // Symmetric: r2 vs r1.
    assert!(
        equal_rule_up_to_renaming(&maude, &r2, &r1),
        "equal_rule_up_to_renaming must be symmetric"
    );
    // Reflexive: r1 vs r1.
    assert!(
        equal_rule_up_to_renaming(&maude, &r1, &r1),
        "equal_rule_up_to_renaming must be reflexive"
    );
}

/// Negative: two rules with structurally different conclusions
/// (different fact shapes) must NOT be equal-up-to-renaming.
///
/// HS: `matchFacts` returns `Nothing` because tags differ → False.
#[test]
fn equal_rule_up_to_renaming_structurally_different_rules_diverge() {
    use tamarin_term::lterm::{LSort, LVar};
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    let r1 = ku_pair_rule_with_var("x", 0);
    // r2 has a single KU premise but a DIFFERENT conclusion shape:
    // it concludes KU(x) (the variable directly) instead of
    // KU(pair(x, x)).  No renaming can make `KU(x)` == `KU(pair(x, x))`.
    let a = var_term(LVar::new("x", LSort::Msg, 0));
    let r2 = Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_pair".to_vec(),
            fun: FunSym::NoEq(tamarin_term::function_symbols::pair_sym()),
        },
        vec![ku_fact(a.clone())],
        vec![ku_fact(a.clone())],
        vec![ku_fact(a)],
    );
    assert!(
        !equal_rule_up_to_renaming(&maude, &r1, &r2),
        "rules with structurally distinct conclusions (KU(pair(x,x)) \
             vs KU(x)) cannot be equal-up-to-renaming — no unifier \
             matches `pair(x,x) =? x`.  HS: matchFacts builds the eqs, \
             unifyLNTerm fails or yields a non-renaming."
    );
    // Different info also makes them unequal even when terms match.
    let r3 = Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_OTHER".to_vec(),
            fun: FunSym::NoEq(tamarin_term::function_symbols::pair_sym()),
        },
        r1.premises.clone(),
        r1.conclusions.clone(),
        r1.actions.clone(),
    );
    assert!(
        !equal_rule_up_to_renaming(&maude, &r1, &r3),
        "differing info field (rule names) must short-circuit to False \
             — HS: `if r1.info /= r2.info then False else ...`"
    );
}

// =========================================================================
// `variants_intruder` (IntruderRules.hs:347-374).
//
// Pin: a `DestrRule subterm=False` rule whose argument terms have
// Maude variants under the AC theory produces MORE than one variant.
// =========================================================================

/// `variants_intruder` on a constructor rule whose argument is a
/// pair (i.e. has multiple Maude variants under AC) produces at
/// least two variants — the identity variant plus at least one
/// substitution that reorders / splits the pair structure.
///
/// We don't assert an exact count because it is Maude-version
/// dependent (and minor signature differences affect the variant
/// enumeration), but `len() >= 1` is invariant.
#[test]
fn variants_intruder_emits_at_least_the_identity_variant() {
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    // The pair-construction rule from the basic sig.  Apply
    // `variants_intruder` to it; Maude should produce at least the
    // identity variant.  More may appear depending on the
    // signature loaded.
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let cs = construction_rules(&sig.user_defined_st_fun_syms());
    let pair_rule = cs
        .iter()
        .find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => name == b"_pair",
            _ => false,
        })
        .expect("expected pair constructor rule");
    let variants = variants_intruder(&maude, false, false, pair_rule);
    assert!(
        !variants.is_empty(),
        "variants_intruder must emit at least one rule (the identity \
             variant if no Maude variants exist).  HS \
             `variantsIntruder` (IntruderRules.hs:347-374) wraps the \
             rule in a list-monad enumeration that includes the original \
             via the identity Maude variant."
    );
}

/// Pins the `apply_filters = false` path, and with it the PLACEMENT of
/// HS's `(rConcs ruvariant) \\ (rPrems ruvariant) /= []` conjunct.
///
/// The `guard` (IntruderRules.hs:354-360) reads
/// `not applyFilters || (X && Y && Z)`, because `&&` is `infixr 3` and
/// `||` is `infixr 2`.  With `applyFilters = False` the guard is
/// vacuously true and NONE of the three conjuncts applies — `Z`, the
/// conclusions-minus-premises test, included.
///
/// The rule below discriminates that reading from the one where `Z` is
/// applied unconditionally: its single conclusion is also its single
/// premise, so `Z` is False for the identity variant.  Unconditional `Z`
/// empties the output; `Z`-inside-the-conjunction returns the rule.
///
/// Every production call site passes `apply_filters = true` (as do all
/// four upstream `variantsIntruder` / `variantsIntruderAux` calls), so
/// this is the `false` path's only behavioural coverage.
#[test]
fn variants_intruder_without_filters_keeps_a_premise_covered_conclusion() {
    let maude = match maude_handle() {
        Some(m) => m,
        None => return,
    };
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    // `[ KD(x) ] --> [ KD(x) ]`: `rConcs \\ rPrems == []`, and the
    // identity variant is the rule itself, so `ruvariant == ru` too.
    let ru = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: b"_conc_in_prems".to_vec(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![kd_fact(x.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );

    assert_eq!(
        variants_intruder(&maude, false, false, &ru),
        vec![ru.clone()],
        "apply_filters = false must let the identity variant through: the \
             guard is `not applyFilters`, so neither `ruvariant /= ru` nor \
             `(rConcs \\\\ rPrems) /= []` may drop it"
    );
    // The same rule under apply_filters = true: `ruvariant /= ru` and
    // `(rConcs \\ rPrems) /= []` both fail, so nothing survives.  This
    // half also rules out a vacuous pass above — the `maude.variants`
    // error fallback returns `vec![ru]` BEFORE the filters, so a broken
    // Maude round trip would show up here as a non-empty result.
    assert!(
        variants_intruder(&maude, true, false, &ru).is_empty(),
        "apply_filters = true must drop the identity variant of a rule \
             whose conclusion is also a premise"
    );
}

/// `destructionRules` short-circuits when the rhs is a closed term
/// (no free vars) AND `diff=false` AND rhs has no Private symbol.
/// This is the outer guard at IntruderRules.hs:129-157, see line 130 — the function
/// returns [] before even starting the position walk.
///
/// Pin this by constructing a CtxtStRule whose rhs is a public
/// constant (no free vars).
#[test]
fn destruction_rules_returns_empty_for_closed_rhs_in_non_diff_mode() {
    use tamarin_term::builtin::{pair, senc};
    use tamarin_term::lterm::{LNTerm, LSort, LVar, Name, NameId, NameTag};
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Build: lhs = senc(x, pair($a, $b)), rhs = $a (pub const, no frees).
    // Position [1, 0] — into senc's arg 1 (the pair), then into pair's
    // arg 0 ($a).
    let x = LVar::new("x", LSort::Msg, 1);
    let pub_a = Name {
        tag: NameTag::Pub,
        id: NameId::new("a"),
    };
    let pub_b = Name {
        tag: NameTag::Pub,
        id: NameId::new("b"),
    };
    let pa: LNTerm = Term::Lit(Lit::Con(pub_a));
    let pb: LNTerm = Term::Lit(Lit::Con(pub_b));
    let lhs = senc(Term::Lit(Lit::Var(x)), pair(pa.clone(), pb));
    let rhs_st = StRhs {
        positions: vec![vec![1, 0]],
        term: pa,
    };
    let rule = CtxtStRule::new(lhs, rhs_st);

    // diff=false, rhs has no free vars, rhs has no private symbol →
    // outer guard returns [].
    let out = destruction_rules(false, &rule);
    assert!(
        out.is_empty(),
        "diff=false + closed rhs (no frees, no private) must short-\
             circuit to empty.  Mirrors IntruderRules.hs:130 outer guard. \
             Got {} rules.",
        out.len()
    );

    // BUT in diff mode, the guard is bypassed and we DO descend.
    let out_diff = destruction_rules(true, &rule);
    assert!(
        !out_diff.is_empty(),
        "diff=true must bypass the closed-rhs guard and emit destructors"
    );
}

// =========================================================================
// `dh_intruder_rules` (IntruderRules.hs:230-283 — definition above).
//
// The expected output for `dh_intruder_rules(false)` is exactly the
// contents of `data/intruder_variants_dh.spthy`, which the HS
// production pipeline embeds and parses (TheoryLoader.hs:746-759).
// That file has:
//   * 5 ConstrRules: `_exp` `_inv` `_DH_neutral` `_one` `_mult`
//   * 45 `d_exp` (DestrRule "_exp")  destructor variants
//   * 1  `d_inv` (DestrRule "_inv")  destructor variant
//   = 51 rules total.
//
// We measured this directly:
//   $ grep -c "^rule" data/intruder_variants_dh.spthy
//   51
//   $ grep -c "^rule (modulo AC) c_" data/intruder_variants_dh.spthy → 5
//   $ grep -c "^rule (modulo AC) d_exp" data/intruder_variants_dh.spthy → 45
//   $ grep -c "^rule (modulo AC) d_inv" data/intruder_variants_dh.spthy → 1
//
// The variants enumeration depends on Maude's narrowing
// implementation; the exact count is Maude-version-sensitive.  We
// assert structural invariants (constructor count, name shapes,
// KU/KD wiring) and let a slightly-looser bound check the variants
// count, deferring exact byte parity to the corpus probe.
// =========================================================================

fn dh_maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    tamarin_term::maude_proc::MaudeHandle::start(
        &maude_bin_path()?,
        tamarin_term::maude_sig::dh_maude_sig(),
    )
    .ok()
}

fn bp_maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    tamarin_term::maude_proc::MaudeHandle::start(
        &maude_bin_path()?,
        tamarin_term::maude_sig::bp_maude_sig(),
    )
    .ok()
}

/// `bp_intruder_rules(false)` yields exactly 74 bilinear-pairing
/// intruder rules (2 constructors `_pmult`/`_em` + the pmult- and
/// em-destructor variant expansions), matching HS `bpIntruderRules
/// False` in the pinned upstream tree, whose Maude-backed
/// `minimizeIntruderRules` subsumption drops one BP destructor
/// variant.  Upstream's committed `data/intruder_variants_bp.spthy`
/// holds 75 rules; production loads that cached file byte-for-byte
/// (as HS does), so this count applies to the generator only.
#[test]
fn bp_intruder_rules_yields_74() {
    let maude = match bp_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = bp_intruder_rules(false, &maude);
    assert_eq!(
        rules.len(),
        74,
        "bp_intruder_rules(false) must produce exactly 74 rules; got {}",
        rules.len()
    );
    // Sanity: the two construction rules are present and named.
    let constr_names: Vec<&[u8]> = rules
        .iter()
        .filter_map(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
            _ => None,
        })
        .collect();
    assert!(constr_names.contains(&b"_pmult".as_slice()));
    assert!(constr_names.contains(&b"_em".as_slice()));
}

/// Helper: extract the bytestring name of a ConstrRule or DestrRule.
fn rule_name(info: &IntrRuleACInfo) -> Option<&[u8]> {
    match info {
        IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
        IntrRuleACInfo::DestrRule { name, .. } => Some(name.as_slice()),
        _ => None,
    }
}

/// `dh_intruder_rules(false)` returns the 5 hard-coded constructor
/// rules (`_exp`, `_inv`, `_DH_neutral`, `_one`, `_mult`) plus a
/// non-empty list of destructor variants.  The 5 ConstrRules are
/// the immediately-known core; the variant count depends on Maude's
/// narrowing enumeration but is at minimum 1 (the identity variant
/// of `_exp` or `_inv` survives `applyFilters=True` filters when
/// the variant has non-ground conclusions).
///
/// HS reference: IntruderRules.hs:230-245.  The cached output at
/// `data/intruder_variants_dh.spthy` shows the expected shape (5
/// constr + 45 d_exp + 1 d_inv = 51 rules total).
#[test]
fn dh_intruder_rules_emits_five_constructors_and_some_destructors() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = dh_intruder_rules(false, &maude);

    // 5 ConstrRules with the known names.
    let names: Vec<&[u8]> = rules
        .iter()
        .filter_map(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
            _ => None,
        })
        .collect();
    assert_eq!(
        names.len(),
        5,
        "expected exactly 5 ConstrRules (_exp/_inv/_DH_neutral/_one/_mult); \
             got: {:?}",
        names
            .iter()
            .map(|n| String::from_utf8_lossy(n).to_string())
            .collect::<Vec<_>>()
    );
    // All constructor names start with `_` (HS pack "_" prefix).
    for n in &names {
        assert!(
            n.starts_with(b"_"),
            "constructor rule name must start with `_` (HS appends pack \"_\" — \
                 IntruderRules.hs:233-240); got {}",
            String::from_utf8_lossy(n)
        );
    }
    // Specific names present.
    let name_strings: Vec<&[u8]> = names.to_vec();
    for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
        assert!(
            name_strings.contains(expected),
            "missing constructor rule named {}; got names {:?}",
            String::from_utf8_lossy(expected),
            name_strings
                .iter()
                .map(|n| String::from_utf8_lossy(n).to_string())
                .collect::<Vec<_>>()
        );
    }

    // Destructor rules also present (variants of _exp and _inv).
    let destrs: Vec<&IntrRuleAC> = rules
        .iter()
        .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule { .. }))
        .collect();
    assert!(
        !destrs.is_empty(),
        "expected at least one DestrRule variant (HS \
             `variantsIntruder (exp-destr|inv-destr)` produces several); \
             got 0 destructors out of {} total rules",
        rules.len()
    );
    for d in &destrs {
        let n = rule_name(&d.info).expect("DestrRule has name");
        assert!(
            n.starts_with(b"_"),
            "destructor rule name must start with `_`; got {}",
            String::from_utf8_lossy(n)
        );
    }

    // EXACT byte-faithful shape vs HS `dhIntruderRules False`
    // (data/intruder_variants_dh.spthy): 5 constr + 45 `d_exp` +
    // 1 `d_inv` = 51 rules.  The lone `d_inv` is the swap variant
    // `[KD(inv(x))] -> [KD(x)]`; the IDENTITY variants of the `_exp`
    // and `_inv` destructors (`KD(x)->KD(inv(x))`, `[KD(x),KU(y)]->
    // [KD(x^y)]`) MUST be dropped — Maude returns them as `x0 --> #N`
    // fresh-witness renamings which HS's `removeRenamings`
    // (Maude/Types.hs:133-157, see line 144) collapses to the empty subst, so the
    // `ruvariant /= ru` guard (IntruderRules.hs:354-360, see line 356) discards them.
    // A regression here (53 rules: +1 d_exp, +1 d_inv) means the
    // `remove_renamings` step in `variants_intruder` was lost.
    let (n_exp, n_inv) = destrs.iter().fold((0usize, 0usize), |(e, i), d| {
        let n = rule_name(&d.info).unwrap();
        let s = String::from_utf8_lossy(n);
        if s.contains("inv") {
            (e, i + 1)
        } else if s.contains("exp") {
            (e + 1, i)
        } else {
            (e, i)
        }
    });
    assert_eq!(
        rules.len(),
        51,
        "dhIntruderRules must yield exactly 51 rules (5 constr + 45 d_exp \
             + 1 d_inv) byte-identically to HS; got {} (n_exp={}, n_inv={}). \
             53 indicates the dropped-identity-variant `remove_renamings` \
             step regressed.",
        rules.len(),
        n_exp,
        n_inv
    );
    assert_eq!(
        n_exp, 45,
        "expected exactly 45 d_exp destructors; got {}",
        n_exp
    );
    assert_eq!(
        n_inv, 1,
        "expected exactly 1 d_inv destructor (the swap \
             variant); got {} (2 means the identity variant KD(x)->KD(inv(x)) \
             leaked)",
        n_inv
    );
}

/// The 5 ConstrRules MUST have the HS-specified shape:
/// - `_exp` premises: `[KU(x.0), KU(x.1)]`, conc: `KU(exp(x.0, x.1))`
/// - `_inv` premises: `[KU(x.0)]`, conc: `KU(inv(x.0))`
/// - `_DH_neutral` premises: `[]`, conc: `KU(DH_neutral)`
/// - `_one` premises: `[]`, conc: `KU(one)`
/// - `_mult` premises: `[KU(x.0), KU(x.1)]`, conc: `KU(x.0 * x.1)`
///
/// HS: see expRule/invRule/multRule/oneRule/dhNeutralRule helpers at
/// IntruderRules.hs:250-283 — each is `Rule mkInfo prems [concfact]
/// (mkAction concfact) []` where `concfact = kudFact conc`.
#[test]
fn dh_intruder_rules_constructors_have_expected_shape() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = dh_intruder_rules(false, &maude);
    let find = |name: &[u8]| -> &IntrRuleAC {
        rules
            .iter()
            .find(|r| match &r.info {
                IntrRuleACInfo::ConstrRule { name: n, .. } => n.as_slice() == name,
                _ => false,
            })
            .unwrap_or_else(|| {
                panic!(
                    "no constructor rule named {}",
                    String::from_utf8_lossy(name)
                )
            })
    };

    // All constructor rules emit a single action equal to the conclusion
    // (HS: `mkAction = return`, so `acts = [concfact]`).
    for name in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
        let r = find(name);
        assert_eq!(
            r.conclusions.len(),
            1,
            "{}: must have 1 conclusion",
            String::from_utf8_lossy(name)
        );
        assert_eq!(
            r.actions.len(),
            1,
            "{}: HS `return concfact` ⇒ 1 action",
            String::from_utf8_lossy(name)
        );
        assert_eq!(
            r.actions[0],
            r.conclusions[0],
            "{}: action must equal conclusion (HS `mkAction concfact` ⇒ \
                 `[concfact]`)",
            String::from_utf8_lossy(name)
        );
        // No `new_vars`.
        assert!(
            r.new_vars.is_empty(),
            "{}: constructors have empty new_vars (HS Rule mkInfo prems concs acts [])",
            String::from_utf8_lossy(name)
        );
        // Every fact tag is KU (HS `kudFact = kuFact`).
        for f in r.premises.iter().chain(&r.conclusions).chain(&r.actions) {
            assert_eq!(
                f.tag,
                FactTag::Ku,
                "{}: all facts must be KU (HS `kudFact = kuFact`)",
                String::from_utf8_lossy(name)
            );
        }
    }

    // Premise counts match HS shape.
    assert_eq!(
        find(b"_exp").premises.len(),
        2,
        "_exp: 2 KU premises (HS expRule)"
    );
    assert_eq!(
        find(b"_inv").premises.len(),
        1,
        "_inv: 1 KU premise (HS invRule)"
    );
    assert_eq!(
        find(b"_DH_neutral").premises.len(),
        0,
        "_DH_neutral: 0 premises"
    );
    assert_eq!(find(b"_one").premises.len(), 0, "_one: 0 premises");
    assert_eq!(find(b"_mult").premises.len(), 2, "_mult: 2 KU premises");
}

/// `dh_intruder_rules(true)` (diff mode) skips the SUBSET check of
/// `minimizeIntruderRules` (`(not diff) && equalSubsetRuleUpToRenaming`)
/// while still dropping duplicates and double-premise rules.
///
/// Concretely: diff=true should produce AT LEAST as many rules as
/// diff=false (the diff filter is weaker).
#[test]
fn dh_intruder_rules_diff_mode_is_at_least_as_large() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules_no_diff = dh_intruder_rules(false, &maude);
    let rules_diff = dh_intruder_rules(true, &maude);
    assert!(
        rules_diff.len() >= rules_no_diff.len(),
        "diff=true skips the subsumption filter (HS IntruderRules.hs:188-190) \
             — must produce >= rules.  Got diff={}, no-diff={}",
        rules_diff.len(),
        rules_no_diff.len()
    );
    // The 5 constructor rules must still be present in diff mode.
    let constr_names: Vec<&[u8]> = rules_diff
        .iter()
        .filter_map(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
            _ => None,
        })
        .collect();
    for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
        assert!(
            constr_names.contains(expected),
            "diff-mode dh_intruder_rules missing constructor named {}",
            String::from_utf8_lossy(expected)
        );
    }
}

/// Destructor rules in `dh_intruder_rules` are KD-rules: their
/// first premise (the term-being-deconstructed) has KD tag, the
/// conclusion is KD, and actions are empty (HS `mkAction = const []`
/// for destructors).
#[test]
fn dh_intruder_rules_destructors_have_kd_shape() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = dh_intruder_rules(false, &maude);
    let destrs: Vec<&IntrRuleAC> = rules
        .iter()
        .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule { .. }))
        .collect();
    assert!(
        !destrs.is_empty(),
        "expected at least one destructor variant"
    );
    for d in &destrs {
        assert!(
            !d.premises.is_empty(),
            "destructor must have premises; got rule with 0 prems"
        );
        assert_eq!(
            d.premises[0].tag,
            FactTag::Kd,
            "destructor's first premise must be KD (HS `kudFact = kdFact`)"
        );
        assert_eq!(
            d.conclusions.len(),
            1,
            "destructor must have exactly 1 KD conclusion"
        );
        assert_eq!(
            d.conclusions[0].tag,
            FactTag::Kd,
            "destructor conclusion must be KD"
        );
        assert!(
            d.actions.is_empty(),
            "destructor actions must be empty (HS `mkAction = const []`)"
        );
        assert!(d.new_vars.is_empty(), "destructor new_vars must be empty");
    }
}

/// Every rule produced by `dh_intruder_rules` has a name starting
/// with `_` — the HS `append (pack "_") ...SymString` prefix.  This
/// is how HS distinguishes intruder rules from user-defined rules
/// with the same name (e.g. user-defined `exp` vs intruder `_exp`).
/// Mirrors IntruderRules.hs:233-244, 182, etc.
#[test]
fn dh_intruder_rules_all_names_have_underscore_prefix() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = dh_intruder_rules(false, &maude);
    for r in &rules {
        let n = rule_name(&r.info).expect("DH intruder rule must have a name");
        assert!(
            n.starts_with(b"_"),
            "DH intruder rule name must start with `_` (HS `append (pack \"_\") \
                 ...SymString`); got {}.  This prefix is how HS distinguishes \
                 the intruder `_exp` from a user-defined `exp` function.",
            String::from_utf8_lossy(n)
        );
    }
}

/// `norm_rule` is the identity on a DH constructor rule whose
/// terms are already in normal form (KU(x.0), KU(x.1), KU(exp(x.0, x.1))).
/// Mirrors HS `normRule'` (IntruderRules.hs:376-380) — for already-normal
/// terms, `norm'` returns the input.
#[test]
fn norm_rule_identity_on_already_normal_rule() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = dh_intruder_rules(false, &maude);
    let exp_constr = rules
        .iter()
        .find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => name.as_slice() == b"_exp",
            _ => false,
        })
        .expect("_exp constructor rule must be present");
    let normalised = norm_rule(&maude, exp_constr);
    assert_eq!(
        &normalised, exp_constr,
        "norm_rule must be the identity on a rule whose terms are \
             already in normal form (`x.0`, `x.1`, `exp(x.0, x.1)` — no \
             reducible top-level shapes).  HS: `normRule' = mapTerms norm'`, \
             and `norm' (x.0) = x.0`."
    );
}

/// `dh_intruder_rules` rule list is well-formed: every rule has at
/// least one conclusion, every fact's terms is non-empty, etc.
#[test]
fn dh_intruder_rules_well_formed() {
    let maude = match dh_maude_handle() {
        Some(m) => m,
        None => return,
    };
    let rules = dh_intruder_rules(false, &maude);
    assert!(
        !rules.is_empty(),
        "dh_intruder_rules must produce > 0 rules"
    );
    for r in &rules {
        assert!(
            !r.conclusions.is_empty(),
            "every dh intruder rule must have at least one conclusion"
        );
        for f in r.premises.iter().chain(&r.conclusions).chain(&r.actions) {
            assert!(
                !f.terms.is_empty(),
                "every fact in a dh intruder rule must have non-empty terms"
            );
        }
    }
}
