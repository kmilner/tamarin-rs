use super::*;

#[test]
fn dh_signature_includes_dh_rules() {
    let sig = dh_maude_sig();
    assert!(sig.enable_dh);
    assert_eq!(sig.rrules().len(), 13);
}

#[test]
fn bp_implies_dh() {
    let sig = bp_maude_sig();
    // bp turns on dh in refresh().
    assert!(sig.enable_dh);
    // 13 dh + 3 bp = 16
    assert_eq!(sig.rrules().len(), 16);
}

#[test]
fn merge_combines_flags() {
    let merged = dh_maude_sig().merge(xor_maude_sig());
    assert!(merged.enable_dh);
    assert!(merged.enable_xor);
    // 13 dh + 3 xor = 16
    assert_eq!(merged.rrules().len(), 16);
}

#[test]
fn empty_signature_has_no_rules() {
    let sig = MaudeSig::default().refresh();
    assert!(sig.rrules().is_empty());
}

/// HS `addFunSym`/`addMacroSym` route through the monoid `<>`
/// (Signature.hs:152-159), which rebuilds from `mempty`
/// (eqConvergent=False, line 145) and so RESETS eqConvergent to false.
///
/// Probed against the real prover (v1.13.0): a `functions:` block placed
/// AFTER an `equations [convergent]:` block prints `equations:` (the
/// convergent flag is dropped), whereas `functions:` BEFORE keeps
/// `equations [convergent]:`.  `add_ctxt_st_rule` must NOT reset, since
/// elaborate.rs sets eq_convergent before the rule loop (mirroring the HS
/// parser's explicit re-set AFTER `foldl addCtxtStRule`,
/// Theory/Text/Parser/Signature.hs:226-227).
#[test]
fn add_fun_sym_resets_eq_convergent() {
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    let sig = MaudeSig {
        eq_convergent: true,
        ..MaudeSig::default()
    };
    let g = NoEqSym::new(
        b"g".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let sig = sig.add_fun_sym(UserDefinedSym::NoEqUser(g));
    assert!(
        !sig.eq_convergent,
        "add_fun_sym must reset eq_convergent (HS monoid <>)"
    );
}

#[test]
fn add_macro_sym_resets_eq_convergent() {
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    let sig = MaudeSig {
        eq_convergent: true,
        ..MaudeSig::default()
    };
    let m = NoEqSym::new(
        b"m".to_vec(),
        1,
        Privacy::Private,
        Constructability::Destructor,
    );
    let sig = sig.add_macro_sym(m);
    assert!(
        !sig.eq_convergent,
        "add_macro_sym must reset eq_convergent (HS monoid <>)"
    );
}

/// `add_ctxt_st_rule` must PRESERVE eq_convergent (no reset), because the
/// Rust elaborator sets eq_convergent BEFORE the add_ctxt_st_rule loop
/// (elaborate.rs's `TheoryItem::Equations` arm), then refreshes — matching
/// the printed `equations [convergent]:` for the normal
/// functions-before-equations corpus ordering.
#[test]
fn add_ctxt_st_rule_preserves_eq_convergent() {
    let sig = MaudeSig {
        eq_convergent: true,
        ..MaudeSig::default()
    };
    let sig = sig.add_ctxt_st_rule(fst_dest_rule());
    assert!(
        sig.eq_convergent,
        "add_ctxt_st_rule must NOT reset eq_convergent"
    );
}

/// An `[AC]` symbol goes to `st_ac_fun_syms` and reaches the derived
/// signature as `AC (ACfct …)` (HS `maudeSig`'s
/// `S.union S.map (AC . ACfct) stACFunSyms`).
#[test]
fn add_fun_sym_routes_ac_symbols() {
    let f = AcFctSym::new(
        b"f".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let sig = MaudeSig::default().add_fun_sym(UserDefinedSym::AcFctUser(f));
    assert!(sig.st_fun_syms.is_empty());
    assert!(sig.st_ac_fun_syms.contains(&f));
    assert!(sig.fun_syms.contains(&FunSym::Ac(AcSym::AcFct(f))));
    assert_eq!(sig.ac_user_fun_syms().len(), 1);
    assert!(sig
        .user_defined_st_fun_syms()
        .contains(&UserDefinedSym::AcFctUser(f)));
    // A user-defined AC symbol makes the theory an AC theory.
    assert!(!sig.has_no_ac_operators());
}

/// HS `ppFunSymb`/`showAttrs` (Signature.hs:273-293): attributes are
/// bracketed after a LEADING space, free symbols print
/// `[private,constructor]` where AC symbols print only `[private]`, and the
/// NDC attributes come last.
#[test]
fn pretty_fun_syms_renders_attributes() {
    let sig = MaudeSig {
        st_fun_syms: [
            NoEqSym::new(
                b"h".to_vec(),
                1,
                Privacy::Public,
                Constructability::Constructor,
            ),
            NoEqSym::new(
                b"p".to_vec(),
                2,
                Privacy::Private,
                Constructability::Constructor,
            )
            .with_ndc(NdcState::IsNdcBoth),
        ]
        .into_iter()
        .collect(),
        st_ac_fun_syms: [
            AcFctSym::new(
                b"ac".to_vec(),
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            ),
            AcFctSym::new(
                b"pac".to_vec(),
                Privacy::Private,
                Constructability::Constructor,
                NdcState::IsNdc,
            ),
        ]
        .into_iter()
        .collect(),
        ..MaudeSig::default()
    }
    .refresh();
    assert_eq!(
        sig.pretty_fun_syms_except(&UserDefinedSig::new()),
        vec![
            "h/1".to_string(),
            "p/2 [private,constructor,NDC,NDC-diff]".to_string(),
            "ac/2 [AC]".to_string(),
            "pac/2 [private,AC,NDC]".to_string(),
        ]
    );
}

/// `xorr(x, x) = zeroo` with `xorr/2 [AC]` — an st rule whose LHS is
/// Ac-headed, so `term_ac_c_free` is false for it.
fn ac_headed_st_rule() -> CtxtStRule {
    let xorr = AcFctSym::new(
        b"xorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    let zeroo = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let x = crate::builtin::msg_var("x", 0);
    let lhs = crate::term::f_app_acfct(xorr, vec![x.clone(), x]);
    let rhs: LNTerm = crate::term::f_app_no_eq(zeroo, vec![]);
    crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).expect("ground-RHS st rule")
}

/// Every flag `st_rules` hands out describes the rule it is paired with —
/// through `add_ctxt_st_rule`, through a bare `insert`, and after a
/// `remove` that shifts the surviving rules' positions.
#[test]
fn st_rules_pair_every_rule_with_its_own_lhs_flag() {
    fn flags_match(rules: &StRules) -> bool {
        rules
            .iter_with_lhs_ac_c_free()
            .all(|(r, f)| f == crate::maude_proc::term_ac_c_free(&r.lhs))
    }
    let sig = pair_maude_sig();
    assert!(flags_match(&sig.st_rules));
    assert!(sig.st_lhs_all_ac_c_free());

    let mut sig = sig.add_ctxt_st_rule(ac_headed_st_rule());
    assert!(flags_match(&sig.st_rules));
    assert!(
        !sig.st_lhs_all_ac_c_free(),
        "the Ac-headed LHS must show up"
    );

    // Mutating the `pub` field directly, with no `refresh` afterwards:
    // the flags follow a removal and a re-insertion that together leave
    // the rule count unchanged.
    assert!(sig.st_rules.remove(&fst_rule()));
    assert!(flags_match(&sig.st_rules));
    assert!(sig.st_rules.insert(snd_dest_rule()));
    assert!(flags_match(&sig.st_rules));
    assert!(!sig.st_lhs_all_ac_c_free());
}

/// `merge` carries the flags of the united rule set.
#[test]
fn merge_keeps_the_lhs_flags_with_their_rules() {
    let ac_sig = MaudeSig {
        st_rules: [ac_headed_st_rule()].into_iter().collect(),
        ..MaudeSig::default()
    }
    .refresh();
    let merged = pair_maude_sig().merge(ac_sig);
    assert!(merged
        .st_rules
        .iter_with_lhs_ac_c_free()
        .all(|(r, f)| f == crate::maude_proc::term_ac_c_free(&r.lhs)));
    assert!(!merged.st_lhs_all_ac_c_free());
}

/// HS `joinNDCinSig` (Signature.hs:236-246) is a record update over
/// `stFunSyms`/`stACFunSyms` that does NOT re-run `maudeSig`, so every
/// derived cache keeps its pre-join NDC states — and `ndc` participates in
/// `NoEqSym`/`AcFctSym` `Eq`/`Ord`, so those are DIFFERENT symbols, not the
/// same symbol read twice.
///
/// This pins the staleness the port inherits, so that adding a `refresh()`
/// to `join_ndc_in_sig` fails here rather than silently diverging:
///   * `fun_syms` (and `no_eq_fun_syms`/`ac_user_fun_syms`/the
///     irreducible+reducible sets read off it) keep `NotNdc`;
///   * `user_defined_st_fun_syms` (HS `userDefinedSTFunSyms`,
///     Signature.hs:166-167) reads the joined `st_fun_syms` for its free
///     half but the stale `acUserFunSyms` (Signature.hs:160-161) for its AC
///     half, so with one name carried by both a free and an `[AC]` symbol
///     the two halves disagree about NDC.
#[test]
fn join_ndc_in_sig_leaves_every_derived_cache_stale() {
    let f_free = NoEqSym::new(
        b"f".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let f_ac = AcFctSym::new(
        b"f".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let sig = MaudeSig {
        st_fun_syms: [f_free].into_iter().collect(),
        st_ac_fun_syms: [f_ac].into_iter().collect(),
        ..MaudeSig::default()
    }
    .refresh();
    let joined = sig.join_ndc_in_sig(FunSym::NoEq(f_free), NdcState::IsNdc);

    // Source of truth: both subterm-signature sets are joined, by NAME.
    let f_free_ndc = f_free.with_ndc(NdcState::IsNdc);
    let f_ac_ndc = f_ac.with_ndc(NdcState::IsNdc);
    assert!(joined.st_fun_syms.contains(&f_free_ndc));
    assert!(joined.st_ac_fun_syms.contains(&f_ac_ndc));

    // Derived caches: untouched, i.e. still carrying the pre-join symbols.
    assert!(joined.fun_syms.contains(&FunSym::NoEq(f_free)));
    assert!(joined.fun_syms.contains(&FunSym::Ac(AcSym::AcFct(f_ac))));
    assert!(!joined.fun_syms.contains(&FunSym::NoEq(f_free_ndc)));
    assert!(!joined
        .fun_syms
        .contains(&FunSym::Ac(AcSym::AcFct(f_ac_ndc))));
    assert!(joined.no_eq_fun_syms().contains(&f_free));
    assert!(joined.ac_user_fun_syms().contains(&f_ac));
    assert!(joined.irreducible_fun_syms.contains(&FunSym::NoEq(f_free)));
    assert!(joined
        .irreducible_fun_syms_fast
        .contains(&FunSym::NoEq(f_free)));

    // The two halves of `user_defined_st_fun_syms` disagree about `f`.
    let user_st = joined.user_defined_st_fun_syms();
    assert!(user_st.contains(&UserDefinedSym::NoEqUser(f_free_ndc)));
    assert!(user_st.contains(&UserDefinedSym::AcFctUser(f_ac)));
    assert!(!user_st.contains(&UserDefinedSym::AcFctUser(f_ac_ndc)));

    // `refresh` is what would close the gap — it is deliberately not called
    // by `join_ndc_in_sig`.
    let refreshed = joined.refresh();
    assert!(refreshed.fun_syms.contains(&FunSym::NoEq(f_free_ndc)));
    assert!(refreshed
        .user_defined_st_fun_syms()
        .contains(&UserDefinedSym::AcFctUser(f_ac_ndc)));
}
