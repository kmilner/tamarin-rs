//! Complete valued families under an inert AC constructor.
use super::super::{canonical_small_ac_answers, valued_variant_rows};
use crate::algebra_backend::AlgebraBackend;
use crate::builtin::{fst, msg_var, pair, snd};
use crate::function_symbols::AcSym;
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_proc::MaudeHandle;
use crate::maude_sig::{mset_maude_sig, pair_maude_sig};
use crate::term::{f_app_ac, f_app_list};
use tamarin_test_support::require_maude_path;

fn projection_family(handle: &MaudeHandle, width: usize, repeated: bool) {
    let xs: Vec<_> = (0..width).map(|i| msg_var("source", i as u64)).collect();
    let product = |factors| f_app_ac(AcSym::Union, factors);
    let factors = |i: usize, left: LNTerm, right: LNTerm| {
        let mut terms = vec![left.clone(), right];
        if repeated && i.is_multiple_of(2) {
            terms.push(left);
        }
        terms
    };
    let query = product(
        xs.iter()
            .enumerate()
            .flat_map(|(i, x)| factors(i, fst(x.clone()), snd(x.clone())))
            .collect(),
    );
    let mut expected = Vec::new();
    for mask in 0..(1 << width) {
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        for (i, x) in xs.iter().enumerate() {
            if mask & (1 << i) == 0 {
                inputs.push(x.clone());
                outputs.extend(factors(i, fst(x.clone()), snd(x.clone())));
            } else {
                let a = msg_var("a", 2 * i as u64);
                let b = msg_var("b", 2 * i as u64 + 1);
                inputs.push(pair(a.clone(), b.clone()));
                outputs.extend(factors(i, a, b));
            }
        }
        inputs.push(product(outputs));
        expected.push(vec![(LVar::new("row", LSort::Msg, 0), f_app_list(inputs))]);
    }
    let raw = handle.variants(&f_app_list(vec![query.clone()])).unwrap();
    assert_eq!(raw.len(), expected.len());
    assert_eq!(
        valued_variant_rows(handle, &[query]),
        canonical_small_ac_answers(expected)
    );
}

#[test]
fn native_oracle_inert_product_matches_all_32_symbolic_projection_rows() {
    let sig = mset_maude_sig().merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    // The ordinary whole-term frontier defers at five inputs. The first
    // and second projections share one input and one choice at each index.
    projection_family(&native, 5, false);
    projection_family(&native, 5, true);
    assert_eq!(native.stats().var_count, 0);
}

#[test]
fn native_oracle_inert_product_variants_keep_joint_images_and_multiplicities() {
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let sig = mset_maude_sig().merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    for repeat in [false, true] {
        projection_family(&native, 2, repeat);
    }
    if let Some(path) = require_maude_path() {
        let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        for repeat in [false, true] {
            projection_family(&maude, 2, repeat);
        }
    }
}

#[test]
fn native_oracle_user_ac_product_keeps_the_other_observations() {
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_no_eq;

    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let ctor = |name: &'static [u8], arity| {
        NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
    };
    let head = AcFctSym::new(
        b"merge",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let first = ctor(b"left", 1);
    let second = ctor(b"right", 1);
    let app = |f, t| f_app_no_eq(f, vec![t]);
    let merge = |ts| f_app_ac(AcSym::AcFct(head), ts);
    let x = msg_var("x", 0);
    let y = msg_var("x", 1);
    let mut sig = pair_maude_sig();
    sig.st_fun_syms.extend([first, second]);
    sig.st_ac_fun_syms.insert(head);
    for (h, ret) in [(first, x.clone()), (second, y.clone())] {
        let lhs = app(h, pair(x.clone(), y.clone()));
        sig.st_rules
            .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, ret)).unwrap());
    }
    let sig = sig.refresh();
    let slots = vec![
        merge(vec![
            app(first, x.clone()),
            app(second, y.clone()),
            x.clone(),
        ]),
        app(first, y.clone()),
        app(second, x),
        msg_var("held", 2),
    ];
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let family = valued_variant_rows(&native, &slots);
    assert_eq!(family.len(), 4);
    if let Some(path) = require_maude_path() {
        let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(family, valued_variant_rows(&maude, &slots));
    }
    assert_eq!(native.stats().var_count, 0);
}
