use crate::algebra_backend::AlgebraBackend;
use crate::builtin::msg_var;
use crate::function_symbols::AcSym;
use crate::lterm::LNTerm;
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::maude_sig::mset_maude_sig;
use crate::rewriting::Equal;
use crate::term::f_app_ac;

fn side(variables: &[u64]) -> LNTerm {
    f_app_ac(
        AcSym::Union,
        variables.iter().map(|&i| msg_var("v", i)).collect(),
    )
}

fn equation(left: &[u64], right: &[u64]) -> Equal<LNTerm> {
    Equal {
        lhs: side(left),
        rhs: side(right),
    }
}

fn homogeneous_ac_existence_skips_substitution_enumeration_and_caches_both_answers() {
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    // For p distinct left variables and q distinct right variables, giving
    // every left image q copies of one witness and every right image p works.
    // The 4×4 family's individual unifiers correspond to edge covers of K4,4.
    for query in [
        vec![equation(&[0, 1], &[2, 3, 4, 5, 6, 7, 8])],
        vec![equation(&[0, 1, 2, 3], &[4, 5, 6, 7])],
    ] {
        let before = native.stats().lean_unify_count;
        assert!(native.unifiable(&query).unwrap());
        assert!(native.unifiable(&query).unwrap());
        assert_eq!(native.stats().lean_unify_count, before + 1);
    }
    // 2X+Y=Z and X+Y=Z force an empty image for X in nonunit AC.
    let mut impossible = [equation(&[0, 0, 1], &[2]), equation(&[0, 1], &[2])];
    for _ in 0..2 {
        let before = native.stats().lean_unify_count;
        assert!(!native.unifiable(&impossible).unwrap());
        assert!(!native.unifiable(&impossible).unwrap());
        assert_eq!(native.stats().lean_unify_count, before + 1);
        impossible.reverse();
    }
    assert_eq!(native.stats().unify_count, 0);

    let mixed = [Equal {
        lhs: side(&[0, 1]),
        rhs: f_app_ac(AcSym::Union, vec![crate::lterm::pub_term("a"); 2]),
    }];
    assert!(!crate::lean_unification::RuleTable::may_be_homogeneous(&mixed));
    assert!(native.unifiable(&mixed).unwrap());

    assert!(matches!(
        native.unify_via_maude(&[]),
        Err(MaudeError::UnsupportedOperation(_))
    ));
    assert!(native.unifiable(&impossible).is_err());
}

#[test]
fn native_oracle_ac_feasibility_matches_small_maude_families() {
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_none() {
        homogeneous_ac_existence_skips_substitution_enumeration_and_caches_both_answers();
    }
    let Some(path) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let hybrid =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Hybrid).unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    for (query, expected) in [
        (vec![equation(&[0, 1], &[2, 3])], true),
        (vec![equation(&[0, 0], &[1, 1, 1])], true),
        (
            vec![equation(&[0, 0, 1], &[2]), equation(&[0, 1], &[2])],
            false,
        ),
    ] {
        assert_eq!(hybrid.unifiable(&query).unwrap(), expected);
        assert_eq!(
            !oracle.unify_via_maude(&query).unwrap().is_empty(),
            expected
        );
    }
    assert_eq!(hybrid.stats().lean_unify_count, 3);
}

#[test]
fn rational_cone_decides_heavy_simultaneous_ac_rows_without_an_oracle() {
    let table = crate::lean_unification::RuleTable::new(&mset_maude_sig()).unwrap();
    let mut left = vec![0; 131];
    left.push(1);
    let right = vec![2; 137];
    let base = equation(&left, &right);
    left.push(1);
    let conflict = equation(&left, &right);
    let compatible = equation(&[0], &[1]);
    // 131X+Y=137Z can coexist with X=Y. Adding one more Y to the
    // same left side forces that input empty, which AC does not permit.
    for (query, expected) in [
        (vec![compatible.clone(), base.clone()], true),
        (vec![conflict.clone(), base.clone()], false),
        (vec![compatible.clone(), conflict, base.clone()], false),
        (vec![base.clone(), compatible, base], true),
    ] {
        assert_eq!(table.ac_feasible(&query).unwrap(), Some(expected));
    }
}
