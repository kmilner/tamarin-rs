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
    assert!(!crate::lean_unification::RuleTable::may_be_homogeneous(
        &mixed
    ));
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

#[test]
fn wide_ac_feasibility_checks_shared_positive_assignments() {
    let sig = mset_maude_sig();
    let table = crate::lean_unification::RuleTable::new(&sig).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    let left = (0..73).collect::<Vec<_>>();
    let right = (73..257).collect::<Vec<_>>();
    let wide = equation(&left, &right);
    // The first group's variables can all have size 184 and the second
    // group's size 73. Both groups can use the same AC atom.
    let equal_left = equation(&[0, 1], &[2, 3]);
    let equal_right = equation(&[74, 75], &[76, 77]);
    let all = (0..257).collect::<Vec<_>>();
    let mut extra = all.clone();
    extra.push(251);
    let impossible = equation(&extra, &all);
    for (query, expected) in [
        (vec![wide.clone()], true),
        (vec![equal_left, wide.clone(), equal_right], true),
        (vec![wide.clone(), impossible], false),
    ] {
        assert_eq!(table.ac_feasible(&query).unwrap(), Some(expected));
        assert_eq!(native.unifiable(&query).unwrap(), expected);
    }
    assert_eq!(native.stats().unify_count, 0);
    // Elimination leaves two pivot coordinates. Free coordinates of size
    // six give x1=4 and x0=767, satisfying both original equations.
    let tail = (1..257).collect::<Vec<_>>();
    let triangular = [equation(&[0, 0], &tail), equation(&[1, 1, 1], &[2, 2])];
    assert_eq!(table.ac_feasible(&triangular).unwrap(), Some(true));
    assert!(native.unifiable(&triangular).unwrap());
    // This conjunction has no common positive assignment. The second row
    // would force the last variable empty after subtracting the first row.
    // Each row in isolation admits a positive assignment.
    let mut added = left;
    added.push(72);
    let incompatible = [wide, equation(&added, &right)];
    assert_eq!(table.ac_feasible(&incompatible).unwrap(), Some(false));
    assert!(!native.unifiable(&incompatible).unwrap());
}

#[test]
fn two_wide_ac_rows_decide_both_sides_of_a_shared_ratio() {
    let sig = mset_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let table = crate::lean_unification::RuleTable::new(&sig).unwrap();
    let v = (1..19).collect::<Vec<_>>();
    let w = (19..37).collect::<Vec<_>>();
    let doubled = |keys: &[u64]| {
        keys.iter()
            .copied()
            .cycle()
            .take(2 * keys.len())
            .collect::<Vec<_>>()
    };
    // X+sum(V)=sum(W). With sum(W)=2sum(V), choose all V=1,
    // all W=2 and X=18. Reversing the ratio forces X negative.
    let base = equation(&(0..19).collect::<Vec<_>>(), &w);
    for (ratio, expected) in [
        (equation(&doubled(&v), &w), true),
        (equation(&v, &doubled(&w)), false),
    ] {
        for rows in [[base.clone(), ratio.clone()], [ratio.clone(), base.clone()]] {
            assert_eq!(table.ac_feasible(&rows).unwrap(), Some(expected));
            assert_eq!(native.unifiable(&rows).unwrap(), expected);
        }
    }
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn repeated_column_profiles_decide_a_wide_three_equation_system() {
    let sig = mset_maude_sig();
    let table = crate::lean_unification::RuleTable::new(&sig).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    let row = |coeffs: [i32; 6]| {
        let mut left = Vec::new();
        let mut right = Vec::new();
        for i in 0..96 {
            let coefficient = coeffs[i % 6];
            let side = if coefficient > 0 {
                &mut left
            } else {
                &mut right
            };
            side.extend(std::iter::repeat_n(
                i as u64,
                coefficient.unsigned_abs() as usize,
            ));
        }
        equation(&left, &right)
    };
    let first = row([4, 0, -2, 3, 0, -3]);
    let second = row([1, -1, 3, -1, 1, 2]);
    // The signed sum of the three equations has coefficients [1,3,5,5,1,1].
    // A positive assignment would make this sum strictly positive.
    let impossible = row([-4, 4, 4, 3, 0, 2]);
    // Per-variable sizes [3,21,3,3,2,5], repeated sixteen times, satisfy all three.
    let possible = row([0, 0, 0, 1, 1, -1]);
    for (third, expected) in [(impossible, false), (possible, true)] {
        let rows = [first.clone(), second.clone(), third];
        assert_eq!(table.ac_feasible(&rows).unwrap(), Some(expected));
        assert_eq!(native.unifiable(&rows).unwrap(), expected);
    }
    assert_eq!(native.stats().unify_count, 0);
}
