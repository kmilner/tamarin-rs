//! Existence of unifiers for homogeneous AC systems on proved-only.
//!
//! Proved-only has one unifier, the proved total export, and answers the
//! existence question through that export's proved existence decision,
//! which lists no family. A wide system has far too many unifiers to list,
//! so the wide shapes below ask for existence alone.

use crate::algebra_backend::AlgebraBackend;
use crate::algebra_provenance::{Command, Origin};
use crate::builtin::msg_var;
use crate::function_symbols::AcSym;
use crate::lterm::LNTerm;
use crate::maude_proc::MaudeHandle;
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

fn native() -> MaudeHandle {
    MaudeHandle::start_with_backend("/nonexistent", mset_maude_sig(), AlgebraBackend::ProvedOnly)
        .unwrap()
}

#[test]
fn existence_is_decided_once_by_the_proved_unifier_and_then_by_its_memo() {
    let native = native();
    // 2X+Y=Z and X+Y=Z force an empty image for X in nonunit AC.
    let impossible = [equation(&[0, 0, 1], &[2]), equation(&[0, 1], &[2])];
    let reversed = [impossible[1].clone(), impossible[0].clone()];
    let possible = [equation(&[0, 1], &[2, 3, 4])];
    for (query, expected) in [
        (&possible[..], true),
        (&impossible[..], false),
        (&reversed[..], false),
    ] {
        let before = native.stats();
        assert_eq!(native.unifiable(query).unwrap(), expected);
        assert_eq!(native.unifiable(query).unwrap(), expected);
        // The existence export decided once and listed no family.
        let decided = native.stats();
        assert_eq!(
            decided.lean_unify_exists_count,
            before.lean_unify_exists_count + 1
        );
        assert_eq!(decided.lean_unify_count, before.lean_unify_count);
        // A decision is not a family: the enumeration asks the unifier.
        assert_eq!(native.unify(query).unwrap().is_empty(), !expected);
        assert_eq!(native.unify(query).unwrap().is_empty(), !expected);
        assert_eq!(native.unifiable(query).unwrap(), expected);
        let listed = native.stats();
        assert_eq!(listed.lean_unify_count, before.lean_unify_count + 1);
        assert_eq!(
            listed.lean_unify_exists_count,
            decided.lean_unify_exists_count
        );
    }
    assert_eq!(native.stats().unify_count, 0);
    let tally = native.provenance();
    // Per query: one decision and one family afresh, three repeats.
    assert_eq!(tally.fresh(Command::Unify, Origin::Proved), 6);
    assert_eq!(tally.cached(Command::Unify, Origin::Proved), 9);
    assert_eq!(tally.total(Command::Unify), 15);

    // A listed family answers the existence question, under the equations
    // as sent and under a renaming of them, without the existence export.
    let native = self::native();
    assert!(!native.unify(&possible).unwrap().is_empty());
    assert!(native.unifiable(&possible).unwrap());
    let renamed = [equation(&[10, 11], &[12, 13, 14])];
    assert!(native.unifiable(&renamed).unwrap());
    // A decision under a renaming answers too, and still lists nothing.
    assert!(!native.unifiable(&impossible).unwrap());
    let renamed = [equation(&[5, 5, 6], &[7]), equation(&[5, 6], &[7])];
    assert!(!native.unifiable(&renamed).unwrap());
    let stats = native.stats();
    assert_eq!(stats.lean_unify_count, 1);
    assert_eq!(stats.lean_unify_exists_count, 1);
    let tally = native.provenance();
    assert_eq!(tally.fresh(Command::Unify, Origin::Proved), 2);
    assert_eq!(tally.cached(Command::Unify, Origin::Proved), 3);

    // An empty listed family answers "none", also under a renaming.
    let native = self::native();
    assert!(native.unify(&impossible).unwrap().is_empty());
    assert!(!native.unifiable(&impossible).unwrap());
    assert!(!native.unifiable(&renamed).unwrap());
    assert_eq!(native.stats().lean_unify_exists_count, 0);
}

#[test]
fn native_oracle_ac_existence_matches_small_maude_families() {
    let Some(path) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let native = native();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    for (query, expected) in [
        (vec![equation(&[0, 1], &[2, 3])], true),
        (vec![equation(&[0, 0], &[1, 1, 1])], true),
        (
            vec![equation(&[0, 0, 1], &[2]), equation(&[0, 1], &[2])],
            false,
        ),
        (
            vec![equation(&[0, 1], &[2, 3]), equation(&[0, 1], &[2, 3, 4])],
            false,
        ),
    ] {
        assert_eq!(native.unifiable(&query).unwrap(), expected);
        assert_eq!(oracle.unifiable(&query).unwrap(), expected);
        assert_eq!(
            native.unify(&query).unwrap().len(),
            oracle.unify(&query).unwrap().len()
        );
    }
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn native_oracle_mixed_size_clash_is_empty_and_the_open_row_keeps_its_family() {
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;

    let Some(path) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let row = |t| Equal {
        lhs: f_app_ac(AcSym::Union, vec![msg_var("x", 0), t]),
        rhs: side(&[2, 3]),
    };
    let heated = hash(msg_var("x", 1));
    let possible = row(heated.clone());
    // x + h(y) and x + h(h(y)) cannot both equal v2 + v3.
    let impossible = [possible.clone(), row(hash(heated))];
    assert!(native.unify(&impossible).unwrap().is_empty());
    assert!(oracle.unify(&impossible).unwrap().is_empty());
    let family = native.unify(std::slice::from_ref(&possible)).unwrap();
    assert!(family.len() > 1);
    assert_eq!(family.len(), oracle.unify(&[possible]).unwrap().len());
}

#[test]
fn native_oracle_width_clash_and_splittable_residual_agree_with_maude() {
    let Some(path) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let native = native();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let (x, y, v) = (msg_var("x", 0), msg_var("y", 1), msg_var("v", 2));
    let atom = crate::lterm::pub_term("a");
    let sum = |xs| f_app_ac(AcSym::Union, xs);
    let first = Equal {
        lhs: sum(vec![x.clone(), atom.clone()]),
        rhs: sum(vec![y.clone(), atom.clone()]),
    };
    for (extra, clash) in [(atom.clone(), true), (v, false)] {
        // Subtracting the first equation leaves extra = a + a. A Msg
        // variable can take that composite image, a single name cannot.
        let second = Equal {
            lhs: sum(vec![x.clone(), atom.clone(), extra]),
            rhs: sum(vec![y.clone(), atom.clone(), atom.clone(), atom.clone()]),
        };
        for query in [
            [first.clone(), second.clone()],
            [second.clone(), first.clone()],
        ] {
            assert_eq!(oracle.unify(&query).unwrap().is_empty(), clash);
            assert_eq!(native.unify(&query).unwrap().is_empty(), clash);
            assert_eq!(native.unifiable(&query).unwrap(), !clash);
        }
    }
}

/// Two distinct variables against seven: every right image is one witness,
/// which either or both left images contain. The family has 3^7 - 2 members.
#[test]
fn two_by_seven_sums_are_unifiable() {
    let query = [equation(&[0, 1], &[2, 3, 4, 5, 6, 7, 8])];
    assert!(native().unifiable(&query).unwrap());
}

/// Four distinct variables against four. The family has one unifier for
/// every edge cover of K4,4.
#[test]
fn four_by_four_sums_are_unifiable() {
    let query = [equation(&[0, 1, 2, 3], &[4, 5, 6, 7])];
    assert!(native().unifiable(&query).unwrap());
}

#[test]
fn heavy_simultaneous_ac_rows_are_decided_without_an_oracle() {
    let native = native();
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
        assert_eq!(native.unifiable(&query).unwrap(), expected);
    }
}

#[test]
fn wide_ac_existence_checks_shared_positive_assignments() {
    let native = native();
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
        assert_eq!(native.unifiable(&query).unwrap(), expected);
    }
    // Elimination leaves two pivot coordinates. Free coordinates of size
    // six give x1=4 and x0=767, satisfying both original equations.
    let tail = (1..257).collect::<Vec<_>>();
    let triangular = [equation(&[0, 0], &tail), equation(&[1, 1, 1], &[2, 2])];
    assert!(native.unifiable(&triangular).unwrap());
    // This conjunction has no common positive assignment. The second row
    // would force the last variable empty after subtracting the first row.
    // Each row in isolation admits a positive assignment.
    let mut added = left;
    added.push(72);
    let incompatible = [wide, equation(&added, &right)];
    assert!(!native.unifiable(&incompatible).unwrap());
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn two_wide_ac_rows_decide_both_sides_of_a_shared_ratio() {
    let native = native();
    let doubled = |keys: &[u64]| {
        keys.iter()
            .copied()
            .cycle()
            .take(2 * keys.len())
            .collect::<Vec<_>>()
    };
    // X+sum(V)=sum(W). With sum(W)=2sum(V), choose all V=1,
    // all W=2 and X=|V|. Reversing the ratio forces X negative.
    for half in [18, 256] {
        let v = (1..=half).collect::<Vec<_>>();
        let w = (half + 1..=2 * half).collect::<Vec<_>>();
        let base = equation(&(0..=half).collect::<Vec<_>>(), &w);
        for (ratio, expected) in [
            (equation(&doubled(&v), &w), true),
            (equation(&v, &doubled(&w)), false),
        ] {
            for rows in [[base.clone(), ratio.clone()], [ratio.clone(), base.clone()]] {
                assert_eq!(native.unifiable(&rows).unwrap(), expected);
            }
        }
    }
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn repeated_column_profiles_decide_a_wide_three_equation_system() {
    let native = native();
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
        assert_eq!(native.unifiable(&rows).unwrap(), expected);
    }
    assert_eq!(native.stats().unify_count, 0);
}
