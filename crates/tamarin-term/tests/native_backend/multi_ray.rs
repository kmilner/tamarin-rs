use super::*;
use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::function_symbols::FunSym;
use tamarin_term::vterm::var_term;

fn union(factors: Vec<LNTerm>) -> LNTerm {
    f_app_ac(AcSym::Union, factors)
}

fn equations(keys: &[LVar]) -> Vec<Equal<LNTerm>> {
    let mut rows = vec![Equal {
        lhs: union(vec![var_term(keys[0]), var_term(keys[1])]),
        rhs: union(vec![var_term(keys[2]), var_term(keys[3])]),
    }];
    for (i, &key) in keys[4..].iter().enumerate() {
        rows.push(Equal {
            lhs: union(vec![var_term(key); 2]),
            rhs: union(vec![var_term(keys[i % 4]); 3]),
        });
    }
    rows
}

fn cover(arm: &[(LVar, LNTerm)], keys: &[LVar]) -> u8 {
    let mut profiles = BTreeMap::<LVar, Vec<usize>>::new();
    assert_eq!(arm.len(), keys.len());
    for (i, k) in keys.iter().enumerate() {
        let (_, image) = arm
            .iter()
            .find(|(v, _)| v == k)
            .expect("every input has a repeated image");
        let Term::App(FunSym::Ac(AcSym::Union), factors) = image else {
            panic!("expected an AC image: {image}");
        };
        for t in factors.iter() {
            let Term::Lit(Lit::Var(w)) = t else {
                panic!("expected a witness in {image}");
            };
            assert_eq!(w.sort, LSort::Msg);
            profiles.entry(*w).or_insert_with(|| vec![0; keys.len()])[i] += 1;
        }
    }
    let mut mask = 0;
    for counts in profiles.values() {
        let left = (0..2).find(|&i| counts[i] != 0).expect("left endpoint");
        let right = (2..4).find(|&i| counts[i] != 0).expect("right endpoint");
        for (i, &actual) in counts.iter().enumerate() {
            let endpoint = i % 4;
            let copies = if i < 4 { 2 } else { 3 };
            let expected = if endpoint == left || endpoint == right {
                copies
            } else {
                0
            };
            assert_eq!(
                actual, expected,
                "incorrect witness multiplicity for input {i}"
            );
        }
        let edge = 1 << (2 * left + right - 2);
        assert_eq!(mask & edge, 0, "two witnesses for the same edge");
        mask |= edge;
    }
    mask
}

#[test]
fn wide_connected_ac_unification_preserves_seven_edge_covers() {
    let keys: Vec<_> = (0..36).map(|i| LVar::new("v", LSort::Msg, i)).collect();
    let mut rows = equations(&keys);
    // In each coordinate 2x = 3a forces a=2k and x=3k. All four
    // original endpoints have tied inputs, so A+B=C+D reduces to the
    // unit-weight K2,2 incidence equation on the four k values.
    // Bits denote AC, AD, BC and BD. Each endpoint needs an incident edge.
    let expected: BTreeSet<_> = (1u8..16)
        .filter(|mask| {
            [0b0011, 0b1100, 0b0101, 0b1010]
                .iter()
                .all(|side| mask & side != 0)
        })
        .collect();
    assert_eq!(expected.len(), 7);
    for order in 0..2 {
        if order == 1 {
            rows.reverse();
            for row in rows.iter_mut().step_by(2) {
                std::mem::swap(&mut row.lhs, &mut row.rhs);
            }
        }
        let h = native();
        let arms = h.unify(&rows).unwrap();
        let masks: BTreeSet<_> = arms.iter().map(|arm| cover(arm, &keys)).collect();
        assert_eq!(arms.len(), expected.len());
        assert_eq!(masks, expected);
        assert_eq!(h.stats().unify_count, 0);
    }
}
