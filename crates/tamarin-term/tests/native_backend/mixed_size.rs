use super::*;
use tamarin_term::builtin::hash;
use tamarin_term::maude_sig::hash_maude_sig;
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::vterm::var_term;

fn handle() -> MaudeHandle {
    MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap()
}

fn union(terms: Vec<LNTerm>) -> LNTerm {
    f_app_ac(AcSym::Union, terms)
}

fn keys() -> [LVar; 4] {
    [
        LVar::new("x", LSort::Msg, 0),
        LVar::new("x", LSort::Msg, 1),
        LVar::new("y", LSort::Msg, 0),
        LVar::new("y", LSort::Msg, 1),
    ]
}

fn equation([x, y, u, v]: [LVar; 4], extra_hash: bool) -> Equal<LNTerm> {
    let hx = hash(var_term(x));
    let mut left = vec![if extra_hash { hash(hx) } else { hx }, var_term(x)];
    left.extend(vec![var_term(y); 4]);
    let mut right = vec![var_term(u); 3];
    right.extend(vec![var_term(v); 5]);
    Equal {
        lhs: union(left),
        rhs: union(right),
    }
}

fn presentations(rows: [Equal<LNTerm>; 2]) -> Vec<[Equal<LNTerm>; 2]> {
    let mut result = vec![];
    for permute in [false, true] {
        for reverse in [false, true] {
            let mut current = rows.clone();
            if permute {
                current.reverse();
            }
            if reverse {
                for row in &mut current {
                    std::mem::swap(&mut row.lhs, &mut row.rhs);
                }
            }
            if !result.contains(&current) {
                result.push(current);
            }
        }
    }
    result
}

#[test]
fn individually_unifiable_rows_reject_incompatible_constructor_sizes() {
    let inputs = keys();
    let [x, y, u, v] = inputs;
    let rows = [equation(inputs, false), equation(inputs, true)];
    let t = pub_term("t");
    for (row, k) in rows.iter().zip([hash(t.clone()), hash(hash(t.clone()))]) {
        // X=t, Y=k+2t, U=3t, V=k solves the row with distinguished factor k.
        let witness = Subst::from_list([
            (x, t.clone()),
            (y, union(vec![k.clone(), t.clone(), t.clone()])),
            (u, union(vec![t.clone(); 3])),
            (v, k),
        ]);
        assert_eq!(
            apply_vterm(&witness, row.lhs.clone()),
            apply_vterm(&witness, row.rhs.clone())
        );
        assert!(handle().unifiable(std::slice::from_ref(row)).unwrap());
    }
    // The original equations have the same right-hand side; the second
    // left-hand side contains one more hash for every simultaneous substitution.
    for query in presentations(rows) {
        let full = handle();
        assert!(full.unify(&query).unwrap().is_empty());
        full.check_backend_status().unwrap();
        assert_eq!(full.stats().unify_count, 0);
        let decision = handle();
        assert!(!decision.unifiable(&query).unwrap());
        decision.check_backend_status().unwrap();
        assert_eq!(decision.stats().unify_count, 0);
    }
}

#[test]
fn removing_one_hash_preserves_real_mixed_ac_unifiers() {
    let inputs = keys();
    let row = equation(inputs, false);
    for query in presentations([row.clone(), row]) {
        let decision = handle();
        assert!(decision.unifiable(&query).unwrap());
        assert_eq!(decision.stats().unify_count, 0);
        let full = handle();
        let arms = full.unify(&query).unwrap();
        assert!(!arms.is_empty());
        for arm in arms {
            let subst = LNSubstVFresh::from_list(arm).fresh_to_free_avoiding_vars(&inputs);
            for eq in &query {
                assert_eq!(
                    apply_vterm(&subst, eq.lhs.clone()),
                    apply_vterm(&subst, eq.rhs.clone())
                );
            }
        }
        full.check_backend_status().unwrap();
        assert_eq!(full.stats().unify_count, 0);
    }
}
