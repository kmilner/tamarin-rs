use super::*;
use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::builtin::hash;
use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
use tamarin_term::maude_sig::{hash_maude_sig, MaudeSig};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::f_app_no_eq;
use tamarin_term::vterm::var_term;

fn union(xs: Vec<LNTerm>) -> LNTerm {
    f_app_ac(AcSym::Union, xs)
}

fn rows(p: LNTerm, s: LNTerm, q: LNTerm, t: LNTerm) -> [Equal<LNTerm>; 2] {
    // Twice the first equality minus the second forces P=Q on every factor.
    [
        Equal {
            lhs: sum(p.clone(), s.clone()),
            rhs: sum(q.clone(), t.clone()),
        },
        Equal {
            lhs: union(vec![p, s.clone(), s]),
            rhs: union(vec![q, t.clone(), t]),
        },
    ]
}

type Family = BTreeSet<Vec<Vec<usize>>>;

fn check_family(sig: &MaudeSig, equations: &[Equal<LNTerm>], keys: &[LVar], expected: &Family) {
    let handle = || {
        MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap()
    };
    let decision = handle();
    assert!(decision.unifiable(equations).unwrap());
    assert_eq!(decision.stats().unify_count, 0);

    let full = handle();
    let arms = full.unify(equations).unwrap();
    assert_eq!(full.stats().unify_count, 0);
    assert_eq!(arms.len(), expected.len());
    let mut family = Family::new();
    for arm in arms {
        assert!(arm.iter().all(|(v, _)| keys.contains(v)));
        let subst = LNSubstVFresh::from_list(arm).fresh_to_free_avoiding_vars(keys);
        for eq in equations {
            assert_eq!(
                apply_vterm(&subst, eq.lhs.clone()),
                apply_vterm(&subst, eq.rhs.clone())
            );
        }
        // Identify a witness by the coordinates containing it, independent of its name.
        let mut profiles = BTreeMap::<LVar, Vec<usize>>::new();
        for (i, &key) in keys.iter().enumerate() {
            let image = apply_vterm(&subst, var_term(key));
            let factors = match &image {
                Term::App(FunSym::Ac(AcSym::Union), xs) => xs.as_ref(),
                _ => std::slice::from_ref(&image),
            };
            for term in factors {
                let Term::Lit(Lit::Var(v)) = term else {
                    panic!("unexpected witness {term:?}")
                };
                assert_eq!(v.sort, LSort::Msg);
                profiles.entry(*v).or_default().push(i);
            }
        }
        let mut columns: Vec<_> = profiles.into_values().collect();
        columns.sort_unstable();
        assert!(family.insert(columns));
    }
    assert_eq!(family, *expected);
}

#[test]
fn coupled_ac_rows_force_hash_arguments_to_unify() {
    let keys = [0, 1, 2, 3].map(|i| LVar::new("v", LSort::Msg, i));
    let [x, y, u, v] = keys.map(var_term);
    let tail = |x: LNTerm, u: LNTerm| {
        let mut xs = vec![x; 5];
        xs.push(u);
        union(xs)
    };
    let mut equations = rows(hash(x.clone()), tail(x, u), hash(y.clone()), tail(y, v));
    let (a, b) = (pub_term("a"), pub_term("b"));
    let partial = Subst::from_list(keys.into_iter().zip([
        a.clone(),
        b.clone(),
        tail(b.clone(), hash(b)),
        tail(a.clone(), hash(a)),
    ]));
    let satisfied = equations
        .each_ref()
        .map(|eq| apply_vterm(&partial, eq.lhs.clone()) == apply_vterm(&partial, eq.rhs.clone()));
    assert_eq!(satisfied, [true, false]);

    let sig = mset_maude_sig().merge(hash_maude_sig());
    let expected = Family::from([vec![vec![0, 1], vec![2, 3]]]);
    check_family(&sig, &equations, &keys, &expected);
    equations.reverse();
    for eq in &mut equations {
        std::mem::swap(&mut eq.lhs, &mut eq.rhs);
    }
    check_family(&sig, &equations, &keys, &expected);
}

#[test]
fn forced_free_arguments_preserve_all_residual_ac_unifiers() {
    let keys = [0, 1, 2, 3, 4, 5, 6, 7].map(|i| LVar::new("v", LSort::Msg, i));
    let inputs = keys.map(var_term);
    let pack = NoEqSym::new(b"pack", 2, Privacy::Public, Constructability::Constructor);
    let mut sig = mset_maude_sig();
    sig.st_fun_syms.insert(pack);
    let equations = rows(
        f_app_no_eq(pack, inputs[..2].to_vec()),
        union(inputs[..4].to_vec()),
        f_app_no_eq(pack, inputs[4..6].to_vec()),
        union(inputs[4..].to_vec()),
    );
    // pack equality identifies the first two argument pairs, leaving A+B=C+D.
    let edges = [[2, 6], [2, 7], [3, 6], [3, 7]];
    let expected: Family = (0..16)
        .filter_map(|mask| {
            let mut columns = vec![vec![0, 4], vec![1, 5]];
            columns.extend(
                edges
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, edge)| edge.to_vec()),
            );
            [2, 3, 6, 7]
                .iter()
                .all(|i| columns.iter().any(|c| c.contains(i)))
                .then_some(columns)
        })
        .collect();
    assert_eq!(expected.len(), 7);
    check_family(&sig.refresh(), &equations, &keys, &expected);
}
