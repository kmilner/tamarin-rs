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

fn handle(sig: &MaudeSig) -> MaudeHandle {
    MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap()
}

/// The family the native backend lists, after asking a second handle the
/// existence question alone.
fn unifiers(sig: &MaudeSig, equations: &[Equal<LNTerm>]) -> Vec<Vec<(LVar, LNTerm)>> {
    let decision = handle(sig);
    assert!(decision.unifiable(equations).unwrap());
    assert_eq!(decision.stats().unify_count, 0);

    let full = handle(sig);
    let arms = full.unify(equations).unwrap();
    assert_eq!(full.stats().unify_count, 0);
    arms
}

/// Check that `arm` binds only `keys` and solves `equations`, and identify
/// each of its witnesses by the coordinates containing it, independent of
/// its name.
fn profile(
    arm: Vec<(LVar, LNTerm)>,
    equations: &[Equal<LNTerm>],
    keys: &[LVar],
) -> Vec<Vec<usize>> {
    assert!(arm.iter().all(|(v, _)| keys.contains(v)));
    let subst = LNSubstVFresh::from_list(arm).fresh_to_free_avoiding_vars(keys);
    for eq in equations {
        assert_eq!(
            apply_vterm(&subst, eq.lhs.clone()),
            apply_vterm(&subst, eq.rhs.clone())
        );
    }
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
    columns
}

fn check_family(sig: &MaudeSig, equations: &[Equal<LNTerm>], keys: &[LVar], expected: &Family) {
    let arms = unifiers(sig, equations);
    assert_eq!(arms.len(), expected.len());
    let mut family = Family::new();
    for arm in arms {
        assert!(family.insert(profile(arm, equations, keys)));
    }
    assert_eq!(family, *expected);
}

/// The images of `keys` under each arm, with the witnesses of an arm named
/// by the numbering that makes its images least, and the arms in order: the
/// same value for two families that differ in the names of their witnesses
/// and in the order of their arms.
fn unnamed(arms: &[Vec<(LVar, LNTerm)>], keys: &[LVar]) -> Vec<Vec<LNTerm>> {
    use tamarin_term::vterm::vars_vterm;
    fn permutations(n: usize) -> Vec<Vec<u64>> {
        if n == 0 {
            return vec![Vec::new()];
        }
        let mut all = Vec::new();
        for shorter in permutations(n - 1) {
            for at in 0..n {
                let mut longer = shorter.clone();
                longer.insert(at, n as u64 - 1);
                all.push(longer);
            }
        }
        all
    }
    let mut family: Vec<_> = arms
        .iter()
        .map(|arm| {
            let subst = LNSubstVFresh::from_list(arm.clone()).fresh_to_free_avoiding_vars(keys);
            let images: Vec<_> = keys
                .iter()
                .map(|key| apply_vterm(&subst, var_term(*key)))
                .collect();
            let witnesses: BTreeSet<LVar> = images.iter().flat_map(vars_vterm).collect();
            assert!(witnesses.len() <= 6, "too many witnesses to number");
            permutations(witnesses.len())
                .into_iter()
                .map(|numbers| {
                    let naming =
                        Subst::from_list(witnesses.iter().zip(numbers).map(|(witness, number)| {
                            (*witness, var_term(LVar::new("w", witness.sort, number)))
                        }));
                    images
                        .iter()
                        .map(|image| apply_vterm(&naming, image.clone()))
                        .collect::<Vec<_>>()
                })
                .min()
                .unwrap()
        })
        .collect();
    family.sort();
    family
}

/// The native family for `equations` is sound, lists the unifier with the
/// witness columns `principal`, and is the family of the Maude backend up
/// to the names of the witnesses and the order of the arms.
fn check_against_maude(
    sig: &MaudeSig,
    equations: &[Equal<LNTerm>],
    keys: &[LVar],
    principal: &[Vec<usize>],
    size: usize,
) {
    let arms = unifiers(sig, equations);
    assert_eq!(arms.len(), size);
    let family: Family = arms
        .iter()
        .map(|arm| profile(arm.clone(), equations, keys))
        .collect();
    assert_eq!(family.len(), size);
    assert!(family.contains(principal));
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        let reference = oracle.unify(equations).unwrap();
        assert_eq!(reference.len(), size);
        assert_eq!(unnamed(&arms, keys), unnamed(&reference, keys));
    }
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
    // Every unifier is an instance of x=y, u=v. Maude 3.5.1 lists that one
    // and four of its instances, and Maude is the oracle for the family.
    let principal = [vec![0, 1], vec![2, 3]];
    check_against_maude(&sig, &equations, &keys, &principal, 5);
    equations.reverse();
    for eq in &mut equations {
        std::mem::swap(&mut eq.lhs, &mut eq.rhs);
    }
    check_against_maude(&sig, &equations, &keys, &principal, 5);
}

#[test]
#[ignore = "proved unify export runs out of memory (12 GB) after 450 s, round 6 of the unifier: pack(v0,v1)+v0+v1+v2+v3 = pack(v4,v5)+v4+v5+v6+v7 with the same row at doubled sums; seven unifiers once the pack arguments are identified. The existence export decides the system; only the family is out of reach"]
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
