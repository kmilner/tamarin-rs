use super::*;

/// Every equation says 2 xᵢ = 3 x₀. Thus x₀ is two copies of one
/// arbitrary term and each other xᵢ is three copies of that same term.
#[test]
fn wide_shared_ratios_have_one_complete_unifier() {
    for (width, factored) in [(36, false), (65, false), (36, true)] {
        check_shared_ratio(width, factored);
    }
}

fn check_shared_ratio(width: u64, factored: bool) {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;

    let variables: Vec<_> = (0..width).map(|i| LVar::new("x", LSort::Msg, i)).collect();
    let copies = |v, n| f_app_ac(AcSym::Union, vec![Term::Lit(Lit::Var(v)); n]);
    let mut equations: Vec<_> = variables[1..]
        .iter()
        .map(|&v| Equal {
            lhs: copies(v, 2),
            rhs: copies(variables[0], 3),
        })
        .collect();
    let alias = LVar::new("alias", LSort::Msg, width);
    if factored {
        equations.push(Equal {
            lhs: Term::Lit(Lit::Var(alias)),
            rhs: hash(Term::Lit(Lit::Var(variables[0]))),
        });
    }
    for order in 0..2 {
        if order == 1 {
            equations.reverse();
            for eq in equations.iter_mut().step_by(2) {
                std::mem::swap(&mut eq.lhs, &mut eq.rhs);
            }
        }
        let handle = MaudeHandle::start_with_backend(
            MISSING,
            mset_maude_sig().merge(hash_maude_sig()),
            AlgebraBackend::ProvedOnly,
        )
        .unwrap();
        let answers = handle.unify(&equations).unwrap();
        let [arm] = answers.as_slice() else {
            panic!(
                "expected exactly one complete answer, got {}",
                answers.len()
            );
        };
        assert_eq!(arm.len(), variables.len() + usize::from(factored));
        let mut shared = None;
        for (i, v) in variables.iter().enumerate() {
            let (_, image) = arm.iter().find(|(key, _)| key == v).unwrap();
            let Term::App(_, factors) = image else {
                panic!("expected repeated witness")
            };
            let Term::Lit(Lit::Var(witness)) = factors[0] else {
                panic!("expected witness")
            };
            assert_eq!(witness.sort, LSort::Msg);
            assert_eq!(*image, copies(witness, if i == 0 { 2 } else { 3 }));
            assert_eq!(*shared.get_or_insert(witness), witness);
        }
        if factored {
            let (_, image) = arm.iter().find(|(key, _)| *key == alias).unwrap();
            assert_eq!(*image, hash(copies(shared.unwrap(), 2)));
        }
        assert_eq!(handle.stats().unify_count, 0);
    }
}
