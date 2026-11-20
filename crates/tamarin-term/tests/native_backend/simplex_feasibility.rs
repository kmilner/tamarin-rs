use super::*;

type Column = [i32; 4];

fn equations(columns: &[Column]) -> Vec<Equal<LNTerm>> {
    (0..4)
        .map(|j| {
            let mut left = Vec::new();
            let mut right = Vec::new();
            for (i, c) in columns.iter().enumerate() {
                let coefficient = c[j];
                let side = if coefficient > 0 {
                    &mut left
                } else {
                    &mut right
                };
                let x = Term::Lit(Lit::Var(LVar::new("v", LSort::Msg, i as u64)));
                side.extend(std::iter::repeat_n(x, coefficient.unsigned_abs() as usize));
            }
            assert!(!left.is_empty() && !right.is_empty());
            Equal {
                lhs: f_app_ac(AcSym::Union, left),
                rhs: f_app_ac(AcSym::Union, right),
            }
        })
        .collect()
}

fn check_native(columns: &[Column], expected: bool) {
    let mut rows = equations(columns);
    for presentation in 0..2 {
        if presentation == 1 {
            rows.reverse();
            for row in rows.iter_mut().step_by(2) {
                std::mem::swap(&mut row.lhs, &mut row.rhs);
            }
        }
        let h = native();
        assert_eq!(h.unifiable(&rows).unwrap(), expected);
        let full = native();
        if expected {
            // Verify the concrete positive witness on the original conjunction.
            // Asking for all unifiers of this 47-column matrix exhaustively
            // enumerates its generator selections in the total reference.
            let atom: LNTerm = pub_term("witness");
            let bindings: Vec<_> = (0..columns.len())
                .map(|i| {
                    let v = LVar::new("v", LSort::Msg, i as u64);
                    (
                        v,
                        f_app_ac(AcSym::Union, vec![atom.clone(); if i < 2 { 45 } else { 2 }]),
                    )
                })
                .collect();
            let subst = tamarin_term::subst::Subst::from_list(bindings);
            for eq in &rows {
                assert_eq!(
                    tamarin_term::subst::apply_vterm(&subst, eq.lhs.clone()),
                    tamarin_term::subst::apply_vterm(&subst, eq.rhs.clone())
                );
            }
        } else {
            assert!(full.unify(&rows).unwrap().is_empty());
        }
        assert_eq!(full.stats().unify_count, 0);
        assert_eq!(h.stats().unify_count, 0);
    }
}

#[test]
fn rank_four_ac_decisions_have_independent_certificates() {
    // The origin and three coordinate unit points supply four independent
    // columns. All four AC equations share this one variable domain.
    let mut grid = Vec::new();
    for p in -2..=2 {
        for q in -1..=1 {
            for r in -1..=1 {
                grid.push([p, q, r, p + 2 * q + 3 * r + 1]);
            }
        }
    }
    // R4 - R1 - 2R2 - 3R3 says that the sum of all image sizes is zero.
    // Every variable must have a nonempty image under ordinary AC.
    assert!(grid.iter().all(|[p, q, r, t]| t - p - 2 * q - 3 * r == 1));
    check_native(&grid, false);

    // Both new columns have coefficient -1 in the same row combination.
    // Map their variables to 45 copies of one atom and all grid variables
    // to two copies. These sizes balance each original row independently.
    let mut possible = vec![[8, 0, 0, 7], [-8, 0, 0, -9]];
    possible.extend(grid);
    for j in 0..4 {
        let balance: i32 = possible
            .iter()
            .enumerate()
            .map(|(i, c)| c[j] * if i < 2 { 45 } else { 2 })
            .sum();
        assert_eq!(balance, 0);
    }
    check_native(&possible, true);
}
