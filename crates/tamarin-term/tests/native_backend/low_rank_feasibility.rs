use super::*;

const ROW_WEIGHTS: [(i32, i32); 6] = [(1, 0), (1, 1), (2, 1), (-2, 1), (-1, 1), (3, -2)];

fn equations(columns: &[(i32, i32)]) -> Vec<Equal<LNTerm>> {
    ROW_WEIGHTS
        .into_iter()
        .map(|(a, b)| {
            let mut left = Vec::new();
            let mut right = Vec::new();
            for (i, &(p, d)) in columns.iter().enumerate() {
                let coefficient = a * p + b * d;
                let side = if coefficient > 0 {
                    &mut left
                } else {
                    &mut right
                };
                let term = Term::Lit(Lit::Var(LVar::new("v", LSort::Msg, i as u64)));
                side.extend(std::iter::repeat_n(
                    term,
                    coefficient.unsigned_abs() as usize,
                ));
            }
            Equal {
                lhs: f_app_ac(AcSym::Union, left),
                rhs: f_app_ac(AcSym::Union, right),
            }
        })
        .collect()
}

#[test]
fn wide_ac_existence_depends_on_two_row_directions_in_either_order_and_orientation() {
    let grid: Vec<_> = (1..=5)
        .flat_map(|d| (-4..=4).map(move |p| (p, d)))
        .collect();
    for possible in [false, true] {
        let mut columns = grid.clone();
        if possible {
            columns.insert(6, (1, -1));
            columns.insert(7, (-1, -1));
            // A positive unifier sends each variable to copies of one common
            // atom. Use two copies on the grid, 135 copies on each extra column.
            for (a, b) in ROW_WEIGHTS {
                let balance: i32 = columns
                    .iter()
                    .map(|&(p, d)| {
                        let size = if d < 0 { 135 } else { 2 };
                        (a * p + b * d) * size
                    })
                    .sum();
                assert_eq!(balance, 0);
            }
        } else {
            // The first two equations impose P=0 and P+D=0. Subtracting
            // gives D=0, impossible for positive sizes on this grid.
            assert!(columns.iter().all(|&(_, d)| d > 0));
        }

        let mut rows = equations(&columns);
        for _ in 0..2 {
            for _ in 0..2 {
                let h = native();
                assert_eq!(h.unifiable(&rows).unwrap(), possible);
                assert_eq!(h.stats().unify_count, 0);
                rows.reverse();
            }
            for row in &mut rows {
                std::mem::swap(&mut row.lhs, &mut row.rhs);
            }
        }
    }
}
