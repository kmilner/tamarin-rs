use super::*;

#[test]
fn three_captures_cover_every_ordered_nonempty_partition_of_eight_factors() {
    let h = native();
    let vars = ["x", "y", "z"].map(|name| LVar::new(name, LSort::Msg, 0));
    let atoms: Vec<_> = (0..8).map(|i| pub_term(format!("a{i}"))).collect();
    let query = [Equal {
        lhs: f_app_ac(AcSym::Union, atoms.clone()),
        rhs: f_app_ac(AcSym::Union, vars.map(|v| Term::Lit(Lit::Var(v))).to_vec()),
    }];
    let mut expected = Vec::new();
    // Each bit chooses a factor for X or Y; the disjoint complement goes to Z.
    let full = (1 << atoms.len()) - 1;
    for x in 1..full {
        let rest = full ^ x;
        let mut y = (rest - 1) & rest;
        while y > 0 {
            let arm = vars
                .into_iter()
                .zip([x, y, rest ^ y])
                .map(|(v, mask)| {
                    let factors = atoms
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, a)| a.clone())
                        .collect();
                    (v, f_app_ac(AcSym::Union, factors))
                })
                .collect::<Vec<_>>();
            expected.push(arm);
            y = (y - 1) & rest;
        }
    }
    expected.sort_unstable();
    assert_eq!(expected.len(), 5_796);
    assert!(h.has_match_eqs(&query).unwrap());
    assert_eq!(h.match_eqs(&query).unwrap(), expected);
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn sort_filtering_precedes_the_output_limit_across_pages() {
    let h = native();
    let vars = [
        LVar::new("x", LSort::Pub, 0),
        LVar::new("y", LSort::Pub, 0),
        LVar::new("z", LSort::Msg, 0),
    ];
    let atoms: Vec<_> = (0..10).map(|i| pub_term(format!("a{i}"))).collect();
    let query = [Equal {
        lhs: f_app_ac(AcSym::Union, atoms.clone()),
        rhs: f_app_ac(AcSym::Union, vars.map(|v| Term::Lit(Lit::Var(v))).to_vec()),
    }];
    // The two public captures must each be one different public constant.
    let mut expected = Vec::new();
    for (x, a) in atoms.iter().enumerate() {
        for (y, b) in atoms.iter().enumerate().filter(|(y, _)| *y != x) {
            let others = atoms
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != x && *i != y)
                .map(|(_, t)| t.clone())
                .collect();
            let mut arm = vec![
                (vars[0], a.clone()),
                (vars[1], b.clone()),
                (vars[2], f_app_ac(AcSym::Union, others)),
            ];
            arm.sort();
            expected.push(arm);
        }
    }
    expected.sort_unstable();
    assert_eq!(h.match_eqs(&query).unwrap(), expected);
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn raw_product_beyond_one_machine_word_has_a_match_without_collecting() {
    let h = native();
    let query = [Equal {
        lhs: f_app_ac(
            AcSym::Union,
            (0..64).map(|i| pub_term(format!("a{i}"))).collect(),
        ),
        rhs: sum(variable("x"), variable("y")),
    }];
    assert!(h.has_match_eqs(&query).unwrap());
    assert_eq!(h.stats().match_count, 0);
}
