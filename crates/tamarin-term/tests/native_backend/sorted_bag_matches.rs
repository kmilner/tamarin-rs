use super::*;
use tamarin_term::lterm::fresh_term;
use tamarin_term::maude_sig::nat_maude_sig;
use tamarin_term::vterm::var_term;

type Arm = Vec<(LVar, LNTerm)>;

fn bag(ts: Vec<LNTerm>) -> LNTerm {
    f_app_ac(AcSym::Union, ts)
}

struct Case {
    rows: Vec<Equal<LNTerm>>,
    raw_arm: Arm,
}

impl Case {
    // The two equations 2X+Y and X+2Y force exactly the supplied images
    // before checking X's declared sort. Y contributes 48 frozen terms.
    fn forced(x: LVar, x_image: Vec<LNTerm>) -> Self {
        let y = LVar::new("y", LSort::Msg, 2);
        let y_image: Vec<_> = (0..48)
            .map(|i| var_term(LVar::new("frozen", LSort::Msg, i)))
            .collect();
        let mut left = x_image.clone();
        left.extend(x_image.iter().cloned());
        left.extend(y_image.iter().cloned());
        let mut right = x_image.clone();
        right.extend(y_image.iter().cloned());
        right.extend(y_image.iter().cloned());
        Self {
            rows: vec![
                Equal {
                    lhs: bag(left),
                    rhs: bag(vec![var_term(x), var_term(x), var_term(y)]),
                },
                Equal {
                    lhs: bag(right),
                    rhs: bag(vec![var_term(x), var_term(y), var_term(y)]),
                },
            ],
            raw_arm: vec![(x, bag(x_image)), (y, bag(y_image))],
        }
    }

    fn check(&self, mut expected: Vec<Arm>) {
        let sig = mset_maude_sig().merge(nat_maude_sig());
        let native =
            MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
        for arm in &mut expected {
            arm.sort();
        }
        expected.sort();
        assert_eq!(
            native.has_match_eqs(&self.rows).unwrap(),
            !expected.is_empty()
        );
        assert_eq!(native.match_eqs(&self.rows).unwrap(), expected);
        let scoped: Vec<_> = self
            .rows
            .iter()
            .map(|e| Equal {
                lhs: e.rhs.clone(),
                rhs: e.lhs.clone(),
            })
            .collect();
        let bindable = [("x", 1), ("y", 2), ("p", 3), ("q", 4)]
            .into_iter()
            .collect();
        assert_eq!(
            native.match_eqs_skolemize_both(&scoped, &bindable).unwrap(),
            expected
        );
        assert_eq!(native.stats().match_count, 0);
    }
}

#[test]
fn shared_narrow_capture_accepts_its_single_frozen_image() {
    for sort in [LSort::Fresh, LSort::Pub, LSort::Nat] {
        let x = LVar::new("x", sort, 1);
        let case = Case::forced(x, vec![var_term(x)]);
        case.check(vec![case.raw_arm.clone()]);
    }

    // A compound NatPlus term is one Nat-sorted frozen factor of Union.
    let x = LVar::new("x", LSort::Nat, 1);
    let n = var_term(LVar::new("frozenNat", LSort::Nat, 11));
    let case = Case::forced(x, vec![f_app_ac(AcSym::NatPlus, vec![n.clone(), n])]);
    case.check(vec![case.raw_arm.clone()]);
}

#[test]
fn shared_narrow_capture_rejects_a_message_product_of_fresh_terms() {
    let x = LVar::new("x", LSort::Fresh, 1);
    for second in ["first", "other"] {
        Case::forced(x, vec![fresh_term("first"), fresh_term(second)]).check(vec![]);
    }
}

#[test]
fn shared_narrow_capture_rejects_a_singleton_of_an_incomparable_sort() {
    let x = LVar::new("x", LSort::Fresh, 1);
    Case::forced(x, vec![pub_term("public")]).check(vec![]);
}

#[test]
fn bare_node_capture_rejects_a_frozen_message_in_a_shared_conjunction() {
    let x = LVar::new("x", LSort::Fresh, 1);
    let mut case = Case::forced(x, vec![var_term(x)]);
    case.rows.push(Equal {
        lhs: pub_term("public"),
        rhs: var_term(LVar::new("p", LSort::Node, 3)),
    });
    case.check(vec![]);
}

#[test]
fn shared_narrow_capture_filters_specific_arms_and_keeps_all_other_bindings() {
    let x = LVar::new("x", LSort::Fresh, 1);
    let mut case = Case::forced(x, vec![var_term(x)]);
    let p = LVar::new("p", LSort::Pub, 3);
    let q = LVar::new("q", LSort::Msg, 4);
    let a = pub_term("a");
    let b = pub_term("b");
    let f = fresh_term("f");
    case.rows.push(Equal {
        lhs: bag(vec![a.clone(), b.clone(), f.clone()]),
        rhs: bag(vec![var_term(p), var_term(q)]),
    });
    // Of the six nonempty two-bag partitions, exactly two give the Pub
    // capture a singleton of its own sort.
    let expected = [(a.clone(), b.clone()), (b, a)]
        .into_iter()
        .map(|(single, rest)| {
            let mut arm = case.raw_arm.clone();
            arm.extend([(p, single), (q, sum(rest, f.clone()))]);
            arm
        })
        .collect();
    case.check(expected);
}

#[test]
fn narrow_captures_compete_for_singletons_without_enumerating_the_full_family() {
    let x = LVar::new("x", LSort::Fresh, 0);
    let y = LVar::new("y", LSort::Fresh, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let pattern = bag(vec![var_term(x), var_term(y), var_term(z)]);
    // The all-distinct input has 3^64 raw placements. X and Y need two
    // eligible occurrences, which may be copies of the same frozen term.
    for extra in [None, Some(fresh_term("other")), Some(var_term(x))] {
        let h = native();
        let expected = extra.is_some();
        let mut atoms = vec![var_term(x)];
        atoms.extend(extra);
        atoms.extend((atoms.len()..64).map(|i| pub_term(format!("p{i}"))));
        assert_eq!(
            h.has_match_eqs(&[Equal {
                lhs: bag(atoms),
                rhs: pattern.clone()
            }])
            .unwrap(),
            expected
        );
        assert_eq!(h.stats().match_count, 0);
        h.check_backend_status().unwrap();
    }
}
