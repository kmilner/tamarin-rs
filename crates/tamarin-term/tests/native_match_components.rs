#![cfg(feature = "lean-unification")]

use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin::{emap, pair};
use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::{bp_maude_sig, mset_maude_sig, nat_maude_sig, pair_maude_sig};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::f_app_ac;
use tamarin_term::vterm::var_term as v;

fn native() -> MaudeHandle {
    let sig = mset_maude_sig()
        .merge(nat_maude_sig())
        .merge(bp_maude_sig())
        .merge(pair_maude_sig());
    MaudeHandle::start_with_backend("/nonexistent/maude", sig, AlgebraBackend::NativeOnly).unwrap()
}

fn sum(args: Vec<LNTerm>) -> LNTerm {
    f_app_ac(AcSym::Union, args)
}

fn eq(subject: LNTerm, pattern: LNTerm) -> Equal<LNTerm> {
    Equal {
        lhs: subject,
        rhs: pattern,
    }
}

fn keys() -> [LVar; 4] {
    ["x", "y", "p", "q"].map(|name| LVar::new(name, LSort::Msg, 0))
}

// 2X+Y and X+2Y uniquely determine X and Y. The variable p in X's
// image is a frozen occurrence, even when p is bound in a different row.
fn wide() -> (Vec<Equal<LNTerm>>, LNTerm) {
    let [x, y, p, _] = keys();
    let atoms: Vec<_> = (0..48)
        .map(|i| v(LVar::new("frozen", LSort::Msg, i)))
        .collect();
    let image = sum(atoms);
    (
        vec![
            eq(
                sum(vec![v(p), v(p), image.clone()]),
                sum(vec![v(x), v(x), v(y)]),
            ),
            eq(
                sum(vec![v(p), image.clone(), image.clone()]),
                sum(vec![v(x), v(y), v(y)]),
            ),
        ],
        image,
    )
}

#[test]
fn independent_ac_commutative_and_free_rows_preserve_shared_subject_names() {
    let [x, y, p, q] = keys();
    let r = LVar::new("r", LSort::Msg, 0);
    let a = pub_term("a");
    let b = pub_term("b");
    let (mut rows, image) = wide();
    rows.push(eq(emap(a.clone(), b.clone()), emap(v(p), v(q))));
    rows.push(eq(pair(v(r), pub_term("tag")), pair(v(r), pub_term("tag"))));
    // The independent free row must retain its explicit identity binding.
    let mut expected = vec![];
    for (p_image, q_image) in [(a.clone(), b.clone()), (b, a)] {
        let mut arm = vec![
            (x, v(p)),
            (y, image.clone()),
            (p, p_image),
            (q, q_image),
            (r, v(r)),
        ];
        arm.sort();
        expected.push(arm);
    }
    expected.sort();
    rows.swap(1, 2); // Interleave the weighted equations with the commutative row.
    for reversed in [false, true] {
        if reversed {
            rows.reverse();
        }
        assert_eq!(native().match_eqs(&rows).unwrap(), expected);
        assert!(native().has_match_eqs(&rows).unwrap());
        let scoped: Vec<_> = rows
            .iter()
            .map(|e| eq(e.rhs.clone(), e.lhs.clone()))
            .collect();
        let names = [x, y, p, q, r]
            .map(|key| (key.name, key.idx))
            .into_iter()
            .collect();
        assert_eq!(
            native().match_eqs_skolemize_both(&scoped, &names).unwrap(),
            expected
        );
    }
}

#[test]
fn mixed_ac_heads_decide_without_materializing_the_cartesian_family() {
    let (mut rows, _) = wide();
    let add = |args| f_app_ac(AcSym::NatPlus, args);
    let n = |i| v(LVar::new("n", LSort::Nat, i));
    // Ten distinct frozen atoms onto three nonempty captures give 55,980 assignments.
    rows.push(eq(
        add((3..13).map(n).collect()),
        add((0..3).map(n).collect()),
    ));
    assert!(native().has_match_eqs(&rows).unwrap());
}

#[test]
fn product_preserves_all_choices_and_conflicting_shared_captures_refute() {
    let [x, y, p, q] = keys();
    let (mut rows, image) = wide();
    let a = pub_term("a");
    let b = pub_term("b");
    rows.push(eq(emap(a.clone(), b.clone()), emap(v(p), v(q))));
    let add = |args| f_app_ac(AcSym::NatPlus, args);
    let n = |i| LVar::new("n", LSort::Nat, i);
    rows.push(eq(add(vec![v(n(2)), v(n(3))]), add(vec![v(n(0)), v(n(1))])));
    let mut expected = vec![];
    for (pi, qi) in [(&a, &b), (&b, &a)] {
        for (ni, mi) in [(2, 3), (3, 2)] {
            let mut arm = vec![
                (x, v(p)),
                (y, image.clone()),
                (p, pi.clone()),
                (q, qi.clone()),
                (n(0), v(n(ni))),
                (n(1), v(n(mi))),
            ];
            arm.sort();
            expected.push(arm);
        }
    }
    expected.sort();
    assert_eq!(native().match_eqs(&rows).unwrap(), expected);
    rows.push(eq(a.clone(), v(x)));
    // The two weighted rows force x to be the frozen p, so x cannot be a.
    assert!(!native().has_match_eqs(&rows).unwrap());
    assert!(native().match_eqs(&rows).unwrap().is_empty());
}

#[test]
fn component_witnesses_do_not_require_enumerating_the_product() {
    let mut rows = vec![];
    let (a, b) = (pub_term("a"), pub_term("b"));
    for i in 0..16 {
        let p = v(LVar::new("p", LSort::Msg, i));
        let q = v(LVar::new("q", LSort::Msg, i));
        rows.push(eq(emap(a.clone(), b.clone()), emap(p, q)));
    }
    // Sixteen independent commutative orientations have 65,536 full arms.
    assert!(native().has_match_eqs(&rows).unwrap());
}

#[test]
fn first_match_agrees_with_maude_on_shared_identities_and_ambiguous_orientations() {
    let Some(path) = tamarin_test_support::require_maude_path() else {
        return;
    };
    let sig = bp_maude_sig();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let hybrid = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Hybrid).unwrap();
    let native = native();
    let [x, y, p, _] = keys();
    let i = LVar::new("i", LSort::Node, 0);
    let orient = eq(emap(v(y), v(p)), emap(v(x), v(y)));
    let mut rows = vec![orient.clone(), eq(v(y), v(x)), eq(v(i), v(i))];
    let mut expected = vec![(x, v(y)), (y, v(p)), (i, v(i))];
    expected.sort();
    assert_eq!(oracle.match_eqs(&rows).unwrap(), vec![expected.clone()]);
    assert_eq!(
        hybrid.first_match_eqs(&rows).unwrap(),
        Some(expected.clone())
    );
    assert_eq!(native.first_match_eqs(&rows).unwrap(), Some(expected));
    rows.push(eq(v(p), v(x)));
    assert!(oracle.match_eqs(&rows).unwrap().is_empty());
    assert_eq!(hybrid.first_match_eqs(&rows).unwrap(), None);
    assert_eq!(native.first_match_eqs(&rows).unwrap(), None);

    let ambiguous = [orient];
    let alternatives = oracle.match_eqs(&ambiguous).unwrap();
    assert_eq!(alternatives.len(), 2);
    assert_eq!(
        hybrid.first_match_eqs(&ambiguous).unwrap().as_ref(),
        alternatives.first()
    );
    assert_eq!(
        native.first_match_eqs(&ambiguous).unwrap().as_ref(),
        alternatives.iter().min()
    );
}

#[test]
fn nested_conjunctions_share_captures_and_preserve_the_scoped_rigid_variable() {
    use tamarin_term::lean_unification::{match_modulo_attributes, Outcome};
    use tamarin_term::term::f_app_list;
    let [x, y, p, _] = keys();
    let subject = f_app_list(vec![f_app_list(vec![v(y), v(p)]), v(y)]);
    let pattern = f_app_list(vec![f_app_list(vec![v(x), v(p)]), v(x)]);
    let native = native();
    let empty = f_app_list(vec![]);
    assert_eq!(
        native.first_match_eqs(&[eq(empty.clone(), empty)]).unwrap(),
        Some(vec![])
    );
    let rows = [eq(subject.clone(), pattern.clone())];
    assert!(native.has_match_eqs(&rows).unwrap());
    let mut expected = vec![(x, v(y)), (p, v(p))];
    expected.sort();
    assert_eq!(native.match_eqs(&rows).unwrap(), vec![expected]);
    let scope = [(x.name, x.idx)].into_iter().collect();
    let scoped = [eq(pattern.clone(), subject.clone())];
    let expected = vec![vec![(x, v(y))]];
    assert_eq!(
        match_modulo_attributes(&native.maude_sig(), &scoped, |key| *key == x).unwrap(),
        Outcome::Complete(expected.clone())
    );
    assert_eq!(
        native.match_eqs_skolemize_both(&scoped, &scope).unwrap(),
        expected
    );
    let conflict = [eq(
        f_app_list(vec![f_app_list(vec![v(y), v(p)]), v(p)]),
        pattern,
    )];
    assert!(!native.has_match_eqs(&conflict).unwrap());
}
