use super::*;
use crate::function_symbols::{Constructability, NoEqSym, Privacy};
use crate::term::f_app_no_eq;

fn select(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_no_eq(symbol(), vec![a, b])
}

fn symbol() -> NoEqSym {
    NoEqSym::new(b"select", 2, Privacy::Public, Constructability::Constructor)
}

fn with_rules(rules: impl IntoIterator<Item = (LNTerm, LNTerm)>) -> MaudeSig {
    let mut sig = signature(rules);
    sig.st_fun_syms.insert(symbol());
    sig.refresh()
}

fn wide() -> LNTerm {
    f_app_ac(
        AcSym::Union,
        (0..64)
            .map(|i| Term::Lit(Lit::Var(LVar::new("f", LSort::Msg, i))))
            .collect(),
    )
}

#[test]
fn projected_rule_reduction_skips_shared_erased_ac_allocations() {
    let (x, y, z, w) = (var("x"), var("y"), var("z"), var("w"));
    let sig = with_rules([(select(bag([x, y, z]), w.clone()), w)]);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    let frozen = var("x"); // A matching key in the rule, a frozen name in the query.
    assert_eq!(
        native.reduce(&select(wide(), frozen.clone())).unwrap(),
        frozen
    );
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn projected_existence_keeps_connected_patterns_and_rhs_choices() {
    use crate::builtin::emap;
    use crate::maude_sig::bp_maude_sig;
    let (x, y, z, r, s) = (var("x"), var("y"), var("z"), var("r"), var("s"));
    let pattern = select(pair(bag([x.clone(), y, z]), hash(x)), emap(r.clone(), s));
    let sig = with_rules([(pattern, r)]).merge(bp_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let query = |required| select(pair(wide(), hash(required)), emap(a.clone(), b.clone()));
    let positive = query(Term::Lit(Lit::Var(LVar::new("f", LSort::Msg, 9))));
    assert_eq!(
        table.successors(&positive, &mut 100_000).unwrap(),
        Some([a.clone(), b.clone()].into_iter().collect())
    );
    let miss = query(pub_term("absent"));
    assert_eq!(
        table.successors(&miss, &mut 100_000).unwrap(),
        Some(BTreeSet::new())
    );
    // The certifier does not accept this table, and the all-paths check does
    // not settle a term this wide, so a raw session reports the table for
    // the irreducible query and for the ambiguous one alike.
    for query in [&miss, &positive] {
        let native = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        assert!(matches!(
            native.reduce(query),
            Err(crate::maude_proc::MaudeError::UnsupportedOperation(
                crate::maude_proc::UNCERTIFIED_TABLE
            ))
        ));
    }
}

#[test]
fn native_oracle_projected_ground_rhs_preserves_the_ac_subproduct_complement() {
    let marker = NoEqSym::new(b"marker", 0, Privacy::Public, Constructability::Constructor);
    let mark = f_app_no_eq(marker, vec![]);
    let x = var("x");
    let mut sig = with_rules([(bag([x.clone(), x]), mark.clone())]);
    sig.st_fun_syms.insert(marker);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let input = bag([a.clone(), a, b.clone()]);
    let result = bag([mark, b]);
    assert_eq!(native.reduce(&input).unwrap(), result);
    let table = RuleTable::new(&sig).unwrap();
    assert_eq!(table.search_with_budget(&input, 1).unwrap(), None);
    assert_eq!(
        table.successors(&input, &mut 100_000).unwrap(),
        Some([result.clone()].into_iter().collect())
    );
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), result);
    }
}

#[test]
fn erased_tree_existence_distinguishes_a_witness_from_exhaustion() {
    use crate::builtin::emap;
    use crate::rewriting::Equal;
    let (a, b) = (pub_term("a"), pub_term("b"));
    let vars = |i| Term::Lit(Lit::Var(LVar::new("value", LSort::Msg, i)));
    let rows: Vec<_> = (0..16)
        .map(|i| Equal {
            lhs: emap(vars(2 * i), vars(2 * i + 1)),
            rhs: emap(a.clone(), b.clone()),
        })
        .collect();
    assert_eq!(
        open_match::has_match_budget(&rows, &mut 5_000).unwrap(),
        Some(true)
    );
    assert_eq!(open_match::has_match_budget(&rows, &mut 1).unwrap(), None);
    assert!(matches!(
        open_match::with_captures_budget(&rows, vec![], &mut 5_000).unwrap(),
        Outcome::Unsupported
    ));
    let conflict = Equal {
        lhs: emap(vars(0), vars(0)),
        rhs: emap(a, b),
    };
    assert_eq!(
        open_match::has_match_budget(&[conflict], &mut 5_000).unwrap(),
        Some(false)
    );
}

#[test]
fn allocation_connected_to_a_returned_key_keeps_its_full_matching_constraints() {
    let (x, y) = (var("x"), var("y"));
    let pattern = select(bag([x.clone(), y]), x.clone());
    let sig = with_rules([(pattern.clone(), x.clone())]);
    let table = RuleTable::new(&sig).unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let app = |key| select(bag([a.clone(), b.clone()]), key);
    let good = app(a.clone());
    assert!(table
        .projected_rule_values(&pattern, &x, &good, &mut 100_000)
        .unwrap()
        .is_none());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    assert_eq!(native.reduce(&good).unwrap(), a);
    let miss = app(pub_term("missing"));
    assert_eq!(native.reduce(&miss).unwrap(), miss);
}

#[test]
fn projected_values_agree_with_every_full_match_on_small_multisets() {
    use crate::builtin::emap;
    use crate::maude_sig::bp_maude_sig;

    let table = RuleTable::new(&with_rules([]).merge(bp_maude_sig())).unwrap();
    let (x, y, r, s) = (var("x"), var("y"), var("r"), var("s"));
    // The frozen "r" can also appear as the image of the rule variable "r".
    let (a, b) = (r.clone(), pub_term("b"));
    for copies in 1..=2 {
        let mut captures = vec![x.clone(); copies];
        captures.push(y.clone());
        let pattern = select(
            pair(f_app_ac(AcSym::Union, captures), x.clone()),
            emap(r.clone(), s.clone()),
        );
        for n in 2..=5 {
            for count_a in 0..=n {
                let mut factors = vec![a.clone(); count_a];
                factors.resize(n, b.clone());
                let subject_bag = f_app_ac(AcSym::Union, factors);
                for (anchor, available) in [(&a, count_a), (&b, n - count_a)] {
                    for other in [&a, &b] {
                        let subject = select(
                            pair(subject_bag.clone(), anchor.clone()),
                            emap(a.clone(), other.clone()),
                        );
                        let Outcome::Complete(arms) =
                            open_match::root(&pattern, &subject, &mut 100_000).unwrap()
                        else {
                            panic!("small reference did not finish: {pattern} at {subject}")
                        };
                        // Each copy of X consumes the frozen anchor once, and Y is nonempty.
                        let feasible = available >= copies && n > copies;
                        assert_eq!(!arms.is_empty(), feasible);
                        for rhs in [
                            pub_term("fixed"),
                            pair(r.clone(), s.clone()),
                            pair(r.clone(), r.clone()),
                        ] {
                            let expect: BTreeSet<_> = arms
                                .iter()
                                .map(|arm| apply_vterm(&Subst::from_list(arm.clone()), rhs.clone()))
                                .collect();
                            assert_eq!(
                                table
                                    .projected_rule_values(&pattern, &rhs, &subject, &mut 100_000)
                                    .unwrap(),
                                Some(expect),
                                "{pattern} -> {rhs} at {subject}"
                            );
                        }
                    }
                }
            }
        }
    }
}
