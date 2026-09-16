// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Connective normalization policies, generated reference comparisons and depth cases.
use super::*;

#[test]
fn wide_guarded_dedup_preserves_order_and_constructor_rules() {
    let atoms: Vec<_> = (0..128)
        .map(|i| {
            Guarded::Atom(ProtoAtom::Last(var_term(BVar::Free(LVar::new(
                "i",
                LSort::Node,
                i,
            )))))
        })
        .collect();
    for size in [0, 1, 2, 16, 17, 64, 256] {
        let items: Vec<_> = (0..size)
            .map(|i| atoms[(i * 17) % atoms.len()].clone())
            .collect();
        assert_eq!(gconj(items.clone()), smart_reference(items.clone(), true));
        assert_eq!(gdisj(items.clone()), smart_reference(items.clone(), false));
        assert_eq!(
            gconj(vec![Guarded::Conj(items.clone().into()), gtrue()]),
            smart_reference(items.clone(), true)
        );
        assert_eq!(
            gdisj(vec![Guarded::Disj(items.clone().into()), gfalse()]),
            smart_reference(items.clone(), false)
        );
        // The size-256 case already duplicates every atom. Exercise the
        // production stored-list normalizer instead of testing only the oracle.
        let raw = Guarded::Disj(vec![Guarded::Disj(items.clone().into())].into());
        assert_eq!(
            normalise_guarded_cow(&raw),
            normalise_guarded_reference(&raw)
        );
    }
    for value in [
        Guarded::Conj(atoms.clone().into()),
        Guarded::Disj(atoms.into()),
    ] {
        assert!(normalise_guarded_cow(&value).is_none());
    }
}

#[test]
fn connective_runs_preserve_structural_results_errors_and_freshening() {
    use crate::formula::{avoid_precise_lnformula, Connective, LNFormula, ProtoFormula};
    fn next(seed: &mut u64) -> usize {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (*seed >> 32) as usize
    }
    fn build(seed: &mut u64, depth: usize, valid: bool) -> LNFormula {
        let n = next(seed);
        if depth == 0 {
            if valid {
                // Equality guards bind the quantified message on either branch.
                let body = ProtoFormula::Atom(ProtoAtom::EqE(
                    var_term(BVar::Bound(0)),
                    tamarin_term::lterm::pub_term("a"),
                ));
                return if n.is_multiple_of(2) {
                    ProtoFormula::exists(("x".into(), LSort::Msg), body.and(ProtoFormula::Tf(true)))
                } else {
                    ProtoFormula::for_all(
                        ("x".into(), LSort::Msg),
                        body.implies(ProtoFormula::Tf(false)),
                    )
                };
            }
            return match n % 4 {
                0 => ProtoFormula::Tf(false),
                1 => ProtoFormula::Tf(true),
                _ => ProtoFormula::Atom(ProtoAtom::Last(bfree("i", (n % 3) as u64, LSort::Node))),
            };
        }
        let left = build(seed, depth - 1, valid);
        match n % 8 {
            0 => ProtoFormula::Not(Box::new(left).into()),
            1 | 2 if !valid => ProtoFormula::Qua(
                if n % 8 == 1 {
                    Quantifier::All
                } else {
                    Quantifier::Ex
                },
                ("x".into(), LSort::Msg),
                Box::new(left).into(),
            ),
            _ => ProtoFormula::Conn(
                match n % 4 {
                    0 => Connective::And,
                    1 => Connective::Or,
                    2 => Connective::Imp,
                    _ => Connective::Iff,
                },
                Box::new(left).into(),
                Box::new(build(seed, depth - 1, valid)).into(),
            ),
        }
    }
    for seed in 0..3000 {
        let f = build(&mut (seed + 1), 5, seed % 2 == 0);
        for polarity in [false, true] {
            let mut fresh = avoid_precise_lnformula(&f);
            let mut old_fresh = fresh.clone();
            let got = convert(polarity, &f, &mut fresh);
            let want = convert_reference(polarity, &f, &mut old_fresh);
            match (got, want) {
                (Ok(got), Ok(want)) => {
                    assert_eq!(got, want, "seed={seed} polarity={polarity} {f:?}")
                }
                (Err(got), Err(want)) => {
                    assert_eq!(format!("{got:?}"), format!("{want:?}"), "seed={seed}")
                }
                (got, want) => panic!("seed={seed}: {got:?} != {want:?}"),
            }
            assert_eq!(
                tamarin_term::lterm::fresh_lvar(&mut fresh, "x", LSort::Msg),
                tamarin_term::lterm::fresh_lvar(&mut old_fresh, "x", LSort::Msg)
            );
        }
    }
}

#[test]
fn flattened_normalization_matches_bottom_up_reference() {
    let a = Guarded::Atom(ProtoAtom::Last(bfree("i", 0, LSort::Node)));
    let b = Guarded::Atom(ProtoAtom::Last(bfree("i", 1, LSort::Node)));
    let mut pool = vec![gtrue(), gfalse(), a, b];
    for i in 0..1200 {
        let x = pool[(i * 7 + 1) % pool.len()].clone();
        let y = pool[(i * 11 + 2) % pool.len()].clone();
        let raw = if i % 2 == 0 {
            Guarded::Conj(vec![x.clone(), y, x].into())
        } else {
            Guarded::Disj(vec![x.clone(), y, x].into())
        };
        let got = normalise_guarded_cow(&raw);
        let want = normalise_guarded_reference(&raw);
        assert_eq!(got, want, "case {i}");
        pool.push(if i % 5 == 0 { got.unwrap_or(raw) } else { raw });
        if pool.len() > 16 {
            pool.truncate(4);
        }
    }
}

#[test]
fn deep_connective_runs_normalize_and_convert_on_small_stacks() {
    use crate::formula::{Connective, LNFormula, ProtoFormula};
    tamarin_test_support::on_stack(256 * 1024, || {
        for conjunction in [false, true] {
            for right_associated in [false, true] {
                let atom = |i| ProtoAtom::Last(bfree("i", i, LSort::Node));
                let mut formula: LNFormula = ProtoFormula::Atom(atom(0));
                let mut guarded = Guarded::Atom(atom(0));
                for i in 1..8192 {
                    let pair = if right_associated {
                        (ProtoFormula::Atom(atom(i)), formula)
                    } else {
                        (formula, ProtoFormula::Atom(atom(i)))
                    };
                    formula = ProtoFormula::Conn(
                        if conjunction {
                            Connective::And
                        } else {
                            Connective::Or
                        },
                        Box::new(pair.0).into(),
                        Box::new(pair.1).into(),
                    );
                    let pair = if right_associated {
                        vec![Guarded::Atom(atom(i)), guarded]
                    } else {
                        vec![guarded, Guarded::Atom(atom(i))]
                    };
                    guarded = if conjunction {
                        Guarded::Conj(pair.into())
                    } else {
                        Guarded::Disj(pair.into())
                    };
                }
                let converted = formula_to_guarded(&formula).unwrap();
                let normalized = normalise_guarded_cow(&guarded).unwrap();
                assert_eq!(converted, normalized);
                assert_eq!(walk::children(&converted).len(), 8192);
            }
        }
    });
}

fn simplify_guarded_with_reference(
    fm: &Guarded,
    valuation: &dyn Fn(&Atom<LNTerm>) -> Option<bool>,
) -> Guarded {
    let eval = |a: &Atom<BLNTerm>| unbind_atom(a).and_then(|la| valuation(&la));
    rewrite(
        fm,
        &mut |d, g| {
            Ok::<_, std::convert::Infallible>(match g {
                Guarded::Atom(a) => Step::Done(Some(eval(a).map_or_else(|| g.clone(), gtf))),
                Guarded::GGuarded {
                    qua: Quantifier::All,
                    vars,
                    guards,
                    ..
                } if vars.is_empty() => {
                    let evals: Vec<_> = guards.iter().map(eval).collect();
                    if evals.contains(&Some(false)) {
                        Step::Done(Some(gtrue()))
                    } else {
                        Step::Descend(
                            d,
                            Some(
                                guards
                                    .iter()
                                    .zip(evals)
                                    .filter(|(_, v)| v.is_none())
                                    .map(|(a, _)| a.clone())
                                    .collect::<Vec<_>>(),
                            ),
                        )
                    }
                }
                Guarded::GGuarded { .. } => Step::Done(Some(g.clone())),
                _ => Step::Descend(d, None),
            })
        },
        &mut |g, kept, children| {
            Ok(Some(match g {
                Guarded::Disj(_) => gdisj(children.unwrap_or_default()),
                Guarded::Conj(_) => gconj(children.unwrap_or_default()),
                Guarded::GGuarded { vars, .. } => gall(
                    vars.to_vec(),
                    kept.unwrap(),
                    children.unwrap().pop().unwrap(),
                ),
                _ => unreachable!(),
            }))
        },
    )
    .unwrap()
    .unwrap()
}

fn gnot_reference(g: &Guarded) -> Guarded {
    rewrite(
        g,
        &mut |d, _| Ok::<_, std::convert::Infallible>(Step::Descend(d, ())),
        &mut |g, (), children| {
            Ok(Some(match g {
                Guarded::Atom(a) => gnot_atom(a),
                Guarded::Disj(_) => gconj(children.unwrap_or_default()),
                Guarded::Conj(_) => gdisj(children.unwrap_or_default()),
                Guarded::GGuarded {
                    qua, vars, guards, ..
                } => {
                    let body = children.unwrap().pop().unwrap();
                    if *qua == Quantifier::All {
                        gex(vars.to_vec(), guards.to_vec(), body)
                    } else {
                        gall(vars.to_vec(), guards.to_vec(), body)
                    }
                }
            }))
        },
    )
    .unwrap()
    .unwrap()
}

fn to_induction_hypothesis_reference(g: &Guarded) -> Result<Guarded, String> {
    rewrite(
        g,
        &mut |d, g| {
            // Reject an invalid guard before rebuilding its potentially large body.
            if matches!(g, Guarded::GGuarded { guards, .. } if guards.iter().any(Atom::is_last)) {
                return Err("formula not last-free".to_string());
            }
            Ok(Step::Descend(d, ()))
        },
        &mut |g, (), mut children| {
            match g {
                Guarded::GGuarded {
                    qua,
                    vars,
                    guards,
                    body: _,
                } => {
                    let body2 = children.as_mut().unwrap().pop().unwrap();
                    // Emit `Last(v)` for every node-sorted bound variable.
                    // Mirrors Haskell's
                    //   lastAtos = [ Last (varTerm (Bound j))
                    //              | (j, (_, LSortNode)) <- zip [0..] (reverse ss) ]
                    // Haskell `reverse ss` (Guarded.hs:613-616, see line 615) — node-sorted binders
                    // emitted in REVERSE quantifier order.  For `∀ k #i #j`, ss
                    // reversed = [#j, #i, k] → lastAtos = [Last(#j), Last(#i)].
                    // Without `.rev()`, our disj order is [#i, #j] (matches HS
                    // case_2 first), inverting `case_1`/`case_2` labels for the
                    // `last`-disjunction split and breaking proof-tree shape diff.
                    // HS `lastAtos = do (j, (_, LSortNode)) <- zip [0..] (reverse ss);
                    //                   return $ Last (varTerm (Bound j))`.
                    // Iterate vars inner-to-outer (rev), filter to node-sorted,
                    // assign DeBruijn `j = 0, 1, ...` in that order.
                    let last_atos: Vec<Guarded> = vars
                        .iter()
                        .rev()
                        .enumerate()
                        .filter(|(_, v)| v.1 == LSort::Node)
                        .map(|(j, _)| {
                            Guarded::Atom(ProtoAtom::Last(var_term(BVar::Bound(j as u64))))
                        })
                        .collect();
                    match qua {
                        Quantifier::All => {
                            // gex ss as (gconj (map gnotAtom lastAtos ++ [gf']))
                            let mut items: Vec<Guarded> =
                                last_atos.iter().map(gnot_reference).collect();
                            items.push(body2);
                            Ok(gex(vars.to_vec(), guards.to_vec(), gconj(items)))
                        }
                        Quantifier::Ex => {
                            // gall ss as (gdisj (map GAto lastAtos ++ [gf']))
                            let mut items = last_atos;
                            items.push(body2);
                            Ok(gall(vars.to_vec(), guards.to_vec(), gdisj(items)))
                        }
                    }
                }
                Guarded::Atom(ProtoAtom::Less(i, j)) => Ok(Guarded::Disj(
                    vec![
                        Guarded::Atom(ProtoAtom::EqE(i.clone(), j.clone())),
                        Guarded::Atom(ProtoAtom::Less(j.clone(), i.clone())),
                    ]
                    .into(),
                )),
                Guarded::Atom(ProtoAtom::Last(_)) => Err("formula not last-free".to_string()),
                Guarded::Atom(a) => Ok(gnot_atom(a)),
                Guarded::Disj(_) => Ok(gconj(children.unwrap_or_default())),
                Guarded::Conj(_) => Ok(gdisj(children.unwrap_or_default())),
            }
            .map(Some)
        },
    )
    .map(Option::unwrap)
}

#[test]
fn smart_rewrites_preserve_raw_connective_shapes() {
    let a = Guarded::Atom(ProtoAtom::Less(
        bfree("i", 0, LSort::Node),
        bfree("i", 1, LSort::Node),
    ));
    let b = Guarded::Atom(ProtoAtom::Last(bfree("i", 1, LSort::Node)));
    let mut pool = vec![gtrue(), gfalse(), a, b];
    for i in 0..3000 {
        let items: Vec<_> = (0..i % 5)
            .map(|j| pool[(i * 7 + j * 3) % pool.len()].clone())
            .collect();
        let raw = match i % 4 {
            0 => Guarded::Conj(items.into()),
            1 => Guarded::Disj(items.into()),
            _ => Guarded::GGuarded {
                qua: if i % 4 == 2 {
                    Quantifier::All
                } else {
                    Quantifier::Ex
                },
                vars: if i % 3 == 0 {
                    vec![("x".into(), LSort::Node)]
                } else {
                    vec![]
                }
                .into(),
                guards: if i % 7 == 0 {
                    vec![ProtoAtom::Last(bfree("i", 0, LSort::Node))]
                } else {
                    vec![]
                }
                .into(),
                body: GuardedBody::new(Guarded::Conj(items.into())),
            },
        };
        assert_eq!(gnot(&raw), gnot_reference(&raw), "negate {i}");
        assert_eq!(
            to_induction_hypothesis(&raw),
            to_induction_hypothesis_reference(&raw),
            "induct {i}"
        );
        for answer in [None, Some(false), Some(true)] {
            assert_eq!(
                simplify_guarded_with(&raw, &|_| answer),
                simplify_guarded_with_reference(&raw, &|_| answer),
                "simplify {i}"
            );
        }
        pool.push(raw);
        if pool.len() > 16 {
            pool.truncate(4);
        }
    }
}

#[test]
fn indexed_binder_substitution_preserves_first_match_and_scope() {
    let x = LVar::new("x", LSort::Msg, 0);
    for size in [2, 16] {
        let entries: Vec<_> = (0..size).map(|i| (x, i)).collect();
        let index = IndexedSubst::new(&entries);
        let atom = ProtoAtom::EqE(var_term(BVar::Free(x)), var_term(BVar::Bound(0)));
        assert_eq!(
            subst_free_atom_at(&index, 7, &atom),
            ProtoAtom::EqE(var_term(BVar::Bound(7)), var_term(BVar::Bound(0)))
        );
        let entries: Vec<_> = (0..size)
            .map(|i| (0, LVar::new("x", LSort::Msg, i)))
            .collect();
        let index = IndexedSubst::new(&entries);
        let atom = ProtoAtom::EqE(var_term(BVar::Bound(7)), var_term(BVar::Bound(6)));
        assert_eq!(
            subst_bound_atom_at(&index, 7, &atom),
            ProtoAtom::EqE(var_term(BVar::Free(x)), var_term(BVar::Bound(6)))
        );
    }
}

#[test]
fn deep_smart_rewrites_and_wide_binders_use_small_stacks() {
    tamarin_test_support::on_stack(256 * 1024, || {
        for conj in [true, false] {
            let atom = |i| {
                Guarded::Atom(ProtoAtom::Less(
                    bfree("i", i, LSort::Node),
                    bfree("i", i + 1, LSort::Node),
                ))
            };
            let mut raw = atom(0);
            for i in 1..8192 {
                let items = vec![raw, atom(i)].into();
                raw = if conj {
                    Guarded::Conj(items)
                } else {
                    Guarded::Disj(items)
                };
            }
            let flat = normalise_guarded_cow(&raw).unwrap();
            assert_eq!(gnot(&raw), gnot(&flat));
            assert_eq!(
                to_induction_hypothesis(&raw),
                to_induction_hypothesis(&flat)
            );
            assert_eq!(simplify_guarded_with(&raw, &|_| None), flat);
        }
        let vars: Vec<_> = (0..8192).map(|i| LVar::new("x", LSort::Msg, i)).collect();
        let guards: Vec<_> = vars
            .iter()
            .map(|v| ProtoAtom::EqE(var_term(*v), pub_term("a")))
            .collect();
        let closed = close_guarded(Quantifier::Ex, vars, guards, gtrue());
        let mut fresh = tamarin_utils::fresh::FastFreshState::nothing_used();
        let (q, vars, guards, body) = open_guarded(&closed, &mut fresh).unwrap();
        assert_eq!(close_guarded(q, vars, guards, body), closed);
    });
}

fn normalise_guarded_reference(g: &Guarded) -> Option<Guarded> {
    let norm =
        |child: &Guarded| normalise_guarded_reference(child).unwrap_or_else(|| child.clone());
    let result = match g {
        Guarded::Atom(_) => return None,
        Guarded::Conj(xs) => smart_reference(xs.iter().map(norm).collect(), true),
        Guarded::Disj(xs) => smart_reference(xs.iter().map(norm).collect(), false),
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => Guarded::GGuarded {
            qua: *qua,
            vars: vars.clone(),
            guards: guards.clone(),
            body: GuardedBody::new(norm(body)),
        },
    };
    (result != *g).then_some(result)
}

fn smart_reference(items: Vec<Guarded>, conjunction: bool) -> Guarded {
    fn flatten(item: Guarded, conjunction: bool, out: &mut Vec<Guarded>) {
        match item {
            Guarded::Conj(xs) if conjunction => {
                for x in xs.iter() {
                    flatten(x.clone(), conjunction, out);
                }
            }
            Guarded::Disj(xs) if !conjunction => {
                for x in xs.iter() {
                    flatten(x.clone(), conjunction, out);
                }
            }
            other => out.push(other),
        }
    }
    let mut flat = Vec::new();
    for item in items {
        flatten(item, conjunction, &mut flat);
    }
    if flat.contains(&if conjunction { gfalse() } else { gtrue() }) {
        return if conjunction { gfalse() } else { gtrue() };
    }
    let mut unique = Vec::new();
    for item in flat {
        if !unique.contains(&item) {
            unique.push(item);
        }
    }
    if unique.len() == 1 {
        return unique.pop().unwrap();
    }
    if conjunction {
        Guarded::Conj(unique.into())
    } else {
        Guarded::Disj(unique.into())
    }
}

// A pending goal is a list even when its canonical formula is a singleton.
fn stored_reference(g: &Guarded) -> Option<Guarded> {
    let normalized = normalise_guarded_reference(g).unwrap_or_else(|| g.clone());
    let result = match (g, normalized) {
        (Guarded::Disj(_), g @ Guarded::Disj(_)) => g,
        (Guarded::Disj(_), g) => Guarded::Disj(vec![g].into()),
        (_, g) => g,
    };
    (result != *g).then_some(result)
}

#[test]
fn connective_policies_match_reference_and_keep_stored_goal_twins() {
    fn build(seed: &mut u64, depth: usize) -> Guarded {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let n = (*seed >> 32) as usize;
        if depth == 0 || n.is_multiple_of(5) {
            return Guarded::Atom(ProtoAtom::Last(bfree("i", (n % 4) as u64, LSort::Node)));
        }
        if n % 5 == 1 {
            return Guarded::GGuarded {
                qua: if n.is_multiple_of(2) {
                    Quantifier::All
                } else {
                    Quantifier::Ex
                },
                vars: vec![("x".into(), LSort::Msg)].into(),
                guards: vec![ProtoAtom::Last(bfree("i", 0, LSort::Node))].into(),
                body: GuardedBody::new(build(seed, depth - 1)),
            };
        }
        let mut items: Vec<_> = (0..n % 5).map(|_| build(seed, depth - 1)).collect();
        if n.is_multiple_of(3) && !items.is_empty() {
            items.push(items[0].clone());
        }
        if n.is_multiple_of(2) {
            Guarded::Conj(items.into())
        } else {
            Guarded::Disj(items.into())
        }
    }
    for seed in 0..4000 {
        let g = build(&mut (seed + 1), 5);
        let expected = normalise_guarded_reference(&g);
        assert_eq!(normalise_guarded_cow(&g), expected, "seed={seed}");
        assert_eq!(
            normalise_stored_formula_cow(&g),
            stored_reference(&g),
            "stored seed={seed}"
        );
        let stored = stored_reference(&g).unwrap_or_else(|| g.clone());
        assert!(
            normalise_stored_formula_cow(&stored).is_none(),
            "stored fixpoint seed={seed}"
        );
        let normalized = expected.unwrap_or_else(|| g.clone());
        assert!(
            normalise_guarded_cow(&normalized).is_none(),
            "fixpoint seed={seed}"
        );
        let items = [g.clone(), gtrue(), g.clone(), gfalse(), normalized];
        // Every prefix exercises absorption both before and after other changes.
        for end in 0..=items.len() {
            let items = &items[..end];
            assert_eq!(gconj(items.to_vec()), smart_reference(items.to_vec(), true));
            assert_eq!(
                gdisj(items.to_vec()),
                smart_reference(items.to_vec(), false)
            );
            let formula = Guarded::Disj(items.to_vec().into());
            let expected = stored_reference(&formula);
            let goal = normalise_disj_list_cow(items).map(|xs| Guarded::Disj(xs.into()));
            assert_eq!(goal, expected, "goal twin seed={seed} end={end}");
        }
    }
}

#[test]
fn connective_cow_borrows_unchanged_lists_and_detects_empty_suffixes() {
    use std::borrow::Cow;
    let a = Guarded::Atom(ProtoAtom::Last(bfree("i", 0, LSort::Node)));
    let b = Guarded::Atom(ProtoAtom::Last(bfree("i", 1, LSort::Node)));
    for policy in [ConnectivePolicy::Conjunction, ConnectivePolicy::Disjunction] {
        for items in [vec![], vec![a.clone()], vec![a.clone(), b.clone()]] {
            assert!(matches!(connective_cow(&items, policy), Cow::Borrowed(_)));
        }
        let empty = policy.wrap(vec![]);
        for items in [
            vec![empty.clone()],
            vec![a.clone(), empty.clone()],
            vec![empty, a.clone()],
            vec![a.clone(), a.clone()],
        ] {
            assert!(matches!(connective_cow(&items, policy), Cow::Owned(_)));
        }
    }
}

// This oracle evaluates Boolean meaning, not compatibility with a conversion.
#[test]
fn propositional_conversion_preserves_truth_and_system_polarity() {
    use crate::formula::{Connective, LNFormula, ProtoFormula as F};
    fn eval(f: &LNFormula) -> bool {
        match f {
            F::Tf(b) => *b,
            F::Not(f) => !eval(f),
            F::Conn(c, a, b) => match c {
                Connective::And => eval(a) && eval(b),
                Connective::Or => eval(a) || eval(b),
                Connective::Imp => !eval(a) || eval(b),
                Connective::Iff => eval(a) == eval(b),
            },
            _ => panic!("propositional input only"),
        }
    }
    fn eval_guarded(g: &Guarded) -> bool {
        match g {
            Guarded::Conj(xs) => xs.iter().all(eval_guarded),
            Guarded::Disj(xs) => xs.iter().any(eval_guarded),
            _ => panic!("propositional output only"),
        }
    }
    use crate::theory::TraceQuantifier::{AllTraces, ExistsTrace};
    for a in [false, true] {
        for b in [false, true] {
            for c in [
                Connective::And,
                Connective::Or,
                Connective::Imp,
                Connective::Iff,
            ] {
                let base = F::Conn(c, Box::new(F::Tf(a)).into(), Box::new(F::Tf(b)).into());
                for f in [base.clone(), base.not()] {
                    for polarity in [false, true] {
                        let got = convert(
                            polarity,
                            &f,
                            &mut crate::formula::avoid_precise_lnformula(&f),
                        )
                        .unwrap();
                        assert_eq!(
                            eval_guarded(&got),
                            eval(&f) != polarity,
                            "{f:?}, negative={polarity}"
                        );
                    }
                    let g = formula_to_guarded(&f).unwrap();
                    for q in [AllTraces, ExistsTrace] {
                        for restriction in [gtrue(), g.clone()] {
                            let sys = crate::constraint::system::formula_to_system(
                                vec![restriction.clone()],
                                crate::constraint::system::SourceKind::RawSources,
                                q,
                                &g,
                            );
                            let expected =
                                (eval(&f) != (q == AllTraces)) && eval_guarded(&restriction);
                            assert_eq!(
                                sys.formulas
                                    .iter()
                                    .chain(sys.lemmas.iter())
                                    .all(|x| eval_guarded(x)),
                                expected
                            );
                        }
                    }
                }
            }
        }
    }
}
