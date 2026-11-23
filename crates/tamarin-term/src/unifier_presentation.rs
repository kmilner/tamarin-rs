//! Witness names for the unifiers of the proved export.
//!
//! A unifier is a substitution from the query's variables to terms over fresh
//! witnesses, and the witnesses carry no meaning beyond their identity. The
//! proof search nevertheless depends on how they are spelled: the name hint
//! of a witness reaches the constraint system, and names and indices decide
//! the stored order of AC arguments and of the cases of a split.
//!
//! The Maude backend spells them as Haskell does. It solves the free part of
//! a request locally, sends only the delayed AC/C equations to the engine,
//! and composes the two with `composeVFresh`, so a witness that stands for a
//! query variable keeps that variable's name and only the engine's own
//! witnesses are called `x`. The proved export answers the whole request and
//! calls every witness `x`.
//!
//! [`present`] gives each arm of the export the spelling the Maude backend
//! would have used. It never changes what an arm says. The result is the arm
//! under an injective renaming of its witnesses that preserves sorts and
//! avoids the query's variables, less bindings that are pure renamings of an
//! unconstrained variable, and every one of those properties is checked on
//! the arm at hand. An arm that fails a check keeps the export's own names.
//!
//! For a request without delayed equations the result is exactly the Maude
//! backend's answer. With delayed equations the engine's witnesses are
//! numbered in the order of this module's traversal, because the order in
//! which Maude prints a unifier is internal to its AC solver.
use crate::lterm::{HasFrees, LNTerm, LVar, Name};
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::subst_vfresh::{compose_vfresh_traced, LNSubstVFresh};
use crate::term::Term;
use crate::vterm::Lit;
use tamarin_utils::{FastMap, FastSet};

type Arm = Vec<(LVar, LNTerm)>;

/// The arms of the proved export for one request, spelled as the Maude
/// backend spells its unifiers. `factored` and `residual` are that backend's
/// split of the request: the unifier of its free part, and the AC/C equations
/// it leaves for the engine.
///
/// `None` when some arm is not the composition this module can check; the
/// caller then keeps the export's names for the whole family.
pub(crate) fn present(
    factored: &Subst<Name, LVar>,
    residual: &[Equal<LNTerm>],
    arms: &[Arm],
) -> Option<Vec<Arm>> {
    // The free part has one most general unifier.
    if residual.is_empty() && arms.len() != 1 {
        return None;
    }
    arms.iter()
        .map(|arm| present_arm(factored, residual, arm))
        .collect()
}

fn present_arm(factored: &Subst<Name, LVar>, residual: &[Equal<LNTerm>], arm: &Arm) -> Option<Arm> {
    let images: FastMap<LVar, &LNTerm> = arm.iter().map(|(v, t)| (*v, t)).collect();
    if images.len() != arm.len() {
        return None;
    }
    // The export binds every query variable, so its range holds witnesses only.
    let mut occurrences: FastMap<LVar, usize> = FastMap::default();
    for (_, image) in arm {
        image.for_each_free(&mut |w| *occurrences.entry(*w).or_default() += 1);
    }
    if occurrences.keys().any(|w| images.contains_key(w)) {
        return None;
    }

    // The engine's part of the arm: the images of the delayed equations'
    // variables, with witnesses called `x` and numbered above those variables
    // in order of first occurrence, as the Maude reply decoder does.
    let mut engine_names: FastMap<LVar, LVar> = FastMap::default();
    let mut engine = Vec::new();
    if !residual.is_empty() {
        let mut variables = Vec::new();
        let mut seen = FastSet::default();
        for eq in residual {
            for side in [&eq.lhs, &eq.rhs] {
                side.for_each_free(&mut |v| {
                    if seen.insert(*v) {
                        variables.push(*v);
                    }
                });
            }
        }
        let highest = variables.iter().map(|v| v.idx).max().unwrap_or(0);
        let mut next = highest.checked_add(1);
        for v in variables {
            let image = (*images.get(&v)?).clone().map_free(&mut |w| {
                *engine_names.entry(w).or_insert_with(|| {
                    let idx = next.unwrap_or(u64::MAX);
                    next = next.and_then(|n| n.checked_add(1));
                    LVar::new("x", w.sort, idx)
                })
            });
            engine.push((v, image));
        }
        // The index space above the query is exhausted.
        next?;
    }
    let engine = LNSubstVFresh::from_list(engine).remove_renamings();
    let (composed, renamed) = compose_vfresh_traced(&engine, factored);

    // How the composition spells each witness of the arm: the engine's
    // witnesses through its index shift, every other one through the query
    // variable it is the image of.
    let mut renaming: FastMap<LVar, LVar> = FastMap::default();
    for (witness, named) in &engine_names {
        if let Some(target) = renamed.get(named) {
            renaming.insert(*witness, *target);
        }
    }
    for (v, image) in composed.iter() {
        let native = images.get(v)?;
        if let Term::Lit(Lit::Var(target)) = image {
            let Term::Lit(Lit::Var(witness)) = native else {
                return None;
            };
            if *renaming.entry(*witness).or_insert(*target) != *target {
                return None;
            }
        }
    }
    if !is_witness_renaming(&renaming, |v| images.contains_key(v)) {
        return None;
    }

    // The composition is the arm under that renaming.
    for (v, native) in &images {
        match composed.image_of(v) {
            Some(image) => {
                let mut total = true;
                let spelled = (*native).clone().map_free(&mut |w| {
                    renaming.get(&w).copied().unwrap_or_else(|| {
                        total = false;
                        w
                    })
                });
                if !total || spelled != *image {
                    return None;
                }
            }
            // The composition leaves an unconstrained variable out. The arm
            // must bind it to a witness of its own that nothing else mentions.
            None => {
                let Term::Lit(Lit::Var(w)) = native else {
                    return None;
                };
                if w.sort != v.sort || occurrences.get(w) != Some(&1) {
                    return None;
                }
            }
        }
    }
    Some(composed.to_list())
}

/// Whether `renaming` sends distinct witnesses to distinct variables of the
/// same sort, none of which is a variable of the query.
fn is_witness_renaming(renaming: &FastMap<LVar, LVar>, in_query: impl Fn(&LVar) -> bool) -> bool {
    let mut targets = FastSet::default();
    renaming.iter().all(|(witness, target)| {
        witness.sort == target.sort && !in_query(target) && targets.insert(*target)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{AcSym, Constructability, FunSym, NoEqSym, Privacy};
    use crate::lterm::LSort;
    use crate::term::f_app;
    use crate::unification::unify_lnterm_factored;

    fn var(name: &'static str, sort: LSort, idx: u64) -> LVar {
        LVar::new(name, sort, idx)
    }

    fn v(lv: LVar) -> LNTerm {
        Term::Lit(Lit::Var(lv))
    }

    fn mult(args: Vec<LNTerm>) -> LNTerm {
        f_app(FunSym::Ac(AcSym::Mult), args)
    }

    fn f(args: Vec<LNTerm>) -> LNTerm {
        let sym = NoEqSym::new(
            "f",
            args.len(),
            Privacy::Public,
            Constructability::Constructor,
        );
        f_app(FunSym::NoEq(sym), args)
    }

    fn split(eqs: &[Equal<LNTerm>]) -> (Subst<Name, LVar>, Vec<Equal<LNTerm>>) {
        unify_lnterm_factored(eqs.to_vec()).expect("the free part unifies")
    }

    /// `presented` is `arm` under some injective renaming of its witnesses
    /// that keeps sorts and avoids the query. Every bijection is tried, so
    /// this does not depend on how [`present`] finds its renaming.
    fn assert_renaming_of(arm: &Arm, presented: &Arm) {
        fn witnesses(arm: &Arm) -> Vec<LVar> {
            let mut out = Vec::new();
            for (_, image) in arm {
                image.for_each_free(&mut |w| {
                    if !out.contains(w) {
                        out.push(*w);
                    }
                });
            }
            out
        }
        fn search(
            from: &[LVar],
            to: &mut Vec<LVar>,
            chosen: &mut FastMap<LVar, LVar>,
            accept: &dyn Fn(&FastMap<LVar, LVar>) -> bool,
        ) -> bool {
            let Some((first, rest)) = from.split_first() else {
                return accept(chosen);
            };
            for i in 0..to.len() {
                let target = to.remove(i);
                chosen.insert(*first, target);
                if search(rest, to, chosen, accept) {
                    return true;
                }
                chosen.remove(first);
                to.insert(i, target);
            }
            false
        }
        let keys: FastSet<LVar> = arm.iter().map(|(k, _)| *k).collect();
        let images: FastMap<LVar, &LNTerm> = presented.iter().map(|(k, t)| (*k, t)).collect();
        // Witnesses of dropped bindings have no counterpart.
        let kept: Arm = arm
            .iter()
            .filter(|(key, _)| images.contains_key(key))
            .cloned()
            .collect();
        assert_eq!(kept.len(), presented.len());
        let found = search(
            &witnesses(&kept),
            &mut witnesses(presented),
            &mut FastMap::default(),
            &|renaming| {
                is_witness_renaming(renaming, |x| keys.contains(x))
                    && kept.iter().all(|(key, image)| {
                        image.clone().map_free(&mut |w| renaming[&w]) == *images[key]
                    })
            },
        );
        assert!(found, "{presented:?} is no renaming of {arm:?}");
    }

    #[test]
    fn a_free_request_is_spelled_exactly_as_the_maude_backend_spells_it() {
        let ea3 = var("ea", LSort::Fresh, 3);
        let ea19 = var("ea", LSort::Fresh, 19);
        let eb19 = var("eb", LSort::Fresh, 19);
        let z = var("z", LSort::Msg, 7);
        let eqs = [
            Equal::new(v(ea3), v(ea19)),
            Equal::new(v(z), mult(vec![v(ea19), v(eb19)])),
        ];
        let (factored, residual) = split(&eqs);
        assert!(residual.is_empty());
        // The export's arm: every variable bound, every witness called `x`.
        let x20 = var("x", LSort::Fresh, 20);
        let x24 = var("x", LSort::Fresh, 24);
        let arm = vec![
            (ea3, v(x20)),
            (ea19, v(x20)),
            (z, mult(vec![v(x20), v(x24)])),
            (eb19, v(x24)),
        ];
        let presented = present(&factored, &residual, std::slice::from_ref(&arm)).unwrap();
        let expected =
            crate::subst_vfresh::compose_vfresh(&LNSubstVFresh::empty(), &factored).to_list();
        assert_eq!(presented, vec![expected]);
        // The witnesses took the names of the variables they stand for.
        let names: Vec<&str> = presented[0]
            .iter()
            .flat_map(|(_, t)| crate::lterm::frees(t))
            .map(|w| w.name)
            .collect();
        assert!(names.iter().all(|n| *n == "ea" || *n == "eb"), "{names:?}");
        assert_renaming_of(&arm, &presented[0]);
    }

    #[test]
    fn an_unconstrained_variable_loses_only_its_private_renaming() {
        let a = var("a", LSort::Msg, 1);
        let b = var("b", LSort::Msg, 2);
        let eqs = [
            Equal::new(f(vec![v(a)]), f(vec![v(a)])),
            Equal::new(v(b), v(b)),
        ];
        let (factored, residual) = split(&eqs);
        let w1 = var("x", LSort::Msg, 3);
        let w2 = var("x", LSort::Msg, 4);
        let arm = vec![(a, v(w1)), (b, v(w2))];
        let presented = present(&factored, &residual, std::slice::from_ref(&arm)).unwrap();
        assert_eq!(presented, vec![Vec::new()]);
        // A witness shared by two variables identifies them: not a renaming.
        let merged = vec![(a, v(w1)), (b, v(w1))];
        assert_eq!(present(&factored, &residual, &[merged]), None);
        // Nor is a binding that narrows the variable's sort.
        let narrowed = vec![(a, v(var("x", LSort::Fresh, 3))), (b, v(w2))];
        assert_eq!(present(&factored, &residual, &[narrowed]), None);
    }

    #[test]
    fn an_arm_that_is_not_the_free_unifier_keeps_its_names() {
        let a = var("a", LSort::Msg, 1);
        let b = var("b", LSort::Msg, 2);
        let eqs = [Equal::new(v(a), f(vec![v(b)]))];
        let (factored, residual) = split(&eqs);
        let w = var("x", LSort::Msg, 3);
        // An instance of the unifier, a second arm, and an arm whose range
        // mentions a query variable are all declined.
        let instance = vec![(a, f(vec![f(vec![v(w)])])), (b, f(vec![v(w)]))];
        assert_eq!(present(&factored, &residual, &[instance]), None);
        let good = vec![(a, f(vec![v(w)])), (b, v(w))];
        assert_eq!(
            present(&factored, &residual, &[good.clone(), good.clone()]),
            None
        );
        let open = vec![(a, f(vec![v(b)]))];
        assert_eq!(present(&factored, &residual, &[open]), None);
        assert!(present(&factored, &residual, &[good]).is_some());
    }

    #[test]
    fn delayed_equations_keep_engine_witnesses_apart_from_named_ones() {
        // a*b =? c*d with a further variable `k` bound by the free part.
        let a = var("a", LSort::Msg, 1);
        let b = var("b", LSort::Msg, 1);
        let c = var("c", LSort::Msg, 1);
        let d = var("d", LSort::Msg, 1);
        let k = var("k", LSort::Msg, 1);
        let n = var("n", LSort::Msg, 1);
        let eqs = [
            Equal::new(mult(vec![v(a), v(b)]), mult(vec![v(c), v(d)])),
            Equal::new(v(k), f(vec![v(n)])),
        ];
        let (factored, residual) = split(&eqs);
        assert_eq!(residual.len(), 1);
        let w = |i| var("x", LSort::Msg, i);
        // The four-way split and the two pairings, as the export returns them.
        let arms = vec![
            vec![
                (a, mult(vec![v(w(2)), v(w(3))])),
                (b, mult(vec![v(w(4)), v(w(5))])),
                (c, mult(vec![v(w(2)), v(w(4))])),
                (d, mult(vec![v(w(3)), v(w(5))])),
                (k, f(vec![v(w(6))])),
                (n, v(w(6))),
            ],
            vec![
                (a, v(w(2))),
                (b, v(w(3))),
                (c, v(w(2))),
                (d, v(w(3))),
                (k, f(vec![v(w(4))])),
                (n, v(w(4))),
            ],
            vec![
                (a, v(w(2))),
                (b, v(w(3))),
                (c, v(w(3))),
                (d, v(w(2))),
                (k, f(vec![v(w(4))])),
                (n, v(w(4))),
            ],
        ];
        let presented = present(&factored, &residual, &arms).unwrap();
        assert_eq!(presented.len(), arms.len());
        for (arm, shown) in arms.iter().zip(&presented) {
            assert_renaming_of(arm, shown);
            let image = |key: LVar| &shown.iter().find(|(k, _)| *k == key).unwrap().1;
            // `n` is no variable of the delayed equation, so its witness is
            // named after it; the engine's witnesses are called `x`.
            let Term::Lit(Lit::Var(named)) = image(n) else {
                panic!("n is bound to a witness")
            };
            assert_eq!(named.name, "n");
            for key in [a, b, c, d] {
                assert!(crate::lterm::frees(image(key))
                    .iter()
                    .all(|x| x.name == "x"));
            }
            // Witnesses sit above every variable of the request.
            for (_, t) in shown {
                assert!(crate::lterm::frees(t).iter().all(|x| x.idx > 1));
            }
        }
    }

    #[test]
    fn a_renaming_must_be_injective_sort_preserving_and_fresh() {
        let w1 = var("x", LSort::Msg, 5);
        let w2 = var("x", LSort::Msg, 6);
        let t = var("a", LSort::Msg, 9);
        let fresh = var("a", LSort::Fresh, 9);
        let none = |_: &LVar| false;
        let one: FastMap<LVar, LVar> = [(w1, t)].into_iter().collect();
        assert!(is_witness_renaming(&one, none));
        assert!(!is_witness_renaming(&one, |x| *x == t));
        let merged: FastMap<LVar, LVar> = [(w1, t), (w2, t)].into_iter().collect();
        assert!(!is_witness_renaming(&merged, none));
        let resorted: FastMap<LVar, LVar> = [(w1, fresh)].into_iter().collect();
        assert!(!is_witness_renaming(&resorted, none));
    }
}
