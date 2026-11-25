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
//! [`present`] proposes, for each arm of the export, the names the Maude
//! backend would have used: a name for every witness of the arm. It does not
//! rename anything, and nothing here is trusted. The proposal goes to the
//! naming export of the algebra library, whose tables the reply is then read
//! through. That export takes a proposal only if no two witnesses of an arm
//! get one name at one sort. The name of a query variable is not a name:
//! the witness then stands for that variable, which the reader accepts only
//! where the witness is the whole image of the variable, and the arm has no
//! binding for it. That is how an unconstrained variable loses the renaming
//! the export gives it.
//!
//! The arm this module expects to be read back is the Maude backend's own
//! composition. The caller compares the two: a family that is read back as
//! anything else was not that composition, and gets the export's own names.
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

/// What this module looks at in an arm of the proved export, under names the
/// caller chose for its witnesses.
pub(crate) struct ArmView {
    /// The query variables, each with the witness it is bound to when its
    /// image is one witness.
    pub(crate) bindings: Vec<(LVar, Option<LVar>)>,
    /// The witnesses in the order of their first occurrence, each with the
    /// number of its occurrences in the arm.
    pub(crate) witnesses: Vec<(LVar, usize)>,
    /// The images of the variables of the delayed equations, and of any
    /// others.
    pub(crate) images: Arm,
}

/// What [`present`] proposes for one arm.
#[derive(Debug, PartialEq)]
pub(crate) struct Spelling {
    /// A name for each witness of the arm, in the order of [`ArmView::witnesses`].
    pub(crate) targets: Vec<LVar>,
    /// The arm under those names, as the Maude backend would return it.
    pub(crate) expected: Arm,
}

/// The names the Maude backend gives the witnesses of the arms of the proved
/// export for one request. `factored` and `residual` are that backend's
/// split of the request: the unifier of its free part, and the AC/C equations
/// it leaves for the engine.
///
/// `None` when some arm cannot be the composition that backend builds; the
/// caller then keeps the export's names for the whole family.
pub(crate) fn present(
    factored: &Subst<Name, LVar>,
    residual: &[Equal<LNTerm>],
    arms: &[ArmView],
) -> Option<Vec<Spelling>> {
    // The free part has one most general unifier.
    if residual.is_empty() && arms.len() != 1 {
        return None;
    }
    arms.iter()
        .map(|arm| present_arm(factored, residual, arm))
        .collect()
}

fn present_arm(
    factored: &Subst<Name, LVar>,
    residual: &[Equal<LNTerm>],
    arm: &ArmView,
) -> Option<Spelling> {
    // The query variables, each with its single witness, in the order of the
    // variables: looked up by binary search.
    let mut singles: Vec<(LVar, Option<LVar>)> = arm.bindings.clone();
    singles.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    if singles.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return None;
    }
    let find = |v: &LVar| singles.binary_search_by(|(key, _)| key.cmp(v)).ok();
    let in_query = |v: &LVar| find(v).is_some();
    // The export binds every query variable, so its range holds witnesses only.
    let mut renaming = Renaming::new(&arm.witnesses)?;
    if arm.witnesses.iter().any(|(w, _)| in_query(w)) {
        return None;
    }

    // The engine's part of the arm: the images of the delayed equations'
    // variables, with witnesses called `x` and numbered above those variables
    // in order of first occurrence, as the Maude reply decoder does.
    let mut engine_names: FastMap<LVar, LVar> = FastMap::default();
    let mut engine = Vec::new();
    if !residual.is_empty() {
        let images: FastMap<LVar, &LNTerm> = arm.images.iter().map(|(v, t)| (*v, t)).collect();
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
    for (witness, named) in &engine_names {
        if let Some(target) = renamed.get(named) {
            renaming.insert(*witness, *target);
        }
    }
    for (v, image) in composed.iter() {
        let single = singles[find(v)?].1;
        if let Term::Lit(Lit::Var(target)) = image {
            let witness = single?;
            if renaming.entry(witness, *target) != *target {
                return None;
            }
        }
    }
    if !renaming.is_witness_renaming(in_query) {
        return None;
    }
    // The composition leaves an unconstrained variable out. The arm must
    // bind it to a witness of its own that nothing else mentions, which
    // takes the variable's own name.
    for (v, single) in &arm.bindings {
        if composed.image_of(v).is_none() {
            let w = (*single)?;
            if w.sort != v.sort || renaming.occurrences(&w) != Some(1) {
                return None;
            }
            renaming.insert(w, *v);
        }
    }
    let targets = renaming.targets()?;
    Some(Spelling {
        targets,
        expected: composed.to_list(),
    })
}

/// A renaming of the witnesses of an arm, held by their position in
/// [`ArmView::witnesses`]. A variable that is not a witness of the arm keeps
/// its target aside, where it still counts for [`Self::is_witness_renaming`].
struct Renaming<'a> {
    witnesses: &'a [(LVar, usize)],
    position: FastMap<LVar, usize>,
    targets: Vec<Option<LVar>>,
    others: Vec<(LVar, LVar)>,
}

impl<'a> Renaming<'a> {
    /// `None` when a witness is listed twice.
    fn new(witnesses: &'a [(LVar, usize)]) -> Option<Self> {
        let mut position = FastMap::default();
        position.reserve(witnesses.len());
        for (at, (w, _)) in witnesses.iter().enumerate() {
            if position.insert(*w, at).is_some() {
                return None;
            }
        }
        Some(Self {
            witnesses,
            position,
            targets: vec![None; witnesses.len()],
            others: Vec::new(),
        })
    }

    /// Set the target of `witness`.
    fn insert(&mut self, witness: LVar, target: LVar) {
        match self.position.get(&witness) {
            Some(&at) => self.targets[at] = Some(target),
            None => match self.others.iter_mut().find(|(w, _)| *w == witness) {
                Some(entry) => entry.1 = target,
                None => self.others.push((witness, target)),
            },
        }
    }

    /// The target of `witness`, which becomes `target` if it has none.
    fn entry(&mut self, witness: LVar, target: LVar) -> LVar {
        match self.position.get(&witness) {
            Some(&at) => *self.targets[at].get_or_insert(target),
            None => match self.others.iter().find(|(w, _)| *w == witness) {
                Some((_, held)) => *held,
                None => {
                    self.others.push((witness, target));
                    target
                }
            },
        }
    }

    /// The number of occurrences of `witness` in the arm.
    fn occurrences(&self, witness: &LVar) -> Option<usize> {
        self.position.get(witness).map(|&at| self.witnesses[at].1)
    }

    /// See [`is_witness_renaming_of`].
    fn is_witness_renaming(&self, in_query: impl Fn(&LVar) -> bool) -> bool {
        let pairs = self
            .witnesses
            .iter()
            .zip(&self.targets)
            .filter_map(|((w, _), target)| Some((*w, (*target)?)))
            .chain(self.others.iter().copied());
        is_witness_renaming_of(pairs, in_query)
    }

    /// A target for every witness of the arm, in their order.
    fn targets(&self) -> Option<Vec<LVar>> {
        self.targets.iter().copied().collect()
    }
}

/// [`is_witness_renaming_of`] for a renaming held in a map.
#[cfg(test)]
fn is_witness_renaming(renaming: &FastMap<LVar, LVar>, in_query: impl Fn(&LVar) -> bool) -> bool {
    is_witness_renaming_of(renaming.iter().map(|(w, t)| (*w, *t)), in_query)
}

/// Whether the pairs of a renaming, each witness once, send distinct
/// witnesses to distinct variables of the same sort, none of which is a
/// variable of the query.
fn is_witness_renaming_of(
    pairs: impl Iterator<Item = (LVar, LVar)>,
    in_query: impl Fn(&LVar) -> bool,
) -> bool {
    let mut targets: Vec<LVar> = Vec::new();
    for (witness, target) in pairs {
        if witness.sort != target.sort || in_query(&target) {
            return false;
        }
        targets.push(target);
    }
    targets.sort_unstable();
    targets.windows(2).all(|pair| pair[0] != pair[1])
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

    /// What [`present`] looks at in an arm of the export.
    fn view(arm: &Arm) -> ArmView {
        let mut witnesses: Vec<(LVar, usize)> = Vec::new();
        for (_, image) in arm {
            image.for_each_free(
                &mut |w| match witnesses.iter_mut().find(|(seen, _)| seen == w) {
                    Some((_, count)) => *count += 1,
                    None => witnesses.push((*w, 1)),
                },
            );
        }
        let bindings = arm
            .iter()
            .map(|(key, image)| match image {
                Term::Lit(Lit::Var(w)) => (*key, Some(*w)),
                _ => (*key, None),
            })
            .collect();
        ArmView {
            bindings,
            witnesses,
            images: arm.clone(),
        }
    }

    fn views(arms: &[Arm]) -> Vec<ArmView> {
        arms.iter().map(view).collect()
    }

    /// The arm as the caller reads it back when the export takes the proposed
    /// names: every witness under its name, a variable bound to its own name
    /// left out, in the order of the variables.
    fn read_back(arm: &Arm, spelling: &Spelling) -> Arm {
        let names: FastMap<LVar, LVar> = view(arm)
            .witnesses
            .iter()
            .map(|(w, _)| *w)
            .zip(spelling.targets.iter().copied())
            .collect();
        let mut read: Arm = arm
            .iter()
            .map(|(key, image)| (*key, image.clone().map_free(&mut |w| names[&w])))
            .filter(|(key, image)| *image != v(*key))
            .collect();
        read.sort_by_key(|(key, _)| *key);
        read
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
        let presented = present(&factored, &residual, &views(std::slice::from_ref(&arm))).unwrap();
        let expected =
            crate::subst_vfresh::compose_vfresh(&LNSubstVFresh::empty(), &factored).to_list();
        assert_eq!(presented.len(), 1);
        assert_eq!(presented[0].expected, expected);
        // The arm under the proposed names is that answer.
        assert_eq!(read_back(&arm, &presented[0]), expected);
        // The witnesses took the names of the variables they stand for.
        assert_eq!(presented[0].targets.len(), 2);
        let names: Vec<&str> = presented[0].targets.iter().map(|w| w.name).collect();
        assert!(names.iter().all(|n| *n == "ea" || *n == "eb"), "{names:?}");
        assert_renaming_of(&arm, &presented[0].expected);
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
        let presented = present(&factored, &residual, &views(std::slice::from_ref(&arm))).unwrap();
        // Each witness takes the name of the variable it is the image of,
        // which leaves the arm without a binding.
        assert_eq!(
            presented,
            vec![Spelling {
                targets: vec![a, b],
                expected: Vec::new()
            }]
        );
        assert_eq!(read_back(&arm, &presented[0]), Vec::new());
        // A witness shared by two variables identifies them: not a renaming.
        let merged = vec![(a, v(w1)), (b, v(w1))];
        assert_eq!(present(&factored, &residual, &views(&[merged])), None);
        // Nor is a binding that narrows the variable's sort.
        let narrowed = vec![(a, v(var("x", LSort::Fresh, 3))), (b, v(w2))];
        assert_eq!(present(&factored, &residual, &views(&[narrowed])), None);
    }

    #[test]
    fn an_arm_that_is_not_the_free_unifier_keeps_its_names() {
        let a = var("a", LSort::Msg, 1);
        let b = var("b", LSort::Msg, 2);
        let eqs = [Equal::new(v(a), f(vec![v(b)]))];
        let (factored, residual) = split(&eqs);
        let w = var("x", LSort::Msg, 3);
        // An instance of the unifier, a second arm, and an arm whose range
        // mentions a query variable get no names.
        let instance = vec![(a, f(vec![f(vec![v(w)])])), (b, f(vec![v(w)]))];
        assert_eq!(present(&factored, &residual, &views(&[instance])), None);
        let good = vec![(a, f(vec![v(w)])), (b, v(w))];
        assert_eq!(
            present(&factored, &residual, &views(&[good.clone(), good.clone()])),
            None
        );
        let open = vec![(a, f(vec![v(b)]))];
        assert_eq!(present(&factored, &residual, &views(&[open])), None);
        let presented = present(&factored, &residual, &views(std::slice::from_ref(&good))).unwrap();
        assert_eq!(read_back(&good, &presented[0]), presented[0].expected);
        // An arm of another shape can get names, since only the bindings to
        // one witness are looked at. It is not read back as the composition,
        // which is what the caller tests.
        let deeper = vec![(a, f(vec![f(vec![v(w)])])), (b, v(w))];
        let presented =
            present(&factored, &residual, &views(std::slice::from_ref(&deeper))).unwrap();
        assert_ne!(read_back(&deeper, &presented[0]), presented[0].expected);
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
        let presented = present(&factored, &residual, &views(&arms)).unwrap();
        assert_eq!(presented.len(), arms.len());
        for (arm, spelling) in arms.iter().zip(&presented) {
            let shown = &spelling.expected;
            assert_eq!(&read_back(arm, spelling), shown);
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
        // Only the images of the delayed equation's variables are looked at,
        // and without them there is nothing to number the engine's witnesses by.
        let mut partial = views(&arms);
        for arm in &mut partial {
            arm.images.retain(|(key, _)| [a, b, c, d].contains(key));
        }
        assert_eq!(
            present(&factored, &residual, &partial).as_ref(),
            Some(&presented)
        );
        for arm in &mut partial {
            arm.images.clear();
        }
        assert_eq!(present(&factored, &residual, &partial), None);
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
