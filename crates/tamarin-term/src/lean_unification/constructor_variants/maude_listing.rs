//! The order and the witness names of Maude's `get variants` listing.
//!
//! A complete family of variants is a set, and its members are substitutions
//! with a fresh range. The proof search still depends on how the family is
//! listed: the order of the members becomes the order of the cases of a rule
//! variant disjunction, and the indices of the witnesses decide the stored
//! order of AC arguments. This module gives a family of the join solver the
//! listing Maude produces. It runs before the certificate check, so the
//! checker sees exactly the family the prover uses.
//!
//! Witnesses are numbered as the Maude reply decoder numbers them: in order
//! of first occurrence over the bindings, above every query variable that is
//! itself called `x`.
//!
//! The order is Maude's order of generation, which this module obtains by
//! replaying folding variant narrowing (`VariantSearch::expandLayer`,
//! `VariantNarrowingSearchState` and `VariantFolder` in Maude's
//! `src/Higher`): layer by layer, each variant of the frontier is narrowed at
//! every non-variable position in breadth-first order, with the equations of
//! the head symbol in module order. The replay only orders a family that was
//! computed elsewhere. It handles terms and rules without AC or C operators,
//! where every narrowing step has one unifier, and it gives up, leaving the
//! family in the solver's order, as soon as it meets anything else or a
//! variant that is not a member of the family.
use super::RuleTable;
use crate::function_symbols::FunSym;
use crate::lean_unification::{subsort, Error, Substitutions};
use crate::lterm::{HasFrees, LNTerm, LSort, LVar};
use crate::maude_sig::MaudeSig;
use crate::maude_types::sort_of_name;
use crate::rewriting::{Equal, RRule};
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app, Term};
use crate::unification::{unify_lterm_no_ac, UnifyError};
use crate::vterm::Lit;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;

/// The replay stops after this many narrowing steps.
const STEP_LIMIT: usize = 4096;

/// One variant of the replay: the images of the query variables and the
/// normal forms of the observations under them.
struct Variant {
    images: Vec<LNTerm>,
    values: Vec<LNTerm>,
}

impl Variant {
    fn terms(&self) -> impl Iterator<Item = &LNTerm> {
        self.images.iter().chain(&self.values)
    }
}

impl RuleTable {
    /// `family` as Maude lists it: in Maude's order when the replay can
    /// establish it, and with Maude's witness numbering.
    pub(crate) fn maude_listing(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        family: Substitutions,
    ) -> Result<Substitutions, Error> {
        let terms = match query {
            Term::App(FunSym::List, args) => args.as_ref(),
            _ => std::slice::from_ref(query),
        };
        let mut keys = Vec::new();
        query.for_each_free(&mut |v| {
            if !keys.contains(v) {
                keys.push(*v);
            }
        });
        let ordered = match self.generation_order(sig, terms, &keys, &family)? {
            Some(order) => {
                let mut members: Vec<_> = family.into_iter().map(Some).collect();
                order
                    .into_iter()
                    .filter_map(|i| members[i].take())
                    .collect()
            }
            None => family,
        };
        Ok(ordered
            .into_iter()
            .map(|member| number_witnesses(&keys, member))
            .collect())
    }

    /// The members of `family` in the order Maude generates them, or `None`
    /// when the replay does not cover this request.
    fn generation_order(
        &self,
        sig: &MaudeSig,
        terms: &[LNTerm],
        keys: &[LVar],
        family: &Substitutions,
    ) -> Result<Option<Vec<usize>>, Error> {
        if family.len() < 2 || !terms.iter().all(plain) {
            return Ok(None);
        }
        // The family, keyed by the canonical form of each member.
        let mut members: FxHashMap<Vec<LNTerm>, usize> = FxHashMap::default();
        for (index, member) in family.iter().enumerate() {
            let subst = Subst::from_list(member.iter().cloned());
            let images: Vec<_> = keys
                .iter()
                .map(|v| apply_vterm(&subst, Term::Lit(Lit::Var(*v))))
                .collect();
            if !images.iter().all(plain) {
                return Ok(None);
            }
            let mut values = Vec::with_capacity(terms.len());
            for t in terms {
                let Some(value) = self.reduce_native(&apply_vterm(&subst, t.clone()))? else {
                    return Ok(None);
                };
                values.push(value);
            }
            let variant = Variant { images, values };
            if !variant.values.iter().all(plain)
                || members.insert(canonical(&variant), index).is_some()
            {
                return Ok(None);
            }
        }
        let rules: Vec<RRule<LNTerm>> = sig.rrules().into_iter().collect();

        let mut root = Variant {
            images: keys.iter().map(|v| Term::Lit(Lit::Var(*v))).collect(),
            values: Vec::with_capacity(terms.len()),
        };
        for t in terms {
            let Some(value) = self.reduce_native(t)? else {
                return Ok(None);
            };
            root.values.push(value);
        }
        let Some(&first) = members.get(&canonical(&root)) else {
            return Ok(None);
        };
        let mut order = vec![first];
        let mut created = vec![root];
        let mut frontier = vec![0];
        let mut steps = 0;
        while !frontier.is_empty() {
            let mut next = Vec::new();
            for parent in frontier {
                let Some(children) = self.narrowings(&rules, &created[parent], &mut steps)? else {
                    return Ok(None);
                };
                for child in children {
                    match members.get(&canonical(&child)) {
                        // A member seen before is subsumed by its first copy.
                        Some(index) if order.contains(index) => {}
                        Some(&index) => {
                            order.push(index);
                            next.push(created.len());
                            created.push(child);
                        }
                        // Maude folds a variant that an earlier one subsumes.
                        // It keeps any other, and the replay does not follow
                        // variants outside the family.
                        None if created.iter().any(|kept| subsumes(kept, &child)) => {}
                        None => return Ok(None),
                    }
                }
            }
            frontier = next;
        }
        Ok((order.len() == family.len()).then_some(order))
    }

    /// Every one-step narrowing of `variant`, in Maude's order.
    fn narrowings(
        &self,
        rules: &[RRule<LNTerm>],
        variant: &Variant,
        steps: &mut usize,
    ) -> Result<Option<Vec<Variant>>, Error> {
        let mut interesting = Vec::new();
        let mut highest = 0;
        for t in &variant.values {
            t.for_each_free(&mut |v| {
                if !interesting.contains(v) {
                    interesting.push(*v);
                }
            });
        }
        for t in variant.terms() {
            t.for_each_free(&mut |v| highest = highest.max(v.idx));
        }
        // The unifiers of all positions, filtered as `UnifierFilter` does: by
        // subsumption on the variables of the variant term.
        struct Step {
            bindings: Vec<LNTerm>,
            unifier: Subst<crate::lterm::Name, LVar>,
            observation: usize,
            path: Vec<usize>,
            rhs: LNTerm,
        }
        let mut kept: Vec<Step> = Vec::new();
        for (observation, path) in positions(&variant.values) {
            let subject = at(&variant.values[observation], &path);
            let Term::App(head, _) = subject else {
                continue;
            };
            for rule in rules {
                if !matches!(&rule.lhs, Term::App(f, _) if f == head) {
                    continue;
                }
                *steps += 1;
                if *steps > STEP_LIMIT || !plain(&rule.lhs) || !plain(&rule.rhs) {
                    return Ok(None);
                }
                tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                let Some(shift) = highest.checked_add(1) else {
                    return Ok(None);
                };
                let mut overflow = false;
                let mut apart = |v: LVar| LVar {
                    idx: v.idx.checked_add(shift).unwrap_or_else(|| {
                        overflow = true;
                        v.idx
                    }),
                    ..v
                };
                let lhs = rule.lhs.clone().map_free(&mut apart);
                let rhs = rule.rhs.clone().map_free(&mut apart);
                if overflow {
                    return Ok(None);
                }
                let unifier = match unify_lterm_no_ac(
                    &sort_of_name,
                    vec![Equal::new(lhs, subject.clone())],
                ) {
                    Ok(unifier) => unifier,
                    Err(UnifyError::NoUnifier) => continue,
                    Err(UnifyError::NeedsAC) => return Ok(None),
                };
                let bindings: Vec<_> = interesting
                    .iter()
                    .map(|v| apply_vterm(&unifier, Term::Lit(Lit::Var(*v))))
                    .collect();
                let mut normal = true;
                for t in &bindings {
                    match self.normal(t)? {
                        Some(n) => normal &= n,
                        None => return Ok(None),
                    }
                }
                if !normal || kept.iter().any(|k| instance(&k.bindings, &bindings)) {
                    continue;
                }
                kept.retain(|k| !instance(&bindings, &k.bindings));
                kept.push(Step {
                    bindings,
                    unifier,
                    observation,
                    path: path.clone(),
                    rhs,
                });
            }
        }
        let mut children = Vec::with_capacity(kept.len());
        'step: for step in kept {
            let apply = |t: &LNTerm| apply_vterm(&step.unifier, t.clone());
            let images: Vec<_> = variant.images.iter().map(apply).collect();
            for t in &images {
                match self.normal(t)? {
                    Some(true) => {}
                    Some(false) => continue 'step,
                    None => return Ok(None),
                }
            }
            let mut values = Vec::with_capacity(variant.values.len());
            for (i, value) in variant.values.iter().enumerate() {
                let narrowed = if i == step.observation {
                    apply(&replace(value, &step.path, &step.rhs))
                } else {
                    apply(value)
                };
                let Some(value) = self.reduce_native(&narrowed)? else {
                    return Ok(None);
                };
                if !plain(&value) {
                    return Ok(None);
                }
                values.push(value);
            }
            children.push(Variant { images, values });
        }
        Ok(Some(children))
    }

    fn normal(&self, t: &LNTerm) -> Result<Option<bool>, Error> {
        Ok(self.reduce_native(t)?.map(|n| n == *t))
    }
}

/// No AC or C operator: unification and matching are syntactic and the
/// stored argument order is the order Maude traverses.
fn plain(t: &LNTerm) -> bool {
    t.all_fun_syms(|f| matches!(f, FunSym::NoEq(_)))
}

/// The positions of `list(cons(t1, cons(t2, …)))` below the cons cells, in
/// the breadth-first order of Maude's `PositionState`: the observation and
/// the path into it. A cons cell queues its element before the next cell.
fn positions(values: &[LNTerm]) -> Vec<(usize, Vec<usize>)> {
    enum Node {
        Cell(usize),
        Term(usize, Vec<usize>),
    }
    let mut out = Vec::new();
    let mut queue = VecDeque::new();
    if !values.is_empty() {
        queue.push_back(Node::Cell(0));
    }
    while let Some(node) = queue.pop_front() {
        match node {
            Node::Cell(i) => {
                queue.push_back(Node::Term(i, Vec::new()));
                if i + 1 < values.len() {
                    queue.push_back(Node::Cell(i + 1));
                }
            }
            Node::Term(i, path) => {
                if let Term::App(_, args) = at(&values[i], &path) {
                    for child in 0..args.len() {
                        let mut below = path.clone();
                        below.push(child);
                        queue.push_back(Node::Term(i, below));
                    }
                }
                out.push((i, path));
            }
        }
    }
    out
}

fn at<'a>(t: &'a LNTerm, path: &[usize]) -> &'a LNTerm {
    path.iter().fold(t, |t, &i| match t {
        Term::App(_, args) => &args[i],
        Term::Lit(_) => t,
    })
}

fn replace(t: &LNTerm, path: &[usize], by: &LNTerm) -> LNTerm {
    match (path, t) {
        ([i, rest @ ..], Term::App(f, args)) => {
            let mut args = args.to_vec();
            args[*i] = replace(&args[*i], rest, by);
            f_app(*f, args)
        }
        _ => by.clone(),
    }
}

/// The variant with its variables renamed in order of first occurrence.
fn canonical(variant: &Variant) -> Vec<LNTerm> {
    let mut names: FxHashMap<LVar, LVar> = FxHashMap::default();
    variant
        .terms()
        .map(|t| {
            t.clone().map_free(&mut |v| {
                let next = names.len() as u64;
                *names.entry(v).or_insert(LVar::new("v", v.sort, next))
            })
        })
        .collect()
}

/// Whether `general` has `variant` as an instance, images and values alike.
fn subsumes(general: &Variant, variant: &Variant) -> bool {
    let mut bound = FxHashMap::default();
    general
        .terms()
        .zip(variant.terms())
        .all(|(pattern, subject)| matches(pattern, subject, &mut bound))
}

/// Whether `specific` is an instance of `general`, coordinate by coordinate.
fn instance(general: &[LNTerm], specific: &[LNTerm]) -> bool {
    let mut bound = FxHashMap::default();
    general
        .iter()
        .zip(specific)
        .all(|(pattern, subject)| matches(pattern, subject, &mut bound))
}

/// Syntactic matching. The variables of the subject are rigid, also when
/// they are spelled like variables of the pattern.
fn matches<'a>(
    pattern: &LNTerm,
    subject: &'a LNTerm,
    bound: &mut FxHashMap<LVar, &'a LNTerm>,
) -> bool {
    match (pattern, subject) {
        (Term::Lit(Lit::Var(v)), _) => match bound.get(v) {
            Some(image) => *image == subject,
            None => {
                let sort = match subject {
                    Term::Lit(Lit::Var(w)) => w.sort,
                    Term::Lit(Lit::Con(c)) => sort_of_name(c),
                    Term::App(..) => LSort::Msg,
                };
                subsort(sort, v.sort) && bound.insert(*v, subject).is_none()
            }
        },
        (Term::Lit(Lit::Con(a)), Term::Lit(Lit::Con(b))) => a == b,
        (Term::App(f, xs), Term::App(g, ys)) => {
            f == g
                && xs.len() == ys.len()
                && xs.iter().zip(ys.iter()).all(|(x, y)| matches(x, y, bound))
        }
        _ => false,
    }
}

/// Rename the witnesses of `member` to `x` with the indices the Maude reply
/// decoder gives them: counted from one in order of first occurrence, and
/// above every query variable that is itself called `x`.
fn number_witnesses(keys: &[LVar], member: Vec<(LVar, LNTerm)>) -> Vec<(LVar, LNTerm)> {
    let mut next = keys
        .iter()
        .filter(|v| v.name == "x")
        .map(|v| v.idx)
        .max()
        .map_or(1, |highest| highest.saturating_add(1).max(1));
    let mut names: FxHashMap<LVar, LVar> = FxHashMap::default();
    // An index space this full cannot be renumbered without a collision.
    let witnesses = {
        let mut seen = Vec::new();
        for (_, image) in &member {
            image.for_each_free(&mut |w| {
                if !seen.contains(w) {
                    seen.push(*w);
                }
            });
        }
        seen.len() as u64
    };
    if next.checked_add(witnesses).is_none() {
        return member;
    }
    member
        .into_iter()
        .map(|(key, image)| {
            let image = image.map_free(&mut |w| {
                *names.entry(w).or_insert_with(|| {
                    let named = LVar::new("x", w.sort, next);
                    next += 1;
                    named
                })
            });
            (key, image)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{fst, pair, sdec, senc, snd};

    fn var(name: &'static str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }

    fn v(lv: LVar) -> LNTerm {
        Term::Lit(Lit::Var(lv))
    }

    #[test]
    fn positions_follow_the_breadth_first_order_of_the_cons_list() {
        let [a, b, c] = [0, 1, 2].map(|i| v(var("a", i)));
        let values = [fst(pair(a.clone(), b.clone())), snd(c.clone())];
        // The first observation, then its child together with the second
        // observation, then one level further down in both.
        assert_eq!(
            positions(&values),
            vec![
                (0, vec![]),
                (0, vec![0]),
                (1, vec![]),
                (0, vec![0, 0]),
                (0, vec![0, 1]),
                (1, vec![0]),
            ]
        );
    }

    #[test]
    fn witnesses_are_numbered_by_first_occurrence_above_query_variables_called_x() {
        let k = var("k", 1);
        let c = var("c", 2);
        let w = |i| v(var("x", i));
        let member = vec![(k, w(9)), (c, senc(w(4), w(9)))];
        assert_eq!(
            number_witnesses(&[k, c], member.clone()),
            vec![(k, w(1)), (c, senc(w(2), w(1)))]
        );
        // A query variable called `x` pushes the witnesses above itself.
        let x3 = var("x", 3);
        assert_eq!(
            number_witnesses(&[k, c, x3], member),
            vec![(k, w(4)), (c, senc(w(5), w(4)))]
        );
    }

    #[test]
    fn matching_keeps_subject_variables_rigid_and_respects_sorts() {
        let a = var("a", 0);
        let fresh = LVar::new("n", LSort::Fresh, 0);
        let [same, mixed, message, nonce] =
            [sdec(v(a), v(a)), sdec(v(a), v(fresh)), v(a), v(fresh)];
        assert!(matches(&same, &same, &mut FxHashMap::default()));
        // One pattern variable cannot stand for two different subterms.
        assert!(!matches(&same, &mixed, &mut FxHashMap::default()));
        // A fresh-sorted pattern variable does not match a message.
        assert!(!matches(&nonce, &message, &mut FxHashMap::default()));
        assert!(matches(&message, &nonce, &mut FxHashMap::default()));
    }
}
