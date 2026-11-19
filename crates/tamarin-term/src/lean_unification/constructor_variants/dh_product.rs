//! Concrete normalization of exponent products using the active DH presentation.
//! A conflict among the signed factors selects a concrete subproduct and an
//! assignment. Each step must replay against the handle's actual inventory.
use super::{InputDomain, RuleTable};
use crate::builtin::{dh_rules, one_const};
use crate::function_symbols::{dh_neutral_sym, exp_sym, inv_sym, one_sym, AcSym, FunSym};
use crate::lean_unification::{open_match, Error, Outcome};
use crate::lterm::{frees, LNTerm, LVar, Name};
use crate::maude_proc::unskolemize;
use crate::rewriting::RRule;
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app, f_app_ac, map_lits, Term};
use crate::vterm::Lit;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

pub(super) fn exact_rules(rules: &BTreeSet<RRule<LNTerm>>) -> bool {
    let heads = [
        FunSym::Ac(AcSym::Mult),
        FunSym::NoEq(inv_sym()),
        FunSym::NoEq(one_sym()),
        FunSym::NoEq(exp_sym()),
        FunSym::NoEq(dh_neutral_sym()),
    ];
    rules
        .iter()
        .filter(|rule| matches!(&rule.lhs,Term::App(f,_) if heads.contains(f)))
        .eq(dh_rules().iter())
}

fn is_group_operation(t: &LNTerm) -> bool {
    matches!(t, Term::App(FunSym::Ac(AcSym::Mult), _))
        || matches!(t, Term::App(FunSym::NoEq(f), _) if *f == inv_sym() || *f == one_sym())
}

enum Next {
    Normal,
    Rewrite(LNTerm),
    Defer,
}

struct Reducer<'a> {
    table: &'a RuleTable,
    reverse: &'a BTreeMap<Name, LVar>,
    work: usize,
}

/// The immutable program consists of the same mult/inv equations validated
/// against this handle. It contains no query variables or previous answers.
fn program() -> &'static [RRule<LNTerm>] {
    static PROGRAM: OnceLock<Vec<RRule<LNTerm>>> = OnceLock::new();
    PROGRAM.get_or_init(|| {
        dh_rules()
            .into_iter()
            .filter(|r| is_group_operation(&r.lhs))
            .collect()
    })
}

fn product_conflict(factors: &[LNTerm]) -> Option<(usize, usize, Vec<LNTerm>)> {
    if let Ok(i) = factors.binary_search(&one_const()) {
        let j = usize::from(i == 0);
        return Some((i, j, vec![factors[j].clone()]));
    }
    let mut inverses = factors.iter().enumerate().filter_map(|(i, t)| match t {
        Term::App(FunSym::NoEq(f), args) if *f == inv_sym() => Some((i, &args[0])),
        _ => None,
    });
    let (i, negative) = inverses.next()?;
    if let Some((j, other)) = inverses.next() {
        return Some((i, j, vec![negative.clone(), other.clone()]));
    }
    let Term::App(FunSym::Ac(AcSym::Mult), neg) = negative else {
        return factors
            .binary_search(negative)
            .ok()
            .map(|j| (i, j, vec![negative.clone()]));
    };
    for (k, n) in neg.iter().enumerate() {
        if let Ok(j) = factors.binary_search(n) {
            let mut rest = neg.to_vec();
            rest.remove(k);
            return Some((i, j, vec![f_app_ac(AcSym::Mult, rest), n.clone()]));
        }
    }
    None
}

impl Reducer<'_> {
    fn at_root(&mut self, t: &LNTerm) -> Result<Next, Error> {
        let Term::App(head, _) = t else {
            return Ok(Next::Normal);
        };
        for rule in program() {
            if !matches!(&rule.lhs, Term::App(f, _) if f == head) {
                continue;
            }
            let Outcome::Complete(matches) = open_match::root(&rule.lhs, t, &mut self.work)? else {
                return Ok(Next::Defer);
            };
            if let Some(bindings) = matches.into_iter().next() {
                let subst = Subst::from_list(bindings);
                return self.replay(rule, t, &subst).map(Next::Rewrite);
            }
        }
        Ok(Next::Normal)
    }

    /// Check both sides before and after restoring the caller's rigid names.
    fn replay(
        &self,
        rule: &RRule<LNTerm>,
        t: &LNTerm,
        subst: &Subst<Name, LVar>,
    ) -> Result<LNTerm, Error> {
        if apply_vterm(subst, rule.lhs.clone()) != *t {
            return Err(Error::InvalidStatus(255));
        }
        let value = apply_vterm(subst, rule.rhs.clone());
        if !self.reverse.is_empty() {
            let thawed = Subst::from_list(
                subst
                    .iter()
                    .map(|(v, u)| (*v, unskolemize(u, self.reverse))),
            );
            if apply_vterm(&thawed, rule.lhs.clone()) != unskolemize(t, self.reverse)
                || apply_vterm(&thawed, rule.rhs.clone()) != unskolemize(&value, self.reverse)
            {
                return Err(Error::InvalidStatus(255));
            }
        }
        Ok(value)
    }

    /// A dirty product has a two-factor redex. Construct its simultaneous
    /// assignment, then use only an actual matching rule from the inventory.
    /// This avoids enumerating arbitrary partitions of a large negative bag.
    fn conflict_step(&mut self, factors: &[LNTerm]) -> Result<Option<Next>, Error> {
        let Some((a, b, parts)) = product_conflict(factors) else {
            return Ok(None);
        };
        let piece = f_app_ac(AcSym::Mult, vec![factors[a].clone(), factors[b].clone()]);
        for rule in program() {
            if !matches!(rule.lhs, Term::App(FunSym::Ac(AcSym::Mult), _)) {
                continue;
            }
            let keys = frees(&rule.lhs);
            if keys.len() != parts.len() {
                continue;
            }
            let subst = Subst::from_list(keys.into_iter().zip(parts.iter().cloned()));
            if !crate::lean_unification::residual::charge_expansion(
                &mut self.work,
                [&rule.lhs, &rule.rhs],
                Some(&subst),
            )? {
                return Ok(Some(Next::Defer));
            }
            if apply_vterm(&subst, rule.lhs.clone()) != piece {
                continue;
            }
            let mut rest: Vec<_> = factors
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != a && *i != b)
                .map(|(_, t)| t.clone())
                .collect();
            rest.push(self.replay(rule, &piece, &subst)?);
            return Ok(Some(Next::Rewrite(f_app_ac(AcSym::Mult, rest))));
        }
        Ok(None)
    }

    fn step(&mut self, t: &LNTerm) -> Result<Next, Error> {
        if self.table.dh_group_root_normal(t) == Some(true) {
            return Ok(Next::Normal);
        }
        let Term::App(FunSym::Ac(AcSym::Mult), factors) = t else {
            return self.at_root(t);
        };
        // Every normality conflict exposed by the signed inventory has a
        // witnessing pair. A failed replay leaves reduction to the generic search.
        Ok(self.conflict_step(factors)?.unwrap_or(Next::Defer))
    }

    fn normalize(&mut self, mut t: LNTerm, fuel: usize) -> Result<Option<LNTerm>, Error> {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        if self.table.irreducible(&t)? {
            return Ok(Some(t));
        }
        // A free constructor absent from the active rule heads is normal as
        // soon as its children are normal. Keep replay and the work budget
        // shared across the entire term.
        if fuel == 0 || self.work == 0 || !self.table.dh_product_context(&t) {
            return Ok(None);
        }
        self.work -= 1;
        if let Term::App(f, xs) = &t {
            let mut ys = Vec::with_capacity(xs.len());
            for x in xs.iter() {
                let Some(y) = self.normalize(x.clone(), fuel - 1)? else {
                    return Ok(None);
                };
                ys.push(y);
            }
            t = f_app(*f, ys);
        }
        match self.step(&t)? {
            Next::Normal => Ok(Some(t)),
            Next::Defer => Ok(None),
            Next::Rewrite(value) => self.normalize(value, fuel - 1),
        }
    }
}

impl RuleTable {
    /// For a sorted substitution with normal images, these expressions have
    /// a defined signed count for every opaque factor class. The inventory's
    /// signed-count invariant makes all reachable normal values agree.
    pub(super) fn dh_signed_expression(&self, t: &LNTerm) -> Result<bool, Error> {
        if is_group_operation(t) {
            let Term::App(_, args) = t else {
                unreachable!()
            };
            for arg in args.iter() {
                if !self.dh_signed_expression(arg)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        self.stably_normal_native(t)
    }

    /// Root normality for a sorted canonical term. Under the exact signed
    /// product inventory every proper-subbag redex violates the same
    /// no-unit, single-inverse, disjoint-occurrence conditions as a root redex.
    pub(super) fn dh_group_root_normal(&self, t: &LNTerm) -> Option<bool> {
        if !self.builtin_dh {
            return None;
        }
        let inverse =
            |term: &LNTerm| matches!(term, Term::App(FunSym::NoEq(f), _) if *f == inv_sym());
        match t {
            Term::App(FunSym::NoEq(f), _) if *f == one_sym() => Some(true),
            Term::App(FunSym::NoEq(f), args) if *f == inv_sym() => {
                let [arg] = args.as_ref() else { return None };
                Some(
                    arg != &one_const()
                        && !inverse(arg)
                        && !matches!(arg, Term::App(FunSym::Ac(AcSym::Mult), xs)
                        if xs.iter().any(inverse)),
                )
            }
            Term::App(FunSym::Ac(AcSym::Mult), factors) => {
                if factors.binary_search(&one_const()).is_ok() {
                    return Some(false);
                }
                let mut inverses = factors.iter().filter(|t| inverse(t));
                let Some(Term::App(_, args)) = inverses.next() else {
                    return Some(true);
                };
                if inverses.next().is_some() {
                    return Some(false);
                }
                let [negative] = args.as_ref() else {
                    return None;
                };
                let negative = match negative {
                    Term::App(FunSym::Ac(AcSym::Mult), xs) => xs.as_ref(),
                    atom => std::slice::from_ref(atom),
                };
                Some(negative.iter().all(|x| factors.binary_search(x).is_err()))
            }
            _ => None,
        }
    }

    pub(super) fn dh_product_context(&self, t: &LNTerm) -> bool {
        is_group_operation(t)
            || matches!(t, Term::App(f @ FunSym::NoEq(_), _)
                if self.symbols.id(*f).is_some_and(|id| self.roots.binary_search(&id).is_err()))
    }

    pub(super) fn dh_product_normal(&self, t: &LNTerm) -> Result<Option<LNTerm>, Error> {
        if !self.builtin_dh
            || self
                .collect(t, &mut Vec::new(), InputDomain::Sorted)
                .is_none()
        {
            return Ok(None);
        }
        if t == &one_const() || self.irreducible(t)? {
            return Ok(Some(t.clone()));
        }
        if !self.dh_product_context(t) {
            return Ok(None);
        }
        // Ordinary reduction keeps every query variable rigid. Whole-query
        // allocation avoids both user constants and collisions between sorts.
        // DH rules contain no literal names, so this renaming fixes the program.
        let vars = frees(t).into_iter().collect();
        let (forward, reverse) = crate::maude_proc::build_skolem_maps(&vars, [t])
            .map_err(|_| Error::FreshVariableOverflow)?;
        let freeze = |u: &LNTerm| {
            map_lits(u, &mut |lit| match lit {
                Lit::Var(v) => Lit::Con(forward[v]),
                name => *name,
            })
        };
        let mut reducer = Reducer {
            table: self,
            reverse: &reverse,
            work: 100_000,
        };
        let Some(normal) = reducer.normalize(freeze(t), 128)? else {
            return Ok(None);
        };
        let answer = unskolemize(&normal, &reverse);
        if freeze(&answer) != normal {
            return Err(Error::InvalidStatus(255));
        }
        Ok(Some(answer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{inv, mult};
    use crate::lterm::{pub_term, LSort};
    use crate::maude_proc::MaudeHandle;
    use crate::maude_sig::dh_maude_sig;

    #[test]
    fn dh_product_normal_preserves_name_collisions_and_checks_live_rules() {
        use crate::subterm_rule::{CtxtStRule, StRhs};

        let mut sig = dh_maude_sig();
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
        // The first frozen image of x would have exactly this identity.
        let c = pub_term("__skMSG__0_x_0_M");
        let table = RuleTable::new(&sig).unwrap();
        let input = mult(x.clone(), inv(c.clone()));
        assert_eq!(
            table.dh_product_normal(&input).unwrap(),
            Some(input.clone())
        );
        let input = mult(input, c);
        assert_eq!(table.dh_product_normal(&input).unwrap(), Some(x.clone()));

        sig.st_rules.insert(CtxtStRule::new(
            inv(x.clone()),
            StRhs {
                positions: vec![vec![0]],
                term: x,
            },
        ));
        let changed = RuleTable::new(&sig).unwrap();
        assert!(!changed.builtin_dh);
        assert_eq!(changed.dh_group_root_normal(&input), None);
        assert_eq!(changed.dh_product_normal(&input).unwrap(), None);
    }

    #[test]
    fn signed_products_only_reduce_through_constructors_absent_from_rule_heads() {
        use crate::builtin::hash;
        use crate::maude_sig::hash_maude_sig;
        use crate::subterm_rule::{CtxtStRule, StRhs};

        let mut sig = dh_maude_sig().merge(hash_maude_sig());
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
        let input = hash(mult(x.clone(), inv(x.clone())));
        let table = RuleTable::new(&sig).unwrap();
        assert_eq!(table.reduce(&input).unwrap(), Some(hash(one_const())));

        sig.st_rules.insert(CtxtStRule::new(
            hash(x.clone()),
            StRhs {
                positions: vec![vec![0]],
                term: x,
            },
        ));
        let table = RuleTable::new(&sig).unwrap();
        assert!(table.builtin_dh);
        assert_eq!(table.dh_product_normal(&input).unwrap(), None);
    }

    #[test]
    fn dh_guard_checks_occurrences_and_the_reducer_checks_children_and_arity() {
        let table = RuleTable::new(&dh_maude_sig()).unwrap();
        let a = pub_term("a");
        let b = pub_term("b");
        let c = pub_term("c");
        let one = one_const();
        let negative = inv(mult(a.clone(), b.clone()));
        let dirty = inv(mult(a.clone(), one.clone()));
        for (term, clear) in [
            (one.clone(), true),
            (inv(a.clone()), true),
            (inv(one.clone()), false),
            (inv(inv(a.clone())), false),
            (dirty.clone(), true),
            (inv(mult(c.clone(), mult(b.clone(), inv(a.clone())))), false),
            (mult(a.clone(), a.clone()), true),
            (mult(a.clone(), one.clone()), false),
            (mult(inv(a.clone()), inv(a.clone())), false),
            (mult(c.clone(), negative.clone()), true),
            (mult(c.clone(), mult(b.clone(), negative)), false),
        ] {
            assert_eq!(table.dh_group_root_normal(&term), Some(clear), "{term}");
        }
        assert_eq!(
            table.dh_product_normal(&dirty).unwrap(),
            Some(inv(a.clone()))
        );

        for (head, args) in [
            (FunSym::NoEq(one_sym()), vec![a.clone()]),
            (FunSym::NoEq(inv_sym()), vec![]),
            (FunSym::NoEq(inv_sym()), vec![a.clone(), b]),
            (FunSym::Ac(AcSym::Mult), vec![]),
            (FunSym::Ac(AcSym::Mult), vec![a]),
        ] {
            let malformed = Term::App(head, args.into());
            assert_eq!(table.dh_product_normal(&malformed).unwrap(), None);
        }
    }

    #[test]
    fn dh_product_normal_agrees_with_maude_on_signed_words() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let sig = dh_maude_sig();
        let table = RuleTable::new(&sig).unwrap();
        let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        let a = Term::Lit(Lit::Var(LVar::new("a", LSort::Msg, 0)));
        let b = Term::Lit(Lit::Var(LVar::new("a", LSort::Fresh, 0)));
        let c = pub_term("c");
        let alphabet = [a.clone(), b.clone(), inv(a.clone()), inv(b.clone())];
        let mut inputs = BTreeSet::new();
        for p in &alphabet {
            for q in &alphabet {
                for r in &alphabet {
                    let pq = mult(p.clone(), q.clone());
                    inputs.insert(mult(pq.clone(), r.clone()));
                    inputs.insert(mult(inv(pq.clone()), r.clone()));
                    inputs.insert(inv(mult(pq, inv(r.clone()))));
                }
            }
        }
        inputs.insert(mult(
            c.clone(),
            mult(
                mult(a.clone(), inv(b.clone())),
                inv(mult(a.clone(), b.clone())),
            ),
        ));
        // Two negative bags, a unit, and overlapping repeated factors each
        // select an actual proper-subproduct step even above the matcher limit.
        let wide = f_app_ac(AcSym::Mult, vec![a.clone(); 15]);
        inputs.insert(f_app_ac(
            AcSym::Mult,
            vec![
                one_const(),
                a.clone(),
                b.clone(),
                wide.clone(),
                inv(mult(wide.clone(), b.clone())),
                inv(mult(a.clone(), c)),
            ],
        ));
        inputs.insert(mult(one_const(), inv(inv(mult(a, b)))));
        inputs.insert(inv(one_const()));
        for input in inputs {
            let expected = maude.reduce(&input).unwrap();
            // With normal arguments, any change Maude makes must be at the
            // root or an AC subbag. Comparing both directions exercises the
            // shortcut independently of the native reducer using it.
            if let Term::App(head, args) = &input {
                let ready = f_app(
                    *head,
                    args.iter().map(|arg| maude.reduce(arg).unwrap()).collect(),
                );
                assert_eq!(
                    table.dh_group_root_normal(&ready),
                    Some(ready == expected),
                    "root normality of {ready:?}"
                );
            }
            let actual = table.dh_product_normal(&input).unwrap();
            assert_eq!(actual, Some(expected), "input {input:?}");
        }
    }
}
