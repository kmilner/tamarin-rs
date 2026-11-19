//! Lift a complete scalar-product family through the active point action and pairing.
use super::{JoinSearch, Row, RuleTable};
use crate::builtin::{emap, exp, mult, one_const, pmult};
use crate::function_symbols::{pmult_sym, CSym, FunSym};
use crate::lean_unification::Error;
use crate::lterm::{LNTerm, LSort, LVar};
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashSet;
use std::borrow::Cow;
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
enum Operation {
    Action,
    Pairing,
}

impl Operation {
    fn from_head(head: FunSym) -> Option<Self> {
        match head {
            FunSym::NoEq(f) if f == pmult_sym() => Some(Self::Action),
            FunSym::C(CSym::EMap) => Some(Self::Pairing),
            _ => None,
        }
    }

    fn flat(self, scalar: &LNTerm, p: &LNTerm, q: &LNTerm) -> Vec<Row> {
        let row = |l, r, n| Row {
            images: vec![l, r],
            values: vec![n],
        };
        match self {
            Self::Action => vec![
                row(scalar.clone(), p.clone(), pmult(scalar.clone(), p.clone())),
                row(one_const(), p.clone(), p.clone()),
            ],
            Self::Pairing => {
                let base = emap(p.clone(), q.clone());
                let power = exp(base.clone(), scalar.clone());
                vec![
                    row(p.clone(), q.clone(), base),
                    row(pmult(scalar.clone(), p.clone()), q.clone(), power.clone()),
                    row(p.clone(), pmult(scalar.clone(), q.clone()), power),
                ]
            }
        }
    }

    fn value(self, base: LNTerm, scalar: &LNTerm) -> LNTerm {
        if scalar == &one_const() {
            return base;
        }
        match self {
            Self::Action => pmult(scalar.clone(), base),
            Self::Pairing => exp(base, scalar.clone()),
        }
    }

    fn lifted(self, l: &LNTerm, r: &LNTerm, product: &LNTerm, p: &LNTerm, q: &LNTerm) -> Row {
        let (left, right, value) = match self {
            Self::Action => {
                let point = pmult(r.clone(), p.clone());
                let value = self.value(p.clone(), product);
                (l.clone(), point, value)
            }
            Self::Pairing => {
                let base = emap(p.clone(), q.clone());
                let value = self.value(base, product);
                (
                    pmult(l.clone(), p.clone()),
                    pmult(r.clone(), q.clone()),
                    value,
                )
            }
        };
        Row {
            images: vec![left, right],
            values: vec![value],
        }
    }
}

fn var(v: LVar) -> LNTerm {
    Term::Lit(Lit::Var(v))
}

impl RuleTable {
    /// The exact bilinear root tests in Inventory.point_normal_iff and
    /// Inventory.map_normal_iff. The caller checks each child separately.
    pub(super) fn bp_root_normal(&self, t: &LNTerm) -> Option<bool> {
        if !self.builtin_bp {
            return None;
        }
        let Term::App(head, args) = t else {
            return None;
        };
        let op = Operation::from_head(*head)?;
        let [l, r] = args.as_ref() else { return None };
        let point = |a: &LNTerm| matches!(a, Term::App(FunSym::NoEq(f), _) if *f == pmult_sym());
        Some(
            !point(r)
                && match op {
                    Operation::Action => l != &one_const(),
                    Operation::Pairing => !point(l),
                },
        )
    }

    fn rigid_signed_operand(&self, t: &LNTerm) -> Result<bool, Error> {
        if super::super::dh_product::is_group_operation(t)
            && let Term::App(_, xs) = t
        {
            for x in xs.iter() {
                if !self.rigid_signed_operand(x)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        Ok(self.join_normal(t)? == Some(true))
    }

    pub(in crate::lean_unification::constructor_variants) fn signed_operand(
        &self,
        t: &LNTerm,
        stable: bool,
    ) -> Result<bool, Error> {
        if stable {
            self.dh_signed_expression(t)
        } else {
            self.rigid_signed_operand(t)
        }
    }

    /// Signed scalar actions on a signed operand. Its opaque leaves are
    /// stable for variants and normal in the concrete reduction query.
    pub(in crate::lean_unification::constructor_variants) fn bp_point_spine(
        &self,
        mut t: &LNTerm,
        stable: bool,
    ) -> Result<bool, Error> {
        if !self.builtin_bp {
            return Ok(false);
        }
        while let Term::App(FunSym::NoEq(f), xs) = t {
            if *f != pmult_sym() {
                break;
            }
            let [a, p] = xs.as_ref() else {
                return Ok(false);
            };
            if !self.signed_operand(a, stable)? {
                return Ok(false);
            }
            t = p;
        }
        self.signed_operand(t, stable)
    }

    pub(super) fn admits_point_inputs(
        &self,
        head: FunSym,
        args: &[LNTerm],
        stable: bool,
    ) -> Result<bool, Error> {
        let Some(op) = Operation::from_head(head) else {
            return Ok(false);
        };
        let [l, r] = args else { return Ok(false) };
        if !self.builtin_bp {
            return Ok(false);
        }
        let left = match op {
            Operation::Action => self.signed_operand(l, stable)?,
            Operation::Pairing => self.bp_point_spine(l, stable)?,
        };
        Ok(left && self.bp_point_spine(r, stable)?)
    }

    fn point_operand<'a>(&self, t: &'a LNTerm) -> Result<Option<Cow<'a, LNTerm>>, Error> {
        if self.join_normal(t)? == Some(true) {
            return Ok(Some(Cow::Borrowed(t)));
        }
        if matches!(t, Term::App(FunSym::NoEq(f), _) if *f == pmult_sym()) {
            return Ok(self.scalar_action_normal(t)?.map(Cow::Owned));
        }
        Ok(self.dh_product_normal(t)?.map(Cow::Owned))
    }

    // A normal point exposes at most one nonunit scalar. Extract from either
    // side of the commutative map before normalizing the common scalar product.
    pub(in crate::lean_unification::constructor_variants) fn scalar_action_normal(
        &self,
        t: &LNTerm,
    ) -> Result<Option<LNTerm>, Error> {
        let Term::App(head, args) = t else {
            return Ok(None);
        };
        let Some(op) = Operation::from_head(*head) else {
            return Ok(None);
        };
        let [l, r] = args.as_ref() else {
            return Ok(None);
        };
        if !self.admits_point_inputs(*head, args, false)? {
            return Ok(None);
        }
        let Some(l) = self.point_operand(l)? else {
            return Ok(None);
        };
        let Some(r) = self.point_operand(r)? else {
            return Ok(None);
        };
        fn expose(t: &LNTerm) -> (Option<&LNTerm>, &LNTerm) {
            if let Term::App(FunSym::NoEq(head), args) = t
                && *head == pmult_sym()
                && let [k, p] = args.as_ref()
            {
                return (Some(k), p);
            }
            (None, t)
        }
        let (right, q) = expose(&r);
        let (left, base) = match op {
            Operation::Action => (Some(l.as_ref()), q.clone()),
            Operation::Pairing => {
                let (k, p) = expose(&l);
                (k, emap(p.clone(), q.clone()))
            }
        };
        let scalar = match (left, right) {
            (Some(a), Some(b)) => {
                let Some(product) = self.reduce_native(&mult(a.clone(), b.clone()))? else {
                    return Ok(None);
                };
                product
            }
            (Some(a), None) | (None, Some(a)) => a.clone(),
            (None, None) => return Ok(Some(base)),
        };
        Ok(Some(op.value(base, &scalar)))
    }

    pub(super) fn scalar_action_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        let Term::App(head, args) = app else {
            return Ok(None);
        };
        let Some(op) = Operation::from_head(*head) else {
            return Ok(None);
        };
        let [Term::Lit(Lit::Var(l)), Term::Lit(Lit::Var(r))] = args.as_ref() else {
            return Ok(None);
        };
        if l == r || l.sort != LSort::Msg || r.sort != LSort::Msg || !self.builtin_bp {
            return Ok(None);
        }
        let formals = [*l, *r];
        let product = mult(var(*l), var(*r));
        let Some(scalars) = self.single_rows(&formals, original, &product, search)? else {
            return Ok(None);
        };

        // Open scalar rows into the ordinary "x" namespace before adding the
        // two independent point witnesses. All three columns share that scope.
        let p = var(LVar::new("point", LSort::Msg, 0));
        let q = var(LVar::new("point", LSort::Msg, 1));
        let scalar = var(LVar::new("scalar", LSort::Msg, 0));
        let unit = one_const();
        let mut candidates = op
            .flat(&scalar, &p, &q)
            .into_iter()
            .collect::<BTreeSet<_>>();
        for scalar_row in scalars {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let scalar_row = scalar_row.rename(original);
            let ([left, right], [value]) =
                (scalar_row.images.as_slice(), scalar_row.values.as_slice())
            else {
                return Err(Error::InvalidStatus(255));
            };
            if left == &unit || right == &unit {
                continue;
            }
            candidates.insert(op.lifted(left, right, value, &p, &q));
            // A normal instance of a bare result witness may be one. Fold the
            // outer root in that case and specialize both scalar inputs at
            // once. A redex in a specialized image persists under substitution.
            if let Term::Lit(Lit::Var(v)) = value
                && v.sort == LSort::Msg
            {
                let specialize = Subst::from_list([(*v, unit.clone())]);
                let a = apply_vterm(&specialize, left.clone());
                let b = apply_vterm(&specialize, right.clone());
                if a == unit || b == unit {
                    continue;
                }
                match (self.join_normal(&a)?, self.join_normal(&b)?) {
                    (Some(false), _) | (_, Some(false)) => {}
                    (Some(true), Some(true)) => {
                        candidates.insert(op.lifted(&a, &b, &unit, &p, &q));
                    }
                    _ => return Ok(None),
                }
            }
        }
        let Some(mut rows) = self.prune_specializations(candidates, &mut search.matching)? else {
            return Ok(None);
        };
        for row in &mut rows {
            *row = row.rename(original);
            let images = std::mem::take(&mut row.images);
            let inputs = Subst::from_list(formals.into_iter().zip(images));
            row.images = keys
                .iter()
                .map(|&v| inputs.image_of(&v).cloned().unwrap_or_else(|| var(v)))
                .collect();
        }
        Ok(Some(rows))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{inv, msg_var};
    use crate::maude_sig::bp_maude_sig;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;

    #[test]
    fn overlapping_point_or_group_rule_disables_lifting() {
        let x = msg_var("x", 0);
        let y = msg_var("x", 1);
        let base = bp_maude_sig();
        assert!(RuleTable::new(&base).unwrap().builtin_bp);
        for lhs in [
            emap(x.clone(), y.clone()),
            pmult(x.clone(), y),
            inv(x.clone()),
        ] {
            let mut changed = base.clone();
            let rule = RRule::new(lhs, x.clone());
            changed
                .st_rules
                .insert(rrule_to_ctxt_st_rule(&rule).unwrap());
            assert!(!RuleTable::new(&changed).unwrap().builtin_bp);
        }
    }
}
