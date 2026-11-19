//! Binary AC variants for the unit and exponent-two cancellation presentation.
//! The active rule bucket determines both the operation and its unit.
use super::{flat_xor, InputDomain, RuleTable};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_unification::{
    ac_sort, canonical_capture, initialize, Error, MatchRows, LEAN_THREAD,
};
use crate::lterm::{LNTerm, LSort, LVar, Name};
use crate::rewriting::RRule;
use crate::subst::Subst;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;

unsafe extern "C" {
    fn tamarin_lean_binary_cancellation_rows() -> *mut std::ffi::c_void;
}

fn msg_var(term: &LNTerm) -> Option<LVar> {
    match term {
        Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => Some(*v),
        _ => None,
    }
}

/// Recognize f(a,a) = e, f(a,e) = a and f(a,a,b) = b, up to AC and
/// independent renaming of each rule. No other rule may act at this head.
pub(super) fn unit_for(head: AcSym, rules: &[RRule<LNTerm>]) -> Option<&LNTerm> {
    if ac_sort(head) != LSort::Msg || rules.len() != 3 {
        return None;
    }
    let mut duplicate = None;
    let mut identity = None;
    let mut extension = false;
    for r in rules {
        let Term::App(FunSym::Ac(f), args) = &r.lhs else {
            return None;
        };
        if *f != head {
            return None;
        }
        match args.as_ref() {
            [a, b] if a == b && msg_var(a).is_some() => {
                let Term::App(FunSym::NoEq(z), children) = &r.rhs else {
                    return None;
                };
                if z.arity != 0 || !children.is_empty() {
                    return None;
                }
                duplicate = Some(&r.rhs);
            }
            [a, b] if msg_var(&r.rhs).is_some() => {
                identity = Some(if a == &r.rhs {
                    b
                } else if b == &r.rhs {
                    a
                } else {
                    return None;
                });
            }
            [a, b, c] if msg_var(&r.rhs).is_some() => {
                extension = [(a, b, c), (b, c, a), (c, a, b)]
                    .into_iter()
                    .any(|(u, v, w)| u == v && msg_var(u).is_some() && w == &r.rhs && w != u);
            }
            _ => return None,
        }
    }
    let zero = duplicate?;
    (extension && identity == Some(zero)).then_some(zero)
}

type ValuedArm = (Subst<Name, LVar>, LNTerm);

impl RuleTable {
    pub(super) fn cancellation_normal(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        let Term::App(FunSym::Ac(head), _) = term else {
            return Ok(None);
        };
        let Some(unit) = self.cancellation_units.get(head) else {
            return Ok(None);
        };
        if self
            .collect(term, &mut Vec::new(), InputDomain::Sorted)
            .is_none()
        {
            return Ok(None);
        }
        // All equality tests on factors must agree with equality modulo B, including
        // commutative applications nested inside a raw caller-supplied term.
        let canonical = canonical_capture(term);
        let Term::App(_, args) = &canonical else {
            return Ok(None);
        };
        for factor in args.iter() {
            if !self.irreducible_native(factor)? {
                return Ok(None);
            }
        }
        let survivors: Vec<_> = flat_xor::odd_operands(args)?
            .into_iter()
            .filter(|t| *t != unit)
            .cloned()
            .collect();
        Ok(Some(if survivors.is_empty() {
            unit.clone()
        } else {
            f_app_ac(*head, survivors)
        }))
    }

    pub(super) fn binary_cancellation_rows(
        &self,
        term: &LNTerm,
    ) -> Result<Option<Vec<ValuedArm>>, Error> {
        let Term::App(FunSym::Ac(head), args) = term else {
            return Ok(None);
        };
        let Some(unit) = self.cancellation_units.get(head) else {
            return Ok(None);
        };
        let [left, right] = args.as_ref() else {
            return Ok(None);
        };
        let (Some(x), Some(y)) = (msg_var(left), msg_var(right)) else {
            return Ok(None);
        };
        if x == y {
            return Ok(None);
        }
        let mut ids = flat_xor::witness_indices(x.idx.max(y.idx), |i| i == x.idx || i == y.idx);
        let mut witness = || {
            ids.next()
                .map(|id| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, id))))
                .ok_or(Error::FreshVariableOverflow)
        };
        let vars = [witness()?, witness()?, witness()?];
        let decode = |mask: u64| -> Result<LNTerm, Error> {
            if mask > 6 {
                return Err(Error::InvalidStatus(255));
            }
            if mask == 0 {
                return Ok(unit.clone());
            }
            Ok(f_app_ac(
                *head,
                vars.iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, v)| v.clone())
                    .collect(),
            ))
        };
        initialize()?;
        LEAN_THREAD.with(|_| {
            // SAFETY: the shim returns an owned row array for MatchRows.
            let rows = MatchRows::new(unsafe { tamarin_lean_binary_cancellation_rows() })?;
            if rows.count() != 1 {
                return Err(Error::InvalidStatus(255));
            }
            let mut answers = Vec::with_capacity(rows.rows(0));
            for r in 0..rows.rows(0) {
                let mut masks = [0; 3];
                if rows.copy_row(0, r, &mut masks)? != 3 {
                    return Err(Error::InvalidStatus(255));
                }
                answers.push((
                    Subst::from_list([(x, decode(masks[0])?), (y, decode(masks[1])?)]),
                    decode(masks[2])?,
                ));
            }
            // The certificate constrains membership. Keep enumeration order and
            // repeated packets unobservable to the caller.
            answers.sort_unstable();
            answers.dedup();
            Ok(Some(answers))
        })
    }
}
