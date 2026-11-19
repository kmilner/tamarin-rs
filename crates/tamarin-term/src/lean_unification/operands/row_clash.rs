//! Subtract two equations at the same AC head and compare rigid residual widths.
use super::super::{ac_children, common_children, Error};
use super::indivisible;
use crate::function_symbols::AcSym;
use crate::lterm::LNTerm;
use crate::rewriting::Equal;

fn shares_open(symbol: AcSym, xs: &[LNTerm], ys: &[LNTerm]) -> bool {
    xs.iter().any(|t| !indivisible(symbol, t) && ys.contains(t))
}

pub(in crate::lean_unification) fn refutes(eqs: &[Equal<LNTerm>]) -> Result<bool, Error> {
    // A missed pair simply leaves the original problem for the ordinary solver.
    if !(2..=16).contains(&eqs.len()) {
        return Ok(false);
    }
    let mut attempts = 0;
    for (i, pivot) in eqs.iter().enumerate() {
        let Some((symbol, pl, pr)) = ac_children(pivot) else {
            continue;
        };
        if pl.len() + pr.len() > 32 {
            continue;
        }
        for row in &eqs[i + 1..] {
            let Some((other, l, r)) = ac_children(row) else {
                continue;
            };
            if other != symbol
                || l.len() + r.len() > 32
                || l.len() + pr.len() == r.len() + pl.len()
                || !shares_open(symbol, pl, l)
                || !shares_open(symbol, pr, r)
            {
                continue;
            }
            if attempts >= 16 {
                return Ok(false);
            }
            attempts += 1;
            let (left, right) =
                common_children::residual_refs(l.iter().chain(pr), r.iter().chain(pl))?;
            if left.len() != right.len()
                && left.iter().chain(&right).all(|t| indivisible(symbol, t))
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra_backend::AlgebraBackend;
    use crate::lterm::{pub_term, LSort, LVar};
    use crate::maude_proc::MaudeHandle;
    use crate::maude_sig::mset_maude_sig;
    use crate::term::{f_app_ac, Term};
    use crate::vterm::Lit;
    use tamarin_test_support::require_maude_path;

    #[test]
    fn native_oracle_width_clash_and_splittable_residual_agree_with_maude() {
        // CI runs this comparison separately from hybrid verification.
        if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
            return;
        }
        let Some(path) = require_maude_path() else {
            return;
        };
        let oracle =
            MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude)
                .unwrap();
        let native =
            MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::NativeOnly)
                .unwrap();
        let var = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
        let (x, y, v) = (var("x", 0), var("y", 1), var("v", 2));
        let atom = pub_term("a");
        let sum = |xs| f_app_ac(AcSym::Union, xs);
        let first = Equal {
            lhs: sum(vec![x.clone(), atom.clone()]),
            rhs: sum(vec![y.clone(), atom.clone()]),
        };
        for (extra, clash) in [(atom.clone(), true), (v, false)] {
            // Subtracting the first equation leaves extra = a + a. A Msg
            // variable can take that composite image, a single name cannot.
            let second = Equal {
                lhs: sum(vec![x.clone(), atom.clone(), extra]),
                rhs: sum(vec![y.clone(), atom.clone(), atom.clone(), atom.clone()]),
            };
            for query in [
                [first.clone(), second.clone()],
                [second.clone(), first.clone()],
            ] {
                assert_eq!(refutes(&query).unwrap(), clash);
                assert_eq!(oracle.unify(&query).unwrap().is_empty(), clash);
                assert_eq!(native.unify(&query).unwrap().is_empty(), clash);
            }
        }
    }
}
