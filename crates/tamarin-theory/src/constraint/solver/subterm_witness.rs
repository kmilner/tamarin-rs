// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Residual subterm witnesses: `finishedSubterms` / `witnessedSubterm` from
//! Theory/Constraint/Solver/ProofMethod.hs, upstream b07e308 (#958).

use std::collections::BTreeSet;

use crate::atom::{Atom, ProtoAtom};
use crate::constraint::system::System;
use crate::fact::FactTag;
use crate::formula::BLNTerm;
use crate::guarded::Guarded;
use tamarin_term::function_symbols::{Constructability, FunSym, Privacy};
use tamarin_term::lterm::{
    get_var, occurs_free, sort_of_lnterm, HasFrees, LNTerm, LSort, LVar, NameTag,
};
use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

/// A residual `s << x` can be witnessed by a nested pair containing every
/// required `s` and a fresh public name. This is sound only when each `s` is
/// publicly constructible and choosing that pair cannot change other
/// constraints, action matching, or the restrictions on knowledge events.
pub(super) fn finished_subterms(sig: &MaudeSig, sys: &System) -> bool {
    let store = &sys.subterm_store;
    // Solved positives and negative variable subterms do not require a new
    // witness, but every store still rejects reducible containing terms.
    if store
        .subterms
        .iter()
        .chain(&store.solved_subterms)
        .map(|st| &st.big)
        .chain(store.neg_subterms.iter().map(|(_, big)| big))
        .any(|big| matches!(big, Term::App(f, _) if sig.reducible_fun_syms_fast.contains(f)))
    {
        return false;
    }
    let residual_vars: BTreeSet<LVar> = store
        .subterms
        .iter()
        .filter_map(|st| get_var(&st.big).filter(|v| v.sort == LSort::Msg))
        .copied()
        .collect();
    if residual_vars.is_empty() {
        return true;
    }

    // Share system-wide data between all candidate containing variables,
    // as Haskell's partially applied witnessedSubterm does.
    let mut fixed_vars = BTreeSet::new();
    for term in store
        .subterms
        .iter()
        .map(|st| &st.small)
        .chain(store.neg_subterms.iter().flat_map(|(s, t)| [s, t]))
    {
        term.for_each_free(&mut |v| {
            fixed_vars.insert(*v);
        });
    }
    let mut formula_vars = BTreeSet::new();
    let mut guards = Vec::new();
    for formula in sys
        .formulas
        .iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        formula.for_each_free(&mut |v| {
            formula_vars.insert(*v);
        });
        guard_atom_groups(formula, &mut guards);
    }
    let node_facts: Vec<_> = sys
        .nodes
        .iter()
        .flat_map(|(_, rule)| {
            rule.premises
                .iter()
                .chain(&rule.conclusions)
                .chain(&rule.actions)
        })
        .collect();
    let action_goals: Vec<_> = sys.unsolved_action_atoms().map(|(_, fact)| fact).collect();
    let actions: Vec<_> = action_goals
        .iter()
        .copied()
        .chain(sys.nodes.iter().flat_map(|(_, rule)| rule.actions.iter()))
        .collect();

    // Removing witnessed groups and then rejecting every remaining message
    // container is equivalent to requiring a witness for each group here.
    residual_vars.iter().all(|x| {
        store
            .subterms
            .iter()
            .filter(|st| get_var(&st.big) == Some(x))
            .all(|st| constructible(&st.small, x, &residual_vars, sig))
            && !fixed_vars.contains(x)
            && !formula_vars.contains(x)
            && store
                .subterms
                .iter()
                .filter(|st| get_var(&st.big) != Some(x))
                .all(|st| !occurs_free(x, &st.big))
            && node_facts.iter().chain(&action_goals).all(|fact| {
                fact.terms
                    .iter()
                    .all(|t| below_free_constructors(t, x, sig))
            })
            && guards.iter().all(|group| {
                if group.iter().any(
                    |atom| matches!(atom, ProtoAtom::Action(_, fact) if fact.tag == FactTag::Ku),
                ) {
                    return false;
                }
                let has_equation = group
                    .iter()
                    .any(|atom| matches!(atom, ProtoAtom::EqE(_, _)));
                !group.iter().any(|atom| {
                    let ProtoAtom::Action(_, pattern) = atom else {
                        return false;
                    };
                    actions.iter().any(|fact| {
                        pattern.tag == fact.tag
                            && pattern.terms.len() == fact.terms.len()
                            && fact.terms.iter().any(|t| occurs_free(x, t))
                            && (has_equation
                                || pattern
                                    .terms
                                    .iter()
                                    .zip(fact.terms.iter())
                                    .any(|(p, t)| guard_inspects(p, t, x)))
                    })
                })
            })
    })
}

fn constructible(t: &LNTerm, x: &LVar, residual_vars: &BTreeSet<LVar>, sig: &MaudeSig) -> bool {
    if sort_of_lnterm(t) == LSort::Nat {
        return false;
    }
    match t {
        Term::Lit(Lit::Con(name)) => name.tag == NameTag::Pub,
        Term::Lit(Lit::Var(v)) => {
            v.sort == LSort::Pub || (v.sort == LSort::Msg && v != x && !residual_vars.contains(v))
        }
        Term::App(f @ FunSym::NoEq(sym), args)
            if sym.privacy == Privacy::Public
                && sym.constructability == Constructability::Constructor =>
        {
            !sig.reducible_fun_syms_fast.contains(f)
                && args.iter().all(|a| constructible(a, x, residual_vars, sig))
        }
        Term::App(_, _) => false,
    }
}

fn below_free_constructors(t: &LNTerm, x: &LVar, sig: &MaudeSig) -> bool {
    match t {
        Term::Lit(_) => true,
        Term::App(f @ FunSym::NoEq(_), args) if sig.irreducible_fun_syms_fast.contains(f) => {
            args.iter().all(|a| below_free_constructors(a, x, sig))
        }
        Term::App(_, args) => !args.iter().any(|a| occurs_free(x, a)),
    }
}

/// Could instantiating x allow this guard to match an action it did not
/// match before? A variable pattern is safe; a constructor pattern at x
/// is not. Distinct symbols or constants cannot start matching the pair.
fn guard_inspects(pattern: &BLNTerm, term: &LNTerm, x: &LVar) -> bool {
    if !occurs_free(x, term) {
        return false;
    }
    match (pattern, term) {
        (Term::Lit(Lit::Var(_)), _) => false,
        (Term::App(_, _), Term::Lit(Lit::Var(_))) => true,
        (Term::App(f, ps), Term::App(g, ts)) if f == g && ps.len() == ts.len() => ps
            .iter()
            .zip(ts.iter())
            .any(|(p, t)| guard_inspects(p, t, x)),
        _ => false,
    }
}

fn guard_atom_groups<'a>(formula: &'a Guarded, groups: &mut Vec<&'a [Atom<BLNTerm>]>) {
    match formula {
        Guarded::Atom(_) => {}
        Guarded::Conj(fs) | Guarded::Disj(fs) => {
            for f in fs.iter() {
                guard_atom_groups(f, groups);
            }
        }
        Guarded::GGuarded { guards, body, .. } => {
            groups.push(guards);
            guard_atom_groups(body, groups);
        }
    }
}

#[cfg(test)]
#[path = "subterm_witness_tests.rs"]
mod tests;
