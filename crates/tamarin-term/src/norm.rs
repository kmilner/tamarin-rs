// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Rewriting.Norm`: `nf_via_haskell*` is HS `nfViaHaskell`,
//! the structural normal-form check.  The `_maude` entry point can also
//! match st-rule LHSes that need AC matching; the pure one counts those as
//! not matching.

use crate::function_symbols::{AcSym, FunSym, NoEqSym};
use crate::lterm::LNTerm;
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::maude_sig::MaudeSig;
use crate::term::Term;

/// HS `nfViaHaskell` (Norm.hs) without a Maude handle.  It is structural:
/// `mult(tid, x)` and `mult(x, tid)` are both normal, whereas comparing with
/// Maude's `reduce` would flag one of them and over-filter
/// `substCreatesNonNormalTerms`.
pub fn nf_via_haskell(msig: &MaudeSig, t: &LNTerm) -> bool {
    match go_nf(t, msig, None) {
        Ok(is_nf) => is_nf,
        Err(_) => unreachable!("the normal-form check asks Maude only through a handle"),
    }
}

/// HS `nfViaHaskell` (Norm.hs), whose `struleApplicable` matches through
/// Maude when an st-rule LHS needs AC matching (e.g. `xorr(x, x) = zeroo`).
/// The HS callers all run in `WithMaude`, so solver callers use this one;
/// the pure variant misses such reductions (csf26-ac CRxor).  `msig` is the
/// handle's [`MaudeSig`], passed in so callers holding it skip the `Arc`
/// clone.  HS runs that match purely, so a failed backend is an error,
/// never "in normal form".
pub fn nf_via_haskell_maude(
    msig: &MaudeSig,
    maude: &MaudeHandle,
    t: &LNTerm,
) -> Result<bool, MaudeError> {
    go_nf(t, msig, Some(maude))
}

fn go_nf(t: &LNTerm, msig: &MaudeSig, maude: Option<&MaudeHandle>) -> Result<bool, MaudeError> {
    // HS dispatches on `viewTerm2`, which recognises the builtin free symbols
    // by complete symbol identity; every other free symbol (including a
    // user-declared one that only shares a builtin's name) is `FAppNoEq`.
    match t {
        Term::Lit(_) => Ok(true),
        Term::App(sym, args) => {
            // 1. Irreducible top: walk subterms.  HS checks membership only
            //    for `FAppNoEq` and `FAppACfct`; the builtin AC operators,
            //    though in `irreducible_fun_syms`, have their own arms below.
            let plain_top = match sym {
                FunSym::NoEq(s) => !s.is_view_term2_special(),
                FunSym::Ac(AcSym::AcFct(_)) => true,
                _ => false,
            };
            if plain_top && msig.irreducible_fun_syms.contains(sym) {
                return all_nf(args, msig, maude);
            }
            // FList is irreducible unconditionally (HS: `FList ts -> all go ts`).
            if matches!(sym, FunSym::List) {
                return all_nf(args, msig, maude);
            }
            // 2. Nullary constants in NF (One, DHNeutral, NatOne).  HS's
            //    `Zero` arm is unreachable (`viewTerm2` has no `Zero` case),
            //    so `zero` takes the `FAppNoEq` arms like any other symbol.
            if let FunSym::NoEq(s) = sym
                && args.is_empty()
                && (s.is_one_sym() || s.is_dh_neutral_sym() || s.is_nat_one_sym())
            {
                return Ok(true);
            }
            // 3. Subterm-rule LHS match → reducible.  HS guards both st-rule
            //    arms on a `FAppNoEq` / `FAppACfct` top symbol (Norm.hs).
            if plain_top {
                for rule in &msig.st_rules {
                    if strule_applicable(maude, t, rule)? {
                        return Ok(false);
                    }
                }
            }
            // 4. Reducible exponent / inverse / mult / xor patterns.
            if let FunSym::NoEq(s) = sym {
                if s.is_exp_sym() && args.len() == 2 {
                    // (a ^ b) ^ c → reducible
                    if is_no_eq_app(&args[0], NoEqSym::is_exp_sym) {
                        return Ok(false);
                    }
                    // a ^ 1 → reducible
                    if is_nullary(&args[1], NoEqSym::is_one_sym) {
                        return Ok(false);
                    }
                    // DH_neutral ^ b → reducible
                    if is_nullary(&args[0], NoEqSym::is_dh_neutral_sym) {
                        return Ok(false);
                    }
                    // else walk subterms
                    return Ok(go_nf(&args[0], msig, maude)? && go_nf(&args[1], msig, maude)?);
                }
                if s.is_inv_sym() && args.len() == 1 {
                    // inv(inv(_)) → reducible
                    if crate::term::is_inverse(&args[0]) {
                        return Ok(false);
                    }
                    // inv(mult(...)) where any factor is inverse → reducible
                    if let Term::App(FunSym::Ac(AcSym::Mult), inner_args) = &args[0]
                        && inner_args.iter().any(crate::term::is_inverse)
                    {
                        return Ok(false);
                    }
                    // inv(one) → reducible
                    if is_nullary(&args[0], NoEqSym::is_one_sym) {
                        return Ok(false);
                    }
                    return go_nf(&args[0], msig, maude);
                }
                if s.is_pmult_sym() && args.len() == 2 {
                    // pmult(_, pmult(_,_)) → reducible
                    if is_no_eq_app(&args[1], NoEqSym::is_pmult_sym) {
                        return Ok(false);
                    }
                    // pmult(one, _) → reducible
                    if is_nullary(&args[0], NoEqSym::is_one_sym) {
                        return Ok(false);
                    }
                    return Ok(go_nf(&args[0], msig, maude)? && go_nf(&args[1], msig, maude)?);
                }
            }
            // 5. AC-headed reducible patterns.
            if let FunSym::Ac(ac) = sym {
                match ac {
                    AcSym::Mult => {
                        // HS: `FMult ts | fAppOne `elem` ts || fAppDHNeutral
                        // `elem` ts || any isProduct ts || invalidMult ts`
                        // (Norm.hs) — the three element tests fuse into one
                        // pass, the disjunction is unchanged.
                        let reducible_factor = |a: &LNTerm| {
                            is_nullary(a, NoEqSym::is_one_sym)
                                || is_nullary(a, NoEqSym::is_dh_neutral_sym)
                                || crate::term::is_product(a)
                        };
                        if args.iter().any(reducible_factor) || invalid_mult(args) {
                            return Ok(false);
                        }
                        return all_nf(args, msig, maude);
                    }
                    AcSym::Xor => {
                        // HS: `FXor ts | fAppZero `elem` ts || any isXor ts ||
                        // invalidXor ts` (Norm.hs).
                        if args
                            .iter()
                            .any(|a| is_nullary(a, NoEqSym::is_zero_sym) || is_xor(a))
                            || invalid_xor(args)
                        {
                            return Ok(false);
                        }
                        return all_nf(args, msig, maude);
                    }
                    // HS's recursive catch-all section: `FUnion ts`,
                    // `FNatPlus ts` and `FAppACfct _ ts` all walk subterms.
                    AcSym::Union | AcSym::NatPlus | AcSym::AcFct(_) => {
                        return all_nf(args, msig, maude);
                    }
                }
            }
            // 6. C-headed (FEMap) reducible patterns.
            if let FunSym::C(_) = sym {
                // em(_, pmult(_,_)) or em(pmult(_,_), _) → reducible
                if args.len() == 2
                    && (is_no_eq_app(&args[0], NoEqSym::is_pmult_sym)
                        || is_no_eq_app(&args[1], NoEqSym::is_pmult_sym))
                {
                    return Ok(false);
                }
                return all_nf(args, msig, maude);
            }
            // 7. Default fallthrough: walk subterms (HS:
            //    `FAppNoEq _ ts -> all go ts`, `FAppC _ ts -> all go ts`).
            all_nf(args, msig, maude)
        }
    }
}

/// `all go ts`, stopping at the first subterm out of normal form.
fn all_nf(ts: &[LNTerm], msig: &MaudeSig, maude: Option<&MaudeHandle>) -> Result<bool, MaudeError> {
    for t in ts {
        if !go_nf(t, msig, maude)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `t` is an application of a free symbol satisfying `is_sym` (one of the
/// [`NoEqSym`] builtin identity predicates).
fn is_no_eq_app(t: &LNTerm, is_sym: fn(&NoEqSym) -> bool) -> bool {
    matches!(t, Term::App(FunSym::NoEq(s), _) if is_sym(s))
}

/// `t` is the nullary application of a builtin constant (`fAppOne`,
/// `fAppZero`, ...), compared by complete symbol identity as HS's `==`/`elem`
/// on terms does.
fn is_nullary(t: &LNTerm, is_sym: fn(&NoEqSym) -> bool) -> bool {
    matches!(t, Term::App(FunSym::NoEq(s), args) if args.is_empty() && is_sym(s))
}

fn is_xor(t: &LNTerm) -> bool {
    matches!(t, Term::App(FunSym::Ac(AcSym::Xor), _))
}

/// `invalidMult` — HS `Norm.hs`.  Detects mult patterns that
/// are not in NF due to inverse cancellation.
fn invalid_mult(ts: &[LNTerm]) -> bool {
    // HS `partition isInverse`: `invSym` itself (any argument count, so a
    // malformed application still trips the two-inverses rule).
    fn inverse_args(term: &LNTerm) -> Option<&[LNTerm]> {
        match term {
            Term::App(FunSym::NoEq(s), args) if s.is_inv_sym() => Some(args.as_ref()),
            _ => None,
        }
    }
    let mut inverse_arg = None;
    let mut saw_inverse = false;
    for term in ts {
        if let Some(args) = inverse_args(term) {
            if saw_inverse {
                return true;
            }
            saw_inverse = true;
            inverse_arg = args.first();
        }
    }
    let Some(inverse_arg) = inverse_arg else {
        return false;
    };
    let factors = ts.iter().filter(|term| inverse_args(term).is_none());
    if let Term::App(FunSym::Ac(AcSym::Mult), inverse_factors) = inverse_arg {
        inverse_factors
            .iter()
            .any(|inverse_factor| factors.clone().any(|factor| factor == inverse_factor))
    } else {
        factors.into_iter().any(|factor| factor == inverse_arg)
    }
}

/// `invalidXor` — HS `Norm.hs`.  True iff `ts` contains
/// duplicates.
fn invalid_xor(ts: &[LNTerm]) -> bool {
    // Smart constructors keep AC arguments sorted, so duplicates are adjacent
    // on the normal path. Keep the quadratic fallback for terms made through
    // `unsafe_f_app` or another invariant-bypassing caller.
    let mut canonical = true;
    for pair in ts.windows(2) {
        match pair[0].cmp(&pair[1]) {
            std::cmp::Ordering::Equal => return true,
            std::cmp::Ordering::Greater => {
                canonical = false;
                break;
            }
            std::cmp::Ordering::Less => {}
        }
    }
    !canonical
        && ts
            .iter()
            .enumerate()
            .any(|(i, term)| ts[i + 1..].contains(term))
}

/// The `StRhs` disambiguation both `struleApplicable` ports apply once the
/// rule's LHS has matched `t`.
fn strule_rewrites(t: &LNTerm, rhs: &crate::subterm_rule::StRhs) -> bool {
    // HS (Norm.hs):
    //   _:_ -> case rhs of
    //            StRhs [] s -> not (t == s)   -- reducible, but RHS might equal t
    //            StRhs _  _ -> True
    // i.e. the disambiguating branch is on the POSITIONS list being empty
    // (`StRhs []`), NOT on the RHS term being ground.  `rRuleToCtxtStRule`
    // always yields non-empty positions (constantPositions of an FApp is
    // never empty; the non-ground branch returns None on empty), so the
    // `StRhs []` arm is effectively dead and a match always returns True.
    if rhs.positions.is_empty() {
        t != &rhs.term
    } else {
        true
    }
}

/// `struleApplicable` (Norm.hs): `solveMatchLNTerm (t `matchWith` lhs)`,
/// i.e. the native matcher first and a Maude `match` only on `NeedsAc`
/// (Term/Unification.hs).  Without a handle an AC problem counts as no
/// match; a Maude failure is an error.
fn strule_applicable(
    maude: Option<&MaudeHandle>,
    t: &LNTerm,
    rule: &crate::subterm_rule::CtxtStRule,
) -> Result<bool, MaudeError> {
    use crate::rewriting::Match;
    use crate::unification::MatchOutcome;
    let lhs = &rule.lhs;
    let problem = Match::match_with(t.clone(), lhs.clone());
    let matched = match crate::unification::solve_match_lterm(
        &crate::lterm::sort_of_name,
        &|_| true,
        problem,
    ) {
        MatchOutcome::NoMatcher => false,
        MatchOutcome::Matched(_) => true,
        MatchOutcome::NeedsAc => match (maude, t, lhs) {
            (None, _, _) => false,
            // `match_raw` reports `NeedsAc` for any two AC-headed sides, as
            // HS `matchRaw` does.  The MSG module declares only `[comm
            // assoc]` / `[comm]` axioms, which keep the root symbol, so two
            // distinct AC roots never match and need no Maude call.
            (_, Term::App(FunSym::Ac(t_sym), _), Term::App(FunSym::Ac(lhs_sym), _))
                if t_sym != lhs_sym =>
            {
                false
            }
            (Some(maude), _, _) => !maude
                .match_eqs(&[crate::rewriting::Equal {
                    lhs: t.clone(),
                    rhs: lhs.clone(),
                }])?
                .is_empty(),
        },
    };
    Ok(matched && strule_rewrites(t, &rule.rhs))
}

// NOTE: `maybeNotNfSubterms` (HS `Term/Rewriting/Norm.hs`) lives
// in the solver, not here — see `contradictions.rs::maybe_not_nf_subterms`,
// which is the HS-faithful copy (it returns `[t]` for a bare `Lit (Var _)`,
// matching HS's `_ -> [t]` wildcard, and `[]` only for `Lit (Con _)`).

#[cfg(test)]
#[path = "norm_tests.rs"]
mod tests;
