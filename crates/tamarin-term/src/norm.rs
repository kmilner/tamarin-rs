// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Rewriting.Norm` — normalisation and normal-form
//! checks via the Maude bridge.
//!
//! Tamarin uses two strategies:
//! 1. **Maude-backed normalisation** (`norm`) — simply asks Maude to
//!    `reduce` the term modulo the theory.
//! 2. **Haskell-side normal-form check** (`nf_via_haskell`) — a
//!    structural walk that returns `false` early when an obviously-
//!    reducible top construct is detected, avoiding a Maude callout
//!    for negative cases.
//!
//! For the Rust port we expose the Maude-backed `norm` directly and
//! the pure structural `nf_via_haskell` check, which decides normal
//! form from syntax alone (independent of any AC canonicalisation
//! Maude might apply).  `nf_via_haskell_maude` is the same structural
//! check for callers that hold a `MaudeHandle`: its subterm-rule arm can
//! additionally match rule LHSes that need AC matching (user-`[AC]`
//! equations), which the pure check has no matcher for.

use crate::function_symbols::{AcSym, FunSym};
use crate::lterm::LNTerm;
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::maude_sig::MaudeSig;
use crate::term::Term;

/// `norm` — normalise a term modulo the configured theory by passing
/// it to Maude's `reduce` operator.
pub fn norm(maude: &MaudeHandle, t: &LNTerm) -> Result<LNTerm, MaudeError> {
    // Variable / constant literals are already normal — skip the
    // Maude round-trip for them.
    if matches!(t, Term::Lit(_)) {
        return Ok(t.clone());
    }
    maude.reduce(t)
}

/// `nfViaHaskell` — pure structural normal-form check.  Mirrors HS
/// `Term/Rewriting/Norm.hs` (`nfViaHaskell`).  Returns `true`
/// iff `t` is in normal form according to the structural rules of the
/// signature, **independent of any AC canonicalisation that Maude
/// might apply**.  This is critical: a term like `mult(tid, x)` and
/// `mult(x, tid)` are *both* in normal form by HS's structural check
/// — neither contains `one`, `DH_neutral`, nested products, or invalid
/// patterns — even though Maude's `reduce` would canonicalise them to
/// the same AC form.  Using `maude.reduce(t) == t` as the NF predicate
/// would wrongly flag AC-reordered terms as "creates non-normal",
/// over-filtering `simpMinimize` arms in `substCreatesNonNormalTerms`
/// and causing wrong-verified outcomes on DH key-secrecy lemmas
/// (JKL_TS2_2004{,_KI_wPFS}).
///
/// HS-faithful pattern set (`nfViaHaskell` in Norm.hs):
///   - irreducible top: walk subterms
///   - reducible exponent / inverse / mult / xor / pmult / emap
///     patterns: return `false`
///   - subterm-rule LHS matches: return `false`
///   - else: walk subterms
pub fn nf_via_haskell(msig: &MaudeSig, t: &LNTerm) -> bool {
    go_nf(t, msig, None)
}

/// Maude-capable variant of [`nf_via_haskell`]: identical structural walk,
/// but the subterm-rule arm can also fire for rules whose LHS contains an
/// Ac-/C-headed subterm (e.g. the user-`[AC]` cancellation equations
/// `xorr(x, x) = zeroo` / `xorr(xorr(x, y), x) = y`).  HS's
/// `struleApplicable` (Norm.hs) matches via `solveMatchLNTerm`
/// inside the `WithMaude` reader, so AC-headed rule LHSes match through
/// Maude; the pure no-AC matcher used by [`nf_via_haskell`] can never
/// match them (its `match_raw` raises `NeedsAC` on any Ac-vs-Ac pair).
/// Callers that hold a handle (the HS sites all do — `nf'` runs in the
/// reader) should use this variant; the pure one under-reports
/// reducibility exactly on those rules, e.g. keeping split cases whose
/// substitution creates `xorr(~k, ~k, …)`, which HS's
/// `substCreatesNonNormalTerms` filter discards (csf26-ac CRxor
/// `splitEqs(2)`: 6 RS cases vs 2 HS cases, flipping the
/// `isSplitGoalSmall` goal ranking and every later split-case number).
pub fn nf_via_haskell_maude(maude: &MaudeHandle, t: &LNTerm) -> bool {
    let sig = maude.maude_sig();
    nf_via_haskell_maude_with_sig(&sig, maude, t)
}

/// As [`nf_via_haskell_maude`], for callers that already hold the handle's
/// [`MaudeSig`] — skips the per-call `Arc` clone.
pub fn nf_via_haskell_maude_with_sig(msig: &MaudeSig, maude: &MaudeHandle, t: &LNTerm) -> bool {
    go_nf(t, msig, Some(maude))
}

fn go_nf(t: &LNTerm, msig: &MaudeSig, maude: Option<&MaudeHandle>) -> bool {
    use crate::function_symbols::{
        AcSym, DH_NEUTRAL_SYM_STRING, EXP_SYM_STRING, INV_SYM_STRING, ONE_SYM_STRING,
        ZERO_SYM_STRING,
    };
    match t {
        Term::Lit(_) => true,
        Term::App(sym, args) => {
            // 1. Irreducible NoEq / user-defined-AC top: walk subterms.
            // HS's `nfViaHaskell` (Norm.hs) gates the
            // irreducible-set lookup on the symbol KIND — it checks
            // `FAppNoEq o ts | (NoEq o) \`S.member\` irreducible` and
            // `FAppACfct o ts | (AC (ACfct o)) \`S.member\` irreducible`.  The
            // builtin AC operators sit in `irreducible_fun_syms` as well, for
            // OTHER consumers (Contradictions.hs `maybeNonNormalTerms`
            // uses `S.member` on the FUN set to decide which subterms to NOT
            // include), but Norm.hs matches them through their own `viewTerm2`
            // constructors, so they must not take this arm: ungated,
            // `Mult(tid, ekI, ekR, inv(tid))` counts as NF — skipping section
            // 5's invalidMult check — which under-filters simpMinimize and
            // admits AC variants HS rejects.
            if matches!(sym, FunSym::NoEq(_) | FunSym::Ac(AcSym::AcFct(_)))
                && msig.irreducible_fun_syms.contains(sym)
            {
                return args.iter().all(|a| go_nf(a, msig, maude));
            }
            // FList is irreducible unconditionally (HS: `FList ts -> all go ts`).
            if matches!(sym, FunSym::List) {
                return args.iter().all(|a| go_nf(a, msig, maude));
            }
            // 2. Nullary constants in NF (One, DHNeutral, Zero, NatOne).
            if let FunSym::NoEq(s) = sym
                && args.is_empty()
                && (s.name == ONE_SYM_STRING
                    || s.name == DH_NEUTRAL_SYM_STRING
                    || s.name == ZERO_SYM_STRING
                    || s.name == crate::function_symbols::NAT_ONE_SYM_STRING)
            {
                return true;
            }
            // 3. Subterm-rule LHS match → reducible.  HS guards both st-rule
            //    arms on a `FAppNoEq` / `FAppACfct` top symbol (Norm.hs).
            if matches!(sym, FunSym::NoEq(_) | FunSym::Ac(AcSym::AcFct(_)))
                && msig
                    .st_rules
                    .iter()
                    .any(|rule| strule_applicable(maude, t, rule))
            {
                return false;
            }
            // 4. Reducible exponent / inverse / mult / xor patterns.
            if let FunSym::NoEq(s) = sym {
                if s.name == EXP_SYM_STRING && args.len() == 2 {
                    // (a ^ b) ^ c → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0]
                        && s2.name == EXP_SYM_STRING
                    {
                        return false;
                    }
                    // a ^ 1 → reducible
                    if is_nullary(&args[1], ONE_SYM_STRING) {
                        return false;
                    }
                    // DH_neutral ^ b → reducible
                    if is_nullary(&args[0], DH_NEUTRAL_SYM_STRING) {
                        return false;
                    }
                    // else walk subterms
                    return go_nf(&args[0], msig, maude) && go_nf(&args[1], msig, maude);
                }
                if s.name == INV_SYM_STRING && args.len() == 1 {
                    // inv(inv(_)) → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0]
                        && s2.name == INV_SYM_STRING
                    {
                        return false;
                    }
                    // inv(mult(...)) where any factor is inverse → reducible
                    if let Term::App(FunSym::Ac(AcSym::Mult), inner_args) = &args[0]
                        && inner_args.iter().any(crate::term::is_inverse)
                    {
                        return false;
                    }
                    // inv(one) → reducible
                    if is_nullary(&args[0], ONE_SYM_STRING) {
                        return false;
                    }
                    return go_nf(&args[0], msig, maude);
                }
                if s.name == crate::function_symbols::PMULT_SYM_STRING && args.len() == 2 {
                    // pmult(_, pmult(_,_)) → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[1]
                        && s2.name == crate::function_symbols::PMULT_SYM_STRING
                    {
                        return false;
                    }
                    // pmult(one, _) → reducible
                    if is_nullary(&args[0], ONE_SYM_STRING) {
                        return false;
                    }
                    return go_nf(&args[0], msig, maude) && go_nf(&args[1], msig, maude);
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
                            is_nullary(a, ONE_SYM_STRING)
                                || is_nullary(a, DH_NEUTRAL_SYM_STRING)
                                || crate::term::is_product(a)
                        };
                        if args.iter().any(reducible_factor) || invalid_mult(args) {
                            return false;
                        }
                        return args.iter().all(|a| go_nf(a, msig, maude));
                    }
                    AcSym::Xor => {
                        // HS: `FXor ts | fAppZero `elem` ts || any isXor ts ||
                        // invalidXor ts` (Norm.hs).
                        if args
                            .iter()
                            .any(|a| is_nullary(a, ZERO_SYM_STRING) || is_xor(a))
                            || invalid_xor(args)
                        {
                            return false;
                        }
                        return args.iter().all(|a| go_nf(a, msig, maude));
                    }
                    // HS's recursive catch-all section: `FUnion ts`,
                    // `FNatPlus ts` and `FAppACfct _ ts` all walk subterms.
                    AcSym::Union | AcSym::NatPlus | AcSym::AcFct(_) => {
                        return args.iter().all(|a| go_nf(a, msig, maude));
                    }
                }
            }
            // 6. C-headed (FEMap) reducible patterns.
            if let FunSym::C(_) = sym {
                // em(_, pmult(_,_)) or em(pmult(_,_), _) → reducible
                if args.len() == 2 {
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0]
                        && s2.name == crate::function_symbols::PMULT_SYM_STRING
                    {
                        return false;
                    }
                    if let Term::App(FunSym::NoEq(s2), _) = &args[1]
                        && s2.name == crate::function_symbols::PMULT_SYM_STRING
                    {
                        return false;
                    }
                }
                return args.iter().all(|a| go_nf(a, msig, maude));
            }
            // 7. Default fallthrough: walk subterms (HS:
            //    `FAppNoEq _ ts -> all go ts`, `FAppC _ ts -> all go ts`).
            args.iter().all(|a| go_nf(a, msig, maude))
        }
    }
}

fn is_nullary(t: &LNTerm, name: &[u8]) -> bool {
    if let Term::App(FunSym::NoEq(s), args) = t {
        s.name == name && args.is_empty()
    } else {
        false
    }
}

fn is_xor(t: &LNTerm) -> bool {
    matches!(t, Term::App(FunSym::Ac(AcSym::Xor), _))
}

/// `invalidMult` — HS `Norm.hs`.  Detects mult patterns that
/// are not in NF due to inverse cancellation.
fn invalid_mult(ts: &[LNTerm]) -> bool {
    use crate::function_symbols::{AcSym, INV_SYM_STRING};
    fn inverse_args(term: &LNTerm) -> Option<&[LNTerm]> {
        match term {
            Term::App(FunSym::NoEq(sym), args) if sym.name == INV_SYM_STRING => Some(args.as_ref()),
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
/// match.  A Maude error is also folded to "no match" (the term stays NF).
fn strule_applicable(
    maude: Option<&MaudeHandle>,
    t: &LNTerm,
    rule: &crate::subterm_rule::CtxtStRule,
) -> bool {
    use crate::rewriting::Match;
    use crate::unification::MatchOutcome;
    let lhs = &rule.lhs;
    let problem = Match::match_with(t.clone(), lhs.clone());
    let matched = match crate::unification::solve_match_lterm(&crate::lterm::sort_of_name, problem)
    {
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
            (Some(maude), _, _) => maude
                .match_eqs(&[crate::rewriting::Equal {
                    lhs: t.clone(),
                    rhs: lhs.clone(),
                }])
                .is_ok_and(|ms| !ms.is_empty()),
        },
    };
    matched && strule_rewrites(t, &rule.rhs)
}

// NOTE: `maybeNotNfSubterms` (HS `Term/Rewriting/Norm.hs`) lives
// in the solver, not here — see `contradictions.rs::maybe_not_nf_subterms`,
// which is the HS-faithful copy (it returns `[t]` for a bare `Lit (Var _)`,
// matching HS's `_ -> [t]` wildcard, and `[]` only for `Lit (Con _)`).

#[cfg(test)]
#[path = "norm_tests.rs"]
mod tests;
