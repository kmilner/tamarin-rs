// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, meiersi, jdreier, rkunnema, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Maude/Parser.hs,
//   lib/term/src/Term/Rewriting/Norm.hs,
//   lib/term/src/Term/SubtermRule.hs, lib/term/src/Term/Unification.hs,
//   lib/theory/src/Theory/Constraint/Solver/Contradictions.hs

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
/// `Term/Rewriting/Norm.hs:54-127` (`nfViaHaskell`).  Returns `true`
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
/// HS-faithful pattern set (`nfViaHaskell` lines 60-99):
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
/// `struleApplicable` (Norm.hs:107-113) matches via `solveMatchLNTerm`
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
            // HS's `nfViaHaskell` (Norm.hs:55-127, see line 62) gates the
            // irreducible-set lookup on the symbol KIND — it checks
            // `FAppNoEq o ts | (NoEq o) \`S.member\` irreducible` and
            // `FAppACfct o ts | (AC (ACfct o)) \`S.member\` irreducible`.  The
            // builtin AC operators sit in `irreducible_fun_syms` as well, for
            // OTHER consumers (Contradictions.hs:149-150 `maybeNonNormalTerms`
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
            if let FunSym::NoEq(s) = sym {
                if args.is_empty()
                    && (s.name == ONE_SYM_STRING
                        || s.name == DH_NEUTRAL_SYM_STRING
                        || s.name == ZERO_SYM_STRING
                        || s.name == crate::function_symbols::NAT_ONE_SYM_STRING)
                {
                    return true;
                }
            }
            // 3. Subterm-rule LHS match → reducible.  Both of HS's st-rule
            //    arms are guarded on the top symbol's KIND — `FAppNoEq _ _`
            //    and `FAppACfct _ _` (Norm.hs:73-74) — so only NoEq- and
            //    user-`[AC]`-headed terms are ever offered to
            //    `struleApplicable`.  Builtin-AC- and C-headed terms have
            //    their own dedicated reducibility patterns (sections 5-6
            //    below) and fall straight past this loop.  The gate wraps the
            //    whole loop rather than either matcher arm, exactly as it sits
            //    above the two arms in HS: an st rule whose LHS is a bare
            //    variable is Ac/C-free and matches ANY subject term, so it
            //    reaches the pure arm on both entry points and would otherwise
            //    make every `Mult`/`Xor`/`Union`/`NatPlus`/`em`-headed term
            //    reducible where HS reports normal form.  (No `.spthy` yields
            //    such a rule — `rrule_to_ctxt_st_rule` rejects a bare-variable
            //    LHS on both of its branches, see subterm_rule.rs — so the gate
            //    is a structural guarantee, not a filter that fires in
            //    practice.)
            //    HS uses `solveMatchLNTerm (t `matchWith` lhs)`
            //    (Norm.hs:107-113).
            //    All builtin subterm rules (pair / senc / sdec / aenc /
            //    adec / sign / verify / ...) have AC-free LHS, so the
            //    no-AC matcher is complete for them; a rule whose LHS
            //    contains an Ac-/C-headed subterm (user `[AC]` equations,
            //    e.g. `xorr(x, x) = zeroo`) needs AC matching, which is
            //    only available when the caller supplied a `MaudeHandle`
            //    (`nf_via_haskell_maude`).  See subterm_rule.rs and
            //    builtin.rs.
            //    The Ac/C-freeness of each rule LHS is a full walk of that LHS,
            //    so each rule carries it (`MaudeSig::st_rules`, a `StRules`)
            //    rather than having it recomputed here — this loop runs at
            //    every `App` node of every NF check.
            if matches!(sym, FunSym::NoEq(_) | FunSym::Ac(AcSym::AcFct(_))) {
                for (rule, lhs_ac_c_free) in msig.st_rules.iter_with_lhs_ac_c_free() {
                    if lhs_ac_c_free {
                        // Head-symbol + arity precheck reproducing match_raw's
                        // first step for concrete-headed patterns
                        // (unification.rs `match_raw`, NoEq arm: `tf == pf &&
                        // targs.len() == pargs.len()`).  When the LHS is an
                        // `App`, a mismatched head or arity means `match_raw`
                        // yields `NoUnifier` (for NoEq/List patterns) — a
                        // definitive no-match — so skip the full
                        // `rule_applies` call.  A non-`App` LHS (bare Var/Lit)
                        // is not pre-skipped — the `if let` simply falls
                        // through to `rule_applies`.  An Ac-/C-free pattern
                        // never raises `NeedsAC` in `match_raw`, so this pure
                        // path is exactly HS's `solveMatchLNTerm` (no Maude
                        // involved).
                        if let Term::App(lhs_head, lhs_args) = &rule.lhs {
                            if lhs_head != sym || lhs_args.len() != args.len() {
                                continue;
                            }
                        }
                        if rule_applies(t, &rule.lhs, &rule.rhs) {
                            return false;
                        }
                    } else if let Some(hnd) = maude {
                        if rule_applies_ac(hnd, t, &rule.lhs, &rule.rhs) {
                            return false;
                        }
                    }
                    // Ac-/C-containing LHS with no handle (pure
                    // `nf_via_haskell`): the no-AC matcher could never match
                    // this rule, so it is skipped.
                }
            }
            // 4. Reducible exponent / inverse / mult / xor patterns.
            if let FunSym::NoEq(s) = sym {
                if s.name == EXP_SYM_STRING && args.len() == 2 {
                    // (a ^ b) ^ c → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0] {
                        if s2.name == EXP_SYM_STRING {
                            return false;
                        }
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
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0] {
                        if s2.name == INV_SYM_STRING {
                            return false;
                        }
                    }
                    // inv(mult(...)) where any factor is inverse → reducible
                    if let Term::App(FunSym::Ac(AcSym::Mult), inner_args) = &args[0] {
                        if inner_args.iter().any(crate::term::is_inverse) {
                            return false;
                        }
                    }
                    // inv(one) → reducible
                    if is_nullary(&args[0], ONE_SYM_STRING) {
                        return false;
                    }
                    return go_nf(&args[0], msig, maude);
                }
                if s.name == crate::function_symbols::PMULT_SYM_STRING && args.len() == 2 {
                    // pmult(_, pmult(_,_)) → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[1] {
                        if s2.name == crate::function_symbols::PMULT_SYM_STRING {
                            return false;
                        }
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
                        // contains one / DH_neutral, nested mult, or invalidMult → reducible
                        if args.iter().any(|a| is_nullary(a, ONE_SYM_STRING)) {
                            return false;
                        }
                        if args.iter().any(|a| is_nullary(a, DH_NEUTRAL_SYM_STRING)) {
                            return false;
                        }
                        if args.iter().any(crate::term::is_product) {
                            return false;
                        }
                        if invalid_mult(args) {
                            return false;
                        }
                        return args.iter().all(|a| go_nf(a, msig, maude));
                    }
                    AcSym::Xor => {
                        if args.iter().any(|a| is_nullary(a, ZERO_SYM_STRING)) {
                            return false;
                        }
                        if args.iter().any(is_xor) {
                            return false;
                        }
                        if invalid_xor(args) {
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
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0] {
                        if s2.name == crate::function_symbols::PMULT_SYM_STRING {
                            return false;
                        }
                    }
                    if let Term::App(FunSym::NoEq(s2), _) = &args[1] {
                        if s2.name == crate::function_symbols::PMULT_SYM_STRING {
                            return false;
                        }
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

/// `invalidMult` — HS `Norm.hs:115-121`.  Detects mult patterns that
/// are not in NF due to inverse cancellation.
fn invalid_mult(ts: &[LNTerm]) -> bool {
    use crate::function_symbols::AcSym;
    // Partition into (inverses, non-inverses).
    let (inverses, factors): (Vec<&LNTerm>, Vec<&LNTerm>) =
        ts.iter().partition(|t| crate::term::is_inverse(t));
    match inverses.len() {
        0 => false,
        1 => {
            // Single inverse: peel its inner.
            let inv_arg = match inverses[0] {
                Term::App(_, a) if !a.is_empty() => &a[0],
                _ => return false,
            };
            // Case: inv(mult(ifactors)) — check ifactors vs factors overlap
            if let Term::App(FunSym::Ac(AcSym::Mult), ifactors) = inv_arg {
                let ifactors_refs: Vec<&LNTerm> = ifactors.iter().collect();
                // (ifactors \\ factors /= ifactors) ||
                // (factors  \\ ifactors /= factors)
                // i.e. the multiset-difference removes something on either side.
                return multiset_diff_changes(&ifactors_refs, &factors)
                    || multiset_diff_changes(&factors, &ifactors_refs);
            }
            // Case: inv(t) — invalid if t `elem` factors.
            factors.iter().any(|f| **f == *inv_arg)
        }
        _ => true, // 2+ inverses → invalid
    }
}

/// Returns true iff multiset-difference `xs \\ ys` differs from `xs`,
/// i.e. at least one element of `xs` is also in `ys`.  Mirrors Haskell
/// `(\\)` (Data.List) on the underlying multisets.
fn multiset_diff_changes(xs: &[&LNTerm], ys: &[&LNTerm]) -> bool {
    let mut consumed: Vec<bool> = vec![false; ys.len()];
    let mut removed_any = false;
    for x in xs {
        for (i, y) in ys.iter().enumerate() {
            if !consumed[i] && **x == **y {
                consumed[i] = true;
                removed_any = true;
                break;
            }
        }
    }
    removed_any
}

/// `invalidXor` — HS `Norm.hs:123-126`.  True iff `ts` contains
/// duplicates.
fn invalid_xor(ts: &[LNTerm]) -> bool {
    // O(n^2) is fine here — typical xor arities are tiny.
    for i in 0..ts.len() {
        for j in (i + 1)..ts.len() {
            if ts[i] == ts[j] {
                return true;
            }
        }
    }
    false
}

/// `struleApplicable` — HS `Norm.hs:107-113`.  Returns true iff the
/// rule's LHS matches `t` AND the rule actually rewrites `t` to
/// something different.
fn rule_applies(t: &LNTerm, lhs: &LNTerm, rhs: &crate::subterm_rule::StRhs) -> bool {
    use crate::rewriting::Match;
    let problem = Match::match_with(t.clone(), lhs.clone());
    let matched =
        crate::unification::solve_match_lterm_no_ac(&|n| crate::lterm::sort_of_name(n), problem);
    matched.is_some() && strule_rewrites(t, rhs)
}

/// The `StRhs` disambiguation both `struleApplicable` ports apply once the
/// rule's LHS has matched `t`.
fn strule_rewrites(t: &LNTerm, rhs: &crate::subterm_rule::StRhs) -> bool {
    // HS (Norm.hs:110-113):
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

/// `struleApplicable` for a rule whose LHS contains Ac-/C-headed subterms:
/// the same HS `solveMatchLNTerm (t `matchWith` lhs)` semantics, with the
/// 3-way native matcher first and a Maude `match` only on `NeedsAc`
/// (mirroring HS `matchViaMaude` on `Left ACProblem`,
/// Term/Unification.hs:235-236), minus the `NeedsAc` pairs the module's
/// axioms already answer (see the root-symbol note below).  Subject vars
/// are rigid in the Maude `match` command on both sides of the port, so the
/// outcomes agree.
/// A Maude transport error is folded to "no match" — the conservative
/// answer (term stays NF), matching the port's other best-effort Maude
/// fallbacks (e.g. simplify.rs `match_atom_via_maude`).
fn rule_applies_ac(
    maude: &MaudeHandle,
    t: &LNTerm,
    lhs: &LNTerm,
    rhs: &crate::subterm_rule::StRhs,
) -> bool {
    use crate::rewriting::Match;
    use crate::unification::MatchOutcome;
    let problem = Match::match_with(t.clone(), lhs.clone());
    let matched = match crate::unification::solve_match_lterm(&crate::lterm::sort_of_name, problem)
    {
        MatchOutcome::NoMatcher => false,
        MatchOutcome::Matched(_) => true,
        MatchOutcome::NeedsAc => match (t, lhs) {
            // Two distinct AC root symbols have no matcher, so the pair is
            // answered here instead of over IPC.  `match P <=? S` solves
            // modulo the MSG module's AXIOMS, never its
            // `eq _ = _ [variant]` equations, and the only axioms any
            // operator carries there are `[comm assoc]` / `[comm]` — no
            // identity element is ever declared
            // (`maude_print.rs::op_ac`/`op_c` plus the user-AC `op` loop,
            // mirroring HS `theoryOpAC`/`theoryOpACUser`,
            // Parser.hs:217-267).  Commutativity and associativity each
            // carry the same symbol at the root of both sides, so the root
            // symbol is invariant across a term's axiom class, and no
            // instance of an `f`-rooted pattern is axiom-equal to a
            // `g`-rooted subject for `f /= g`.  `match_raw` reports
            // `NeedsAc` for *any* two AC-headed sides — it deliberately
            // does not compare the symbols, mirroring HS `matchRaw`
            // (Unification.hs:336-360, see line 356) — so the comparison
            // belongs here.
            (Term::App(FunSym::Ac(t_sym), _), Term::App(FunSym::Ac(lhs_sym), _))
                if t_sym != lhs_sym =>
            {
                false
            }
            _ => maude
                .match_eqs(&[crate::rewriting::Equal {
                    lhs: t.clone(),
                    rhs: lhs.clone(),
                }])
                .is_ok_and(|ms| !ms.is_empty()),
        },
    };
    matched && strule_rewrites(t, rhs)
}

// NOTE: `maybeNotNfSubterms` (HS `Term/Rewriting/Norm.hs:165-171`) lives
// in the solver, not here — see `contradictions.rs::maybe_not_nf_subterms`,
// which is the HS-faithful copy (it returns `[t]` for a bare `Lit (Var _)`,
// matching HS's `_ -> [t]` wildcard, and `[]` only for `Lit (Con _)`).

#[cfg(test)]
#[path = "norm_tests.rs"]
mod tests;
