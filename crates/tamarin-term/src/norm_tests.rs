// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_sig::pair_maude_sig;
use crate::vterm::Lit;

use tamarin_test_support::require_maude_path;

#[test]
fn invalid_mult_detects_only_cancellable_products() {
    use crate::builtin::{inv, msg_var, mult};

    let a = msg_var("a", 0);
    let b = msg_var("b", 0);
    let c = msg_var("c", 0);
    assert!(!invalid_mult(&[]));
    assert!(!invalid_mult(&[inv(a.clone()), b.clone()]));
    assert!(invalid_mult(&[inv(a.clone()), a.clone()]));
    assert!(invalid_mult(&[
        inv(mult(a.clone(), b.clone())),
        b.clone(),
        c.clone()
    ]));
    assert!(invalid_mult(&[inv(a), inv(b)]));

    // Even an invariant-bypassing nullary `inv` still counts as an inverse
    // for the two-inverses rejection rule.
    let malformed_inv =
        crate::term::unsafe_f_app(FunSym::NoEq(crate::function_symbols::inv_sym()), Vec::new());
    assert!(invalid_mult(&[malformed_inv, inv(c)]));
}

#[test]
fn invalid_xor_handles_canonical_and_unsafe_argument_order() {
    use crate::builtin::msg_var;

    let a = msg_var("a", 0);
    let b = msg_var("b", 1);
    let c = msg_var("c", 2);
    assert!(!invalid_xor(&[a.clone(), b.clone(), c]));
    assert!(invalid_xor(&[a.clone(), a.clone(), b.clone()]));
    assert!(invalid_xor(&[a.clone(), b, a]));
}

#[test]
fn norm_var_skips_maude() {
    let path = match require_maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let v = LVar::new("x", LSort::Msg, 0);
    let t: LNTerm = Term::Lit(Lit::Var(v));
    let n = norm(&h, &t).unwrap();
    assert_eq!(t, n);
}

#[test]
#[allow(non_snake_case)]
fn nf_via_haskell_detects_inverse_cancellation() {
    let path = match require_maude_path() {
        Some(p) => p,
        None => return,
    };
    let mut sig = crate::maude_sig::pair_maude_sig();
    sig.enable_dh = true;
    sig = sig.refresh();
    let h = MaudeHandle::start(&path, sig.clone()).unwrap();
    let tid = LVar::new("tid", LSort::Fresh, 0);
    let ekI = LVar::new("ekI", LSort::Fresh, 0);
    let ekR = LVar::new("ekR", LSort::Fresh, 0);
    let tid_term: LNTerm = Term::Lit(Lit::Var(tid));
    let ekI_term: LNTerm = Term::Lit(Lit::Var(ekI));
    let ekR_term: LNTerm = Term::Lit(Lit::Var(ekR));
    let inv_tid: LNTerm = Term::App(
        FunSym::NoEq(crate::function_symbols::inv_sym()),
        vec![tid_term.clone()].into(),
    );
    let mult: LNTerm = Term::App(
        FunSym::Ac(AcSym::Mult),
        vec![tid_term, ekI_term, ekR_term, inv_tid].into(),
    );
    // Test: mult(tid, ekI, ekR, inv(tid)) should NOT be in NF
    // (invalid_mult fires because tid appears as a factor and inside inv).
    assert!(
        !nf_via_haskell(&h.maude_sig(), &mult),
        "mult(tid, ekI, ekR, inv(tid)) should be non-NF"
    );
}

// `nf_via_haskell_maude` must detect reducibility through user-`[AC]`
// cancellation equations, whose st-rule LHSes are Ac-headed and thus
// invisible to the pure no-AC matcher (csf26-ac CRxor: `xorr/2 [AC]`
// with `xorr(x, x) = zeroo` and `xorr(xorr(x, y), x) = y`).  Without
// the Maude-backed st-rule arm, split cases whose substitution creates
// `xorr(~k, ~k, …)` survive `substCreatesNonNormalTerms`, inflating
// the `splitEqs` case set (6 RS cases vs 2 HS) and flipping the
// `isSplitGoalSmall` goal ranking.
#[test]
fn nf_via_haskell_maude_matches_user_ac_strule() {
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::rewriting::RRule;
    let path = match require_maude_path() {
        Some(p) => p,
        None => return,
    };
    let xorr = AcFctSym::new(
        b"xorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    let zeroo_sym = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let mut sig = crate::maude_sig::pair_maude_sig();
    sig.st_ac_fun_syms.insert(xorr);
    sig.st_fun_syms.insert(zeroo_sym);
    let x = crate::builtin::msg_var("x", 0);
    let y = crate::builtin::msg_var("y", 0);
    let zeroo: LNTerm = crate::term::f_app_no_eq(zeroo_sym, vec![]);
    // xorr(x, x) = zeroo  and  xorr(xorr(x, y), x) = y.
    let lhs1 = crate::term::f_app_acfct(xorr, vec![x.clone(), x.clone()]);
    let lhs2 = crate::term::f_app_acfct(
        xorr,
        vec![
            crate::term::f_app_acfct(xorr, vec![x.clone(), y.clone()]),
            x.clone(),
        ],
    );
    sig.st_rules.insert(
        crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(lhs1, zeroo))
            .expect("ground-RHS st rule"),
    );
    sig.st_rules.insert(
        crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(lhs2, y))
            .expect("subterm-RHS st rule"),
    );
    let sig = sig.refresh();
    let h = MaudeHandle::start(&path, sig).unwrap();
    let k = crate::builtin::fresh_var("k", 0);
    let na = crate::builtin::fresh_var("na", 0);
    let w = crate::builtin::msg_var("w", 0);
    // xorr(~k, ~k): matches xorr(x, x) → non-NF (Maude AC match).
    let dup = crate::term::f_app_acfct(xorr, vec![k.clone(), k.clone()]);
    assert!(
        !nf_via_haskell_maude(&h, &dup),
        "xorr(~k, ~k) must be non-NF via the AC st-rule match"
    );
    // The pure entry point cannot see the Ac-headed rule — documents
    // why handle-holding callers must use the Maude variant.
    assert!(
        nf_via_haskell(&h.maude_sig(), &dup),
        "pure nf_via_haskell has no AC matcher for Ac-headed st rules"
    );
    // xorr(~k, ~k, w): 3-arg flattened form, matches xorr(x, x, y)
    // (the flattened second rule) → non-NF.
    let dup3 = crate::term::f_app_acfct(xorr, vec![k.clone(), k.clone(), w]);
    assert!(
        !nf_via_haskell_maude(&h, &dup3),
        "xorr(~k, ~k, w) must be non-NF via the flattened cancellation rule"
    );
    // xorr(~k, ~na): no duplicate — stays NF.
    let ok = crate::term::f_app_acfct(xorr, vec![k, na]);
    assert!(
        nf_via_haskell_maude(&h, &ok),
        "xorr(~k, ~na) must remain NF"
    );
}

// A term rooted at one user-`[AC]` symbol is never reducible by an st
// rule rooted at a different one, however similarly shaped: `match`
// solves modulo the MSG module's `[comm assoc]` axioms, which preserve
// the root symbol.  `rule_applies_ac` answers that pair itself; this
// pins both halves — the answer, and Maude's agreement with it.
#[test]
fn cross_ac_symbol_strule_never_applies() {
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::rewriting::{Equal, RRule};
    let path = match require_maude_path() {
        Some(p) => p,
        None => return,
    };
    let xorr = AcFctSym::new(
        b"xorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    let yorr = AcFctSym::new(
        b"yorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    let zeroo_sym = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let mut sig = crate::maude_sig::pair_maude_sig();
    sig.st_ac_fun_syms.insert(xorr);
    sig.st_ac_fun_syms.insert(yorr);
    sig.st_fun_syms.insert(zeroo_sym);
    let x = crate::builtin::msg_var("x", 0);
    let zeroo: LNTerm = crate::term::f_app_no_eq(zeroo_sym, vec![]);
    // `xorr(x, x) = zeroo` and `yorr(x, zeroo) = x`.  Both roots must
    // head a rule, else the term takes `go_nf`'s irreducible-top arm and
    // the st-rule loop never runs.
    let x_rule_lhs = crate::term::f_app_acfct(xorr, vec![x.clone(), x.clone()]);
    let y_rule_lhs = crate::term::f_app_acfct(yorr, vec![x.clone(), zeroo.clone()]);
    sig.st_rules.insert(
        crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(x_rule_lhs.clone(), zeroo.clone()))
            .expect("ground-RHS st rule"),
    );
    sig.st_rules.insert(
        crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(y_rule_lhs, x))
            .expect("subterm-RHS st rule"),
    );
    let sig = sig.refresh();
    let h = MaudeHandle::start(&path, sig).unwrap();
    let k = crate::builtin::fresh_var("k", 0);
    let dup = crate::term::f_app_acfct(yorr, vec![k.clone(), k.clone()]);
    assert!(
        nf_via_haskell_maude(&h, &dup),
        "yorr(~k, ~k) must stay NF — the xorr rule cannot reach it"
    );
    // The yorr rule itself still fires, so the term above is NF because
    // of the AC symbols, not because the st-rule loop went quiet.
    let cancels = crate::term::f_app_acfct(yorr, vec![k, zeroo]);
    assert!(
        !nf_via_haskell_maude(&h, &cancels),
        "yorr(~k, zeroo) must be non-NF via its own rule"
    );
    // The pattern is non-ground, so this is a real Maude round-trip and
    // not the ground short-circuit in `match_eqs`.
    assert!(
        h.match_eqs(&[Equal {
            lhs: dup,
            rhs: x_rule_lhs,
        }])
        .expect("maude match")
        .is_empty(),
        "maude must report no match for a pattern rooted at another AC symbol"
    );
}

/// Both of HS's st-rule arms are guarded on the top symbol's kind —
/// `FAppNoEq _ _` and `FAppACfct _ _` (Norm.hs:73-74) — so a term headed
/// by a builtin AC operator or by `em` never reaches `struleApplicable`,
/// however permissive the rule's LHS.  The sharpest witness is an st rule
/// whose LHS is a bare variable: it matches every subject term, so an
/// ungated loop would report every `Mult`/`Xor`/`Union`/`NatPlus`/`em`
/// term reducible where HS reports normal form.  The gate has to sit above
/// the pure/Maude matcher split, since a variable LHS is Ac/C-free and so
/// takes the pure arm on both entry points.
///
/// The rule is built directly because the text frontend cannot produce it:
/// `rrule_to_ctxt_st_rule`'s ground-RHS branch rejects a bare-literal LHS
/// outright (the deliberate divergence from HS's non-exhaustive
/// `constantPositions`, SubtermRule.hs:67-71), and its non-ground branch
/// rejects because every position it can find inside a variable LHS is the
/// empty one.  `CtxtStRule` is `pub`, so the gate is what keeps `go_nf`
/// HS-faithful for any in-process constructor.
#[test]
fn bare_variable_strule_lhs_never_reduces_builtin_ac_or_c_terms() {
    use crate::builtin::{emap, fresh_var, fst, msg_var};
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::{f_app_ac, f_app_no_eq};
    let zeroo_sym = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let mut sig = pair_maude_sig();
    sig.st_fun_syms.insert(zeroo_sym);
    // `x = zeroo`: bare-variable LHS, ground RHS, empty positions — the
    // `StRhs [] s` arm of `strule_rewrites`, which reduces every term that
    // is not `zeroo` itself.
    sig.st_rules.insert(CtxtStRule::new(
        msg_var("x", 0),
        StRhs {
            positions: Vec::new(),
            term: f_app_no_eq(zeroo_sym, vec![]),
        },
    ));
    let sig = sig.refresh();
    let k = fresh_var("k", 0);
    let na = fresh_var("na", 0);
    let subjects = [
        f_app_ac(AcSym::Mult, vec![k.clone(), na.clone()]),
        f_app_ac(AcSym::Xor, vec![k.clone(), na.clone()]),
        f_app_ac(AcSym::Union, vec![k.clone(), na.clone()]),
        f_app_ac(AcSym::NatPlus, vec![k.clone(), na.clone()]),
        emap(k.clone(), na.clone()),
    ];
    // Arm 1: no handle — the rule's LHS is Ac/C-free, so this is the pure
    // matcher's arm, the one whose head+arity precheck a non-`App` LHS
    // slips past.
    for s in &subjects {
        assert!(
            nf_via_haskell(&sig, s),
            "builtin-AC-/C-headed terms are not offered to struleApplicable: {s:?}"
        );
    }
    // Control: a NoEq-headed term IS offered, so HS's `FAppNoEq _ _` arm
    // fires and the rule reduces it — the loop is gated, not inert.
    let fst_k = fst(k.clone());
    assert!(
        !nf_via_haskell(&sig, &fst_k),
        "a NoEq-headed term must still reach the st-rule loop"
    );
    // Arm 2: same verdicts with a handle in hand.  The handle carries the
    // plain pairing signature rather than `sig`: emitting `eq x = zeroo
    // [variant]` into the MSG module makes every Maude `reduce` diverge
    // (the Haskell prover hangs on the equivalent `.spthy`), and the gate
    // means no rule of `sig` is ever sent over IPC anyway.
    let path = match require_maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    for s in &subjects {
        assert!(
            nf_via_haskell_maude_with_sig(&sig, &h, s),
            "the Maude-backed arm applies the same kind gate: {s:?}"
        );
    }
    assert!(
        !nf_via_haskell_maude_with_sig(&sig, &h, &fst_k),
        "a NoEq-headed term must still reach the st-rule loop"
    );
}

/// `go_nf`'s st-rule arm reads the Ac/C-free flag each `st_rules` entry
/// carries, so the flag it sees always belongs to the rule it is matching.
/// An insert that never reaches `refresh` cannot shift a flag onto its
/// neighbour: the Ac-headed rule added here sorts among the pairing rules,
/// and both verdicts (`fst(pair(x1, x2))` reducible, `pair(x1, x2)` normal)
/// survive it.  No Maude handle needed — the pairing rule LHSes are
/// Ac/C-free, and the pure entry point skips the Ac-headed one.
#[test]
fn go_nf_reads_each_rule_s_own_lhs_flag() {
    use crate::builtin::{fst, msg_var, pair};
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::rewriting::RRule;
    let mut sig = pair_maude_sig();
    let reducible = fst(pair(msg_var("x", 1), msg_var("x", 2)));
    let normal = pair(msg_var("x", 1), msg_var("x", 2));
    assert!(!nf_via_haskell(&sig, &reducible));
    assert!(nf_via_haskell(&sig, &normal));

    // `xorr(x, x) = zeroo`, whose LHS is Ac-headed (flag `false`).
    let xorr = AcFctSym::new(
        b"xorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    let zeroo_sym = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let x = crate::builtin::msg_var("x", 0);
    let ac_rule = crate::subterm_rule::rrule_to_ctxt_st_rule(&RRule::new(
        crate::term::f_app_acfct(xorr, vec![x.clone(), x]),
        crate::term::f_app_no_eq(zeroo_sym, vec![]),
    ))
    .expect("ground-RHS st rule");
    sig.st_rules.insert(ac_rule);
    assert_eq!(
        sig.st_rules
            .iter_with_lhs_ac_c_free()
            .map(|(r, f)| (crate::maude_proc::term_ac_c_free(&r.lhs), f))
            .filter(|(want, got)| want != got)
            .count(),
        0,
        "every flag must describe the rule it is paired with"
    );
    assert!(!nf_via_haskell(&sig, &reducible));
    assert!(nf_via_haskell(&sig, &normal));
}
