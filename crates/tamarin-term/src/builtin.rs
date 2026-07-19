// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, beschmi, jdreier, PhilipLukertWork, charlie-j, BTom-GH,
//   rsasse, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Builtin/Convenience.hs,
//   lib/term/src/Term/Builtin/Rules.hs, lib/term/src/Term/Term.hs

//! Port of `Term.Builtin.{Signature, Convenience, Rules}` from
//! `lib/term/src/Term/Builtin/`.
//!
//! Predefined function symbols, smart constructors, and rewrite-rule sets
//! for the prover's built-in equational theories. Function symbols and
//! signatures cover DH, BP, XOR, multiset, pair, encryption, signatures,
//! hashing, and location reports; rewrite-rule sets are ported for DH, BP,
//! XOR, multiset, pair, encryption, and signatures. The `Rules.hs`
//! destructor / location sets are ported too: `location_report_rules`,
//! `pair_dest_rules` (covering the `fstDestRule`/`sndDestRule` shapes),
//! `sym_enc_dest_rules`, and `asym_enc_dest_rules`.

use std::collections::BTreeSet;

use crate::function_symbols::{
    AcSym, Constructability, NoEqFunSig, NoEqSym, Privacy,
};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::rewriting::RRule;
use crate::term::{f_app_ac, f_app_no_eq, Term};
use crate::vterm::var_term;

// =============================================================================
// Builtin NoEq symbols
// =============================================================================

fn pub_ctor(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
}
fn priv_ctor(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Private, Constructability::Constructor)
}
fn pub_dest(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Destructor)
}

pub fn sdec_sym() -> NoEqSym { pub_ctor(b"sdec", 2) }
pub fn senc_sym() -> NoEqSym { pub_ctor(b"senc", 2) }
pub fn adec_sym() -> NoEqSym { pub_ctor(b"adec", 2) }
pub fn aenc_sym() -> NoEqSym { pub_ctor(b"aenc", 2) }
pub fn sign_sym() -> NoEqSym { pub_ctor(b"sign", 2) }
pub fn reveal_sign_sym() -> NoEqSym { pub_ctor(b"revealSign", 2) }
pub fn rep_sym() -> NoEqSym { priv_ctor(b"rep", 2) }
pub fn check_rep_sym() -> NoEqSym { pub_dest(b"check_rep", 2) }
pub fn verify_sym() -> NoEqSym { pub_ctor(b"verify", 3) }
pub fn reveal_verify_sym() -> NoEqSym { pub_ctor(b"revealVerify", 3) }
pub fn pk_sym() -> NoEqSym { pub_ctor(b"pk", 1) }
pub fn hash_sym() -> NoEqSym { pub_ctor(b"h", 1) }
pub fn extract_message_sym() -> NoEqSym { pub_ctor(b"getMessage", 1) }
pub fn get_rep_sym() -> NoEqSym { pub_dest(b"get_rep", 1) }
pub fn report_sym() -> NoEqSym { pub_ctor(b"report", 1) }
pub fn true_sym() -> NoEqSym { pub_ctor(b"true", 0) }

pub fn sdec_dest_sym() -> NoEqSym { sdec_sym().with_destructor() }
pub fn adec_dest_sym() -> NoEqSym { adec_sym().with_destructor() }
pub fn verify_dest_sym() -> NoEqSym { verify_sym().with_destructor() }

// =============================================================================
// Builtin signatures
// =============================================================================

fn sig(items: impl IntoIterator<Item = NoEqSym>) -> NoEqFunSig {
    items.into_iter().collect()
}

pub fn sym_enc_fun_sig() -> NoEqFunSig { sig([sdec_sym(), senc_sym()]) }
pub fn asym_enc_fun_sig() -> NoEqFunSig { sig([adec_sym(), aenc_sym(), pk_sym()]) }
pub fn signature_fun_sig() -> NoEqFunSig {
    sig([sign_sym(), verify_sym(), true_sym(), pk_sym()])
}
pub fn reveal_signature_fun_sig() -> NoEqFunSig {
    sig([reveal_sign_sym(), reveal_verify_sym(), extract_message_sym(), true_sym(), pk_sym()])
}
pub fn location_report_fun_sig() -> NoEqFunSig {
    sig([rep_sym(), check_rep_sym(), get_rep_sym(), report_sym()])
}
pub fn hash_fun_sig() -> NoEqFunSig { sig([hash_sym()]) }
pub fn sym_enc_fun_dest_sig() -> NoEqFunSig { sig([sdec_dest_sym(), senc_sym()]) }
pub fn asym_enc_fun_dest_sig() -> NoEqFunSig { sig([adec_dest_sym(), aenc_sym(), pk_sym()]) }
pub fn signature_fun_dest_sig() -> NoEqFunSig {
    sig([sign_sym(), verify_dest_sym(), true_sym(), pk_sym()])
}

// =============================================================================
// Convenience smart constructors over `Term<A>`
// =============================================================================

pub fn mult<A: Ord + Clone>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_ac(AcSym::Mult, vec![a, b])
}
pub fn union<A: Ord + Clone>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_ac(AcSym::Union, vec![a, b])
}
pub fn xor<A: Ord + Clone>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_ac(AcSym::Xor, vec![a, b])
}
/// Mirrors `Convenience.hs` `(++:)`; retained for AC-constructor family
/// completeness, no caller yet.
pub fn nat_plus<A: Ord + Clone>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_ac(AcSym::NatPlus, vec![a, b])
}

pub fn adec<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(adec_sym(), vec![a, b])
}
pub fn aenc<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(aenc_sym(), vec![a, b])
}
pub fn sdec<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(sdec_sym(), vec![a, b])
}
pub fn senc<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(senc_sym(), vec![a, b])
}
pub fn sign<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(sign_sym(), vec![a, b])
}
pub fn verify<A>(a: Term<A>, b: Term<A>, c: Term<A>) -> Term<A> {
    f_app_no_eq(verify_sym(), vec![a, b, c])
}
pub fn pk<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(pk_sym(), vec![a])
}
pub fn hash<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(hash_sym(), vec![a])
}
pub fn true_const<A>() -> Term<A> {
    f_app_no_eq(true_sym(), vec![])
}

pub fn pair<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(crate::function_symbols::pair_sym(), vec![a, b])
}
pub fn fst<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(crate::function_symbols::fst_sym(), vec![a])
}
pub fn snd<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(crate::function_symbols::snd_sym(), vec![a])
}

pub fn exp<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(crate::function_symbols::exp_sym(), vec![a, b])
}
pub fn inv<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(crate::function_symbols::inv_sym(), vec![a])
}
pub fn one_const<A>() -> Term<A> {
    f_app_no_eq(crate::function_symbols::one_sym(), vec![])
}
pub fn dh_neutral<A>() -> Term<A> {
    f_app_no_eq(crate::function_symbols::dh_neutral_sym(), vec![])
}
pub fn zero_const<A>() -> Term<A> {
    f_app_no_eq(crate::function_symbols::zero_sym(), vec![])
}
pub fn pmult<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(crate::function_symbols::pmult_sym(), vec![a, b])
}
pub fn emap<A: Ord + Clone>(a: Term<A>, b: Term<A>) -> Term<A> {
    crate::term::f_app_c(crate::function_symbols::CSym::EMap, vec![a, b])
}

pub fn msg_var(name: &str, idx: u64) -> LNTerm {
    var_term(LVar::new(name, LSort::Msg, idx))
}
pub fn fresh_var(name: &str, idx: u64) -> LNTerm {
    var_term(LVar::new(name, LSort::Fresh, idx))
}
pub fn pub_var(name: &str, idx: u64) -> LNTerm {
    var_term(LVar::new(name, LSort::Pub, idx))
}

// =============================================================================
// Builtin rewrite rules
// =============================================================================

fn rule(lhs: LNTerm, rhs: LNTerm) -> RRule<LNTerm> {
    RRule::new(lhs, rhs)
}

/// `dhRules`: Lankford's presentation of Diffie-Hellman with the finite
/// variant property.
pub fn dh_rules() -> BTreeSet<RRule<LNTerm>> {
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let x3 = msg_var("x", 3);
    let one = one_const::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let neutral = dh_neutral::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let mut s = BTreeSet::new();
    s.insert(rule(exp(x1.clone(), one.clone()), x1.clone()));
    s.insert(rule(
        exp(exp(x1.clone(), x2.clone()), x3.clone()),
        exp(x1.clone(), mult(x2.clone(), x3.clone())),
    ));
    s.insert(rule(exp(neutral.clone(), x1.clone()), neutral.clone()));
    s.insert(rule(mult(x1.clone(), one.clone()), x1.clone()));
    s.insert(rule(inv(inv(x1.clone())), x1.clone()));
    s.insert(rule(inv(one.clone()), one.clone()));
    s.insert(rule(mult(x1.clone(), inv(x1.clone())), one.clone()));
    s.insert(rule(
        mult(inv(x1.clone()), inv(x2.clone())),
        inv(mult(x1.clone(), x2.clone())),
    ));
    s.insert(rule(
        mult(inv(mult(x1.clone(), x2.clone())), x2.clone()),
        inv(x1.clone()),
    ));
    s.insert(rule(
        inv(mult(inv(x1.clone()), x2.clone())),
        mult(x1.clone(), inv(x2.clone())),
    ));
    s.insert(rule(
        mult(x1.clone(), mult(inv(x1.clone()), x2.clone())),
        x2.clone(),
    ));
    s.insert(rule(
        mult(inv(x1.clone()), mult(inv(x2.clone()), x3.clone())),
        mult(inv(mult(x1.clone(), x2.clone())), x3.clone()),
    ));
    s.insert(rule(
        mult(inv(mult(x1.clone(), x2.clone())), mult(x2.clone(), x3.clone())),
        mult(inv(x1.clone()), x3.clone()),
    ));
    s
}

/// `xorRules`: Xor presentation with the finite variant property.
pub fn xor_rules() -> BTreeSet<RRule<LNTerm>> {
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let zero = zero_const::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let mut s = BTreeSet::new();
    s.insert(rule(xor(x1.clone(), zero.clone()), x1.clone()));
    s.insert(rule(xor(x1.clone(), x1.clone()), zero.clone()));
    s.insert(rule(xor(x1.clone(), xor(x1.clone(), x2.clone())), x2.clone()));
    s
}

/// `bpRules`: bilinear-pairing rules (extends `dh_rules`).
pub fn bp_rules() -> BTreeSet<RRule<LNTerm>> {
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let x3 = msg_var("x", 3);
    let one = one_const::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let mut s = BTreeSet::new();
    s.insert(rule(pmult(one.clone(), x1.clone()), x1.clone()));
    s.insert(rule(
        pmult(x3.clone(), pmult(x2.clone(), x1.clone())),
        pmult(mult(x3.clone(), x2.clone()), x1.clone()),
    ));
    s.insert(rule(
        emap(x1.clone(), pmult(x2.clone(), x3.clone())),
        exp(emap(x1.clone(), x3.clone()), x2.clone()),
    ));
    s
}

/// `msetRules`: multisets have no rewrite rules.
pub fn mset_rules() -> BTreeSet<RRule<LNTerm>> { BTreeSet::new() }

// =============================================================================
// Builtin subterm rules — direct port of `Term.Builtin.Rules`
// =============================================================================
//
// These return `CtxtStRule` directly (with explicit RHS positions) so the
// `MaudeSig.st_rules` field can carry them through to
// `subtermIntruderRules` / `destructionRules`.  Without these,
// `[ symmetric-encryption ]` etc. signatures have no rewrite rules,
// so the intruder-rule generator can't emit decryption destructors —
// crypto-protocol corpus lemmas trip up.

/// `pairRules`: `fst(<x, y>) = x`, `snd(<x, y>) = y`.
pub fn pair_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        fst(pair(x1.clone(), x2.clone())),
        StRhs { positions: vec![vec![0, 0]], term: x1.clone() },
    ));
    s.insert(CtxtStRule::new(
        snd(pair(x1.clone(), x2.clone())),
        StRhs { positions: vec![vec![0, 1]], term: x2 },
    ));
    s
}

/// `pairDestRules` (Rules.hs:115-115): the DESTRUCTOR variant of
/// `pair_rules`, used by the `dest-pairing` builtin.  Same rewrite
/// shapes as `fstRule`/`sndRule` but rooted at the destructor symbols:
/// `fstDest(pair(x1,x2)) = x1` (`fstDestRule`) and
/// `sndDest(pair(x1,x2)) = x2` (`sndDestRule`).
pub fn pair_dest_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        f_app_no_eq(crate::function_symbols::fst_dest_sym(),
                    vec![pair(x1.clone(), x2.clone())]),
        StRhs { positions: vec![vec![0, 0]], term: x1.clone() },
    ));
    s.insert(CtxtStRule::new(
        f_app_no_eq(crate::function_symbols::snd_dest_sym(),
                    vec![pair(x1.clone(), x2.clone())]),
        StRhs { positions: vec![vec![0, 1]], term: x2 },
    ));
    s
}

/// `symEncRules`: `sdec(senc(x, y), y) = x`.
pub fn sym_enc_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        sdec(senc(x1.clone(), x2.clone()), x2),
        StRhs { positions: vec![vec![0, 0]], term: x1 },
    ));
    s
}

/// `asymEncRules`: `adec(aenc(x, pk(y)), y) = x`.
pub fn asym_enc_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        adec(aenc(x1.clone(), pk(x2.clone())), x2),
        StRhs { positions: vec![vec![0, 0]], term: x1 },
    ));
    s
}

/// `signatureRules`: `verify(sign(x, y), x, pk(y)) = true`.
pub fn signature_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let true_term: LNTerm = true_const::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        verify(sign(x1.clone(), x2.clone()), x1, pk(x2)),
        StRhs { positions: vec![vec![0, 0]], term: true_term },
    ));
    s
}

/// `locationReportRules` (Rules.hs:112-114): `check_rep(rep(x1,x2), x2) = x1`
/// and `get_rep(rep(x1,x2)) = x1`.  Used by the `locations-report` builtin.
pub fn location_report_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        f_app_no_eq(check_rep_sym(),
            vec![f_app_no_eq(rep_sym(), vec![x1.clone(), x2.clone()]), x2.clone()]),
        StRhs { positions: vec![vec![0, 0]], term: x1.clone() },
    ));
    s.insert(CtxtStRule::new(
        f_app_no_eq(get_rep_sym(),
            vec![f_app_no_eq(rep_sym(), vec![x1.clone(), x2.clone()])]),
        StRhs { positions: vec![vec![0, 0]], term: x1 },
    ));
    s
}

/// `symEncDestRules` (Rules.hs:116-116): `sdecDest(senc(x1,x2), x2) = x1` —
/// the DESTRUCTOR variant of `sym_enc_rules`, used by the
/// `dest-symmetric-encryption` builtin.
pub fn sym_enc_dest_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        f_app_no_eq(sdec_dest_sym(), vec![senc(x1.clone(), x2.clone()), x2]),
        StRhs { positions: vec![vec![0, 0]], term: x1 },
    ));
    s
}

/// `asymEncDestRules` (Rules.hs:117-117): `adecDest(aenc(x1, pk(x2)), x2) = x1`
/// — the DESTRUCTOR variant of `asym_enc_rules`, used by the
/// `dest-asymmetric-encryption` builtin.
pub fn asym_enc_dest_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        f_app_no_eq(adec_dest_sym(), vec![aenc(x1.clone(), pk(x2.clone())), x2]),
        StRhs { positions: vec![vec![0, 0]], term: x1 },
    ));
    s
}

/// `revealSignatureRules`: `revealVerify(revealSign(x,y), x, pk(y)) = true`
/// plus `getMessage(revealSign(x,y)) = x`.  Mirrors
/// `Term.Builtin.Rules.revealSignatureRules` (Rules.hs:110-111).
pub fn reveal_signature_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let true_term: LNTerm = true_const::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let mut s = BTreeSet::new();
    let reveal_sign_term = f_app_no_eq(reveal_sign_sym(), vec![x1.clone(), x2.clone()]);
    s.insert(CtxtStRule::new(
        f_app_no_eq(reveal_verify_sym(),
            vec![reveal_sign_term.clone(), x1.clone(), pk(x2)]),
        StRhs { positions: vec![vec![0, 0]], term: true_term },
    ));
    s.insert(CtxtStRule::new(
        f_app_no_eq(extract_message_sym(), vec![reveal_sign_term]),
        StRhs { positions: vec![vec![0, 0]], term: x1 },
    ));
    s
}

/// `signatureDestRules`: `verifyDest(sign(x, y), x, pk(y)) = true`.
/// Mirrors `Term.Builtin.Rules.signatureDestRules` (Rules.hs:118-118).
pub fn signature_dest_rules() -> BTreeSet<crate::subterm_rule::CtxtStRule> {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let x1 = msg_var("x", 1);
    let x2 = msg_var("x", 2);
    let true_term: LNTerm = true_const::<crate::vterm::Lit<crate::lterm::Name, LVar>>();
    let mut s = BTreeSet::new();
    s.insert(CtxtStRule::new(
        f_app_no_eq(verify_dest_sym(),
            vec![sign(x1.clone(), x2.clone()), x1, pk(x2)]),
        StRhs { positions: vec![vec![0, 0]], term: true_term },
    ));
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::FunSym;

    #[test]
    fn dh_rule_count_matches_haskell() {
        // Haskell's S.fromList of 13 unique rules.
        assert_eq!(dh_rules().len(), 13);
    }

    #[test]
    fn xor_rule_count() {
        assert_eq!(xor_rules().len(), 3);
    }

    #[test]
    fn bp_rule_count() {
        assert_eq!(bp_rules().len(), 3);
    }

    #[test]
    fn convenience_constructors_compose() {
        let m: LNTerm = mult(msg_var("x", 0), msg_var("y", 0));
        if let Term::App(FunSym::Ac(AcSym::Mult), ts) = m {
            assert_eq!(ts.len(), 2);
        } else { panic!(); }
    }

    #[test]
    fn signatures_have_right_arities() {
        assert!(asym_enc_fun_sig().contains(&aenc_sym()));
        assert!(asym_enc_fun_sig().contains(&pk_sym()));
        assert_eq!(verify_sym().arity, 3);
    }
}
