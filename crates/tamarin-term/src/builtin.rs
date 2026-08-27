// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Builtin.{Signature, Convenience, Rules}` from
//! `lib/term/src/Term/Builtin/`.
//!
//! Predefined function symbols, smart constructors, and rewrite-rule sets
//! for the prover's built-in equational theories: DH, BP, XOR, multiset,
//! pair, encryption, signatures, hashing, and location reports — including
//! the `dest-*` builtins' destructor-rooted rule variants
//! (`pair_dest_rules`, `sym_enc_dest_rules`, `asym_enc_dest_rules`,
//! `signature_dest_rules`).

use std::collections::BTreeSet;

use crate::function_symbols::{
    dh_neutral_sym, exp_sym, fst_dest_sym, fst_sym, inv_sym, one_sym, pair_sym, pmult_sym,
    snd_dest_sym, snd_sym, zero_sym, AcSym, CSym, Constructability, NoEqFunSig, NoEqSym, Privacy,
};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::positions::Position;
use crate::rewriting::RRule;
use crate::subterm_rule::{CtxtStRule, StRhs};
use crate::term::{f_app_ac, f_app_c, f_app_no_eq, Term};
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

pub fn sdec_sym() -> NoEqSym {
    pub_ctor(b"sdec", 2)
}
pub fn senc_sym() -> NoEqSym {
    pub_ctor(b"senc", 2)
}
pub fn adec_sym() -> NoEqSym {
    pub_ctor(b"adec", 2)
}
pub fn aenc_sym() -> NoEqSym {
    pub_ctor(b"aenc", 2)
}
pub fn sign_sym() -> NoEqSym {
    pub_ctor(b"sign", 2)
}
pub fn reveal_sign_sym() -> NoEqSym {
    pub_ctor(b"revealSign", 2)
}
pub fn rep_sym() -> NoEqSym {
    priv_ctor(b"rep", 2)
}
pub fn check_rep_sym() -> NoEqSym {
    pub_dest(b"check_rep", 2)
}
pub fn verify_sym() -> NoEqSym {
    pub_ctor(b"verify", 3)
}
pub fn reveal_verify_sym() -> NoEqSym {
    pub_ctor(b"revealVerify", 3)
}
pub fn pk_sym() -> NoEqSym {
    pub_ctor(b"pk", 1)
}
pub fn hash_sym() -> NoEqSym {
    pub_ctor(b"h", 1)
}
pub fn extract_message_sym() -> NoEqSym {
    pub_ctor(b"getMessage", 1)
}
pub fn get_rep_sym() -> NoEqSym {
    pub_dest(b"get_rep", 1)
}
pub fn report_sym() -> NoEqSym {
    pub_ctor(b"report", 1)
}
pub fn true_sym() -> NoEqSym {
    pub_ctor(b"true", 0)
}

pub fn sdec_dest_sym() -> NoEqSym {
    sdec_sym().with_destructor()
}
pub fn adec_dest_sym() -> NoEqSym {
    adec_sym().with_destructor()
}
pub fn verify_dest_sym() -> NoEqSym {
    verify_sym().with_destructor()
}

// =============================================================================
// Builtin signatures
// =============================================================================

fn set_of<T: Ord>(items: impl IntoIterator<Item = T>) -> BTreeSet<T> {
    items.into_iter().collect()
}

pub fn sym_enc_fun_sig() -> NoEqFunSig {
    set_of([sdec_sym(), senc_sym()])
}
pub fn asym_enc_fun_sig() -> NoEqFunSig {
    set_of([adec_sym(), aenc_sym(), pk_sym()])
}
pub fn signature_fun_sig() -> NoEqFunSig {
    set_of([sign_sym(), verify_sym(), true_sym(), pk_sym()])
}
pub fn reveal_signature_fun_sig() -> NoEqFunSig {
    set_of([
        reveal_sign_sym(),
        reveal_verify_sym(),
        extract_message_sym(),
        true_sym(),
        pk_sym(),
    ])
}
pub fn location_report_fun_sig() -> NoEqFunSig {
    set_of([rep_sym(), check_rep_sym(), get_rep_sym(), report_sym()])
}
pub fn hash_fun_sig() -> NoEqFunSig {
    set_of([hash_sym()])
}
pub fn sym_enc_fun_dest_sig() -> NoEqFunSig {
    set_of([sdec_dest_sym(), senc_sym()])
}
pub fn asym_enc_fun_dest_sig() -> NoEqFunSig {
    set_of([adec_dest_sym(), aenc_sym(), pk_sym()])
}
pub fn signature_fun_dest_sig() -> NoEqFunSig {
    set_of([sign_sym(), verify_dest_sym(), true_sym(), pk_sym()])
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
/// Mirrors `Convenience.hs` `(++:)`.
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
    f_app_no_eq(pair_sym(), vec![a, b])
}
pub fn fst<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(fst_sym(), vec![a])
}
pub fn snd<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(snd_sym(), vec![a])
}

pub fn exp<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(exp_sym(), vec![a, b])
}
pub fn inv<A>(a: Term<A>) -> Term<A> {
    f_app_no_eq(inv_sym(), vec![a])
}
pub fn one_const<A>() -> Term<A> {
    f_app_no_eq(one_sym(), vec![])
}
pub fn dh_neutral<A>() -> Term<A> {
    f_app_no_eq(dh_neutral_sym(), vec![])
}
pub fn zero_const<A>() -> Term<A> {
    f_app_no_eq(zero_sym(), vec![])
}
pub fn pmult<A>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_no_eq(pmult_sym(), vec![a, b])
}
pub fn emap<A: Ord + Clone>(a: Term<A>, b: Term<A>) -> Term<A> {
    f_app_c(CSym::EMap, vec![a, b])
}

/// HS `Convenience.hs:55-59#x1` binds `x1`, `x2` and `x3` once as the message
/// variables every builtin rewrite rule below is written over.
fn x1() -> LNTerm {
    msg_var("x", 1)
}
fn x2() -> LNTerm {
    msg_var("x", 2)
}
fn x3() -> LNTerm {
    msg_var("x", 3)
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
    set_of([
        rule(exp(x1(), one_const()), x1()),
        rule(exp(exp(x1(), x2()), x3()), exp(x1(), mult(x2(), x3()))),
        rule(exp(dh_neutral(), x1()), dh_neutral()),
        rule(mult(x1(), one_const()), x1()),
        rule(inv(inv(x1())), x1()),
        rule(inv(one_const()), one_const()),
        rule(mult(x1(), inv(x1())), one_const()),
        rule(mult(inv(x1()), inv(x2())), inv(mult(x1(), x2()))),
        rule(mult(inv(mult(x1(), x2())), x2()), inv(x1())),
        rule(inv(mult(inv(x1()), x2())), mult(x1(), inv(x2()))),
        rule(mult(x1(), mult(inv(x1()), x2())), x2()),
        rule(
            mult(inv(x1()), mult(inv(x2()), x3())),
            mult(inv(mult(x1(), x2())), x3()),
        ),
        rule(
            mult(inv(mult(x1(), x2())), mult(x2(), x3())),
            mult(inv(x1()), x3()),
        ),
    ])
}

/// `xorRules`: Xor presentation with the finite variant property.
pub fn xor_rules() -> BTreeSet<RRule<LNTerm>> {
    set_of([
        rule(xor(x1(), zero_const()), x1()),
        rule(xor(x1(), x1()), zero_const()),
        rule(xor(x1(), xor(x1(), x2())), x2()),
    ])
}

/// `bpRules`: bilinear-pairing rules (extends `dh_rules`).
pub fn bp_rules() -> BTreeSet<RRule<LNTerm>> {
    set_of([
        rule(pmult(one_const(), x1()), x1()),
        rule(
            pmult(x3(), pmult(x2(), x1())),
            pmult(mult(x3(), x2()), x1()),
        ),
        rule(emap(x1(), pmult(x2(), x3())), exp(emap(x1(), x3()), x2())),
    ])
}

/// `msetRules`: multisets have no rewrite rules.
pub fn mset_rules() -> BTreeSet<RRule<LNTerm>> {
    BTreeSet::new()
}

// =============================================================================
// Builtin subterm rules — direct port of `Term.Builtin.Rules`
// =============================================================================
//
// These return `CtxtStRule` directly (with explicit RHS positions), the shape
// `MaudeSig.st_rules` carries through to `subtermIntruderRules` /
// `destructionRules` — the generator that turns a `[ symmetric-encryption ]`
// signature into its decryption destructors.

/// The rewrite `lhs -> rhs`, where `positions` gives the positions at which
/// `rhs` occurs in `lhs` (HS `CtxtStRule` over an `StRhs`,
/// Term/SubtermRule.hs:40-45).
fn st_rule(lhs: LNTerm, positions: Vec<Position>, rhs: LNTerm) -> CtxtStRule {
    CtxtStRule::new(
        lhs,
        StRhs {
            positions,
            term: rhs,
        },
    )
}

/// `fstRule` (Rules.hs:101): `fst(<x1,x2>) = x1`.
pub fn fst_rule() -> CtxtStRule {
    st_rule(fst(pair(x1(), x2())), vec![vec![0, 0]], x1())
}

/// `sndRule` (Rules.hs:102): `snd(<x1,x2>) = x2`.
pub fn snd_rule() -> CtxtStRule {
    st_rule(snd(pair(x1(), x2())), vec![vec![0, 1]], x2())
}

/// `fstDestRule` (Rules.hs:103): `fstDest(<x1,x2>) = x1`, the destructor-rooted
/// variant of [`fst_rule`].
pub fn fst_dest_rule() -> CtxtStRule {
    st_rule(
        f_app_no_eq(fst_dest_sym(), vec![pair(x1(), x2())]),
        vec![vec![0, 0]],
        x1(),
    )
}

/// `sndDestRule` (Rules.hs:104): `sndDest(<x1,x2>) = x2`, the destructor-rooted
/// variant of [`snd_rule`].
pub fn snd_dest_rule() -> CtxtStRule {
    st_rule(
        f_app_no_eq(snd_dest_sym(), vec![pair(x1(), x2())]),
        vec![vec![0, 1]],
        x2(),
    )
}

/// `pairRules` (Rules.hs:106).
pub fn pair_rules() -> BTreeSet<CtxtStRule> {
    set_of([fst_rule(), snd_rule()])
}

/// `pairDestRules` (Rules.hs:115): the DESTRUCTOR variant of `pair_rules`,
/// used by the `dest-pairing` builtin.
pub fn pair_dest_rules() -> BTreeSet<CtxtStRule> {
    set_of([fst_dest_rule(), snd_dest_rule()])
}

/// `symEncRules`: `sdec(senc(x, y), y) = x`.
pub fn sym_enc_rules() -> BTreeSet<CtxtStRule> {
    set_of([st_rule(
        sdec(senc(x1(), x2()), x2()),
        vec![vec![0, 0]],
        x1(),
    )])
}

/// `asymEncRules`: `adec(aenc(x, pk(y)), y) = x`.
pub fn asym_enc_rules() -> BTreeSet<CtxtStRule> {
    set_of([st_rule(
        adec(aenc(x1(), pk(x2())), x2()),
        vec![vec![0, 0]],
        x1(),
    )])
}

/// `signatureRules`: `verify(sign(x, y), x, pk(y)) = true`.
pub fn signature_rules() -> BTreeSet<CtxtStRule> {
    set_of([st_rule(
        verify(sign(x1(), x2()), x1(), pk(x2())),
        vec![vec![0, 0]],
        true_const(),
    )])
}

/// `locationReportRules` (Rules.hs:112-114): `check_rep(rep(x1,x2), x2) = x1`
/// and `get_rep(rep(x1,x2)) = x1`.  Used by the `locations-report` builtin.
pub fn location_report_rules() -> BTreeSet<CtxtStRule> {
    let rep = || f_app_no_eq(rep_sym(), vec![x1(), x2()]);
    set_of([
        st_rule(
            f_app_no_eq(check_rep_sym(), vec![rep(), x2()]),
            vec![vec![0, 0]],
            x1(),
        ),
        st_rule(
            f_app_no_eq(get_rep_sym(), vec![rep()]),
            vec![vec![0, 0]],
            x1(),
        ),
    ])
}

/// `symEncDestRules` (Rules.hs:116-116): `sdecDest(senc(x1,x2), x2) = x1` —
/// the DESTRUCTOR variant of `sym_enc_rules`, used by the
/// `dest-symmetric-encryption` builtin.
pub fn sym_enc_dest_rules() -> BTreeSet<CtxtStRule> {
    set_of([st_rule(
        f_app_no_eq(sdec_dest_sym(), vec![senc(x1(), x2()), x2()]),
        vec![vec![0, 0]],
        x1(),
    )])
}

/// `asymEncDestRules` (Rules.hs:117-117): `adecDest(aenc(x1, pk(x2)), x2) = x1`
/// — the DESTRUCTOR variant of `asym_enc_rules`, used by the
/// `dest-asymmetric-encryption` builtin.
pub fn asym_enc_dest_rules() -> BTreeSet<CtxtStRule> {
    set_of([st_rule(
        f_app_no_eq(adec_dest_sym(), vec![aenc(x1(), pk(x2())), x2()]),
        vec![vec![0, 0]],
        x1(),
    )])
}

/// `revealSignatureRules`: `revealVerify(revealSign(x,y), x, pk(y)) = true`
/// plus `getMessage(revealSign(x,y)) = x`.  Mirrors
/// `Term.Builtin.Rules.revealSignatureRules` (Rules.hs:110-111).
pub fn reveal_signature_rules() -> BTreeSet<CtxtStRule> {
    let reveal_sign = || f_app_no_eq(reveal_sign_sym(), vec![x1(), x2()]);
    set_of([
        st_rule(
            f_app_no_eq(reveal_verify_sym(), vec![reveal_sign(), x1(), pk(x2())]),
            vec![vec![0, 0]],
            true_const(),
        ),
        st_rule(
            f_app_no_eq(extract_message_sym(), vec![reveal_sign()]),
            vec![vec![0, 0]],
            x1(),
        ),
    ])
}

/// `signatureDestRules`: `verifyDest(sign(x, y), x, pk(y)) = true`.
/// Mirrors `Term.Builtin.Rules.signatureDestRules` (Rules.hs:118-118).
pub fn signature_dest_rules() -> BTreeSet<CtxtStRule> {
    set_of([st_rule(
        f_app_no_eq(verify_dest_sym(), vec![sign(x1(), x2()), x1(), pk(x2())]),
        vec![vec![0, 0]],
        true_const(),
    )])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::FunSym;

    /// Render a rule set in the form in which Maude receives its equations.
    /// The output has one `lhs = rhs` line per rule.  The lines follow the
    /// `BTreeSet` (= HS `Set`) iteration order.  That is the order in which
    /// `MaudeSig::rrules` gives the rules to the module builder.
    fn rendered(rules: &BTreeSet<RRule<LNTerm>>) -> Vec<String> {
        rules
            .iter()
            .map(|r| {
                format!(
                    "{} = {}",
                    crate::pretty::pretty_lnterm(&r.lhs),
                    crate::pretty::pretty_lnterm(&r.rhs)
                )
            })
            .collect()
    }

    /// `dhRules` (Rules.hs:47-61) is Lankford's DH presentation, which has 13
    /// rules.  A count alone constrains no symbol, no argument and no
    /// nesting.  One mistyped `inv` or `*` still gives 13 rules and a
    /// different equational theory, with no message.  Each line below is the
    /// matching HS rule.  Its AC arguments are in canonical order, which
    /// means `fAppAC`-sorted and flattened.
    #[test]
    fn dh_rules_match_haskell() {
        assert_eq!(
            rendered(&dh_rules()),
            [
                "x.1^one = x.1",
                "DH_neutral^x.1 = DH_neutral",
                "x.1^x.2^x.3 = x.1^(x.2*x.3)",
                "inv(inv(x.1)) = x.1",
                "inv(one) = one",
                "inv((x.2*inv(x.1))) = (x.1*inv(x.2))",
                "(x.1*x.2*inv(x.1)) = x.2",
                "(x.1*inv(x.1)) = one",
                "(x.1*one) = x.1",
                "(x.2*x.3*inv((x.1*x.2))) = (x.3*inv(x.1))",
                "(x.2*inv((x.1*x.2))) = inv(x.1)",
                "(x.3*inv(x.1)*inv(x.2)) = (x.3*inv((x.1*x.2)))",
                "(inv(x.1)*inv(x.2)) = inv((x.1*x.2))",
            ]
        );
    }

    /// `xorRules` (Rules.hs:91-95).  `x.1⊕x.1⊕x.2 = x.2` is the flattened
    /// three-argument form of HS's `x1 +: x1 +: x2`.  `fAppAC` flattens the
    /// nested `+:` when it builds the term.  `x1 +: x1` keeps both copies.
    #[test]
    fn xor_rules_match_haskell() {
        assert_eq!(
            rendered(&xor_rules()),
            [
                "(x.1⊕x.1) = zero",
                "(x.1⊕x.1⊕x.2) = x.2",
                "(x.1⊕zero) = x.1",
            ]
        );
    }

    /// `bpRules` (Rules.hs:71-78) is the bilinear-pairing extension of DH.
    #[test]
    fn bp_rules_match_haskell() {
        assert_eq!(
            rendered(&bp_rules()),
            [
                "pmult(x.3, pmult(x.2, x.1)) = pmult((x.2*x.3), x.1)",
                "pmult(one, x.1) = x.1",
                "em(x.1, pmult(x.2, x.3)) = em(x.1, x.3)^x.2",
            ]
        );
    }

    /// `msetRules` (Rules.hs:87) is empty.  Multisets are pure AC.  They have
    /// no rewrite rules of their own.
    #[test]
    fn mset_rules_are_empty() {
        assert!(mset_rules().is_empty());
    }

    /// Each AC convenience wrapper (Convenience.hs `(*:)`/`(+:)`/`(++:)`)
    /// carries its own symbol.  Each one calls the `f_app_ac` smart
    /// constructor.  A nested application of the same operator therefore
    /// flattens, and the arguments come back in canonical order.
    #[test]
    fn convenience_ac_constructors_carry_their_symbol_and_normalise() {
        let a = msg_var("a", 0);
        let b = msg_var("b", 0);
        let c = msg_var("c", 0);
        let cases: [(LNTerm, AcSym); 4] = [
            (mult(mult(b.clone(), a.clone()), c.clone()), AcSym::Mult),
            (union(union(b.clone(), a.clone()), c.clone()), AcSym::Union),
            (xor(xor(b.clone(), a.clone()), c.clone()), AcSym::Xor),
            (
                nat_plus(nat_plus(b.clone(), a.clone()), c.clone()),
                AcSym::NatPlus,
            ),
        ];
        for (t, want) in cases {
            match t {
                Term::App(FunSym::Ac(sym), ts) => {
                    assert_eq!(sym, want);
                    assert_eq!(
                        &ts[..],
                        &[a.clone(), b.clone(), c.clone()][..],
                        "{want:?} arguments must be flattened and sorted"
                    );
                }
                other => panic!("expected an AC application, got {other:?}"),
            }
        }
    }

    /// The builtin signatures are the `NoEqSym` tuples of
    /// `Term.Builtin.Signature` (Term/Builtin/Signature.hs:19-44), grouped at
    /// Term/Builtin/Signature.hs:61-97.  Each symbol's arity, privacy and
    /// constructability appears in the output, in the `functions:` block.
    /// The three values also decide which intruder rules the code generates.
    /// The test therefore compares all three for each symbol.  A test of
    /// membership alone lets a change of `Public` or `Constructor` pass.  The
    /// `dest-*` signatures differ from their plain siblings in nothing else.
    #[test]
    fn signatures_match_haskell() {
        fn rendered(sig: &NoEqFunSig) -> Vec<String> {
            sig.iter()
                .map(|s| {
                    format!(
                        "{}/{} {} {}",
                        String::from_utf8_lossy(s.name),
                        s.arity,
                        match s.privacy {
                            Privacy::Public => "public",
                            Privacy::Private => "private",
                        },
                        match s.constructability {
                            Constructability::Constructor => "ctor",
                            Constructability::Destructor => "dest",
                        },
                    )
                })
                .collect()
        }
        assert_eq!(
            rendered(&sym_enc_fun_sig()),
            ["sdec/2 public ctor", "senc/2 public ctor"]
        );
        assert_eq!(
            rendered(&asym_enc_fun_sig()),
            [
                "adec/2 public ctor",
                "aenc/2 public ctor",
                "pk/1 public ctor"
            ]
        );
        assert_eq!(
            rendered(&signature_fun_sig()),
            [
                "pk/1 public ctor",
                "sign/2 public ctor",
                "true/0 public ctor",
                "verify/3 public ctor",
            ]
        );
        assert_eq!(
            rendered(&reveal_signature_fun_sig()),
            [
                "getMessage/1 public ctor",
                "pk/1 public ctor",
                "revealSign/2 public ctor",
                "revealVerify/3 public ctor",
                "true/0 public ctor",
            ]
        );
        assert_eq!(
            rendered(&location_report_fun_sig()),
            [
                "check_rep/2 public dest",
                "get_rep/1 public dest",
                "rep/2 private ctor",
                "report/1 public ctor",
            ]
        );
        assert_eq!(rendered(&hash_fun_sig()), ["h/1 public ctor"]);
        // The `dest-*` variants differ from the plain ones in one value only.
        // That value is the constructability of the reducing symbol.
        assert_eq!(
            rendered(&sym_enc_fun_dest_sig()),
            ["sdec/2 public dest", "senc/2 public ctor"]
        );
        assert_eq!(
            rendered(&asym_enc_fun_dest_sig()),
            [
                "adec/2 public dest",
                "aenc/2 public ctor",
                "pk/1 public ctor"
            ]
        );
        assert_eq!(
            rendered(&signature_fun_dest_sig()),
            [
                "pk/1 public ctor",
                "sign/2 public ctor",
                "true/0 public ctor",
                "verify/3 public dest",
            ]
        );
    }
}
