use super::*;
use tamarin_term::builtin::{exp, one_const, pair, xor, zero_const};
use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::maude_sig::{dh_maude_sig, minimal_maude_sig, xor_maude_sig, MaudeSig};
use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
use tamarin_term::term::{f_app_list, f_app_no_eq};

fn scan_symbol() -> NoEqSym {
    NoEqSym::new(b"scan", 1, Privacy::Public, Constructability::Constructor)
}

fn scan(t: LNTerm) -> LNTerm {
    f_app_no_eq(scan_symbol(), vec![t])
}

fn theory() -> MaudeSig {
    let mut sig = minimal_maude_sig(false)
        .merge(dh_maude_sig())
        .merge(xor_maude_sig());
    sig.st_fun_syms.insert(scan_symbol());
    sig.st_rules.insert(CtxtStRule::new(
        scan(zero_const()),
        StRhs {
            positions: vec![],
            term: zero_const(),
        },
    ));
    sig.refresh()
}

fn node() -> LNTerm {
    Term::Lit(Lit::Con(Name::new(NameTag::Node, "event")))
}

// The DH unit exposes the second copy of the XOR summand.
fn cancellation() -> LNTerm {
    let a = pub_term("a");
    xor(exp(a.clone(), one_const()), a)
}

#[test]
fn certified_dh_xor_reduction_crosses_both_groups_and_the_checked_depth() {
    let sig = theory();
    // One DH rewrite and one XOR rewrite expose zero to 31 successive scan rules.
    let input = pair(node(), (0..31).fold(cancellation(), |t, _| scan(t)));
    let want = pair(node(), zero_const());
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let maude =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        assert_eq!(maude.reduce(&input).unwrap(), want);
    }
    let native = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::ProvedOnly).unwrap();
    assert_eq!(native.reduce(&input).unwrap(), want);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn certified_dh_xor_joint_variants_keep_the_sorted_zero_beside_a_node() {
    let sig = theory();
    let key = LVar::new("input", LSort::Msg, 0);
    let input = Term::Lit(Lit::Var(key));
    let mask = xor(node(), cancellation());
    let want = xor(node(), zero_const());
    let query = f_app_list(vec![scan(input.clone()), input.clone(), mask.clone()]);
    let check = |backend: &MaudeHandle| {
        let rows = backend.variants(&query).unwrap();
        let mut seen = [false; 2];
        for row in rows {
            let image = row
                .into_iter()
                .find(|(k, _)| *k == key)
                .map_or(input.clone(), |(_, t)| t);
            if image == zero_const() {
                assert_eq!(backend.reduce(&scan(image)).unwrap(), zero_const());
                seen[1] = true;
            } else {
                assert!(matches!(image, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg));
                let open = scan(image);
                assert_eq!(backend.reduce(&open).unwrap(), open);
                seen[0] = true;
            }
        }
        assert_eq!(seen, [true, true]);
        assert_eq!(backend.reduce(&mask).unwrap(), want);
    };
    if let Some(path) = tamarin_test_support::require_maude_path() {
        check(&MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap());
    }
    let native = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::ProvedOnly).unwrap();
    check(&native);
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}
