use super::*;
use tamarin_term::builtin::{emap, inv, one_const, pair, pmult, xor, zero_const};
use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::maude_sig::{
    bp_maude_sig, dh_maude_sig, minimal_maude_sig, xor_maude_sig, MaudeSig,
};
use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
use tamarin_term::term::{f_app_list, f_app_no_eq};

fn signature() -> MaudeSig {
    minimal_maude_sig(false)
        .merge(dh_maude_sig())
        .merge(bp_maude_sig())
}

fn node() -> LNTerm {
    Term::Lit(Lit::Con(Name::new(NameTag::Node, "event")))
}

#[test]
fn bilinear_variants_preserve_open_scalars_and_kind_level_pairing() {
    let sig = signature();
    let key = LVar::new("scalar", LSort::Msg, 9);
    let x = Term::Lit(Lit::Var(key));
    let base = pub_term("base");
    // The node blocks extraction from the map. The point action inside
    // its other argument can still normalize.
    let mask = emap(node(), pmult(one_const(), base.clone()));
    let expected_mask = emap(node(), base.clone());
    let action = |s| pmult(s, base.clone());
    let query = f_app_list(vec![action(x.clone()), x.clone(), mask.clone()]);
    let check = |h: &MaudeHandle| {
        let rows = h.variants(&query).unwrap();
        let (mut open, mut unit) = (false, false);
        for row in rows {
            let image = row
                .into_iter()
                .find(|(v, _)| *v == key)
                .map_or(x.clone(), |(_, t)| t);
            let t = action(image.clone());
            if image == one_const() {
                assert_eq!(h.reduce(&t).unwrap(), base);
                unit = true;
            } else {
                assert_eq!(h.reduce(&t).unwrap(), t);
                open |= matches!(image, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg);
            }
        }
        assert!(open && unit);
        assert_eq!(h.reduce(&mask).unwrap(), expected_mask);
        let blocked = emap(node(), pmult(pub_term("nonunit"), base.clone()));
        assert_eq!(h.reduce(&blocked).unwrap(), blocked);
    };
    if let Some(path) = tamarin_test_support::require_maude_path() {
        check(&MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap());
    }
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    check(&h);
    assert_eq!(h.stats().var_count, 0);
    assert_eq!(h.stats().norm_count, 0);
}

#[test]
fn bilinear_extraction_on_both_sides_cancels_under_xor_and_user_equations() {
    let mut sig = signature().merge(xor_maude_sig());
    let scan = NoEqSym::new(b"scan", 1, Privacy::Public, Constructability::Constructor);
    let apply = |t| f_app_no_eq(scan, vec![t]);
    sig.st_fun_syms.insert(scan);
    sig.st_rules.insert(CtxtStRule::new(
        apply(zero_const()),
        StRhs {
            positions: vec![],
            term: zero_const(),
        },
    ));
    let sig = sig.refresh();
    let (a, p, q) = (pub_term("scalar"), pub_term("left"), pub_term("right"));
    let scaled = emap(pmult(a.clone(), p.clone()), pmult(inv(a), q.clone()));
    let sum = xor(scaled, emap(p, q));
    // Either map argument can extract first. Both orders produce the same
    // plain pairing, which then cancels under XOR and exposes the user rule.
    let input = pair(node(), (0..32).fold(sum, |t, _| apply(t)));
    let expected = pair(node(), zero_const());
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), expected);
    }
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    assert_eq!(h.reduce(&input).unwrap(), expected);
    assert_eq!(h.stats().norm_count, 0);
}
