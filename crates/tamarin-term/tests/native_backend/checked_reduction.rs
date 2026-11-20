use super::*;
use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
use tamarin_term::term::f_app_no_eq;

#[test]
fn complete_table_reduction_certifies_the_whole_kind_level_context() {
    let constant = |name| NoEqSym::new(name, 0, Privacy::Public, Constructability::Constructor);
    let [a, b, c] = ["rA", "rB", "rC"].map(|name| constant(name.as_bytes()));
    let mut sig = mset_maude_sig();
    sig.st_fun_syms.extend([a, b, c]);
    let [a, b, c] = [a, b, c].map(|f| f_app_no_eq(f, vec![]));
    let redex = sum(a.clone(), b.clone());
    let rule = |rhs| {
        CtxtStRule::new(
            redex.clone(),
            StRhs {
                term: rhs,
                positions: vec![],
            },
        )
    };
    sig.st_rules.insert(rule(c.clone()));
    let node = Term::Lit(Lit::Var(LVar::new("caller", LSort::Node, 99)));
    let input = sum(sum(node.clone(), b), a.clone());
    let new =
        |sig| MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let h = new(sig.clone().refresh());
    assert_eq!(h.reduce(&input).unwrap(), sum(node, c));
    assert_eq!(h.stats().norm_count, 0);

    sig.st_rules.insert(rule(a));
    let ambiguous = new(sig.refresh());
    assert!(matches!(
        ambiguous.reduce(&input),
        Err(MaudeError::UnsupportedOperation("normalization"))
    ));
    assert_eq!(ambiguous.stats().norm_count, 0);
}

#[test]
fn certified_constant_definition_expands_in_a_wide_kind_level_product() {
    let mut sig = mset_maude_sig();
    let [defined, item] = [b"expansion".as_slice(), b"item"]
        .map(|name| NoEqSym::new(name, 0, Privacy::Public, Constructability::Constructor));
    sig.st_fun_syms.extend([defined, item]);
    let [constant, item] = [defined, item].map(|symbol| f_app_no_eq(symbol, vec![]));
    sig.st_rules.insert(CtxtStRule::new(
        constant.clone(),
        StRhs {
            term: sum(item.clone(), item.clone()),
            positions: vec![],
        },
    ));
    let h = MaudeHandle::start_with_backend(MISSING, sig.refresh(), AlgebraBackend::NativeOnly)
        .unwrap();
    // The Node child forces the general kind-level path. Its bounded search
    // cannot preflight the 64 other factors, but the table certificate is total.
    let node = Term::Lit(Lit::Var(LVar::new("outside", LSort::Node, 0)));
    let product = |mut factors: Vec<LNTerm>| {
        factors.push(node.clone());
        f_app_ac(AcSym::Union, factors)
    };
    let input = product(vec![constant; 64]);
    assert_eq!(h.reduce(&input).unwrap(), product(vec![item; 128]));
    let variants = h.variants(&input).unwrap();
    assert_eq!(variants.len(), 1);
    assert!(variants[0].len() <= 1);
    for (key, value) in &variants[0] {
        assert_eq!(Term::Lit(Lit::Var(*key)), node);
        assert!(matches!(value, Term::Lit(Lit::Var(v)) if v.sort == LSort::Node));
    }
    assert_eq!((h.stats().norm_count, h.stats().var_count), (0, 0));
    h.check_backend_status().unwrap();
}
