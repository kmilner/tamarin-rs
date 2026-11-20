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
