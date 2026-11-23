use super::*;
use crate::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
use crate::term::f_app_acfct;

fn union() -> AcFctSym {
    AcFctSym {
        name: b"merge",
        privacy: Privacy::Public,
        constructability: Constructability::Constructor,
        ndc: NdcState::NotNdc,
    }
}

#[test]
fn native_only_independent_reductions_under_an_inert_user_ac() {
    let u = var("u");
    let k = var("k");
    let product = |args| f_app_acfct(union(), args);
    let mut sig = signature([(
        hash(pair(u.clone(), k.clone())),
        product(vec![u, k.clone()]),
    )]);
    sig.st_ac_fun_syms.insert(union());
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    // Each factor exposes a product with the outer head. Independent choices
    // of the first redex would create at least 2^14 distinct whole states.
    let mut args = Vec::new();
    let mut factors = Vec::new();
    for i in 0..14 {
        let left = pub_term(format!("p{i}"));
        args.push(hash(pair(left.clone(), k.clone())));
        factors.extend([left, k.clone()]);
    }
    args.push(k.clone());
    factors.push(k);
    assert_eq!(native.reduce(&product(args)).unwrap(), product(factors));
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_inert_product_preserves_open_factors_and_multiplicities() {
    let x = var("x");
    let y = var("y");
    let input = bag([
        hash(pair(x.clone(), y.clone())),
        hash(pair(y.clone(), x.clone())),
        x.clone(),
    ]);
    let expected = bag([x.clone(), y.clone(), y.clone(), x.clone(), x.clone()]);
    let sig = signature([(hash(pair(x.clone(), y.clone())), bag([x, y]))]);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    assert_eq!(native.reduce(&input).unwrap(), expected);
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(maude.reduce(&input).unwrap(), expected);
    }
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn active_product_and_ambiguous_operand_still_defer() {
    let x = var("x");
    let y = var("y");
    let x_and_y = hash(pair(x.clone(), y.clone()));
    let product = bag([x.clone(), y.clone()]);
    let changed = (x_and_y.clone(), product);
    let input = bag([hash(pair(pub_term("a"), pub_term("b"))), pub_term("b")]);
    for other in [
        // A root rule may consume the operand before it exposes a product.
        (bag([x_and_y.clone(), y.clone()]), y),
        // A literal excluded from ordinary rule compilation still makes
        // this root active, even though the compiled bucket is absent.
        (bag([x_and_y.clone(), pub_term("b")]), x.clone()),
        // A genuinely ambiguous child has two distinct normal forms.
        (x_and_y, x),
    ] {
        let sig = signature([changed.clone(), other]);
        let handle =
            MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly)
                .unwrap();
        assert!(matches!(
            handle.reduce(&input),
            Err(crate::maude_proc::MaudeError::UnsupportedOperation(
                crate::maude_proc::UNCERTIFIED_TABLE
            ))
        ));
        assert_eq!(handle.stats().norm_count, 0);
    }
}

#[test]
fn wider_product_slot_preserves_the_sort_of_a_changing_nat_operand() {
    use crate::function_symbols::nat_one_sym;
    use crate::maude_sig::nat_maude_sig;
    use crate::term::f_app_no_eq;

    let one = f_app_no_eq(nat_one_sym(), vec![]);
    let two = f_app_ac(AcSym::NatPlus, vec![one.clone(), one.clone()]);
    let flag = pub_term("flag");
    let input = bag([two.clone(), flag.clone()]);
    for (rhs, valid) in [(one.clone(), true), (hash(one.clone()), false)] {
        let sig = signature([(two.clone(), rhs)])
            .merge(nat_maude_sig())
            .refresh();
        // The certifier accepts neither table, and a raw session reports
        // that. The session of a theory follows one rewrite path. The second
        // rule does not keep the sort of its left side, but the reduct keeps
        // the sort of this input, a multiset, which is all the path export
        // promises: that it is the normal form rests on the author's premise.
        let raw = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        assert!(matches!(
            raw.reduce(&input),
            Err(crate::maude_proc::MaudeError::UnsupportedOperation(
                crate::maude_proc::UNCERTIFIED_TABLE
            ))
        ));
        let native = theory_session(&sig);
        let expected = if valid {
            one.clone()
        } else {
            hash(one.clone())
        };
        assert_eq!(
            native.reduce(&input).unwrap(),
            bag([expected, flag.clone()])
        );
        assert_eq!(native.stats().norm_count, 0);
    }
}
