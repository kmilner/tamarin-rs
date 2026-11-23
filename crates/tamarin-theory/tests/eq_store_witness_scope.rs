//! A unifier witness must stay distinct from the variables a disjunction
//! already binds.
//!
//! The store below is the step at which native-only proof search on
//! `ake/dh/UM_one_pass_attack` stopped terminating. The applied substitution
//! is an instance of the stored variant, so the only unifier renames the three
//! variables of the new images. The native solver named its witnesses `x.0`
//! and `~x.1`, the lowest indices the query left unused, which are also the
//! variables the variant binds. Reading those witnesses as the bound variables
//! added `x.0 = x.12` to a store that had just replaced `x.0` by
//! `x.12 * inv(~x.11 * x.13)`, and every later step multiplied the exponent by
//! one more inverse.

use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin::{exp, inv, mult};
use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::dh_maude_sig;
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;
use tamarin_theory::tools::equation_store::{EquationStore, LNSubst};

const MISSING: &str = "/nonexistent/eq-store-witness-scope-must-not-start-maude";

fn v(var: LVar) -> LNTerm {
    Term::Lit(Lit::Var(var))
}

/// `{x.0 -> a * inv(~b * c), z.0 -> 'g'^(a * inv(c)), ~x.1 -> ~b}`.
fn bindings(a: LVar, b: LVar, c: LVar) -> Vec<(LVar, LNTerm)> {
    vec![
        (
            LVar::new("x", LSort::Msg, 0),
            mult(v(a), inv(mult(v(b), v(c)))),
        ),
        (
            LVar::new("z", LSort::Msg, 0),
            exp(pub_term("g"), mult(v(a), inv(v(c)))),
        ),
        (LVar::new("x", LSort::Fresh, 1), v(b)),
    ]
}

fn check(handle: &MaudeHandle) {
    let mut store = EquationStore::empty();
    store.add_disj(vec![LNSubstVFresh::from_list(bindings(
        LVar::new("x", LSort::Msg, 424),
        LVar::new("x", LSort::Fresh, 214),
        LVar::new("x", LSort::Msg, 425),
    ))]);
    let introduced = [
        LVar::new("x", LSort::Msg, 12),
        LVar::new("x", LSort::Fresh, 11),
        LVar::new("x", LSort::Msg, 13),
    ];
    let applied = LNSubst::from_list(bindings(introduced[0], introduced[1], introduced[2]));
    store.apply_eq_store(handle, &applied).unwrap();

    let [disjunction] = store.conj.as_slice() else {
        panic!("expected one disjunction, got {:?}", store.conj)
    };
    let [arm] = disjunction.substs.as_slice() else {
        panic!("expected one arm, got {:?}", disjunction.substs)
    };
    let arm = arm.to_list();
    let mut images = Vec::new();
    for (key, image) in &arm {
        assert!(
            introduced.contains(key),
            "{key:?} is not in the applied substitution's range: {arm:?}"
        );
        let Term::Lit(Lit::Var(witness)) = image else {
            panic!("{key:?} must be renamed, not instantiated: {arm:?}")
        };
        assert_eq!(witness.sort, key.sort, "{arm:?}");
        assert!(
            !images.contains(witness),
            "two variables identified: {arm:?}"
        );
        images.push(*witness);
    }
}

#[test]
fn maude_witnesses_do_not_bind_the_variables_a_variant_replaced() {
    if let Some(path) = tamarin_test_support::require_maude_path() {
        check(
            &MaudeHandle::start_with_backend(&path, dh_maude_sig(), AlgebraBackend::Maude).unwrap(),
        );
    }
}

#[test]
fn native_witnesses_do_not_bind_the_variables_a_variant_replaced() {
    if AlgebraBackend::NativeOnly.validate().is_err() {
        return;
    }
    let handle =
        MaudeHandle::start_with_backend(MISSING, dh_maude_sig(), AlgebraBackend::NativeOnly)
            .unwrap();
    check(&handle);
    handle.check_backend_status().unwrap();
}
