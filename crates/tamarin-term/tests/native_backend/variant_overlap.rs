use super::*;
use std::collections::BTreeSet;
use tamarin_term::builtin::msg_var;
use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
use tamarin_term::rewriting::RRule;
use tamarin_term::subst::apply_vterm;
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::subterm_rule::rrule_to_ctxt_st_rule;
use tamarin_term::term::f_app_no_eq;
use tamarin_term::vterm::var_term;

fn symbol(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
}

fn select(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_no_eq(symbol(b"select", 2), vec![a, b])
}

fn out() -> LNTerm {
    f_app_no_eq(symbol(b"out", 0), vec![])
}

fn wrap(input: LNTerm) -> LNTerm {
    f_app_no_eq(symbol(b"wrap", 1), vec![input])
}

fn handle(rules: Vec<(LNTerm, LNTerm)>) -> MaudeHandle {
    let mut sig = mset_maude_sig();
    sig.st_fun_syms
        .extend([symbol(b"select", 2), symbol(b"out", 0), symbol(b"wrap", 1)]);
    for (lhs, rhs) in rules {
        sig.st_rules
            .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap());
    }
    MaudeHandle::start_with_backend(MISSING, sig.refresh(), AlgebraBackend::NativeOnly).unwrap()
}

fn pattern(width: usize) -> LNTerm {
    f_app_ac(
        AcSym::Union,
        (0..width).map(|i| msg_var("v", i as u64)).collect(),
    )
}

fn check_variants(width: usize, result: fn(LNTerm) -> LNTerm) {
    let w = msg_var("w", 0);
    let rhs = result(w.clone());
    let h = handle(vec![(select(pattern(width), w), rhs)]);
    let keys = [
        LVar::new("x", LSort::Msg, 10),
        LVar::new("y", LSort::Msg, 11),
    ];
    let [x, y] = keys.map(var_term);
    let query = select(x.clone(), y.clone());
    let arms = h.variants(&query).unwrap();
    let mut widths = vec![];

    for arm in arms {
        assert!(arm.iter().all(|(key, _)| keys.contains(key)));
        let subst = LNSubstVFresh::from_list(arm).fresh_to_free_avoiding_vars(&keys);
        let first = apply_vterm(&subst, x.clone());
        let second = apply_vterm(&subst, y.clone());
        let Term::Lit(Lit::Var(second_var)) = second else {
            panic!("constrained second input")
        };
        assert_eq!(second_var.sort, LSort::Msg);
        let output = h.reduce(&select(first.clone(), second.clone())).unwrap();
        let inputs = match &first {
            Term::Lit(Lit::Var(_)) => {
                assert_eq!(output, select(first.clone(), second));
                std::slice::from_ref(&first)
            }
            Term::App(FunSym::Ac(AcSym::Union), factors) => {
                assert_eq!(output, result(second));
                factors.as_ref()
            }
            _ => panic!("unexpected first input {first:?}"),
        };
        let mut variables = BTreeSet::from([second_var]);
        for t in inputs {
            let Term::Lit(Lit::Var(v)) = t else {
                panic!("nonvariable input factor")
            };
            assert_eq!(v.sort, LSort::Msg);
            assert!(
                variables.insert(*v),
                "input coordinates must remain independent"
            );
        }
        widths.push(inputs.len());
    }
    widths.sort_unstable();
    assert_eq!(widths, [1, width]);
    assert_eq!(h.stats().var_count, 0);
}

#[test]
fn ac_overlap_preserves_variants_with_outputs_determined_by_inputs() {
    for width in [3, 4] {
        check_variants(width, std::convert::identity);
        check_variants(width, |_| out());
        check_variants(width, wrap);
    }
}

#[test]
fn agreeing_self_overlaps_do_not_hide_divergent_branches() {
    let w = msg_var("w", 0);
    let h = handle(vec![
        (select(pattern(4), w.clone()), w),
        (
            select(msg_var("other", 0), out()),
            f_app_ac(AcSym::Union, vec![out(), out()]),
        ),
    ]);
    // select(a+b+c+d, out) reduces to both out and out+out.
    assert!(matches!(
        h.variants(&select(msg_var("x", 9), msg_var("y", 10))),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
}
