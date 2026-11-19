use super::*;

#[test]
fn total_free_rule_contracts_before_independent_erased_redexes() {
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::term::f_app_no_eq;
    let select = NoEqSym::new(b"select", 2, Privacy::Public, Constructability::Constructor);
    let at = |left, right| f_app_no_eq(select, vec![left, right]);
    let mut sig = signature([(at(var("left"), var("right")), var("right"))]);
    sig.st_fun_syms.insert(select);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.refresh(), AlgebraBackend::NativeOnly)
            .unwrap();
    let mut erased = pub_term("end");
    for i in 0..14 {
        let redex = fst(pair(pub_term(format!("value{i}")), pub_term("unused")));
        erased = pair(redex, erased);
    }
    let right = fst(pair(var("caller"), pub_term("tag")));
    let narrow = crate::lterm::fresh_term("narrow");
    assert_eq!(
        native.reduce(&at(erased.clone(), narrow.clone())).unwrap(),
        narrow
    );
    assert_eq!(native.reduce(&at(erased, right)).unwrap(), var("caller"));
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_total_contraction_handles_duplicated_and_reordered_inputs() {
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::term::f_app_no_eq;
    let pack = NoEqSym::new(b"pack", 3, Privacy::Public, Constructability::Constructor);
    let apply = |a, b, c| f_app_no_eq(pack, vec![a, b, c]);
    let (x, y, z) = (var("x"), var("y"), var("z"));
    let mut sig = signature([(
        apply(x.clone(), y, z.clone()),
        pair(z.clone(), pair(x.clone(), z)),
    )]);
    sig.st_fun_syms.insert(pack);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let dirty = |key| fst(pair(key, pub_term("erased")));
    let frozen = var("z");
    let input = apply(
        dirty(frozen.clone()),
        dirty(var("unused")),
        dirty(x.clone()),
    );
    let normal = pair(x.clone(), pair(frozen, x));
    assert_eq!(native.reduce(&input).unwrap(), normal);
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_none()
        && let Some(path) = tamarin_test_support::require_maude_path()
    {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), normal);
    }
}

#[test]
fn unsorted_or_constrained_rules_cannot_claim_a_total_root() {
    use crate::builtin::msg_var;
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::maude_proc::MaudeError;
    use crate::term::f_app_no_eq;
    let choose = NoEqSym::new(b"choose", 2, Privacy::Public, Constructability::Constructor);
    let at = |a, b| f_app_no_eq(choose, vec![a, b]);
    let (x, y) = (var("x"), var("y"));
    let input = at(pub_term("one"), pub_term("two"));
    let narrow = Term::Lit(Lit::Var(LVar::new("v", LSort::Fresh, 0)));
    let make = |rules| {
        let mut sig = signature(rules);
        sig.st_fun_syms.insert(choose);
        sig.refresh()
    };
    for sig in [
        make(vec![(at(x.clone(), x.clone()), x.clone())]),
        make(vec![(at(narrow.clone(), y.clone()), narrow)]),
        make(vec![
            (at(x.clone(), y.clone()), x.clone()),
            (at(x.clone(), y.clone()), y.clone()),
        ]),
        make(vec![(at(x.clone(), y.clone()), msg_var("not_in_lhs", 2))]),
    ] {
        assert!(RuleTable::new(&sig)
            .unwrap()
            .total_free_contract(&input)
            .unwrap()
            .is_none());
    }
    // An unambiguous rule at choose does not establish uniqueness of its result.
    let competing = make(vec![
        (at(x.clone(), y.clone()), fst(x.clone())),
        (fst(pair(x.clone(), y.clone())), y),
    ]);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", competing, AlgebraBackend::NativeOnly)
            .unwrap();
    assert!(matches!(
        native.reduce(&at(pair(pub_term("one"), pub_term("two")), x)),
        Err(MaudeError::UnsupportedOperation("normalization"))
    ));
}

#[test]
fn total_free_contraction_bounds_duplicates_and_checks_erased_arguments() {
    let x = var("x");
    let duplicate = signature([(hash(x.clone()), pair(x.clone(), x.clone()))]);
    let table = RuleTable::new(&duplicate).unwrap();
    let mut wide = x;
    for _ in 0..15 {
        wide = pair(wide.clone(), wide);
    }
    assert!(table.total_free_contract(&hash(wide)).unwrap().is_none());

    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::term::f_app_no_eq;
    let keep = NoEqSym::new(b"keep", 2, Privacy::Public, Constructability::Constructor);
    let call = |a, b| f_app_no_eq(keep, vec![a, b]);
    let mut sig = signature([(call(var("x"), var("y")), var("x"))]);
    sig.st_fun_syms.insert(keep);
    let table = RuleTable::new(&sig.refresh()).unwrap();
    let wrong = Term::Lit(Lit::Var(LVar::new("node", LSort::Node, 0)));
    assert!(table
        .total_free_contract(&call(var("valid"), wrong))
        .unwrap()
        .is_none());
}
