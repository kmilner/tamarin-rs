use super::*;
use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
use tamarin_term::term::{f_app_list, f_app_no_eq};

#[test]
fn checked_variant_frontier_preserves_shared_inputs_under_a_kind_level_ac_rewrite() {
    let symbol =
        |name, arity| NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor);
    let [a, b, c] = ["va", "vb", "vc"].map(|name| symbol(name.as_bytes(), 0));
    let f = symbol(b"variant_probe", 1);
    let mut sig = mset_maude_sig();
    sig.st_fun_syms.extend([a, b, c, f]);
    let [a, b, c] = [a, b, c].map(|head| f_app_no_eq(head, vec![]));
    let call = |arg| f_app_no_eq(f, vec![arg]);
    let rule = |lhs, term| {
        CtxtStRule::new(
            lhs,
            StRhs {
                term,
                positions: vec![],
            },
        )
    };
    let redex = sum(a.clone(), b.clone());
    sig.st_rules.insert(rule(redex.clone(), c.clone()));
    sig.st_rules.insert(rule(call(a.clone()), b.clone()));

    // Node is retained outside the redex. This product is legal at the Maude
    // kind level and cannot be captured in a Msg-sorted rewrite variable.
    let node = Term::Lit(Lit::Con(Name::new(NameTag::Node, "vnode")));
    let context = sum(sum(node.clone(), b.clone()), a.clone());
    let x = LVar::new("vx", LSort::Msg, 41);
    let var = Term::Lit(Lit::Var(x));
    let q = f_app_list(vec![context.clone(), call(var.clone()), var]);
    let new =
        |sig| MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let h = new(sig.clone().refresh());
    let reference = tamarin_term::lean_unification::variants_for_convergent_theory(&sig, &q)
        .unwrap()
        .unwrap();
    for answers in [reference, h.variants(&q).unwrap()] {
        let mut found = [false; 2];
        for row in answers {
            let image = row
                .into_iter()
                .find(|(key, _)| *key == x)
                .map(|(_, value)| value)
                .unwrap_or(Term::Lit(Lit::Var(x)));
            if image == a {
                assert_eq!(h.reduce(&call(image)).unwrap(), b);
                found[0] = true;
            } else {
                assert!(matches!(image, Term::Lit(Lit::Var(w)) if w.sort == LSort::Msg));
                let value = call(image);
                assert_eq!(h.reduce(&value).unwrap(), value);
                found[1] = true;
            }
        }
        assert_eq!(found, [true; 2]);
    }
    assert_eq!(h.reduce(&context).unwrap(), sum(node, c));
    assert_eq!((h.stats().var_count, h.stats().norm_count), (0, 0));

    sig.st_rules.insert(rule(redex, a));
    let ambiguous = new(sig.refresh());
    assert!(matches!(
        ambiguous.variants(&q),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
    assert_eq!(ambiguous.stats().var_count, 0);
}

#[test]
fn user_equations_followed_by_pairing_compute_both_open_variants() {
    use tamarin_term::builtin::{fst, pair};

    let symbol =
        |name, arity| NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor);
    let stages = [b"g0", b"g1", b"g2", b"g3", b"g4", b"g5"].map(|s| symbol(s, 1));
    let [a, b] = [b"ga", b"gb"].map(|s| symbol(s, 0));
    let mut sig = pair_maude_sig();
    sig.st_fun_syms.extend(stages);
    sig.st_fun_syms.extend([a, b]);
    let [a, b] = [a, b].map(|f| f_app_no_eq(f, vec![]));
    let x = LVar::new("operand", LSort::Msg, 0);
    let var = Term::Lit(Lit::Var(x));
    let call = |head, arg| f_app_no_eq(head, vec![arg]);
    let rule = |lhs, term| {
        CtxtStRule::new(
            lhs,
            StRhs {
                term,
                positions: vec![],
            },
        )
    };
    for heads in stages.windows(2) {
        sig.st_rules.insert(rule(
            call(heads[0], var.clone()),
            call(heads[1], var.clone()),
        ));
    }
    sig.st_rules.insert(rule(
        call(stages[5], a.clone()),
        fst(pair(b.clone(), a.clone())),
    ));
    let q = f_app_list(vec![call(stages[0], var.clone()), var.clone()]);
    let reference = tamarin_term::lean_unification::variants_for_convergent_theory(&sig, &q)
        .unwrap()
        .unwrap();
    let handle =
        MaudeHandle::start_with_backend(MISSING, sig.refresh(), AlgebraBackend::NativeOnly)
            .unwrap();
    for rows in [reference, handle.variants(&q).unwrap()] {
        let mut open = false;
        let mut specialized = false;
        for row in rows {
            let image = row
                .into_iter()
                .find(|(key, _)| *key == x)
                .map_or(var.clone(), |(_, t)| t);
            let value = handle.reduce(&call(stages[0], image.clone())).unwrap();
            if image == a {
                assert_eq!(value, b);
                specialized = true;
            } else {
                assert!(matches!(image, Term::Lit(Lit::Var(_))));
                assert_eq!(value, call(stages[5], image));
                open = true;
            }
        }
        assert!(open && specialized);
    }
    assert_eq!(
        (handle.stats().var_count, handle.stats().norm_count),
        (0, 0)
    );
    handle.check_backend_status().unwrap();
}

#[test]
fn mixed_dh_and_ground_result_equation_cover_open_and_specialized_inputs() {
    use tamarin_term::builtin::{exp, inv};
    use tamarin_term::lean_unification::{
        reduction_for_convergent_theory, variants_for_convergent_theory,
    };
    use tamarin_term::maude_sig::dh_maude_sig;

    let sym =
        |name, arity| NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor);
    let [tag, result] = [b"tag".as_slice(), b"result"].map(|name| sym(name, 0));
    let probe = sym(b"probe", 1);
    let mut sig = dh_maude_sig();
    sig.st_fun_syms.extend([tag, result, probe]);
    let [tag, result] = [tag, result].map(|f| f_app_no_eq(f, vec![]));
    let call = |x| f_app_no_eq(probe, vec![x]);
    sig.st_rules.insert(CtxtStRule::new(
        call(tag.clone()),
        StRhs {
            positions: vec![],
            term: exp(exp(result.clone(), tag.clone()), inv(tag.clone())),
        },
    ));
    let sig = sig.refresh();
    let x = LVar::new("input", LSort::Msg, 5);
    let var = Term::Lit(Lit::Var(x));
    let query = f_app_list(vec![call(var.clone()), var.clone()]);
    let mut families = vec![variants_for_convergent_theory(&sig, &query)
        .unwrap()
        .unwrap()];
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        families.push(oracle.variants(&query).unwrap());
        assert_eq!(oracle.stats().var_count, 1);
    }
    for rows in families {
        let (mut open, mut specialized) = (false, false);
        for row in rows {
            let image = row
                .into_iter()
                .find(|(k, _)| *k == x)
                .map_or(var.clone(), |(_, v)| v);
            let t = call(image.clone());
            let value = reduction_for_convergent_theory(&sig, &t).unwrap().unwrap();
            if image == tag {
                assert_eq!(value, result);
                specialized = true;
            } else {
                assert!(matches!(image, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg));
                assert_eq!(value, t);
                open = true;
            }
        }
        assert!(open && specialized);
    }
}
