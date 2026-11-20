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
    let normal = sum(node, c);
    assert_eq!(
        tamarin_term::lean_unification::reduction_for_convergent_theory(&sig, &input).unwrap(),
        Some(normal.clone())
    );
    assert_eq!(h.reduce(&input).unwrap(), normal);
    assert_eq!(h.stats().norm_count, 0);

    sig.st_rules.insert(rule(a));
    assert_eq!(
        tamarin_term::lean_unification::reduction_for_convergent_theory(&sig, &input).unwrap(),
        None
    );
    let ambiguous = new(sig.refresh());
    assert!(matches!(
        ambiguous.reduce(&input),
        Err(MaudeError::UnsupportedOperation("normalization"))
    ));
    assert_eq!(ambiguous.stats().norm_count, 0);
}

#[test]
fn general_reduction_composes_a_user_equation_with_dh_exponent_cancellation() {
    use tamarin_term::builtin::{exp, fresh_var, inv, msg_var};
    use tamarin_term::lean_unification::reduction_for_convergent_theory;
    use tamarin_term::maude_sig::dh_maude_sig;

    let round_trip = NoEqSym::new(
        b"roundtrip",
        2,
        Privacy::Public,
        Constructability::Constructor,
    );
    let mut sig = dh_maude_sig();
    sig.st_fun_syms.insert(round_trip);
    let x = msg_var("x", 0);
    let k = msg_var("k", 1);
    sig.st_rules.insert(CtxtStRule::new(
        f_app_no_eq(round_trip, vec![x.clone(), k.clone()]),
        StRhs {
            term: exp(exp(x, k.clone()), inv(k)),
            positions: vec![],
        },
    ));
    let sig = sig.refresh();
    let original = fresh_var("shared", 41);
    // The user rule, exponent tower, inverse cancellation and unit power
    // take four rewrites. Certifying the endpoint requires a second stage.
    let input = f_app_no_eq(round_trip, vec![original.clone(), pub_term("key")]);
    assert_eq!(
        reduction_for_convergent_theory(&sig, &input).unwrap(),
        Some(original.clone())
    );
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), original);
        assert_eq!(oracle.stats().norm_count, 1);
    }
}

#[test]
fn certified_mixed_table_retries_reduction_past_the_checked_depth() {
    use tamarin_term::maude_sig::dh_maude_sig;

    let symbol = |name: &'static [u8], arity| {
        NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
    };
    let scan = symbol(b"scan", 1);
    let frame = symbol(b"frame", 2);
    let ok = symbol(b"ok", 0);
    let mut sig = dh_maude_sig();
    sig.st_fun_syms.extend([scan, frame, ok]);
    let ok = f_app_no_eq(ok, vec![]);
    let scan_once = |t| f_app_no_eq(scan, vec![t]);
    sig.st_rules.insert(CtxtStRule::new(
        scan_once(ok.clone()),
        StRhs {
            term: ok.clone(),
            positions: vec![],
        },
    ));

    // Only the innermost scan matches. The Node argument routes this query to
    // the kind-level reducer, and the DH tower rule precludes the size budget.
    let node = Term::Lit(Lit::Var(LVar::new("i", LSort::Node, 0)));
    let wrap = |t| f_app_no_eq(frame, vec![node.clone(), t]);
    let input = wrap((0..33).fold(ok.clone(), |t, _| scan_once(t)));
    let expected = wrap(ok);
    let sig = sig.refresh();
    let h =
        MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap();
    assert_eq!(h.reduce(&input).unwrap(), expected);
    assert_eq!(h.stats().norm_count, 0);
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), expected);
    }
}

#[test]
fn full_table_checks_macro_expansion_at_the_term_boundary() {
    use tamarin_term::builtin::{fst, pair};
    use tamarin_term::lean_unification::{
        reduction_for_convergent_theory, variants_for_convergent_theory,
    };

    let alias = NoEqSym::new(
        b"project_after_expansion",
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let sig = pair_maude_sig().add_macro_sym(alias);
    let value = pub_term("projected");
    let expanded = fst(pair(value.clone(), pub_term("discarded")));
    assert_eq!(
        reduction_for_convergent_theory(&sig, &expanded).unwrap(),
        Some(value)
    );
    assert_eq!(
        variants_for_convergent_theory(&sig, &expanded).unwrap(),
        Some(vec![vec![]])
    );
    let unexpanded = f_app_no_eq(alias, vec![pub_term("input")]);
    assert_eq!(
        reduction_for_convergent_theory(&sig, &unexpanded).unwrap(),
        None
    );
    assert_eq!(
        variants_for_convergent_theory(&sig, &unexpanded).unwrap(),
        None
    );
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

#[test]
fn projection_tables_reduce_inside_wide_kind_level_contexts() {
    use tamarin_term::builtin::{fst, pair, sdec, senc, snd};
    use tamarin_term::maude_sig::sym_enc_maude_sig;

    let sig = pair_maude_sig()
        .merge(mset_maude_sig())
        .merge(sym_enc_maude_sig());
    let h =
        MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap();
    let node = Term::Lit(Lit::Var(LVar::new("outside", LSort::Node, 0)));
    let a = pub_term("a");
    let b = pub_term("b");
    let encrypted = senc(fst(pair(a.clone(), b.clone())), b.clone());
    let good = snd(pair(b.clone(), sdec(encrypted.clone(), b)));
    // Each blocked redex has a matching head. One fails the sort check and
    // the other fails the repeated-key constraint, even after its child reduces.
    let stuck = fst(pair(a.clone(), node.clone()));
    let wrong_key = pub_term("wrong_key");
    let product = |item, rejected| {
        let mut terms = vec![item; 32];
        terms.extend([
            stuck.clone(),
            node.clone(),
            sdec(rejected, wrong_key.clone()),
        ]);
        f_app_ac(AcSym::Union, terms)
    };
    let input = product(good, encrypted);
    let expected = product(a.clone(), senc(a, pub_term("b")));
    assert_eq!(h.reduce(&input).unwrap(), expected);
    assert_eq!(h.stats().norm_count, 0);
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), expected);
        assert_eq!(oracle.stats().norm_count, 1);
    }
}
