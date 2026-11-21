//! Keep the numeric input of the Lean presentation theorems tied to the
//! production encoder. Rows are read back in the same order as Packet::rows().
use super::Packet;
use crate::builtin::{dh_neutral, exp, inv, msg_var, mult, one_const, xor, zero_const};
use crate::lterm::LNTerm;
use crate::maude_sig::{
    asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, location_report_maude_sig, minimal_maude_sig,
    reveal_signature_maude_sig, signature_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};

#[test]
fn physical_dh_table_matches_the_lean_presentation() {
    check_packet(
        dh_maude_sig(),
        &dh_observations(),
        "DHWire",
        include_str!(concat!(
            env!("TAMARIN_ALGEBRA_LEAN_DIR"),
            "/Tamarin/DHWireData.lean"
        )),
    );
}

fn dh_with_destructors() -> MaudeSig {
    minimal_maude_sig(false)
        .merge(dh_maude_sig())
        .merge(sym_enc_maude_sig())
        .merge(asym_enc_maude_sig())
        .merge(signature_maude_sig())
        .merge(reveal_signature_maude_sig())
        .merge(location_report_maude_sig())
}

#[test]
fn physical_dh_and_destructor_table_matches_the_lean_presentation() {
    check_packet(
        dh_with_destructors(),
        &dh_observations(),
        "DHConstructorWire",
        include_str!(concat!(
            env!("TAMARIN_ALGEBRA_LEAN_DIR"),
            "/Tamarin/DHConstructorWireData.lean"
        )),
    );
}

fn dh_observations() -> [LNTerm; 5] {
    let [x, y, z] = [1, 2, 3].map(|i| msg_var("x", i));
    [
        exp(x.clone(), y.clone()),
        inv(z),
        one_const(),
        dh_neutral(),
        mult(x, y),
    ]
}

#[test]
fn physical_xor_and_destructor_table_matches_the_lean_presentation() {
    check_packet(
        minimal_maude_sig(false)
            .merge(xor_maude_sig())
            .merge(sym_enc_maude_sig()),
        &[xor(msg_var("x", 1), msg_var("x", 2)), zero_const()],
        "XorConstructorWire",
        include_str!(concat!(
            env!("TAMARIN_ALGEBRA_LEAN_DIR"),
            "/Tamarin/XorConstructorWireData.lean"
        )),
    );
}

#[test]
fn physical_joint_group_table_matches_the_lean_presentation() {
    let sig = minimal_maude_sig(false)
        .merge(dh_maude_sig())
        .merge(xor_maude_sig());
    check_packet(
        sig,
        &dh_observations(),
        "JointGroupWire",
        include_str!(concat!(
            env!("TAMARIN_ALGEBRA_LEAN_DIR"),
            "/Tamarin/JointGroupWireData.lean"
        )),
    );
}

#[test]
fn physical_bilinear_and_xor_table_matches_the_lean_presentation() {
    let sig = minimal_maude_sig(false)
        .merge(dh_maude_sig())
        .merge(bp_maude_sig())
        .merge(xor_maude_sig());
    check_packet(
        sig,
        &dh_observations(),
        "BilinearWire",
        include_str!(concat!(
            env!("TAMARIN_ALGEBRA_LEAN_DIR"),
            "/Tamarin/BilinearWireData.lean"
        )),
    );
}

fn check_packet(sig: MaudeSig, observations: &[LNTerm], namespace: &str, fixture: &str) {
    let packet = Packet::full_table(&sig, observations).unwrap().unwrap();
    let mut rows = vec![&[][..]; packet.nodes.len()];
    for (words, &id) in &packet.nodes {
        rows[id as usize] = words.as_ref();
    }
    let physical = packet.rows();
    assert_eq!(physical.len(), rows.len());
    for (row, words) in physical.iter().zip(&rows) {
        assert_eq!((row.data, row.size), (words.as_ptr(), words.len()));
    }
    let (roots, rules) = packet.equations.split_at(observations.len());
    let arrays = format!(
        "def declarations : Array UInt64 := {:?}\ndef nodes : Array (Array UInt64) := {:?}\ndef ruleRoots : Array UInt64 := {:?}\ndef observationRoots : Array UInt64 := {:?}",
        packet.declarations, rows, rules, roots
    ).replace('[', "#[");
    let compact = |text: &str| text.split_whitespace().collect::<String>();
    let (_, fixture) = fixture
        .split_once(&format!("namespace Tamarin.{namespace}\n"))
        .unwrap();
    let fixture = fixture
        .strip_suffix(&format!("end Tamarin.{namespace}\n"))
        .unwrap();
    assert_eq!(
        compact(fixture),
        compact(&arrays),
        "{namespace} packet changed:\n{arrays}"
    );
}

#[test]
fn native_oracle_constructor_extension_reduces_and_generates_guarded_variants() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, pair, pk, sdec, senc, sign, true_const, verify};
    use crate::lean_unification::{
        reduction_for_convergent_theory, variants_for_convergent_theory,
    };
    use crate::lterm::pub_term;
    use crate::maude_proc::MaudeHandle;

    let sig = dh_with_destructors();
    let message = pub_term("message");
    let key = pub_term("key");
    let power = exp(exp(message.clone(), key.clone()), inv(key.clone()));
    let decrypted = sdec(senc(power, key.clone()), key.clone());
    let projected = fst(pair(decrypted, key.clone()));
    let check = |term| verify(sign(message.clone(), key.clone()), term, pk(key.clone()));
    let ground = check(projected);
    assert_eq!(
        reduction_for_convergent_theory(&sig, &ground).unwrap(),
        Some(true_const())
    );

    // The open verification term is already normal. Specializing its message
    // creates a second variant in which the signature check reduces to true.
    let x = msg_var("message", 42);
    let query = check(x.clone());
    let check_rows = |rows: crate::lean_unification::Substitutions| {
        let mut open = false;
        let mut success = false;
        for row in rows {
            let image = row
                .iter()
                .find_map(|(v, term)| {
                    (x == crate::term::Term::Lit(crate::vterm::Lit::Var(*v))).then_some(term)
                })
                .unwrap_or(&x);
            open |= matches!(image, crate::term::Term::Lit(crate::vterm::Lit::Var(_)));
            success |= image == &message;
        }
        assert!(open && success);
    };
    check_rows(
        variants_for_convergent_theory(&sig, &query)
            .unwrap()
            .unwrap(),
    );
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(maude.reduce(&ground).unwrap(), true_const());
        check_rows(maude.variants(&query).unwrap());
    }
}

#[test]
fn native_oracle_declared_ac_group_composes_with_builtin_groups() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, pmult};
    use crate::function_symbols::{AcFctSym, AcSym, Constructability, NdcState, Privacy};
    use crate::lterm::pub_term;
    use crate::maude_proc::MaudeHandle;
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::f_app_ac;

    let mut sig = dh_with_destructors()
        .merge(bp_maude_sig())
        .merge(xor_maude_sig());
    let join = AcFctSym::new(
        b"join",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    sig.st_ac_fun_syms.insert(join);
    let op = |a, b| f_app_ac(AcSym::AcFct(join), vec![a, b]);
    let [x, y] = [17, 23].map(|i| msg_var("local", i));
    for (lhs, term) in [
        (op(x.clone(), x.clone()), zero_const()),
        (op(x.clone(), zero_const()), x.clone()),
        (op(x.clone(), op(y.clone(), x)), y),
    ] {
        sig.st_rules.insert(CtxtStRule::new(
            lhs,
            StRhs {
                term,
                positions: vec![],
            },
        ));
    }
    let sig = sig.refresh();
    let a = pub_term("a");
    let base = emap(a.clone(), a.clone());
    let input = op(
        emap(pmult(one_const(), a.clone()), a),
        xor(base.clone(), zero_const()),
    );
    let packet = Packet::full_table(&sig, std::slice::from_ref(&input))
        .unwrap()
        .unwrap();
    super::initialize().unwrap();
    assert!(super::LEAN_THREAD
        .with(|_| packet.certifies_table(&packet.equations[1..], 0))
        .unwrap());
    let h = MaudeHandle::start_with_backend(
        "/nonexistent/maude",
        sig.clone(),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    assert_eq!(h.reduce(&input).unwrap(), zero_const());
    assert_eq!(h.stats().norm_count, 0);
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), zero_const());
    }
}

#[test]
fn native_oracle_ac_unit_reduces_only_with_a_message_partner() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::function_symbols::{AcFctSym, AcSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::lterm::{pub_term, Name, NameTag};
    use crate::maude_proc::MaudeHandle;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::{f_app_ac, f_app_no_eq, Term};
    use crate::vterm::Lit;

    let join = AcFctSym::new(
        b"join",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let empty = NoEqSym::new(b"empty", 0, Privacy::Public, Constructability::Constructor);
    let unit = f_app_no_eq(empty, vec![]);
    let op = |a, b| f_app_ac(AcSym::AcFct(join), vec![a, b]);
    let x = msg_var("x", 7);
    let mut theory = minimal_maude_sig(false);
    theory.st_fun_syms.insert(empty);
    theory.st_ac_fun_syms.insert(join);
    theory
        .st_rules
        .insert(rrule_to_ctxt_st_rule(&RRule::new(op(unit.clone(), x.clone()), x)).unwrap());
    let node = Term::Lit(Lit::Con(Name::new(NameTag::Node, "event")));
    let msg = pub_term("data");
    let blocked = op(unit.clone(), node.clone());
    let queries = [
        (op(unit.clone(), msg.clone()), msg.clone()),
        (blocked.clone(), blocked.clone()),
        (op(blocked, msg.clone()), op(node, msg)),
    ];
    for sig in [
        theory.clone().refresh(),
        theory
            .merge(dh_maude_sig())
            .merge(bp_maude_sig())
            .merge(xor_maude_sig())
            .refresh(),
    ] {
        let packet = Packet::full_table(&sig, &[]).unwrap().unwrap();
        super::initialize().unwrap();
        assert!(super::LEAN_THREAD
            .with(|_| packet.certifies_table(&packet.equations, 0))
            .unwrap());
        let native = MaudeHandle::start_with_backend(
            "/nonexistent/maude",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        let oracle = tamarin_test_support::require_maude_path().map(|path| {
            MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap()
        });
        for (input, expected) in &queries {
            assert_eq!(native.reduce(input).unwrap(), *expected);
            if let Some(maude) = &oracle {
                assert_eq!(maude.reduce(input).unwrap(), *expected);
            }
        }
        assert_eq!(native.stats().norm_count, 0);
    }
}

#[test]
fn native_oracle_constructor_results_rebuild_the_open_capture() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::union;
    use crate::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
    use crate::lterm::{pub_term, LSort, LVar, Name, NameTag};
    use crate::maude_proc::MaudeHandle;
    use crate::maude_sig::mset_maude_sig;
    use crate::rewriting::RRule;
    use crate::subst::apply_vterm;
    use crate::subst_vfresh::LNSubstVFresh;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::{f_app_list, f_app_no_eq, Term};
    use crate::vterm::{var_term, Lit};

    let [decode, boxed, ok, bad] = [b"decode".as_slice(), b"box", b"ok", b"bad"]
        .map(|name| NoEqSym::new(name, 1, Privacy::Public, Constructability::Constructor));
    let call = |head, t| f_app_no_eq(head, vec![t]);
    let x = msg_var("x", 17);
    let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
    let mut theory = mset_maude_sig();
    theory.st_fun_syms.extend([decode, boxed, ok, bad]);
    let lhs = call(decode, call(boxed, x.clone()));
    theory.st_rules.insert(rule(lhs, call(ok, x.clone())));

    // The Node makes the product a kind-level observation, and its six
    // factors exceed the bounded frontier's work allowance.
    let marker = pub_term("marker");
    let node = Term::Lit(Lit::Con(Name::new(NameTag::Node, "event")));
    let product = (1..6).fold(node, |t, _| union(t, marker.clone()));
    let key = LVar::new("input", LSort::Msg, 42);
    let input = var_term(key);
    let query = f_app_list(vec![
        call(decode, input.clone()),
        input.clone(),
        product.clone(),
    ]);
    let open_msg = |t: &LNTerm| matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg);
    let check_rows = |h: &MaudeHandle, oracle: Option<&MaudeHandle>| {
        let mut open = false;
        let mut specialized = false;
        assert_eq!(h.reduce(&product).unwrap(), product);
        for row in h.variants(&query).unwrap() {
            assert!(row.iter().all(|(v, _)| *v == key));
            let subst = LNSubstVFresh::from_list(row).fresh_to_free_avoiding_vars(&[key]);
            let image = apply_vterm(&subst, input.clone());
            let application = call(decode, image.clone());
            let result = match &image {
                Term::App(FunSym::NoEq(f), args) if *f == boxed => {
                    let [capture] = args.as_ref() else {
                        panic!("expected one box argument")
                    };
                    specialized |= open_msg(capture);
                    call(ok, capture.clone())
                }
                _ => {
                    open |= open_msg(&image);
                    application.clone()
                }
            };
            // Unfiltered folding can include redundant specializations. Each
            // image must be normal, and rebuilding must preserve its capture.
            assert_eq!(h.reduce(&image).unwrap(), image);
            assert_eq!(h.reduce(&application).unwrap(), result);
            if let Some(maude) = oracle {
                assert_eq!(maude.reduce(&image).unwrap(), image);
                assert_eq!(maude.reduce(&application).unwrap(), result);
            }
        }
        assert!(open && specialized);
    };
    let admitted = |sig: &MaudeSig| {
        let packet = Packet::full_table(sig, &[]).unwrap().unwrap();
        super::initialize().unwrap();
        super::LEAN_THREAD
            .with(|_| packet.certifies_table(&packet.equations, 0))
            .unwrap()
    };
    for mut sig in [
        theory.clone().refresh(),
        theory.merge(xor_maude_sig()).refresh(),
    ] {
        let oracle = tamarin_test_support::require_maude_path().map(|path| {
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap()
        });
        if let Some(maude) = &oracle {
            check_rows(maude, None);
        }
        let h = MaudeHandle::start_with_backend(
            "/nonexistent/maude",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        check_rows(&h, oracle.as_ref());
        assert_eq!((h.stats().var_count, h.stats().norm_count), (0, 0));
        assert!(admitted(&sig));

        // Only the specialization x := box(y) overlaps. The two normal
        // results on this input, ok(box(y)) and bad(y), are distinguishable.
        sig.st_rules.insert(rule(
            call(decode, call(boxed, call(boxed, x.clone()))),
            call(bad, x.clone()),
        ));
        assert!(!admitted(&sig.refresh()));
    }
}

#[test]
fn native_oracle_defined_patterns_and_results_join_on_specialization() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::union;
    use crate::function_symbols::{AcFctSym, AcSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::lterm::{pub_term, LSort, LVar, Name, NameTag};
    use crate::maude_proc::MaudeHandle;
    use crate::maude_sig::mset_maude_sig;
    use crate::rewriting::RRule;
    use crate::subst::apply_vterm;
    use crate::subst_vfresh::LNSubstVFresh;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::{f_app_ac, f_app_list, f_app_no_eq, Term};
    use crate::vterm::{var_term, Lit};

    let symbol = |name: &[u8], arity| {
        NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
    };
    let [decode, boxed, inspect, check] =
        [b"decode".as_slice(), b"box", b"inspect", b"check"].map(|name| symbol(name, 1));
    let [a, b] = [b"a", b"b"].map(|name| symbol(name, 0));
    let mut sig = mset_maude_sig();
    sig.st_fun_syms
        .extend([decode, boxed, inspect, check, a, b]);
    let [a, b] = [a, b].map(|f| f_app_no_eq(f, vec![]));
    let call = |f, t| f_app_no_eq(f, vec![t]);
    let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
    let x = msg_var("x", 17);
    let outer = |x| call(inspect, call(check, x));
    let decoder = |x| call(decode, call(boxed, x));
    for equation in [
        rule(decoder(x.clone()), call(check, x.clone())),
        rule(call(check, a.clone()), b.clone()),
        rule(outer(x.clone()), x),
    ] {
        sig.st_rules.insert(equation);
    }
    let joins = rule(call(inspect, b.clone()), a.clone());
    sig.st_rules.insert(joins.clone());
    let mut sig = sig.refresh();

    // The kind-level multiset pushes this open query beyond bounded folding.
    let node = Term::Lit(Lit::Con(Name::new(NameTag::Node, "event")));
    let mask = (1..6).fold(node, |t, _| union(t, pub_term("marker")));
    let key = LVar::new("input", LSort::Msg, 42);
    let input = var_term(key);
    let query = f_app_list(vec![
        decoder(input.clone()),
        outer(input.clone()),
        input.clone(),
        mask,
    ]);
    let check_rows = |h: &MaudeHandle| {
        let (mut open, mut hit) = (false, false);
        for row in h.variants(&query).unwrap() {
            assert!(row.iter().all(|(v, _)| *v == key));
            let restored = LNSubstVFresh::from_list(row).fresh_to_free_avoiding_vars(&[key]);
            let image = apply_vterm(&restored, input.clone());
            open |= matches!(&image, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg);
            hit |= image == a;
            let expected = if image == a {
                b.clone()
            } else {
                call(check, image.clone())
            };
            assert_eq!(h.reduce(&image).unwrap(), image);
            assert_eq!(h.reduce(&decoder(image.clone())).unwrap(), expected);
            assert_eq!(h.reduce(&outer(image.clone())).unwrap(), image);
        }
        assert!(open && hit);
    };
    if let Some(path) = tamarin_test_support::require_maude_path() {
        check_rows(
            &MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap(),
        );
    }
    let h = MaudeHandle::start_with_backend(
        "/nonexistent/maude",
        sig.clone(),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    check_rows(&h);
    assert_eq!((h.stats().var_count, h.stats().norm_count), (0, 0));

    let admitted = |sig: &MaudeSig| {
        let packet = Packet::full_table(sig, &[]).unwrap().unwrap();
        super::initialize().unwrap();
        super::LEAN_THREAD
            .with(|_| packet.certifies_table(&packet.equations, 4))
            .unwrap()
    };
    assert!(admitted(&sig));

    // Add a user-declared AC unit to the same table. Its unit is the
    // constant that exposes the nested overlap and the active RHS call.
    let join = AcFctSym::new(
        b"join",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let join_a = |t| f_app_ac(AcSym::AcFct(join), vec![t, a.clone()]);
    let local = msg_var("item", 19);
    sig.st_ac_fun_syms.insert(join);
    sig.st_rules.insert(rule(join_a(local.clone()), local));
    sig = sig.refresh();
    assert!(admitted(&sig));
    let mixed = join_a(decoder(outer(a.clone())));
    let mixed_handle = MaudeHandle::start_with_backend(
        "/nonexistent/maude",
        sig.clone(),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    assert_eq!(mixed_handle.reduce(&mixed).unwrap(), b);
    assert_eq!(mixed_handle.stats().norm_count, 0);
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let maude =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        assert_eq!(maude.reduce(&mixed).unwrap(), b);
    }

    // inspect(check(a)) now has distinct normal forms reached at its root and inside its argument.
    sig.st_rules.remove(&joins);
    assert!(!admitted(&sig.refresh()));
}
