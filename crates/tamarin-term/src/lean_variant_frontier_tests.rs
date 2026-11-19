//! Value and substitution checks for finite variant narrowing.
use super::{canonical_small_ac_answers, valued_variant_rows};
use crate::algebra_backend::AlgebraBackend;
use crate::builtin::msg_var;
use crate::function_symbols::{AcFctSym, AcSym, Constructability, NdcState, NoEqSym, Privacy};
use crate::lean_unification::{Outcome, RuleTable, Substitutions};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_proc::MaudeHandle;
use crate::maude_sig::{hash_maude_sig, MaudeSig};
use crate::rewriting::RRule;
use crate::subterm_rule::rrule_to_ctxt_st_rule;
use crate::term::{f_app_ac, f_app_list, f_app_no_eq};
use tamarin_test_support::require_maude_path;

fn symbol(name: &'static [u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
}

fn add_rule(sig: &mut MaudeSig, lhs: LNTerm, rhs: LNTerm) {
    sig.st_rules
        .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap());
}

fn handles(sig: MaudeSig) -> Option<(MaudeHandle, MaudeHandle)> {
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return None;
    }
    let path = require_maude_path()?;
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    Some((native, maude))
}

// Each entry describes the first observed value as an AC product. The second
// observed value is x. Input images precede the two values in valued_variant_rows.
#[derive(Clone, Copy)]
enum Query {
    XRed,
    XX,
    XY,
    XRedBlue,
}

impl Query {
    fn factors(self, x: &[LNTerm], y: &[LNTerm], markers: &[LNTerm; 2]) -> Vec<LNTerm> {
        let extras = match self {
            Self::XRed => &markers[..1],
            Self::XX => x,
            Self::XY => y,
            Self::XRedBlue => markers,
        };
        [x, extras].concat()
    }

    // In a normal input each marker occurs at most once. Condition on which
    // markers collide in the product, then let each affected input contain
    // exactly those markers or those markers and a nonempty independent rest.
    fn expected(self, op: AcSym, markers: &[LNTerm; 2]) -> Substitutions {
        let inputs = if matches!(self, Self::XY) { 2 } else { 1 };
        let masks = if matches!(self, Self::XRed) { 2 } else { 4 };
        let mut rows = Vec::new();
        for collisions in 0..masks {
            for tails in 0..(1 << inputs) {
                let mut images = Vec::new();
                for i in 0..inputs {
                    let mut terms: Vec<_> = markers
                        .iter()
                        .enumerate()
                        .filter(|(bit, _)| collisions & (1 << bit) != 0)
                        .map(|(_, m)| m.clone())
                        .collect();
                    if tails & (1 << i) != 0 {
                        terms.push(msg_var("rest", i as u64));
                    }
                    images.push(terms);
                }
                if images.iter().any(Vec::is_empty) {
                    continue;
                }
                let y = images.get(1).map_or(&[][..], Vec::as_slice);
                let mut factors = self.factors(&images[0], y, markers);
                // R and B contract; equal occurrences of a tail do not.
                for marker in markers {
                    let mut seen = false;
                    factors.retain(|t| t != marker || !std::mem::replace(&mut seen, true));
                }
                let mut values: Vec<_> = images.into_iter().map(|ts| f_app_ac(op, ts)).collect();
                values.push(f_app_ac(op, factors));
                values.push(values[0].clone());
                rows.push(vec![(LVar::new("row", LSort::Msg, 0), f_app_list(values))]);
            }
        }
        canonical_small_ac_answers(rows)
    }
}

// Ground reduction in Maude uses the proper AC subproduct rewrite even when
// variant generation omits its extension. Check coverage over rigid name
// multiplicities and every subset of the two markers in each actual input.
fn check_ground_coverage(
    maude: &MaudeHandle,
    slots: &[LNTerm],
    rows: &Substitutions,
    op: AcSym,
    markers: &[LNTerm; 2],
) {
    use crate::lterm::{frees_list, pub_term};
    use crate::subst::{apply_vterm, Subst};
    use std::collections::BTreeSet;
    let mut pool = Vec::new();
    for mask in 0..4 {
        for names in 0..=2 {
            let mut atoms = vec![pub_term("c"); names];
            for (i, marker) in markers.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    atoms.push(marker.clone());
                }
            }
            if !atoms.is_empty() {
                pool.push(f_app_ac(op, atoms));
            }
        }
    }
    // Each ground assignment to the at most two distinct variables of a
    // row is simultaneous across all images and result columns.
    let instantiate = |t: &LNTerm| {
        let mut vars = frees_list(t);
        vars.sort();
        vars.dedup();
        assert!(vars.len() <= 2);
        let mut instances = BTreeSet::new();
        for a in &pool {
            for b in &pool {
                let subst = Subst::from_list(vars.iter().copied().zip([a.clone(), b.clone()]));
                instances.insert(apply_vterm(&subst, t.clone()));
            }
        }
        instances
    };
    let represented: BTreeSet<_> = rows.iter().flat_map(|row| instantiate(&row[0].1)).collect();
    let mut keys = frees_list(&f_app_list(slots.to_vec()));
    keys.sort();
    keys.dedup();
    let key_terms = keys.into_iter().map(crate::vterm::var_term);
    let observations = f_app_list(key_terms.chain(slots.iter().cloned()).collect());
    for concrete in instantiate(&observations) {
        let crate::term::Term::App(_, fields) = concrete else {
            unreachable!()
        };
        let target = f_app_list(fields.iter().map(|t| maude.reduce(t).unwrap()).collect());
        assert!(
            represented.contains(&target),
            "missing {target} for {}",
            slots[0]
        );
    }
}

#[test]
fn native_oracle_finite_ac_variants_include_proper_subproducts() {
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let merge = AcFctSym::new(
        b"merge",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let op = AcSym::AcFct(merge);
    let mut sig = hash_maude_sig();
    sig.st_ac_fun_syms.insert(merge);
    let markers = [symbol(b"red", 0), symbol(b"blue", 0)].map(|m| {
        sig.st_fun_syms.insert(m);
        let value = f_app_no_eq(m, vec![]);
        add_rule(
            &mut sig,
            f_app_ac(op, vec![value.clone(), value.clone()]),
            value.clone(),
        );
        value
    });
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
    let oracles = tamarin_test_support::maude_path().map(|path| {
        let raw =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        // This rule contracts the same two occurrences under a nonempty AC
        // remainder. It adds an explicit narrowing position for Maude.
        let mut extended = sig;
        let rest = msg_var("extra", 3);
        for marker in &markers {
            let lhs = f_app_ac(op, vec![marker.clone(), marker.clone(), rest.clone()]);
            let rhs = f_app_ac(op, vec![marker.clone(), rest.clone()]);
            add_rule(&mut extended, lhs, rhs);
        }
        let extended =
            MaudeHandle::start_with_backend(&path, extended.refresh(), AlgebraBackend::Maude)
                .unwrap();
        (raw, extended)
    });
    let x = msg_var("x", 0);
    let y = msg_var("y", 1);
    for (kind, count) in [
        (Query::XRed, 3),
        (Query::XX, 7),
        (Query::XY, 13),
        (Query::XRedBlue, 7),
    ] {
        let factors = kind.factors(std::slice::from_ref(&x), std::slice::from_ref(&y), &markers);
        let slots = [f_app_ac(op, factors), x.clone()];
        let expected = kind.expected(op, &markers);
        assert_eq!(expected.len(), count);
        // Maude 3.5.1 omits proper AC extension variants for these two raw
        // ground equations. For example x = merge(red,z) makes merge(x,red)
        // reduce to x. Both Maude rows (identity and x=red) miss that value.
        let actual = valued_variant_rows(&native, &slots);
        assert_eq!(actual, expected, "{}", slots[0]);
        if let Some((raw, extended)) = &oracles {
            let reference = valued_variant_rows(raw, &slots);
            assert!(!reference.is_empty());
            assert!(
                reference.iter().all(|r| expected.contains(r)),
                "{}",
                slots[0]
            );
            assert_eq!(
                valued_variant_rows(extended, &slots),
                expected,
                "{}",
                slots[0]
            );
            check_ground_coverage(raw, &slots, &actual, op, &markers);
        }
    }
    assert_eq!(native.stats().var_count, 0);
}

#[test]
fn native_oracle_finite_commutative_frontier_keeps_both_orientations() {
    use crate::builtin::{emap, hash};
    use crate::maude_sig::bp_maude_sig;

    let mut sig = bp_maude_sig().merge(hash_maude_sig());
    let [red, result] = [b"red".as_slice(), b"result"].map(|name| {
        let k = symbol(name, 0);
        sig.st_fun_syms.insert(k);
        f_app_no_eq(k, vec![])
    });
    let x = msg_var("x", 0);
    let y = msg_var("y", 1);
    let observe = |a, b| emap(hash(a), hash(b));
    add_rule(&mut sig, observe(red.clone(), x.clone()), result.clone());
    let Some((native, maude)) = handles(sig.refresh()) else {
        return;
    };
    // The rigid hash heads exclude point multiplication. Either observed
    // message can specialize to red, and the overlapping cases agree.
    for (other, count) in [(y.clone(), 3), (x.clone(), 2)] {
        let slots = [observe(x.clone(), other.clone()), x.clone(), other];
        let expected = valued_variant_rows(&maude, &slots);
        assert_eq!(expected.len(), count);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
    }
    for t in [observe(red.clone(), y.clone()), observe(x, red)] {
        assert_eq!(native.reduce(&t).unwrap(), result);
    }
}

fn unwrap_signature() -> (MaudeSig, NoEqSym, NoEqSym) {
    let unwrap = symbol(b"unwrap", 1);
    let box_ = symbol(b"box", 1);
    let wrap = symbol(b"wrap", 1);
    let mut sig = hash_maude_sig();
    sig.st_fun_syms.extend([unwrap, box_, wrap]);
    let x = msg_var("x", 0);
    for tag in [box_, wrap] {
        let lhs = f_app_no_eq(unwrap, vec![f_app_no_eq(tag, vec![x.clone()])]);
        add_rule(&mut sig, lhs, x.clone());
    }
    (sig.refresh(), unwrap, box_)
}

#[test]
fn native_oracle_finite_free_variant_frontiers() {
    let (sig, unwrap, _) = unwrap_signature();
    let unbox = |x| f_app_no_eq(unwrap, vec![x]);
    let Some((native, maude)) = handles(sig) else {
        return;
    };
    let (x, y) = (msg_var("m", 0), msg_var("m", 1));
    for (slots, count) in [
        (vec![unbox(x.clone()), x.clone()], 3),
        (vec![unbox(unbox(x.clone())), x.clone()], 7),
        (vec![unbox(x.clone()), unbox(y.clone()), x.clone(), y], 9),
    ] {
        let expected = valued_variant_rows(&maude, &slots);
        assert_eq!(expected.len(), count);
        assert_eq!(valued_variant_rows(&native, &slots), expected, "{slots:?}");
    }
    assert_eq!(native.stats().var_count, 0);
}

#[test]
fn variant_frontier_defers_ambiguous_values_and_incomplete_rule_buckets() {
    let (mut sig, unwrap, box_) = unwrap_signature();
    let x = msg_var("x", 0);
    let unbox = |a| f_app_no_eq(unwrap, vec![a]);
    let boxed = |a| f_app_no_eq(box_, vec![a]);
    let query = f_app_list(vec![unbox(x.clone()), x.clone()]);
    let marker = symbol(b"result", 0);
    sig.st_fun_syms.insert(marker);
    let mut ambiguous = sig.clone();
    // For x=box(z), the same input has distinct irreducible results z and
    // result. The public family returns only substitutions.
    add_rule(&mut ambiguous, unbox(boxed(x)), f_app_no_eq(marker, vec![]));
    let table = RuleTable::new(&ambiguous.refresh()).unwrap();
    assert_eq!(table.joined_variants(&query).unwrap(), Outcome::Unsupported);
    // Runtime name literals in a rule have separate Maude/query identities.
    // A visible supported sibling rule cannot license partial answers.
    add_rule(
        &mut sig,
        unbox(crate::lterm::pub_term("opaque")),
        f_app_no_eq(marker, vec![]),
    );
    let table = RuleTable::new(&sig.refresh()).unwrap();
    assert_eq!(table.joined_variants(&query).unwrap(), Outcome::Unsupported);
}

#[test]
fn variant_frontier_budget_discards_partial_answers() {
    let (sig, unwrap, _) = unwrap_signature();
    let table = RuleTable::new(&sig).unwrap();
    let x = msg_var("m", 0);
    let unbox = |t| f_app_no_eq(unwrap, vec![t]);
    // Besides the identity, either tag may be removed at each layer.
    // Ten layers give 2047 irredundant variants before pairing with x.
    let deep = (0..10).fold(x.clone(), |term, _| unbox(term));
    assert_eq!(
        table
            .joined_variants(&f_app_list(vec![deep, x.clone()]))
            .unwrap(),
        Outcome::Unsupported
    );
    let shallow = f_app_list(vec![unbox(x.clone()), x]);
    assert!(
        matches!(table.joined_variants(&shallow).unwrap(), Outcome::Complete(rows) if rows.len() == 3)
    );
}

#[test]
fn variant_frontier_closed_cycle_without_normal_values_is_empty() {
    use crate::subterm_rule::{CtxtStRule, StRhs};
    let looper = symbol(b"loop", 1);
    let mut sig = hash_maude_sig();
    sig.st_fun_syms.insert(looper);
    let q = f_app_no_eq(looper, vec![msg_var("x", 0)]);
    sig.st_rules.insert(CtxtStRule::new(
        q.clone(),
        StRhs {
            positions: vec![],
            term: q.clone(),
        },
    ));
    let table = RuleTable::new(&sig.refresh()).unwrap();
    assert_eq!(
        table.joined_variants(&q).unwrap(),
        Outcome::Complete(vec![])
    );
}

#[test]
fn native_oracle_frontier_compares_normal_results_on_overlapping_specializations() {
    let f = symbol(b"choose", 2);
    let mut sig = hash_maude_sig();
    sig.st_fun_syms.insert(f);
    let [a, b, left, right] = [b"a".as_slice(), b"b", b"left", b"right"].map(|name| {
        let k = symbol(name, 0);
        sig.st_fun_syms.insert(k);
        f_app_no_eq(k, vec![])
    });
    let x = msg_var("x", 0);
    let y = msg_var("y", 0);
    let choose = |x, y| f_app_no_eq(f, vec![x, y]);
    // Each branch looks functional at its own most general images.
    // Instantiating both at (a,b) exposes two distinct irreducible values.
    add_rule(&mut sig, choose(a, y.clone()), left);
    add_rule(&mut sig, choose(x.clone(), b), right);
    let sig = sig.refresh();
    let table = RuleTable::new(&sig).unwrap();
    let query = f_app_list(vec![choose(x.clone(), y.clone()), x, y]);
    assert_eq!(table.joined_variants(&query).unwrap(), Outcome::Unsupported);
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly).unwrap();
    assert!(matches!(
        native.variants(&query),
        Err(crate::maude_proc::MaudeError::UnsupportedOperation(
            "variant generation"
        ))
    ));
}

#[test]
fn native_oracle_stale_free_rule_head_cannot_certify_a_false_normal_form() {
    use crate::builtin::hash;
    let x = msg_var("x", 0);
    let t = hash(hash(x.clone()));
    // Without AC, both the whole-tree symbol filter and the structural
    // matcher are eligible. Their old indexes still classify hash as inert.
    let mut sig = hash_maude_sig();
    add_rule(&mut sig, t.clone(), x.clone());
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_none() {
        let native = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        assert_eq!(native.reduce(&t).unwrap(), x);
    }
    if let Some(path) = tamarin_test_support::maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&t).unwrap(), x);
    }
}

#[test]
fn native_oracle_nested_repeated_ac_destructors() {
    let merge = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let extract = symbol(b"extract", 1);
    let mut sig = hash_maude_sig();
    sig.st_ac_fun_syms.insert(merge);
    sig.st_fun_syms.insert(extract);
    let sum = |terms| f_app_ac(AcSym::AcFct(merge), terms);
    let d = |t| f_app_no_eq(extract, vec![t]);
    let v = msg_var("v", 0);
    add_rule(&mut sig, d(sum(vec![v.clone(), v.clone()])), v);
    let Some((native, oracle)) = handles(sig.refresh()) else {
        return;
    };
    let x = msg_var("x", 0);
    let y = msg_var("y", 1);
    for (copies, count) in [(1, 35), (3, 10)] {
        let mut terms = vec![x.clone(); copies];
        terms.push(y.clone());
        let slots = [d(d(sum(terms))), x.clone(), y.clone()];
        let expected = valued_variant_rows(&oracle, &slots);
        assert_eq!(expected.len(), count);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_guarded_multi_rule_frontier_preserves_shared_inputs_and_rejects_conflicts() {
    let combine = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let d = symbol(b"decode", 1);
    let wrapper = symbol(b"wrap", 1);
    let marker = symbol(b"marker", 0);
    let mut sig = hash_maude_sig();
    sig.st_ac_fun_syms.insert(combine);
    sig.st_fun_syms.extend([d, wrapper, marker]);
    let sum = |terms| f_app_ac(AcSym::AcFct(combine), terms);
    let call = |f, t| f_app_no_eq(f, vec![t]);
    let v = msg_var("v", 0);
    add_rule(
        &mut sig,
        call(d, sum(vec![v.clone(), v.clone()])),
        v.clone(),
    );
    add_rule(&mut sig, call(d, call(wrapper, v.clone())), v.clone());
    let x = msg_var("x", 0);
    let y = msg_var("y", 1);
    let slots = [call(d, call(d, sum(vec![x.clone(), y.clone()]))), x, y];
    let obs = f_app_list(slots.to_vec());
    let positive = sig.clone().refresh();
    let table = RuleTable::new(&positive).unwrap();
    let Outcome::Complete(rows) = table.joined_variants(&obs).unwrap() else {
        panic!("the live decode rules agree on normal inputs");
    };
    assert_eq!(rows.len(), 36);

    // With x = y = wrap(a), the inner result is wrap(a). Two live
    // rules can now give the distinct normal results a and marker.
    add_rule(
        &mut sig,
        call(d, call(wrapper, v)),
        f_app_no_eq(marker, vec![]),
    );
    let conflicting = RuleTable::new(&sig.refresh()).unwrap();
    assert!(matches!(
        conflicting.joined_variants(&obs).unwrap(),
        Outcome::Unsupported
    ));
    let a = crate::lterm::pub_term("a");
    let w = call(wrapper, a);
    let concrete = call(d, call(d, sum(vec![w.clone(), w])));
    assert_eq!(conflicting.reduce_native(&concrete).unwrap(), None);

    if let Some((native, oracle)) = handles(positive) {
        let expected = valued_variant_rows(&oracle, &slots);
        assert_eq!(expected.len(), 36);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
        assert_eq!(native.stats().var_count, 0);
    }
}
