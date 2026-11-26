use super::*;
use crate::algebra_backend::AlgebraBackend;
use crate::builtin::{emap, exp, fresh_var, inv, msg_var, pmult};
use crate::maude_sig::bp_maude_sig;

#[test]
fn native_oracle_pairing_power_preserves_joint_witnesses() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = bp_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = msg_var("x", 0);
    let y = msg_var("y", 1);
    let r = fresh_var("r", 0);
    for (point, count) in [(x.clone(), 8), (y, 160)] {
        let slots = [
            exp(emap(x.clone(), point.clone()), r.clone()),
            point,
            x.clone(),
            r.clone(),
        ];
        let got = valued_variant_rows(&native, &slots);
        let wanted = valued_variant_rows(&oracle, &slots);
        assert_eq!(wanted.len(), count);
        assert_eq!(got.len(), wanted.len());
        assert_eq!(got, wanted);
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_power_over_changing_point_spines() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = bp_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = msg_var("x", 0);
    let r = fresh_var("r", 0);
    let a = pub_term("a");
    let b = pub_term("b");
    let left = pmult(r.clone(), pmult(x.clone(), a.clone()));
    let right = pmult(inv(r.clone()), b.clone());
    let map = emap(left, right);
    let slots = [exp(map, r.clone()), x, r.clone()];
    let got = valued_variant_rows(&native, &slots);
    let wanted = valued_variant_rows(&oracle, &slots);
    assert_eq!(wanted.len(), 6);
    assert_eq!(got, wanted);

    let left = pmult(r.clone(), pmult(r.clone(), a.clone()));
    let right = pmult(inv(r.clone()), b.clone());
    let cancelled = exp(emap(left, right), inv(r));
    let result = native.reduce(&cancelled).unwrap();
    assert_eq!(result, emap(a, b));
    assert_eq!(result, oracle.reduce(&cancelled).unwrap());
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}
