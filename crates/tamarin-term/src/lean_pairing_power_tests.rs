use super::*;
use crate::algebra_backend::AlgebraBackend;
use crate::builtin::{emap, exp, fresh_var, msg_var};
use crate::maude_sig::bp_maude_sig;

#[test]
fn native_oracle_pairing_power_preserves_joint_witnesses() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = bp_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
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
