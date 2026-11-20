//! Keep the numeric input of the Lean presentation theorems tied to the
//! production encoder. Rows are read back in the same order as Packet::rows().
use super::Packet;
use crate::builtin::{dh_neutral, exp, inv, msg_var, mult, one_const, xor, zero_const};
use crate::lterm::LNTerm;
use crate::maude_sig::{
    asym_enc_maude_sig, dh_maude_sig, location_report_maude_sig, minimal_maude_sig,
    reveal_signature_maude_sig, signature_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};

#[test]
fn physical_dh_table_matches_the_lean_presentation() {
    check_packet(
        dh_maude_sig(),
        &dh_observations(),
        "DHWire",
        include_str!("../../../../../lean/Tamarin/DHWireData.lean"),
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
        include_str!("../../../../../lean/Tamarin/DHConstructorWireData.lean"),
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
        include_str!("../../../../../lean/Tamarin/XorConstructorWireData.lean"),
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
