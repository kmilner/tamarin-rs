//! Keep the numeric input of the Lean DH presentation theorem tied to the
//! production encoder. Rows are read back in the same order as Packet::rows().
use super::Packet;
use crate::builtin::{dh_neutral, exp, inv, msg_var, mult, one_const};
use crate::maude_sig::dh_maude_sig;

#[test]
fn physical_dh_table_matches_the_lean_presentation() {
    let [x, y, z] = [1, 2, 3].map(|i| msg_var("x", i));
    let observations = [
        exp(x.clone(), y.clone()),
        inv(z),
        one_const(),
        dh_neutral(),
        mult(x, y),
    ];
    let packet = Packet::full_table(&dh_maude_sig(), &observations)
        .unwrap()
        .unwrap();
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
    let (_, fixture) = include_str!("../../../../../lean/Tamarin/DHWireData.lean")
        .split_once("namespace Tamarin.DHWire\n")
        .unwrap();
    let fixture = fixture.strip_suffix("end Tamarin.DHWire\n").unwrap();
    assert_eq!(
        compact(fixture),
        compact(&arrays),
        "DH packet changed:\n{arrays}"
    );
}
