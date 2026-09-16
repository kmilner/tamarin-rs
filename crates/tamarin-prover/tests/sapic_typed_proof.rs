//! Generated SAPIC rule names are part of the stored-proof format.

mod common;

#[test]
fn replay_preserves_typed_sapic_case_names() {
    if !common::maude_available() {
        return;
    }
    // Proof captured from the pinned Haskell prover. Plain loading must check
    // it successfully without --prove repairing a renamed or missing case.
    let source = r#"theory TypedProof
begin
process: new x:lol; event Seen(x)
lemma seen: exists-trace "Ex x #i. Seen(x) @ i"
simplify
solve( State_1( x ) ▶₀ #i )
  case newxlol_0_
  SOLVED
qed
end
"#;
    let (code, stdout, stderr) = common::run_raw(
        "tamarin_sapic_typed_proof",
        "stored",
        source,
        &["--derivcheck-timeout=0"],
    );
    assert_eq!(code, 0, "{stderr}");
    assert!(
        stdout.contains("seen (exists-trace): verified (3 steps)"),
        "{stdout}"
    );
    assert!(stdout.contains("case newxlol_0_"), "{stdout}");
    assert!(stdout.contains("rule (modulo E) newxlol_0_["), "{stdout}");
    assert!(stdout.contains("process=\"new x.1:lol;\""), "{stdout}");
    assert!(!stdout.contains("unannotated"), "{stdout}");
}
