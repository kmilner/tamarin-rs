// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

mod common;

#[test]
fn auto_sources_keeps_injectivity_based_on_macro_expanded_original_rules() {
    if !common::maude_available() {
        return;
    }
    let source = r#"theory MacroInjectiveAuto begin
builtins: symmetric-encryption
macros: projection(x) = fst(<x,'c'>)
rule Create: [Fr(~id)] --[Cr(~id)]-> [S(projection(~id)), Once(~id)]
rule Use: [S(id), Once(id)] --[Use(id)]-> [S(id)]
rule Fin: [S(id)] --[Fin(id), FinArgument(id,$x)]-> []
rule Key: [Fr(~k)] --> [!Key(~k)]
rule Dec: [!Key(~k),In(x)] --[Dec(sdec(x,~k))]-> [Out(sdec(x,~k))]
tactic: prem
presort: S
prio:
  regex "last\(#j\)"
prio:
  regex "▶₀ #j"
lemma induction_counterexample [use_induction, heuristic={prem}]:
  "All id #i #j #k. Cr(id)@i & Fin(id)@j & Fin(id)@k & #i < #j & #i < #k
    & not (Ex #u. Use(id)@u) ==> F"
end
"#;
    let (code, stdout, stderr) = common::run_raw(
        "tamarin_injective_auto_sources",
        "original_e",
        source,
        &[
            "--prove",
            "--auto-sources",
            "--no-ndc",
            "--derivcheck-timeout=0",
            "--quit-on-warning",
            "--processors=1",
        ],
    );
    assert_eq!(code, 0, "{stderr}");
    // The original first argument is reducible, so S is not marked injective
    // even though the unfolded member has the fresh name as its first term.
    assert!(
        !stdout.contains("looping facts with injective instances:"),
        "{stdout}"
    );
    // Pristine Haskell a75fec7f: using the compiled member instead enables
    // extra injectivity simplifications and changes the induction proof.
    assert!(
        stdout.contains("induction_counterexample (all-traces): falsified - found trace (5 steps)"),
        "{stdout}"
    );
    assert!(
        stdout.contains("AUTO_typing (all-traces): verified (8 steps)"),
        "{stdout}"
    );
}
