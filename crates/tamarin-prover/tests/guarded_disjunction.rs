// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

mod common;

/// Upstream #882 collapses duplicate alternatives at construction time. This
/// must insert a self-ordering atom, rather than retain a disjunction goal.
#[test]
fn negated_last_tautology_has_the_upstream_cyclic_proof() {
    if !common::maude_available() {
        return;
    }
    let (code, output, error) = common::run_raw(
        "tamarin_guarded_disjunction",
        "last_tautology",
        r#"theory LastTautology begin
rule Emit: [] --[A()]-> []
lemma nested: "All #i. A()@i ==> (not last(i) | last(i))"
end"#,
        &["--prove"],
    );
    assert_eq!(code, 0, "{error}");
    assert!(
        output.contains("simplify\nby contradiction /* cyclic */"),
        "{output}"
    );
    assert!(
        output.contains("nested (all-traces): verified (2 steps)"),
        "{output}"
    );
    assert!(
        !output.contains("by contradiction /* from formulas */"),
        "{output}"
    );
}
