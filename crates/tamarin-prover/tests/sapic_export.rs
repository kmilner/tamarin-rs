// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Typed-export round trips for upstream #960's `typeTheoryForExport`
//! in `Sapic/Typing.hs`.

mod common;

const PATTERNS: &str = r#"theory Patterns begin
let P(pat_x) = in(pat_x); event Seen(pat_x)
let Twice(pat_x) = in(pat_x); in(pat_x); event Twice(pat_x)
let Nested(pat_x) = P(pat_x)
let Value(x) = event Value(x)
process: new pat_x; (P(<'a','b'>) | Twice('c') | Nested('d') | Value('e'))
lemma supplied_patterns: "All x #i. Seen(x)@i ==> x = <'a','b'> | x = 'd'"
lemma repeated_pattern: "All x #i. Twice(x)@i ==> x = 'c'"
lemma pair_reachable: exists-trace "Ex #i. Seen(<'a','b'>)@i"
lemma nested_reachable: exists-trace "Ex #i. Seen('d')@i"
lemma repeated_reachable: exists-trace "Ex #i. Twice('c')@i"
lemma ordinary_parameter: exists-trace "Ex #i. Value('e')@i"
end"#;

const OPEN: &str = r#"theory Open begin
let P = event Seen(x)
let Wrapped(x) = P
process: (new x; event Created(x); P) |
         (new x; event Created(x); P) | Wrapped('a')
lemma caller_binding:
  "All x #i. Seen(x)@i ==> x = 'a' | (Ex #j. Created(x)@j & j < i)"
lemma distinct_callers: exists-trace
  "Ex x y #i #j #k #l. Created(x)@i & Created(y)@j &
   Seen(x)@k & Seen(y)@l & not(x = y)"
lemma closed_wrapper: exists-trace "Ex #i. Seen('a')@i"
end"#;

const LOCATIONS: &str = r#"theory Locations begin
builtins: locations-report
predicates: Report(x,l) <=> T
let Pattern(pat_x) = in(pat_x); event Pattern(report(pat_x))
let Open = event Caller(report(x))
let Inner = (event Inner(report(x)))@'inner'
process: (Pattern('a'))@'outer' |
         (new x; (Open)@x) | (new x; (Inner)@'outer')
lemma pattern_location: exists-trace "Ex #i. Pattern(rep('a','outer'))@i"
lemma caller_location: exists-trace "Ex x #i. Caller(rep(x,x))@i"
lemma inner_location: exists-trace "Ex x #i. Inner(rep(x,'inner'))@i"
lemma inner_overrides_caller: "All x l #i. Inner(rep(x,l))@i ==> l = 'inner'"
end"#;

fn run(stem: &str, source: &str, flags: &[&str]) -> (i32, String, String) {
    common::run_raw("tamarin_sapic_export", stem, source, flags)
}

#[test]
fn typed_exports_preserve_patterns_bindings_locations_and_proofs() {
    if !common::maude_available() {
        return;
    }
    for (name, source, named, lemmas) in [
        ("patterns", PATTERNS, Some("Value"), 6),
        ("open", OPEN, Some("Wrapped"), 3),
        ("locations", LOCATIONS, None, 4),
    ] {
        let (code, exported, err) = run(name, source, &["-m=spthytyped", "--quit-on-warning"]);
        assert_eq!(code, 0, "{name}: {err}");
        let parsed = tamarin_parser::parse_theory(&exported, &[]).unwrap();
        let theory = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        let defs: Vec<_> = theory.process_defs().map(|p| p.name.as_str()).collect();
        assert_eq!(defs, named.into_iter().collect::<Vec<_>>(), "{name}");
        for (kind, input) in [("source", source), ("roundtrip", exported.as_str())] {
            let (code, output, err) = run(
                &format!("{name}_{kind}"),
                input,
                &["--prove", "--quit-on-warning"],
            );
            assert_eq!(code, 0, "{name}/{kind}: {err}");
            let results: Vec<_> = output
                .lines()
                .filter(|s| s.contains(" (all-traces):") || s.contains(" (exists-trace):"))
                .collect();
            assert_eq!(results.len(), lemmas, "{name}/{kind}: {output}");
            assert!(
                results.iter().all(|s| s.contains(": verified")),
                "{name}/{kind}: {results:?}"
            );
        }
    }
}

#[test]
fn typed_export_removes_open_msr_definitions_without_spurious_parameters() {
    if !common::maude_available() {
        return;
    }
    let source = "theory OpenMsrTyped begin
        let P = [F(x), G(x:a)] --> []; out(x)
        process: P
        end";
    let (code, exported, err) = run("msr", source, &["-m=spthytyped", "--quit-on-warning"]);
    assert_eq!(code, 0, "{err}");
    let parsed = tamarin_parser::parse_theory(&exported, &[]).unwrap();
    let theory = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
    assert_eq!(theory.process_defs().count(), 0);
    assert_eq!(exported.matches(":a").count(), 3, "{exported}");
}

#[test]
fn typed_export_checks_declarations_and_unused_arguments_before_inlining() {
    if !common::maude_available() {
        return;
    }
    for (label, process) in [("used", "P('c')"), ("unused", "0")] {
        for (signature, succeeds) in [("f/1", true), ("f(b):b", false)] {
            let source = format!(
                "theory Types begin
                functions: {signature}
                let P(pat_x:a) = in(pat_x:a); out(f(pat_x:a))
                process: {process}
                end"
            );
            let (code, exported, err) = run(
                &format!("types_{label}_{succeeds}"),
                &source,
                &["-m=spthytyped", "--quit-on-warning"],
            );
            if succeeds {
                assert_eq!(code, 0, "{label}: {err}");
                assert!(exported.contains("function: f (a) : Any"), "{exported}");
            } else {
                assert_eq!(code, 1, "{label}: {exported}");
                assert!(err.contains("Typing error: expected term"), "{err}");
            }
        }
    }
    let source = "theory UnusedArgument begin
        let P(pat_x,y) = in(pat_x); out('a')
        process: P('x',unbound)
        end";
    let (code, _, err) = run(
        "unused_arg",
        source,
        &["-m=spthytyped", "--quit-on-warning"],
    );
    assert_eq!(code, 1);
    assert!(
        err.contains("The variable(s) unbound are not bound."),
        "{err}"
    );
}
