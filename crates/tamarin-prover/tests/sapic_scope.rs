// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Nested closed-call scope regressions from upstream #960's
//! `Theory/Sapic/Process.hs` (`expandProcessCall`).

mod common;

#[test]
fn nested_closed_binders_keep_their_scope_through_open_wrappers() {
    if !common::maude_available() {
        return;
    }
    for (name, wrapper) in [
        ("open", "let W(x) = O"),
        ("closed", "let W(x) = ClosedO()"),
        ("direct", "let W(x) = C()"),
        ("renamed", "let W(y) = O"),
    ] {
        let source = format!(
            "theory NestedClosedScope begin
            let C() = new x; event Seen(x)
            let O = C()
            let ClosedO() = C()
            {wrapper}
            process: W('a')
            lemma reachable: exists-trace \"Ex x #i. Seen(x)@i\"
            lemma fresh_value: \"All x #i. Seen(x)@i ==> not (x = 'a')\"
            end"
        );
        let (code, output, err) = common::run_raw(
            "tamarin_sapic_scope",
            name,
            &source,
            &["--prove", "--quit-on-warning"],
        );
        assert_eq!(code, 0, "{name}: {err}");
        for lemma in ["reachable (exists-trace)", "fresh_value (all-traces)"] {
            assert!(
                output.contains(&format!("{lemma}: verified")),
                "{name}: {output}"
            );
        }
    }
}

#[test]
fn nested_local_pattern_name_is_not_an_outer_pattern_parameter() {
    if !common::maude_available() {
        return;
    }
    let source = "theory NestedLocalPattern begin
        let C() = in(pat_x); event Seen(pat_x)
        let O = C()
        let W(pat_x) = O
        process: W('a')
        lemma another_input: exists-trace \"Ex #i. Seen('b')@i\"
        lemma only_argument: \"All x #i. Seen(x)@i ==> x = 'a'\"
        end";
    let (code, output, err) = common::run_raw(
        "tamarin_sapic_scope",
        "local_pattern",
        source,
        &["--prove", "--quit-on-warning"],
    );
    assert_eq!(code, 0, "{err}");
    assert!(
        output.contains("another_input (exists-trace): verified"),
        "{output}"
    );
    assert!(
        output.contains("only_argument (all-traces): falsified"),
        "{output}"
    );
}

#[test]
fn nested_closed_calls_still_reject_repeated_local_binders() {
    if !common::maude_available() {
        return;
    }
    for (kind, binder) in [("new", "new x"), ("input", "in(x)")] {
        for (wrapper, params) in [("open", ""), ("closed", "()")] {
            let source = format!(
                "theory NestedClosedRebinding begin
                let C() = {binder}; {binder}; event Seen(x)
                let O{params} = C()
                process: O{params}
                end"
            );
            let (code, output, err) = common::run_raw(
                "tamarin_sapic_scope",
                &format!("{wrapper}_{kind}"),
                &source,
                &["--quit-on-warning"],
            );
            assert_eq!(code, 1, "{wrapper}/{kind}: {output}");
            assert!(
                output.contains("Variable bound twice") || err.contains("Variable bound twice"),
                "{wrapper}/{kind}: {output}\n{err}"
            );
        }
    }
}
