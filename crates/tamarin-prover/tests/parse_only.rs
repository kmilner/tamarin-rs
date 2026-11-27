// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The `--parse-only` printer is a fixed point on reparsable output.
//!
//! The printer's bytes against the oracle are the `po_*` divergence
//! fixtures and the `--parse-only` rows of cli_refs; this file checks that
//! printing a parsed theory and parsing the print gives the same print.

use std::process::Command;

/// Write `files` into a fresh per-test temp dir and run
/// `tamarin-rs --parse-only <inputs>` FROM that dir (bare file names, so any
/// path-bearing output matches the oracle capture invocation exactly),
/// returning `(exit code, stdout, stderr)`.
fn run_parse_only(test: &str, files: &[(&str, &str)], inputs: &[&str]) -> (i32, String, String) {
    let dir = std::env::temp_dir().join(format!("tamarin_rs_parse_only_{}", test));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    for (name, body) in files {
        std::fs::write(dir.join(name), body).expect("write fixture");
    }
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    cmd.current_dir(&dir).arg("--parse-only");
    for i in inputs {
        cmd.arg(i);
    }
    let out = cmd.output().expect("spawn tamarin-rs");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn assert_round_trip(test: &str, source: &str) -> String {
    let source_name = "source.spthy";
    let (first_code, first, first_err) =
        run_parse_only(test, &[(source_name, source)], &[source_name]);
    assert_eq!(first_code, 0, "first parse failed:\n{first_err}");

    let printed_name = "printed.spthy";
    let (second_code, second, second_err) = run_parse_only(
        &format!("{test}_printed"),
        &[(printed_name, &first)],
        &[printed_name],
    );
    assert_eq!(
        second_code, 0,
        "printed theory failed to parse:\n{second_err}"
    );
    assert_eq!(second, first, "theory changed on its second print");
    first
}

/// The output constructs changed upstream specifically to make open theories
/// reparsable. Exercise them together, pin the first print to the patched
/// Haskell output, then require the second print to be identical.
#[test]
fn reparsable_output_round_trip() {
    let printed = assert_round_trip(
        "reparsable_output_round_trip",
        r#"theory RoundTrip
begin

builtins: locations-report, reliable-channel, dest-pairing
options: translation-progress, translation-allow-pattern-lookups,
         translation-state-optimisation, translation-asynchronous-channels,
         translation-compress-events
functions: f(bitstring):skey, dec(bitstring):bitstring [destructor]

export queries: "  path \\\\ and quote \\\" stay"

let P(x) = out(x)

process:
  ((new x; P(x)) | (event E() + out('y')))@'loc'

equivLemma:
  (new x; out(x))
  (out('a') | out('b'))

end
"#,
    );
    assert_eq!(
        printed,
        r#"theory RoundTrip

begin

// Function signature and definition of the equational theory E

functions: check_rep/2 [destructor], dec/1 [destructor], f/1,
           fst/1 [destructor], get_rep/1 [destructor], pair/2,
           rep/2 [private,constructor], report/1, snd/1 [destructor]
equations:
    check_rep(rep(x.1, x.2), x.2) = x.1,
    fst(<x.1, x.2>) = x.1,
    get_rep(rep(x.1, x.2)) = x.1,
    snd(<x.1, x.2>) = x.2

options: translation-progress, translation-allow-pattern-lookups,
         translation-state-optimisation, translation-asynchronous-channels,
         translation-compress-events

builtins: locations-report

builtins: reliable-channel

builtins: dest-pairing

function: f (bitstring) : skey

function: dec (bitstring) : bitstring [destructor]

export queries : "  path \\\\ and quote \\\" stay"

let  P (x) = out(x)

process:
  ((new x;
    P(x)) | (event E( ) + out('y')))@'loc'

equivLemma:
  (new x;
   out(x))
  (out('a') | out('b'))

end
"#
    );
}
