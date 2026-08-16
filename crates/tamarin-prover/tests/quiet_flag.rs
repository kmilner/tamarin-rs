// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--quiet` is inert: it suppresses nothing the Haskell binary prints.
//!
//! HS registers the flag (`flagNone ["quiet"] (addEmptyArg "quiet")`,
//! TheoryLoader.hs:159-163) and never reads it back — the sole consumer is
//! commented out at TheoryLoader.hs:414-416, and `argExists "quiet"` occurs
//! nowhere else in the tree.  So `ensureMaudeAndGetVersion`'s banner
//! (Console.hs:150-155), the `[Theory X] …` `traceM` markers
//! (TheoryLoader.hs:451, 496, 581, 594, 696; CloseRule.hs:383, 386) and
//! `ppRep`'s `summary of summaries:` block (Batch.hs:87-316) all appear with
//! and without the flag.
//!
//! The pinned oracle (Git revision ef3f0468) confirms it: on [`THEORY`],
//! `--quiet` and unflagged runs produce byte-identical stdout AND stderr.
//! The expectations below are those bytes, minus the three banner lines
//! (machine-local maude path and version), the `Generated from:` block's
//! build info, the analyzed path (a temp dir) and the wall-clock
//! `processing time:` line.

mod common;

use common::{joined, maude_available, normalize_stdout, strip_maude_banner};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_quiet_flag";

/// A theory that loads, translates and closes, with nothing to prove.
const THEORY: &str = "theory Quiet\nbegin\n\nrule Init:\n  [ ] --[ Start() ]-> [ St() ]\n\n\
                      lemma reachable:\n  exists-trace \"Ex #i. Start()@i\"\n\nend\n";

/// Run the built binary on [`THEORY`] with `extra` flags, returning
/// `(exit code, normalized stdout, stderr minus the maude banner)`.
fn run_binary(stem: &str, extra: &[&str]) -> (i32, String, String) {
    let (code, stdout, stderr) = common::run_raw(TMP_DIR, stem, THEORY, extra);
    (code, normalize_stdout(&stdout), strip_maude_banner(&stderr))
}

/// The oracle's `--quiet` stderr for [`THEORY`] after the banner: seven
/// markers, in this order.
const EXPECTED_STDERR: &[&str] = &[
    "[Theory Quiet] Theory loaded",
    "[Theory Quiet] Theory translated",
    "[Theory Quiet] No Deconstruction Chain checks started",
    "[Theory Quiet] No Deconstruction Chain checks ended",
    "[Theory Quiet] Derivation checks started",
    "[Theory Quiet] Derivation checks ended",
    "[Theory Quiet] Theory closed",
];

/// The oracle's `--quiet` stdout for [`THEORY`], normalized by
/// [`normalize_stdout`].  The lone `"  "` line is HS `ppRep`'s separator
/// (Batch.hs:146-148).
const EXPECTED_STDOUT: &[&str] = &[
    "theory Quiet",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "rule (modulo E) Init:",
    "   [ ] --[ Start( ) ]-> [ St( ) ]",
    "",
    "  /* has exactly the trivial AC variant */",
    "",
    "lemma reachable:",
    "  exists-trace \"\u{2203} #i. Start( ) @ #i\"",
    "/*",
    "guarded formula characterizing all satisfying traces:",
    "\"\u{2203} #i. (Start( ) @ #i)\"",
    "*/",
    "by sorry",
    "",
    "/* All wellformedness checks were successful. */",
    "",
    "/*",
    "Generated from:",
    "Tamarin version 1.13.0",
    "Maude version <local maude>",
    "<build info>",
    "<build info>",
    "*/",
    "",
    "end",
    "",
    "==============================================================================",
    "summary of summaries:",
    "",
    "analyzed: <in file>",
    "",
    "  ",
    "  reachable (exists-trace): analysis incomplete (1 steps)",
    "",
    "==============================================================================",
];

/// `--quiet` keeps the maude banner (stripped here, asserted present) and
/// every `[Theory Quiet] …` marker.
#[test]
fn quiet_keeps_maude_banner_and_theory_markers() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, _, stderr) = run_binary("quiet_markers", &["--quiet"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, joined(EXPECTED_STDERR));
}

/// `--quiet` keeps the whole stdout stream, `summary of summaries:` block
/// included.
#[test]
fn quiet_keeps_summary_of_summaries() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_binary("quiet_summary", &["--quiet"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_STDOUT));
}

/// The flag changes nothing: `--quiet` and a bare run agree on both streams.
#[test]
fn quiet_output_equals_unflagged_output() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (q_code, q_out, q_err) = run_binary("quiet_same", &["--quiet"]);
    let (p_code, p_out, p_err) = run_binary("quiet_same", &[]);
    assert_eq!(q_code, p_code);
    assert_eq!(q_err, p_err);
    assert_eq!(q_out, p_out);
}
