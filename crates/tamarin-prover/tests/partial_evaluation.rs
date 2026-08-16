// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end byte pins for `--partial-evaluation`.
//!
//! HS applies it inside `closeTranslatedTheory` (TheoryLoader.hs:675-698),
//! between the theory close and `proveTheory`: `applyPartialEvaluation`
//! (Prover.hs:237-264) replaces the closed theory's proto-rules with the
//! abstract interpretation's refined set, splices the abstract-state report
//! ahead of them as a `TextItem` and re-closes.  So a plain load — no
//! `--prove` — already shows the whole effect on stdout, while the
//! `Debug.Trace` step lines (AbstractInterpretation.hs:109-119) are lazy
//! thunks forced during rendering and therefore land on stderr AFTER the
//! `[Theory X] Theory closed` marker.
//!
//! Every expectation below is verbatim oracle bytes from the pinned v1.13.0
//! binary (Git revision ef3f0468) on [`THEORY`], with only the machine-local
//! lines blanked: the three maude banner lines (path + local version), the
//! `Generated from:` block's `Maude version` / `Git revision:` /
//! `Compiled at:`, the `analyzed:` temp path and the wall-clock
//! `processing time:` line.
//!
//! Maude: [`maude_available`] resolves through the common harness ladder —
//! `$MAUDE_PATH` (asserted to exist), the system prefixes, a `$PATH` walk,
//! then linuxbrew — and PANICS when nothing resolves, so a bare `cargo test`
//! cannot skip the maude-backed pins here silently; `TAM_ALLOW_NO_MAUDE=1`
//! is the only opt-in to the skip.
//! [`strip_maude_banner`] is the positive control: it panics when a run that
//! should have started maude produced no banner.

mod common;

use common::{joined, maude_available, normalize_stdout, strip_maude_banner};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_partial_evaluation";

/// `crates/tamarin-prover/tests/fixtures/single_recv.spthy`, inline: two
/// rules declared `Send` then `Recv`, so the alphabetical re-emission that
/// `applyPartialEvaluation`'s `Set`-round-trip forces is observable, plus one
/// exists-trace lemma to keep the `summary of summaries:` block non-empty.
const THEORY: &str = "theory SingleRecv\nbegin\n\n\
                      rule Send:\n  [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]\n\n\
                      rule Recv:\n  [ In(x) ] --[ R(x) ]-> [ ]\n\n\
                      lemma chain:\n  exists-trace\n  \
                      \"Ex k #i #j. S(k) @ i & R(k) @ j\"\n\nend\n";

/// Run the built binary on [`THEORY`] with `extra` flags, returning
/// `(exit code, normalized stdout, raw stderr)`.  The banner is NOT stripped
/// here: `--parse-only` never starts Maude (Batch.hs:91-95), so the tests that
/// want it gone call [`strip_maude_banner`] themselves.
fn run_binary(stem: &str, extra: &[&str]) -> (i32, String, String) {
    let (code, stdout, stderr) = common::run_raw(TMP_DIR, stem, THEORY, extra);
    (code, normalize_stdout(&stdout), stderr)
}

/// The oracle's `--partial-evaluation=summary` stdout for [`THEORY`],
/// normalized by [`normalize_stdout`].  Two things to read off it: the
/// `text{*…*}` report `applyPartialEvaluation` splices at the position of the
/// first rule item (`replaceProtoRules`, Prover.hs:249-255), and the rules coming back in
/// alphabetical order — `Recv` before `Send`, the reverse of the source.
const EXPECTED_STDOUT: &[&str] = &[
    "theory SingleRecv",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "text{* the abstract state after partial evaluation contains 3 facts:",
    "",
    "1. Fr( ~z )",
    "",
    "2. Out( z )",
    "",
    "3. In( z )",
    "",
    "This abstract state results in 2 refined multiset rewriting rules.",
    "Note that the original number of multiset rewriting rules was 2.",
    "",
    "*}",
    "",
    "rule (modulo E) Recv:",
    "   [ In( x ) ] --[ R( x ) ]-> [ ]",
    "",
    "  /* has exactly the trivial AC variant */",
    "",
    "rule (modulo E) Send:",
    "   [ Fr( ~k ) ] --[ S( ~k ) ]-> [ Out( ~k ) ]",
    "",
    "  /* has exactly the trivial AC variant */",
    "",
    "lemma chain:",
    "  exists-trace \"\u{2203} k #i #j. (S( k ) @ #i) \u{2227} (R( k ) @ #j)\"",
    "/*",
    "guarded formula characterizing all satisfying traces:",
    "\"\u{2203} k #i #j. (S( k ) @ #i) \u{2227} (R( k ) @ #j)\"",
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
    "  chain (exists-trace): analysis incomplete (1 steps)",
    "",
    "==============================================================================",
];

/// The `text{*…*}` block of [`EXPECTED_STDOUT`]: `render ppAbsState`
/// (Prover.hs:257-264) wrapped by `prettyFormalComment` (lib/theory/src/Pretty.hs:19-21).
/// The blank lines around the numbered fact list are the two `$--$` joins
/// (Text/PrettyPrint/Class.hs:112-114); the one before `*}` is the `".\n\n"` ending the last
/// `text`.
const EXPECTED_REPORT: &[&str] = &[
    "text{* the abstract state after partial evaluation contains 3 facts:",
    "",
    "1. Fr( ~z )",
    "",
    "2. Out( z )",
    "",
    "3. In( z )",
    "",
    "This abstract state results in 2 refined multiset rewriting rules.",
    "Note that the original number of multiset rewriting rules was 2.",
    "",
    "*}",
];

/// The oracle's `--partial-evaluation=summary` stderr for [`THEORY`] after
/// the banner: the seven close-pipeline markers, then the `Summary` trace —
/// one line per fixpoint iteration except the last
/// (AbstractInterpretation.hs:109-113), with its leading space.
const EXPECTED_STDERR_SUMMARY: &[&str] = &[
    "[Theory SingleRecv] Theory loaded",
    "[Theory SingleRecv] Theory translated",
    "[Theory SingleRecv] No Deconstruction Chain checks started",
    "[Theory SingleRecv] No Deconstruction Chain checks ended",
    "[Theory SingleRecv] Derivation checks started",
    "[Theory SingleRecv] Derivation checks ended",
    "[Theory SingleRecv] Theory closed",
    " partial evaluation: step 0 added 1 facts",
];

/// The same stderr under `=verbose` (`Tracing`,
/// AbstractInterpretation.hs:114-119): the step line, a blank, the newly
/// added facts as `nest 2 (numbered' …)`, a blank.
const EXPECTED_STDERR_VERBOSE: &[&str] = &[
    "[Theory SingleRecv] Theory loaded",
    "[Theory SingleRecv] Theory translated",
    "[Theory SingleRecv] No Deconstruction Chain checks started",
    "[Theory SingleRecv] No Deconstruction Chain checks ended",
    "[Theory SingleRecv] Derivation checks started",
    "[Theory SingleRecv] Derivation checks ended",
    "[Theory SingleRecv] Theory closed",
    " partial evaluation: step 0 added 1 facts",
    "",
    "  1. Out( z )",
    "",
];

/// The abstract-state report lands in stdout byte for byte, at the position
/// of the theory's first rule item.
#[test]
fn summary_injects_abstract_state_comment() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_binary("pe_report", &["--partial-evaluation=summary"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert!(
        stdout.contains(&joined(EXPECTED_REPORT)),
        "stdout missing the abstract-state report:\n{stdout}"
    );
    assert_eq!(stdout, joined(EXPECTED_STDOUT));
}

/// The `Summary` trace is on stderr, after the `Theory closed` marker.
#[test]
fn summary_emits_step_trace_on_stderr() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, _, stderr) = run_binary("pe_trace", &["--partial-evaluation=summary"]);
    let stderr = strip_maude_banner(&stderr);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, joined(EXPECTED_STDERR_SUMMARY));
}

/// The re-close re-emits the rules alphabetically: `Recv` before `Send`,
/// where an unflagged run keeps the source order.
#[test]
fn partial_evaluation_resorts_rules() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, pe_stdout, stderr) = run_binary("pe_sort", &["--partial-evaluation=summary"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let recv = pe_stdout
        .find("rule (modulo E) Recv:")
        .expect("Recv rule in PE stdout");
    let send = pe_stdout
        .find("rule (modulo E) Send:")
        .expect("Send rule in PE stdout");
    assert!(recv < send, "expected Recv before Send:\n{pe_stdout}");

    let (code, plain_stdout, stderr) = run_binary("pe_sort", &[]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let recv = plain_stdout
        .find("rule (modulo E) Recv:")
        .expect("Recv rule in unflagged stdout");
    let send = plain_stdout
        .find("rule (modulo E) Send:")
        .expect("Send rule in unflagged stdout");
    assert!(send < recv, "expected source order:\n{plain_stdout}");
    assert!(!plain_stdout.contains("text{*"));
}

/// `=verbose` adds the numbered list of the facts the step contributed,
/// indented under `nest 2` — the separator line between entries carries that
/// indentation, so an empty separator would fail this.
#[test]
fn verbose_appends_numbered_fact_list() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, _, stderr) = run_binary("pe_verbose", &["--partial-evaluation=verbose"]);
    let stderr = strip_maude_banner(&stderr);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, joined(EXPECTED_STDERR_VERBOSE));
}

/// The style selects the trace only: stdout is byte-identical either way.
#[test]
fn stdout_identical_between_styles() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (s_code, s_out, s_err) = run_binary("pe_styles", &["--partial-evaluation=summary"]);
    let (v_code, v_out, v_err) = run_binary("pe_styles", &["--partial-evaluation=verbose"]);
    assert_eq!(s_code, 0, "stderr: {s_err}");
    assert_eq!(v_code, 0, "stderr: {v_err}");
    assert_eq!(s_out, v_out);
    assert_eq!(s_out, joined(EXPECTED_STDOUT));
    assert_ne!(strip_maude_banner(&s_err), strip_maude_banner(&v_err));
}

/// `--parse-only` returns before `closeTheory` (Batch.hs:198-199), so the
/// flag is inert there: no trace, no report, and the open theory keeps its
/// source rule order.
#[test]
fn parse_only_skips_pe() {
    let (code, stdout, stderr) = run_binary(
        "pe_parse_only",
        &["--parse-only", "--partial-evaluation=verbose"],
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, "[Theory SingleRecv] Theory loaded\n");
    assert!(!stdout.contains("text{*"), "stdout: {stdout}");
    assert!(!stdout.contains("partial evaluation"), "stdout: {stdout}");
    let recv = stdout
        .find("rule (modulo E) Recv:")
        .expect("Recv rule in parse-only stdout");
    let send = stdout
        .find("rule (modulo E) Send:")
        .expect("Send rule in parse-only stdout");
    assert!(send < recv, "expected source order:\n{stdout}");
}

/// An unrecognised value is a clap parse error: rc 2 on stderr, before the
/// maude probe or any file IO.  (HS deferred the rejection into the file
/// loop; canonical clap validates the value up front.)
#[test]
fn unknown_style_is_a_parse_error() {
    let (code, stdout, stderr) = run_binary("pe_bogus", &["--partial-evaluation=banana"]);
    assert_eq!(code, 2, "stderr: {stderr}");
    assert_eq!(stdout, "");
    assert!(
        stderr.contains("--partial-evaluation"),
        "the error names the flag:\n{stderr}"
    );
    assert!(
        !stderr.contains("maude tool:"),
        "a parse error must precede the maude probe:\n{stderr}"
    );
}
