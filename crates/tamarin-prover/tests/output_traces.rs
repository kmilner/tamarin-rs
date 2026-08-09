// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--output-json` / `--output-dot` end-to-end pins.
//!
//! HS `outputTraces` (Batch.hs:249-317) serialises the constraint system of
//! every `Finished Solved` proof node, in lemma declaration order, once per
//! input file — and only from `processThy`'s close-and-prove branch
//! (Batch.hs:223-231).  Every earlier branch returns first, so `--parse-only`
//! (Batch.hs:198-199), `--precompute-only` (:202-208), `-m` (:211-221) and a
//! run with no input files (`helpAndExit`, Batch.hs:90) create NO file at all.
//!
//! The expectations below are the pinned v1.13.0 oracle's bytes.  Both
//! documents are byte-asserted in full against a captured oracle fixture.
//!
//! MAUDE_PATH trap: [`maude_available`] probes ONLY `$MAUDE_PATH` and two
//! hardcoded absolute paths — never `$PATH`.  On machines whose maude lives
//! elsewhere (e.g. /home/linuxbrew/.linuxbrew/bin/maude) a bare `cargo test`
//! SKIPS every solved-trace pin here and reports green; run with
//! `MAUDE_PATH=/path/to/maude cargo test -p tamarin-prover`.

mod common;

use std::path::{Path, PathBuf};

use common::{fixture, maude_available};

/// The 186-byte in-repo fixture: two rules and one exists-trace lemma
/// `chain`, satisfied by the theory, so `--prove=chain` yields exactly one
/// `Finished Solved` node.
const SINGLE_RECV: &str = "single_recv.spthy";

/// A second theory with the same shape under a different name, for the
/// "last input file wins" pin (HS `writeFile` truncates per file).
const SECOND_RECV: &str = "theory SecondRecv\nbegin\n\nrule Send:\n  \
                           [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]\n\nrule Recv:\n  \
                           [ In(x) ] --[ R(x) ]-> [ ]\n\nlemma chain:\n  exists-trace\n  \
                           \"Ex k #i #j. S(k) @ i & R(k) @ j\"\n\nend\n";

/// HS `traceOutputLabel` (Batch.hs:290-303) on the fixture's single solved
/// node, verbatim from the oracle capture's `digraph` line.  Note the missing
/// separator between `chain` and the proof path: the root's only case name is
/// the empty string, so `intercalate "-" ["", "Send"]` contributes `-Send`.
const SR_LABEL: &str = "trace_SingleRecv_SL2-AS0-CL0-A1-C1-NB_chain-Send";

/// A fresh per-test temp dir holding the two trace paths.
struct Case {
    dir: PathBuf,
    json: PathBuf,
    dot: PathBuf,
}

impl Case {
    fn new(test: &str) -> Case {
        let dir = std::env::temp_dir().join(format!("tamarin_rs_output_traces_{}", test));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("mkdir");
        Case {
            json: dir.join("traces.json"),
            dot: dir.join("traces.dot"),
            dir,
        }
    }

    fn write(&self, name: &str, body: &str) -> PathBuf {
        let p = self.dir.join(name);
        std::fs::write(&p, body).expect("write theory");
        p
    }

    /// Run the binary with both trace flags plus `extra`, returning the exit
    /// code.  The trace flags precede `extra` so a test can still override
    /// them positionally.
    fn run(&self, extra: &[&str], inputs: &[&Path]) -> i32 {
        let json = format!("--output-json={}", self.json.display());
        let dot = format!("--output-dot={}", self.dot.display());
        let mut flags: Vec<&str> = vec![&json, &dot];
        flags.extend_from_slice(extra);
        common::run_binary(&flags, inputs).0
    }

    fn assert_neither_exists(&self, mode: &str) {
        assert!(
            !self.json.exists(),
            "{mode}: HS never creates the --output-json file here",
        );
        assert!(
            !self.dot.exists(),
            "{mode}: HS never creates the --output-dot file here",
        );
    }

    fn json_bytes(&self) -> Vec<u8> {
        std::fs::read(&self.json).expect("--output-json file written")
    }

    fn dot_text(&self) -> String {
        std::fs::read_to_string(&self.dot).expect("--output-dot file written")
    }

    fn dot_len(&self) -> u64 {
        std::fs::metadata(&self.dot)
            .expect("--output-dot file written")
            .len()
    }
}

// ---------------------------------------------------------------------
// Negative cases: the branches that return before `outputTraces`
// ---------------------------------------------------------------------

/// `null inFiles = helpAndExit …` (Batch.hs:90) fires before `processThy`.
#[test]
fn no_input_files_writes_no_trace_files() {
    let c = Case::new("no_input_files");
    assert_eq!(c.run(&[], &[]), 1);
    c.assert_neither_exists("no input files");
}

/// A parse error `die`s inside `loadTheory`, long before `outputTraces`.
#[test]
fn parse_error_writes_no_trace_files() {
    let c = Case::new("parse_error");
    let bad = c.write("bad.spthy", "theory Bad begin\nrule\n");
    assert_eq!(c.run(&[], &[&bad]), 1);
    c.assert_neither_exists("parse error");
}

/// `parseOnlyMode` (Batch.hs:198-199) returns before the close-and-prove arm.
#[test]
fn parse_only_writes_no_trace_files() {
    let c = Case::new("parse_only");
    let f = fixture(SINGLE_RECV);
    assert_eq!(c.run(&["--parse-only"], &[&f]), 0);
    c.assert_neither_exists("--parse-only");
}

/// `precomputeOnlyMode` (Batch.hs:202-208) likewise.
#[test]
fn precompute_only_writes_no_trace_files() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("precompute_only");
    let f = fixture(SINGLE_RECV);
    assert_eq!(c.run(&["--precompute-only"], &[&f]), 0);
    c.assert_neither_exists("--precompute-only");
}

/// `isTranslateOnlyMode` (Batch.hs:211-221) likewise — `-m` never closes the
/// theory, so there is nothing to serialise and no file is created.
#[test]
fn translate_only_writes_no_trace_files() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("translate_only");
    let f = fixture(SINGLE_RECV);
    assert_eq!(c.run(&["-m=spthy"], &[&f]), 0);
    c.assert_neither_exists("-m=spthy");
}

// ---------------------------------------------------------------------
// The no-trace documents
// ---------------------------------------------------------------------

/// Without `--prove` the fixture's lemma has no stored proof, so
/// `systemsWithMetadata` is empty: `sequentsToJSONPretty graphOptions []` is
/// aeson-pretty's `{graphs: []}` (20 bytes, no trailing newline) and
/// `intercalate "\n" [] == ""` is a 0-byte dot file.  Byte-identical to the
/// oracle's `noprove_sr.{json,dot}`.
#[test]
fn no_traces_writes_the_hs_empty_documents() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("no_traces");
    let f = fixture(SINGLE_RECV);
    assert_eq!(c.run(&[], &[&f]), 0);
    assert_eq!(c.json_bytes(), b"{\n    \"graphs\": []\n}");
    assert_eq!(c.dot_len(), 0);
}

// ---------------------------------------------------------------------
// The solved-trace documents
// ---------------------------------------------------------------------

/// Full-byte pin of `--prove=chain --output-json` against the oracle capture.
/// JSON carries no volatile lines, so nothing is normalised away.
#[test]
fn solved_trace_json_matches_the_oracle_bytes() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("json_bytes");
    let f = fixture(SINGLE_RECV);
    assert_eq!(c.run(&["--prove=chain"], &[&f]), 0);
    let want = std::fs::read(fixture("single_recv_traces.json")).expect("oracle fixture");
    let got = c.json_bytes();
    assert_eq!(
        String::from_utf8_lossy(&got),
        String::from_utf8_lossy(&want),
        "--output-json must be byte-identical to the oracle capture",
    );
}

/// Full-byte pin of `--prove=chain --output-dot` against the oracle capture:
/// `showDot`'s framing (Text/Dot.hs:234-248), the `traceOutputLabel` digraph
/// id, and the whole `Text.Dot` element block — counter node ids, record
/// ports, quoted attribute values, attribute order and statement order.
#[test]
fn solved_trace_dot_matches_the_oracle_bytes() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("dot_bytes");
    let f = fixture(SINGLE_RECV);
    assert_eq!(c.run(&["--prove=chain"], &[&f]), 0);
    let got = c.dot_text();
    let want = std::fs::read_to_string(fixture("single_recv_traces.dot")).expect("oracle fixture");
    assert_eq!(
        got, want,
        "--output-dot must be byte-identical to the oracle capture",
    );
    // The label ADVERTISES the `GraphOptions` the body was rendered with
    // (`…_SL2-AS0-CL0-A1-C1-NB_…`) but `trace_label_options` derives it from
    // `GraphOptions::default()` independently of the value the writer passes.
    // The fixture pins both halves at once, so state what it is pinning: the
    // oracle's own label, and compression (the label's `C1`) having folded the
    // `Fresh` node into its consumer.
    assert!(want.starts_with(&format!("digraph \"{SR_LABEL}\" {{\n")));
    assert!(!want.contains(": Fresh"));
}

/// HS `writeFile` truncates, and `processThy` runs once per input file
/// (`mapM (timedIO . processThy versionData) inFiles`, Batch.hs:116), so the
/// LAST file's traces are what survive (Batch.hs:262-272).
#[test]
fn last_input_file_wins() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("last_file_wins");
    let first = fixture(SINGLE_RECV);
    let second = c.write("second_recv.spthy", SECOND_RECV);
    assert_eq!(c.run(&["--prove=chain"], &[&first, &second]), 0);
    let json = String::from_utf8(c.json_bytes()).expect("utf8");
    assert!(
        json.contains("trace_SecondRecv_SL2-AS0-CL0-A1-C1-NB_chain-Send"),
        "the LAST file's traces must survive; got:\n{json}",
    );
    assert!(
        !json.contains("trace_SingleRecv_"),
        "the first file's traces must have been truncated away; got:\n{json}",
    );
    let dot = c.dot_text();
    assert!(dot.contains("digraph \"trace_SecondRecv_"));
    assert!(!dot.contains("digraph \"trace_SingleRecv_"));
}

/// `intercalate "\n" $ map serializeDot labelledSystems` (Batch.hs:265) with
/// several solved nodes.  Each graph already ends `}\n`, so the separator
/// leaves EXACTLY one blank line between the closing brace and the next
/// `digraph`, and the file ends with a single `}\n`.
#[test]
fn several_solved_lemmas_are_joined_by_one_blank_line() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("multi_graph");
    let f = c.write(
        "two_lemmas.spthy",
        "theory TwoLemmas\nbegin\n\nrule Send:\n  \
         [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]\n\nrule Recv:\n  \
         [ In(x) ] --[ R(x) ]-> [ ]\n\nlemma sent:\n  exists-trace\n  \
         \"Ex k #i. S(k) @ i\"\n\nlemma chain:\n  exists-trace\n  \
         \"Ex k #i #j. S(k) @ i & R(k) @ j\"\n\nend\n",
    );
    assert_eq!(c.run(&["--prove"], &[&f]), 0);
    let dot = c.dot_text();
    assert_eq!(
        dot.matches("digraph \"").count(),
        2,
        "one graph per solved node:\n{dot}"
    );
    assert_eq!(
        dot.matches("}\n\ndigraph \"").count(),
        1,
        "graphs must be separated by exactly one blank line:\n{dot}"
    );
    assert!(
        dot.ends_with("\n\n}\n"),
        "tail: {:?}",
        &dot[dot.len() - 8..]
    );
}

// ---------------------------------------------------------------------
// Unwritable targets: the IOException that escapes `outputTraces`
// ---------------------------------------------------------------------

/// Neither writer is guarded in HS (`writeFile` / `BL.writeFile`,
/// Batch.hs:262-271), so a target that cannot be opened raises an
/// `IOException` that escapes to GHC's runtime: `tamarin-prover: <path>:
/// <opener>: <reason>` on stderr, NOTHING on stdout, exit 1.  The opener names
/// the frame that opened the handle and so differs between the two writers —
/// `withFile` for the dot text writer, `withBinaryFile` for the lazy
/// ByteString JSON one.
///
/// Oracle-verified per row against the pinned v1.13.0 binary (byte-identical
/// stderr, rc 1, empty stdout).
#[test]
fn unwritable_trace_targets_report_the_ghc_io_exception() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let c = Case::new("unwritable_targets");
    let thy = fixture(SINGLE_RECV);
    let a_dir = c.dir.join("a_dir");
    std::fs::create_dir_all(&a_dir).expect("mkdir");
    let dangling = c.dir.join("no_such_dir").join("x.out");
    // A path whose PARENT is a regular file: `open` stops at ENOTDIR, which
    // shares `InappropriateType` with EISDIR but carries its own `strerror`.
    let under_file = Path::new(&thy).join("x.out");
    // ENAMETOOLONG, the one reachable `InvalidArgument`.
    let too_long = c.dir.join("a".repeat(400));

    // (flag, path, expected `<path>: <opener>: <reason>` tail)
    let cases: [(&str, PathBuf, &str); 8] = [
        (
            "--output-json",
            a_dir.clone(),
            "withBinaryFile: inappropriate type (Is a directory)",
        ),
        (
            "--output-dot",
            a_dir.clone(),
            "withFile: inappropriate type (Is a directory)",
        ),
        (
            "--output-json",
            dangling.clone(),
            "withBinaryFile: does not exist (No such file or directory)",
        ),
        (
            "--output-dot",
            dangling.clone(),
            "withFile: does not exist (No such file or directory)",
        ),
        (
            "--output-json",
            under_file.clone(),
            "withBinaryFile: inappropriate type (Not a directory)",
        ),
        (
            "--output-dot",
            under_file.clone(),
            "withFile: inappropriate type (Not a directory)",
        ),
        (
            "--output-json",
            too_long.clone(),
            "withBinaryFile: invalid argument (File name too long)",
        ),
        (
            "--output-dot",
            too_long.clone(),
            "withFile: invalid argument (File name too long)",
        ),
    ];
    for (flag, path, tail) in cases {
        let arg = format!("{flag}={}", path.display());
        let (rc, out, err) = common::run_binary(&["--prove=chain", &arg], &[&thy]);
        assert_eq!(rc, 1, "{arg}: HS exits 1");
        assert_eq!(out, "", "{arg}: HS writes nothing to stdout");
        let want = format!("tamarin-prover: {}: {tail}\n", path.display());
        assert!(
            err.ends_with(&want),
            "{arg}: expected stderr to end with\n{want}\ngot:\n{err}",
        );
    }
}
