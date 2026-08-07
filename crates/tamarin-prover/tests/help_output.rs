// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-parity pins for `tamarin-rs --help` and the three subcommand helps.
//!
//! The oracle renders one help text per `TamarinMode` (Console.hs:341-345), so
//! there are four: batch ([`ORACLE_HELP`], 9776 bytes), `interactive`
//! ([`ORACLE_INTERACTIVE_HELP`], 4854), `test` ([`ORACLE_TEST_HELP`], 992) and
//! `variants` ([`ORACLE_VARIANTS_HELP`], 855) — each captured verbatim from the
//! pinned oracle at exit 0 with empty stderr.  The port reproduces each
//! byte-for-byte except for the rows naming flags its parser rejects
//! (`HelpPin::omitted`), plus a clearly fenced trailing group for the flags the
//! port accepts and the oracle does not.  The two halves are asserted
//! separately so a change to either is unambiguous.

use std::process::Command;

use tamarin_prover::cli::help_text;
use tamarin_prover::{parse_args, Subcommand};

/// One mode's help pin: the oracle capture, the rows the port drops from it,
/// and the trailer it appends.
struct HelpPin {
    /// The mode whose help [`help_text`] must render.
    mode: Subcommand,
    /// argv that selects this help from the binary.
    argv: &'static [&'static str],
    /// Verbatim oracle stdout for `argv`.
    oracle: &'static str,
    /// Oracle flags whose rows the port omits, because [`parse_args`] answers
    /// `Unknown flag` for each.
    omitted: &'static [&'static str],
    /// The oracle lines the port drops: the [`Self::omitted`] rows plus their
    /// wrapped continuation lines, verbatim from the capture.
    dropped: &'static str,
    /// Byte at which this rendering's description column starts — cmdargs sizes
    /// it from the mode's widest left cell plus a two-byte gutter.
    desc_col: usize,
    /// The group the port appends after the oracle's README block.
    trailer: &'static str,
    /// [`Self::desc_col`] for [`Self::trailer`], which is laid out at its own
    /// column when the mode's is too narrow for the port-only rows.
    trailer_col: usize,
}

const PINS: [HelpPin; 4] = [
    HelpPin {
        mode: Subcommand::Batch,
        argv: &["--help"],
        oracle: ORACLE_HELP,
        omitted: &OMITTED_ORACLE_FLAGS,
        dropped: DROPPED_ORACLE_ROWS,
        desc_col: 76,
        trailer: RS_ONLY_TRAILER,
        trailer_col: 76,
    },
    HelpPin {
        mode: Subcommand::Interactive,
        argv: &["interactive", "--help"],
        oracle: ORACLE_INTERACTIVE_HELP,
        omitted: &OMITTED_INTERACTIVE_FLAGS,
        dropped: DROPPED_INTERACTIVE_ROWS,
        desc_col: 50,
        trailer: RS_ONLY_TRAILER_COL50,
        trailer_col: 50,
    },
    HelpPin {
        mode: Subcommand::Variants,
        argv: &["variants", "--help"],
        oracle: ORACLE_VARIANTS_HELP,
        omitted: &[],
        dropped: "",
        desc_col: 21,
        trailer: RS_ONLY_TRAILER_COL26,
        trailer_col: 26,
    },
    HelpPin {
        mode: Subcommand::Test,
        argv: &["test", "--help"],
        oracle: ORACLE_TEST_HELP,
        omitted: &[],
        dropped: "",
        desc_col: 25,
        trailer: RS_ONLY_TRAILER_COL26,
        trailer_col: 26,
    },
];

/// Oracle flags whose rows the batch help omits, because [`parse_args`] answers
/// `Unknown flag` for each (HS `theoryLoadFlags`, TheoryLoader.hs:187-207).
const OMITTED_ORACLE_FLAGS: [&str; 3] = [
    "--proverif-no-source-lemmas",
    "--proverif-no-multiset",
    "--proverif-no-precise",
];

/// As [`OMITTED_ORACLE_FLAGS`], for `interactive`: the same three rows plus the
/// two `interactiveMode`-only flags the port has no arm for (Interactive.hs:61
/// and 63-64).
const OMITTED_INTERACTIVE_FLAGS: [&str; 5] = [
    "--browser",
    "--load-json",
    "--proverif-no-source-lemmas",
    "--proverif-no-multiset",
    "--proverif-no-precise",
];

/// The eight batch-help lines the port drops: the [`OMITTED_ORACLE_FLAGS`]
/// rows plus their wrapped continuation lines, verbatim from the capture.
const DROPPED_ORACLE_ROWS: &str = r"     --proverif-no-source-lemmas                                            Do not export source lemmas as
                                                                            ProVerif axioms
     --proverif-no-multiset                                                 Do not export multiset
                                                                            semantics to ProVerif
                                                                            (DistinctFact events and
                                                                            restriction)
     --proverif-no-precise                                                  Do not set preciseActions in
                                                                            ProVerif output";

/// The seven `interactive`-help lines the port drops — see
/// [`OMITTED_INTERACTIVE_FLAGS`].
const DROPPED_INTERACTIVE_ROWS: &str = r"     --browser                                    Open the interactive interface in the default web browser
     --load-json[=FILE]                           Load a JSON graph file (see --output-json) for standalone
                                                  viewing at /loadjson (WORKDIR may be omitted)
     --proverif-no-source-lemmas                  Do not export source lemmas as ProVerif axioms
     --proverif-no-multiset                       Do not export multiset semantics to ProVerif
                                                  (DistinctFact events and restriction)
     --proverif-no-precise                        Do not set preciseActions in ProVerif output";

/// The trailing group the port appends after the oracle's README block.
const RS_ONLY_TRAILER: &str = r"------------------------------------------------------------------------------
Flags accepted by this Rust port only; the Haskell tamarin-prover rejects
every flag below with 'Unknown flag'.
     --processors=N                                                         Worker threads for internal
                                                                            parallelism (default: all cores;
                                                                            N=1 is byte-identical to
                                                                            sequential output)
     --maude-processes=M                                                    Maude subprocesses the workers
                                                                            share (default: --processors;
                                                                            ~30-100 MB each; M=1 uses one)
     --data-dir=DIR                                                         Override the bundled data/ dir
  -h                                                                        Alias for -?
------------------------------------------------------------------------------
Flags the Haskell prover documents under its 'interactive' mode help,
which this port also accepts here:
  -p --port[=PORT]                                                          Port to listen on
  -i --interface[=INTERFACE]                                                Interface to listen on
     --image-format[=PNG|SVG]                                               image format used for graphs
                                                                            (default SVG)
     --debug                                                                Show server debugging output
     --no-logging                                                           Suppress web server logs.
------------------------------------------------------------------------------
";

/// [`RS_ONLY_TRAILER`]'s first group in `interactive`'s geometry.
const RS_ONLY_TRAILER_COL50: &str = r"------------------------------------------------------------------------------
Flags accepted by this Rust port only; the Haskell tamarin-prover rejects
every flag below with 'Unknown flag'.
     --processors=N                               Worker threads for internal parallelism (default: all
                                                  cores; N=1 is byte-identical to sequential output)
     --maude-processes=M                          Maude subprocesses the workers share (default:
                                                  --processors; ~30-100 MB each; M=1 uses one)
     --data-dir=DIR                               Override the bundled data/ dir
  -h                                              Alias for -?
------------------------------------------------------------------------------
This port runs one flat argument parser: every flag the other commands'
help documents is accepted here too, though the Haskell prover answers
'Unknown flag' for it under this command.
------------------------------------------------------------------------------
";

/// [`RS_ONLY_TRAILER_COL50`] for `variants` and `test`, whose own description
/// columns (21 and 25) are narrower than the widest RS-only left cell.
const RS_ONLY_TRAILER_COL26: &str = r"------------------------------------------------------------------------------
Flags accepted by this Rust port only; the Haskell tamarin-prover rejects
every flag below with 'Unknown flag'.
     --processors=N       Worker threads for internal parallelism (default: all cores; N=1 is byte-identical
                          to sequential output)
     --maude-processes=M  Maude subprocesses the workers share (default: --processors; ~30-100 MB each; M=1
                          uses one)
     --data-dir=DIR       Override the bundled data/ dir
  -h                      Alias for -?
------------------------------------------------------------------------------
This port runs one flat argument parser: every flag the other commands'
help documents is accepted here too, though the Haskell prover answers
'Unknown flag' for it under this command.
------------------------------------------------------------------------------
";

/// Verbatim stdout of `tamarin-prover --help` from the pinned oracle
/// (`tamarin-prover-testing/.stack-work/.../9.6.7/bin/tamarin-prover`,
/// 9776 bytes, exit 0, stderr empty).  Rendered by HS with
/// `showText (Wrap 110) $ helpText [] HelpFormatOne mode`
/// (Console.hs:341-359).  Reproduced here so the test owns oracle bytes
/// rather than re-deriving them from the implementation.
const ORACLE_HELP: &str = r"tamarin-prover [COMMAND] ... [OPTIONS] FILES
  Security protocol analysis and verification.

Commands:
  interactive  Start a web-server to construct proofs interactively.
  variants     Compute the variants of the intruder rules for DH-exponentiation.
  test         Self-test the tamarin-prover installation.

Flags:
     --prove[=LEMMAPREFIX*|LEMMANAME]                                       Attempt to prove all lemmas
                                                                            that start with LEMMAPREFIX or
                                                                            the lemma which name is LEMMANAME
                                                                            (can be repeated).
     --lemma[=LEMMAPREFIX*|LEMMANAME]                                       Select lemma(s) by name or
                                                                            prefx (can be repeated)
     --stop-on-trace[=DFS|BFS|SEQDFS|SORRY|NONE]                            How to search for traces
                                                                            (default DFS)
  -b --bound[=INT]                                                          Bound the depth of the proofs
     --heuristic[=(C|I|O|P|S|c|i|o|p|s|{.})+]                               Sequence of proof method
                                                                            rankings to use (default 's')
     --partial-evaluation[=SUMMARY|VERBOSE]                                 Partially evaluate multiset
                                                                            rewriting system
  -D --defines[=STRING]                                                     Define flags for
                                                                            pseudo-preprocessor.
     --diff                                                                 Turn on observational
                                                                            equivalence mode using diff
                                                                            terms.
     --quit-on-warning                                                      Strict mode that quits on any
                                                                            warning that is emitted.
     --auto-sources                                                         Try to auto-generate sources
                                                                            lemmas
     --oraclename[=FILE]                                                    Path to the oracle heuristic
                                                                            (default
                                                                            './theory_filename.oracle',
                                                                            fallback './oracle')
     --oracle-only                                                          When set, the oracle heuristic
                                                                            will stop proof search if the
                                                                            oracle does not rank any proof
                                                                            goals.
     --quiet                                                                Do not display computation
                                                                            steps of oracle or tactic.
  -v --verbose                                                              Display full information when
                                                                            calculating proof.
  -c --open-chains[=PositiveInteger]                                        Limits the number of open
                                                                            chains to be resoled during
                                                                            precomputations (default 10)
  -s --saturation[=PositiveInteger]                                         Limits the number of
                                                                            saturations during
                                                                            precomputations (default 5)
  -d --derivcheck-timeout[=INT]                                             Set timeout for message
                                                                            derivation checks in sec (default
                                                                            5). 0 deactivates check.
     --proverif-no-reuse-lemmas                                             Do not export reuse lemmas as
                                                                            ProVerif axioms
     --proverif-no-source-lemmas                                            Do not export source lemmas as
                                                                            ProVerif axioms
     --proverif-no-restrictions                                             Do not export restrictions to
                                                                            ProVerif
     --proverif-no-multiset                                                 Do not export multiset
                                                                            semantics to ProVerif
                                                                            (DistinctFact events and
                                                                            restriction)
     --proverif-no-precise                                                  Do not set preciseActions in
                                                                            ProVerif output
     --replication-bound[=INT]                                              Replication bound for DeepSec
                                                                            export
     --no-ndc                                                               Deactivate the no
                                                                            deconstruction chain (NDC) check
                                                                            (enabled by default)
     --no-compress                                                          Do not use compressed sequent
                                                                            visualization
     --parse-only                                                           Just parse the input file and
                                                                            pretty print it as-is
     --precompute-only                                                      Just run precomputation and
                                                                            show partial deconstructions
  -o --output[=FILE]                                                        Output file
  -O --Output[=DIR]                                                         Output directory
  -m --output-module[=spthytyped|spthy|msr|proverifequiv|proverif|deepsec]  What to output:
                                                                             -spthy with explicit types
                                                                            inferred
                                                                             -spthy (including Sapic
                                                                            Processes)
                                                                             -pure msrs (with Sapic
                                                                            translation)
                                                                             -ProVerif export for the
                                                                            equivalence lemmas
                                                                             -ProVerif export for the
                                                                            reachability lemmas
                                                                             -DeepSec export for the
                                                                            equivalences lemmas.
     --output-json=FILE --oj                                                Serialize found traces as JSON
                                                                            to FILE.
     --output-dot=FILE --od                                                 Serialize found traces as dot
                                                                            to FILE.
     --with-dot[=FILE]                                                      Path to GraphViz 'dot' tool
     --with-json[=FILE]                                                     Path to JSON rendering tool
                                                                            (not working with --diff)
     --with-maude[=FILE]                                                    Path to 'maude' rewriting tool
About:
  -? --help                                                                 Display help message
  -V --version                                                              Print version information

------------------------------------------------------------------------------
To show help for different commands, type tamarin-prover [Command] --help.
------------------------------------------------------------------------------
See 'https://github.com/tamarin-prover/tamarin-prover/blob/master/README.md'
for usage instructions and pointers to examples.
------------------------------------------------------------------------------

";

/// Verbatim stdout of `tamarin-prover interactive --help` from the pinned
/// oracle (4854 bytes, exit 0, stderr empty).
const ORACLE_INTERACTIVE_HELP: &str = r"interactive [COMMAND] ... [OPTIONS] WORKDIR
  Start a web-server to construct proofs interactively.

Commands:
  interactive  Start a web-server to construct proofs interactively.
  variants     Compute the variants of the intruder rules for DH-exponentiation.
  test         Self-test the tamarin-prover installation.

Flags:
  -p --port[=PORT]                                Port to listen on
  -i --interface[=INTERFACE]                      Interface to listen on (use '*4' for all IPv4 interfaces)
     --browser                                    Open the interactive interface in the default web browser
     --image-format[=PNG|SVG]                     image format used for graphs (default SVG)
     --load-json[=FILE]                           Load a JSON graph file (see --output-json) for standalone
                                                  viewing at /loadjson (WORKDIR may be omitted)
     --debug                                      Show server debugging output
     --no-logging                                 Suppress web server logs.
     --prove[=LEMMAPREFIX*|LEMMANAME]             Attempt to prove all lemmas that start with LEMMAPREFIX
                                                  or the lemma which name is LEMMANAME (can be repeated).
     --lemma[=LEMMAPREFIX*|LEMMANAME]             Select lemma(s) by name or prefx (can be repeated)
     --stop-on-trace[=DFS|BFS|SEQDFS|SORRY|NONE]  How to search for traces (default DFS)
  -b --bound[=INT]                                Bound the depth of the proofs
     --heuristic[=(C|I|O|P|S|c|i|o|p|s|{.})+]     Sequence of proof method rankings to use (default 's')
     --partial-evaluation[=SUMMARY|VERBOSE]       Partially evaluate multiset rewriting system
  -D --defines[=STRING]                           Define flags for pseudo-preprocessor.
     --diff                                       Turn on observational equivalence mode using diff terms.
     --quit-on-warning                            Strict mode that quits on any warning that is emitted.
     --auto-sources                               Try to auto-generate sources lemmas
     --oraclename[=FILE]                          Path to the oracle heuristic (default
                                                  './theory_filename.oracle', fallback './oracle')
     --oracle-only                                When set, the oracle heuristic will stop proof search if
                                                  the oracle does not rank any proof goals.
     --quiet                                      Do not display computation steps of oracle or tactic.
  -v --verbose                                    Display full information when calculating proof.
  -c --open-chains[=PositiveInteger]              Limits the number of open chains to be resoled during
                                                  precomputations (default 10)
  -s --saturation[=PositiveInteger]               Limits the number of saturations during precomputations
                                                  (default 5)
  -d --derivcheck-timeout[=INT]                   Set timeout for message derivation checks in sec (default
                                                  5). 0 deactivates check.
     --proverif-no-reuse-lemmas                   Do not export reuse lemmas as ProVerif axioms
     --proverif-no-source-lemmas                  Do not export source lemmas as ProVerif axioms
     --proverif-no-restrictions                   Do not export restrictions to ProVerif
     --proverif-no-multiset                       Do not export multiset semantics to ProVerif
                                                  (DistinctFact events and restriction)
     --proverif-no-precise                        Do not set preciseActions in ProVerif output
     --replication-bound[=INT]                    Replication bound for DeepSec export
     --no-ndc                                     Deactivate the no deconstruction chain (NDC) check
                                                  (enabled by default)
     --with-dot[=FILE]                            Path to GraphViz 'dot' tool
     --with-json[=FILE]                           Path to JSON rendering tool (not working with --diff)
     --with-maude[=FILE]                          Path to 'maude' rewriting tool
About:
  -? --help                                       Display help message

------------------------------------------------------------------------------
To show help for different commands, type tamarin-prover [Command] --help.
------------------------------------------------------------------------------
See 'https://github.com/tamarin-prover/tamarin-prover/blob/master/README.md'
for usage instructions and pointers to examples.
------------------------------------------------------------------------------

";

/// Verbatim stdout of `tamarin-prover variants --help` from the pinned oracle
/// (855 bytes, exit 0, stderr empty).
const ORACLE_VARIANTS_HELP: &str = r"variants [COMMAND] ... [OPTIONS]
  Compute the variants of the intruder rules for DH-exponentiation.

Commands:
  interactive  Start a web-server to construct proofs interactively.
  variants     Compute the variants of the intruder rules for DH-exponentiation.
  test         Self-test the tamarin-prover installation.

Flags:
  -O --Output[=DIR]  Output directory
About:
  -? --help          Display help message

------------------------------------------------------------------------------
To show help for different commands, type tamarin-prover [Command] --help.
------------------------------------------------------------------------------
See 'https://github.com/tamarin-prover/tamarin-prover/blob/master/README.md'
for usage instructions and pointers to examples.
------------------------------------------------------------------------------

";

/// Verbatim stdout of `tamarin-prover test --help` from the pinned oracle
/// (992 bytes, exit 0, stderr empty).
const ORACLE_TEST_HELP: &str = r"test [COMMAND] ... [OPTIONS] FILES
  Self-test the tamarin-prover installation.

Commands:
  interactive  Start a web-server to construct proofs interactively.
  variants     Compute the variants of the intruder rules for DH-exponentiation.
  test         Self-test the tamarin-prover installation.

Flags:
     --with-dot[=FILE]    Path to GraphViz 'dot' tool
     --with-json[=FILE]   Path to JSON rendering tool (not working with --diff)
     --with-maude[=FILE]  Path to 'maude' rewriting tool
About:
  -? --help               Display help message

------------------------------------------------------------------------------
To show help for different commands, type tamarin-prover [Command] --help.
------------------------------------------------------------------------------
See 'https://github.com/tamarin-prover/tamarin-prover/blob/master/README.md'
for usage instructions and pointers to examples.
------------------------------------------------------------------------------

";

/// `pin.oracle` with the `pin.omitted` rows (and their wrapped continuation
/// lines) removed — what the port must emit verbatim.  Deriving it here rather
/// than storing a second copy makes the omission the *only* difference the test
/// tolerates.
fn expected_head(pin: &HelpPin) -> String {
    let dc = pin.desc_col;
    let mut out = String::with_capacity(pin.oracle.len());
    let mut skipping = false;
    for line in pin.oracle.split_inclusive('\n') {
        let is_continuation = line.len() > dc && line[..dc].bytes().all(|b| b == b' ');
        if !is_continuation {
            skipping = pin.omitted.iter().any(|f| line.trim_start().starts_with(f));
        }
        if !skipping {
            out.push_str(line);
        }
    }
    out
}

/// The left (flag) cell of a cmdargs flag row, or `None` for any other line.
///
/// A flag row is exactly `desc_col` bytes of left cell followed by a
/// description, and its left cell starts with a `-`.  That rejects the
/// section headers (`Flags:`, `About:`), the `Commands:` rows, the prose of
/// the README block, the 78-dash separators, and the continuation lines of a
/// wrapped description (whose left cell is blank).
fn flag_row_left_cell(line: &str, desc_col: usize) -> Option<&str> {
    let left = line.get(..desc_col)?.trim();
    if !left.starts_with('-') || left.bytes().all(|b| b == b'-') {
        return None;
    }
    Some(left)
}

/// Every long flag the help advertises, as it appears in a row's left cell
/// (`--prove[=LEMMAPREFIX*|LEMMANAME]` -> `--prove`,
/// `--output-json=FILE --oj` -> `--output-json`, `--oj`).
fn advertised_long_flags(help: &str, desc_col: usize) -> Vec<String> {
    let mut out = Vec::new();
    for line in help.lines() {
        let Some(left) = flag_row_left_cell(line, desc_col) else {
            continue;
        };
        for tok in left.split_whitespace() {
            if let Some(name) = tok.strip_prefix("--") {
                let name = name
                    .split(['[', '='])
                    .next()
                    .expect("split always yields one element");
                if !name.is_empty() {
                    out.push(format!("--{name}"));
                }
            }
        }
    }
    out
}

/// Every short flag the help advertises (`-b`, `-?`, `-h`, ...).
fn advertised_short_flags(help: &str, desc_col: usize) -> Vec<String> {
    let mut out = Vec::new();
    for line in help.lines() {
        let Some(left) = flag_row_left_cell(line, desc_col) else {
            continue;
        };
        for tok in left.split_whitespace() {
            if tok.starts_with("--") {
                continue;
            }
            if let Some(rest) = tok.strip_prefix('-') {
                if rest.chars().count() == 1 {
                    out.push(tok.to_string());
                }
            }
        }
    }
    out
}

/// What the binary prints for a mode's `--help`: `help_text(mode)` plus the
/// newline `println!` adds (run.rs and main.rs both emit it that way).
fn printed_help(pin: &HelpPin) -> String {
    let mut s = help_text(pin.mode);
    s.push('\n');
    s
}

#[test]
fn help_head_is_oracle_byte_identical() {
    for pin in &PINS {
        let printed = printed_help(pin);
        let head = expected_head(pin);
        assert!(
            printed.starts_with(&head),
            "{:?} --help must open with the oracle rendering byte-for-byte\n\
             --- first differing byte ---\n{}",
            pin.argv,
            first_difference(&printed, &head)
        );
    }
}

#[test]
fn help_tail_is_the_rs_only_trailer() {
    for pin in &PINS {
        let printed = printed_help(pin);
        let head = expected_head(pin);
        assert_eq!(&printed[head.len()..], pin.trailer, "{:?}", pin.argv);
    }
}

#[test]
fn help_omits_exactly_the_flags_the_parser_rejects() {
    for pin in &PINS {
        let printed = printed_help(pin);
        for f in pin.omitted {
            assert!(
                pin.oracle.contains(f),
                "{f} must appear in the {:?} oracle help",
                pin.argv
            );
            assert!(
                !printed.contains(f),
                "{f} must not be advertised by {:?}: the parser rejects it",
                pin.argv
            );
            let err = parse_args(&[f.to_string()])
                .err()
                .unwrap_or_else(|| panic!("{f} must be rejected"))
                .to_string();
            assert_eq!(err, format!("Unknown flag: {f}"));
        }
        // The head is the oracle text minus exactly these rows and nothing
        // else: walk the oracle's lines against the head's (a subsequence of
        // them) and collect what the walk skips.
        let head = expected_head(pin);
        let mut head_lines = head.lines();
        let mut next_head = head_lines.next();
        let mut dropped: Vec<&str> = Vec::new();
        for line in pin.oracle.lines() {
            if next_head == Some(line) {
                next_head = head_lines.next();
            } else {
                dropped.push(line);
            }
        }
        assert_eq!(
            next_head, None,
            "the {:?} head is not a subsequence of the oracle",
            pin.argv
        );
        let want: Vec<&str> = if pin.dropped.is_empty() {
            Vec::new()
        } else {
            pin.dropped.lines().collect()
        };
        assert_eq!(dropped, want, "{:?}", pin.argv);
    }
}

#[test]
fn help_advertises_no_flag_the_parser_rejects() {
    for pin in &PINS {
        // Head and trailer can sit at different columns, so scan each at its
        // own: reading a row at the wrong width would slice the left cell.
        let head = expected_head(pin);
        let mut flags = advertised_long_flags(&head, pin.desc_col);
        flags.extend(advertised_long_flags(pin.trailer, pin.trailer_col));
        for f in flags {
            if let Err(e) = parse_args(std::slice::from_ref(&f)) {
                assert!(
                    !e.to_string().starts_with("Unknown flag"),
                    "{:?} advertises {f}, which the parser rejects: {e}",
                    pin.argv
                );
            }
        }
        let mut shorts = advertised_short_flags(&head, pin.desc_col);
        shorts.extend(advertised_short_flags(pin.trailer, pin.trailer_col));
        for f in shorts {
            if let Err(e) = parse_args(std::slice::from_ref(&f)) {
                assert!(
                    !e.to_string().starts_with("Unknown flag"),
                    "{:?} advertises {f}, which the parser rejects: {e}",
                    pin.argv
                );
            }
        }
    }
}

#[test]
fn binary_help_stdout_and_exit_code() {
    // Every mode answers `--help` on STDOUT with rc 0 and an empty stderr, and
    // each prints its OWN help — HS dispatches on the mode before the mode's
    // `run` sees the flag (Console.hs:333-338).
    for pin in &PINS {
        let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .args(pin.argv)
            .output()
            .unwrap_or_else(|e| panic!("run tamarin-rs {:?}: {e}", pin.argv));
        assert_eq!(out.status.code(), Some(0), "{:?}", pin.argv);
        assert!(
            out.stderr.is_empty(),
            "oracle writes nothing to stderr for {:?}; got {:?}",
            pin.argv,
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            printed_help(pin),
            "{:?}",
            pin.argv
        );
    }
    // The four are genuinely different documents, not one text four times.
    for (i, a) in PINS.iter().enumerate() {
        for b in &PINS[i + 1..] {
            assert_ne!(
                printed_help(a),
                printed_help(b),
                "{:?} and {:?} must render different help",
                a.argv,
                b.argv
            );
        }
    }
}

#[test]
fn short_help_alias_matches_long() {
    // `-?` is the oracle's help short flag (`helpFlag = flagHelpSimple`,
    // Console.hs:291-292); the oracle answers `Unknown flag: -h`, while this
    // port also accepts `-h` and advertises it in the RS-only group.
    for flag in ["-?", "-h"] {
        let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .arg(flag)
            .output()
            .unwrap_or_else(|e| panic!("run tamarin-rs {flag}: {e}"));
        assert_eq!(out.status.code(), Some(0), "{flag}");
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            printed_help(&PINS[0]),
            "{flag}"
        );
    }
}

#[test]
fn no_input_files_reprints_the_help_after_an_error_line_on_stdout() {
    // HS `batchMode`'s run calls `helpAndExit thisMode (Just "no input files
    // given")` (Batch.hs:90), and `helpAndExit` (Console.hs:341-359) `putStrLn`s
    // the header and the help block — STDOUT — before `exitFailure`.  Pinned
    // against the oracle, which writes 9805 bytes to stdout, nothing to stderr
    // and exits 1 for a bare `tamarin-prover`.
    let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .output()
        .expect("run tamarin-rs with no arguments");
    assert_eq!(out.status.code(), Some(1));
    assert!(
        out.stderr.is_empty(),
        "the help-and-exit path writes nothing to stderr; got {:?}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let want = format!("error: no input files given\n\n{}", printed_help(&PINS[0]));
    assert_eq!(stdout, want);
}

#[test]
fn interactive_without_workdir_reprints_the_help_after_an_error_line_on_stdout() {
    // HS `Interactive.run` dispatches on the WORKDIR argument before any tool
    // check: `helpAndExit thisMode (Just "no working directory specified")`
    // (Interactive.hs:76-80).  Oracle-pinned: the error header and the
    // `interactive` help on STDOUT, nothing on stderr (no maude banner), rc 1.
    let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .arg("interactive")
        .output()
        .expect("run tamarin-rs interactive");
    assert_eq!(out.status.code(), Some(1));
    assert!(
        out.stderr.is_empty(),
        "the help-and-exit path writes nothing to stderr; got {:?}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let want = format!(
        "error: no working directory specified\n\n{}",
        printed_help(&PINS[1])
    );
    assert_eq!(stdout, want);
}

#[test]
fn unknown_flag_is_a_bare_stderr_line_with_no_help() {
    // cmdargs rejects the command line inside `processArgs`
    // (Console.hs:362-372), before any mode runs: `Unknown flag: <flag>\n` on
    // stderr, nothing on stdout, no help block, rc 1.  Oracle-pinned for a long
    // flag, a long flag with a value (the NAME alone is echoed), a short flag,
    // and a flag placed after the file argument.
    for (argv, want) in [
        (vec!["--nonsense", "x.spthy"], "Unknown flag: --nonsense\n"),
        (
            vec!["--nonsense=5", "x.spthy"],
            "Unknown flag: --nonsense\n",
        ),
        (vec!["x.spthy", "--nonsense"], "Unknown flag: --nonsense\n"),
        (vec!["-z", "x.spthy"], "Unknown flag: -z\n"),
        (
            vec!["interactive", "--nonsense"],
            "Unknown flag: --nonsense\n",
        ),
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .args(&argv)
            .output()
            .unwrap_or_else(|e| panic!("run tamarin-rs {argv:?}: {e}"));
        assert_eq!(out.status.code(), Some(1), "{argv:?}");
        assert_eq!(String::from_utf8_lossy(&out.stderr), want, "{argv:?}");
        assert!(
            out.stdout.is_empty(),
            "{argv:?} must write nothing to stdout; got {:?}",
            String::from_utf8_lossy(&out.stdout)
        );
    }
}

/// Render the first byte at which `got` leaves `want`, with context.
fn first_difference(got: &str, want: &str) -> String {
    let at = got
        .bytes()
        .zip(want.bytes())
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| got.len().min(want.len()));
    let lo = at.saturating_sub(120);
    format!(
        "byte {at}\n got: {:?}\nwant: {:?}",
        &got[lo..(at + 120).min(got.len())],
        &want[lo..(at + 120).min(want.len())]
    )
}
