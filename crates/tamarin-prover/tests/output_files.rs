// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Which files each mode writes, and their shape (HS Batch.hs).  `-o`/`-O`
//! documents go through `writeFileWithDirs` verbatim, so they end in `end`
//! with no trailing newline; `--parse-only` and the modes that return before
//! `outputTraces` write nothing.  The trace files' bytes for a found trace
//! are the divergence fixtures' `traces` slice and output_traces.rs.
//!
//! Each row runs the binary in a fresh directory; `{OUT}` in its flags names
//! that directory, and every expectation names a path inside it.

mod common;

use common::{fixture, maude_available, run_binary};

enum Expect {
    /// The path does not exist.
    Absent,
    /// The directory exists and holds no file.
    EmptyDir,
    /// The file holds exactly these bytes.
    Bytes(&'static str),
    /// The file starts and ends as given, and contains every fragment.
    Document {
        starts: &'static str,
        ends: &'static str,
        contains: &'static [&'static str],
    },
}

struct Case {
    name: &'static str,
    /// Fixtures under tests/fixtures; `parse_error.spthy` does not parse.
    inputs: &'static [&'static str],
    args: &'static [&'static str],
    rc: i32,
    stdout_empty: bool,
    files: &'static [(&'static str, Expect)],
}

const TRACES: &[&str] = &["--output-json={OUT}/t.json", "--output-dot={OUT}/t.dot"];

const CASES: &[Case] = &[
    // -o on a proving run: the closed theory with its proof, verbatim.
    Case {
        name: "prove_output_file",
        inputs: &["single_recv.spthy"],
        args: &["--prove=chain", "--output={OUT}/out.spthy", "--quiet"],
        rc: 0,
        stdout_empty: false,
        files: &[(
            "out.spthy",
            Expect::Document {
                starts: "theory SingleRecv",
                ends: "\nend",
                contains: &["lemma chain", "SOLVED // trace found", "qed"],
            },
        )],
    },
    // --prove naming no lemma: the -o document keeps the lemma `by sorry`.
    Case {
        name: "prove_filter_output_file",
        inputs: &["single_recv.spthy"],
        args: &["--prove=nonexistent", "--output={OUT}/out.spthy", "--quiet"],
        rc: 0,
        stdout_empty: false,
        files: &[(
            "out.spthy",
            Expect::Document {
                starts: "theory SingleRecv",
                ends: "\nend",
                contains: &["lemma chain", "by sorry"],
            },
        )],
    },
    // -O writes <basename>_analyzed.spthy.
    Case {
        name: "output_dir",
        inputs: &["single_recv.spthy"],
        args: &["--Output={OUT}/dir"],
        rc: 0,
        stdout_empty: false,
        files: &[(
            "dir/single_recv_analyzed.spthy",
            Expect::Document {
                starts: "theory SingleRecv\n",
                ends: "\nend",
                contains: &[],
            },
        )],
    },
    // Translate mode with -o: the document goes to the file, not stdout.
    Case {
        name: "translate_output_file",
        inputs: &["single_recv.spthy"],
        args: &["-m=spthy", "-o={OUT}/out.spthy"],
        rc: 0,
        stdout_empty: true,
        files: &[(
            "out.spthy",
            Expect::Document {
                starts: "theory SingleRecv",
                ends: "\nend",
                contains: &[],
            },
        )],
    },
    // --parse-only ignores -o and -O.
    Case {
        name: "parse_only_output_file",
        inputs: &["single_recv.spthy"],
        args: &["--parse-only", "--output={OUT}/out.spthy"],
        rc: 0,
        stdout_empty: false,
        files: &[("out.spthy", Expect::Absent)],
    },
    Case {
        name: "parse_only_output_dir",
        inputs: &["single_recv.spthy"],
        args: &["--parse-only", "--Output={OUT}/dir"],
        rc: 0,
        stdout_empty: false,
        files: &[("dir", Expect::EmptyDir)],
    },
    // The trace files are written only on the close path.
    Case {
        name: "traces_no_input",
        inputs: &[],
        args: TRACES,
        rc: 1,
        stdout_empty: true,
        files: &[("t.json", Expect::Absent), ("t.dot", Expect::Absent)],
    },
    Case {
        name: "traces_parse_error",
        inputs: &["parse_error.spthy"],
        args: TRACES,
        rc: 1,
        stdout_empty: true,
        files: &[("t.json", Expect::Absent), ("t.dot", Expect::Absent)],
    },
    Case {
        name: "traces_parse_only",
        inputs: &["single_recv.spthy"],
        args: &[
            "--parse-only",
            "--output-json={OUT}/t.json",
            "--output-dot={OUT}/t.dot",
        ],
        rc: 0,
        stdout_empty: false,
        files: &[("t.json", Expect::Absent), ("t.dot", Expect::Absent)],
    },
    Case {
        name: "traces_precompute_only",
        inputs: &["single_recv.spthy"],
        args: &[
            "--precompute-only",
            "--output-json={OUT}/t.json",
            "--output-dot={OUT}/t.dot",
        ],
        rc: 0,
        stdout_empty: false,
        files: &[("t.json", Expect::Absent), ("t.dot", Expect::Absent)],
    },
    Case {
        name: "traces_translate_only",
        inputs: &["single_recv.spthy"],
        args: &[
            "-m=spthy",
            "--output-json={OUT}/t.json",
            "--output-dot={OUT}/t.dot",
        ],
        rc: 0,
        stdout_empty: false,
        files: &[("t.json", Expect::Absent), ("t.dot", Expect::Absent)],
    },
    // Without a proof there is no trace: aeson-pretty's empty graph list and
    // a 0-byte dot file.
    Case {
        name: "traces_without_proof",
        inputs: &["single_recv.spthy"],
        args: TRACES,
        rc: 0,
        stdout_empty: false,
        files: &[
            ("t.json", Expect::Bytes("{\n    \"graphs\": []\n}")),
            ("t.dot", Expect::Bytes("")),
        ],
    },
];

#[test]
fn every_mode_writes_exactly_its_files() {
    if !maude_available() {
        return;
    }
    let mut failures = Vec::new();
    for case in CASES {
        let dir = std::env::temp_dir().join(format!(
            "tamarin_rs_output_files_{}_{}",
            case.name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("mkdir");
        if case
            .files
            .iter()
            .any(|(_, e)| matches!(e, Expect::EmptyDir))
        {
            std::fs::create_dir_all(dir.join("dir")).expect("mkdir");
        }
        let out = dir.to_str().expect("utf-8 temp dir");
        let args: Vec<String> = case.args.iter().map(|a| a.replace("{OUT}", out)).collect();
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let inputs: Vec<_> = case.inputs.iter().map(|i| fixture(i)).collect();
        let inputs: Vec<&std::path::Path> = inputs.iter().map(|p| p.as_path()).collect();
        let (code, stdout, stderr) = run_binary(&args, &inputs);
        let mut problems = Vec::new();
        if code != case.rc {
            problems.push(format!("exited {code}, want {}", case.rc));
        }
        if case.stdout_empty != stdout.is_empty() {
            problems.push(format!("stdout empty: {}", stdout.is_empty()));
        }
        for (path, expect) in case.files {
            let p = dir.join(path);
            let body = std::fs::read_to_string(&p).ok();
            let ok = match expect {
                Expect::Absent => !p.exists(),
                Expect::EmptyDir => std::fs::read_dir(&p).is_ok_and(|mut d| d.next().is_none()),
                Expect::Bytes(want) => body.as_deref() == Some(*want),
                Expect::Document {
                    starts,
                    ends,
                    contains,
                } => body.as_deref().is_some_and(|b| {
                    b.starts_with(starts)
                        && b.ends_with(ends)
                        && contains.iter().all(|c| b.contains(c))
                }),
            };
            if !ok {
                problems.push(format!("{path}: unexpected state {body:?}"));
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
        if !problems.is_empty() {
            failures.push(format!(
                "{}:\n  {}\n  stderr:\n{stderr}",
                case.name,
                problems.join("\n  ")
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
