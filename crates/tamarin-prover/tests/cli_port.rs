// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! CLI behaviour the port owns: its own error wording, and deliberate
//! divergences from the oracle.  Nothing here is compared with Haskell bytes
//! (cli_refs and the divergence fixtures do that); each row pins the exit
//! code and fragments the port's stdout and stderr must (or, `!`-prefixed,
//! must not) contain.

mod common;

use common::{fixture, maude_available, run_binary};

struct Case {
    name: &'static str,
    /// Fixtures under tests/fixtures.
    inputs: &'static [&'static str],
    args: &'static [&'static str],
    rc: i32,
    /// `None`: stdout must be empty.
    stdout: Option<&'static [&'static str]>,
    stderr: &'static [&'static str],
}

const CASES: &[Case] = &[
    // A parse error: rc 1, nothing on stdout, a diagnostic, and the theory
    // is never loaded.
    Case {
        name: "parse_error",
        inputs: &["parse_error.spthy"],
        args: &[],
        rc: 1,
        stdout: None,
        stderr: &["error", "!Theory loaded"],
    },
    // An oracle script that cannot be executed fails the batch without
    // printing the failed theory.
    Case {
        name: "missing_oracle",
        inputs: &["oracle_missing.spthy"],
        args: &["--prove=test"],
        rc: 1,
        stdout: None,
        stderr: &["oracle exec error:"],
    },
    // A malformed `configuration:` block is an error in the modes that close
    // the theory, and ignored in translate mode.
    Case {
        name: "config_block_close",
        inputs: &["config_bogus.spthy"],
        args: &[],
        rc: 1,
        stdout: None,
        stderr: &["configuration block:"],
    },
    Case {
        name: "config_block_translate",
        inputs: &["config_bogus.spthy"],
        args: &["-m=spthy"],
        rc: 0,
        stdout: Some(&["theory Cfg"]),
        stderr: &[],
    },
    // A user `em/2` without bilinear pairing is a plain function, where the
    // oracle crashes: the exists-trace lemma is proven through `c_em`.
    Case {
        name: "em_without_bilinear_pairing",
        inputs: &["em_no_bp.spthy"],
        args: &["--prove", "--derivcheck-timeout=0"],
        rc: 0,
        stdout: Some(&["l (exists-trace): verified", "!has no variants"]),
        stderr: &[],
    },
    // A --heuristic value the oracle would refuse is a loud rejection, never
    // a silent prove under the default ranking.
    Case {
        name: "heuristic_unknown_ranking",
        inputs: &["cli_flags_basic.spthy"],
        args: &["--derivcheck-timeout=300", "--prove", "--heuristic=x"],
        rc: 1,
        stdout: None,
        stderr: &["unknown goal ranking"],
    },
    Case {
        name: "heuristic_undeclared_tactic",
        inputs: &["cli_flags_basic.spthy"],
        args: &[
            "--derivcheck-timeout=300",
            "--prove",
            "--heuristic={nosuch}",
        ],
        rc: 1,
        stdout: None,
        stderr: &["not declared in the theory"],
    },
    Case {
        name: "heuristic_unterminated",
        inputs: &["cli_flags_basic.spthy"],
        args: &[
            "--derivcheck-timeout=300",
            "--prove",
            "--heuristic={unterminated",
        ],
        rc: 1,
        stdout: None,
        stderr: &["unterminated '{'"],
    },
    // The export modules are not ported.
    Case {
        name: "module_proverif",
        inputs: &["single_recv.spthy"],
        args: &["-m=proverif"],
        rc: 1,
        stdout: None,
        stderr: &["--output-module=proverif", "not yet ported"],
    },
    Case {
        name: "module_proverifequiv",
        inputs: &["single_recv.spthy"],
        args: &["-m=proverifequiv"],
        rc: 1,
        stdout: None,
        stderr: &["--output-module=proverifequiv", "not yet ported"],
    },
    Case {
        name: "module_deepsec",
        inputs: &["single_recv.spthy"],
        args: &["-m=deepsec"],
        rc: 1,
        stdout: None,
        stderr: &["--output-module=deepsec", "not yet ported"],
    },
];

fn contains_all(name: &str, stream: &str, text: &str, fragments: &[&str]) -> Vec<String> {
    fragments
        .iter()
        .filter_map(|f| match f.strip_prefix('!') {
            Some(absent) if text.contains(absent) => {
                Some(format!("{name}: {stream} must not contain {absent:?}"))
            }
            None if !text.contains(f) => Some(format!("{name}: {stream} lacks {f:?}")),
            _ => None,
        })
        .collect()
}

#[test]
fn every_port_owned_cli_case_holds() {
    if !maude_available() {
        return;
    }
    let mut failures = Vec::new();
    for case in CASES {
        let inputs: Vec<_> = case.inputs.iter().map(|i| fixture(i)).collect();
        let inputs: Vec<&std::path::Path> = inputs.iter().map(|p| p.as_path()).collect();
        let (code, stdout, stderr) = run_binary(case.args, &inputs);
        let mut problems = Vec::new();
        if code != case.rc {
            problems.push(format!("{}: exited {code}, want {}", case.name, case.rc));
        }
        match case.stdout {
            None if !stdout.is_empty() => {
                problems.push(format!("{}: stdout must be empty", case.name))
            }
            None => {}
            Some(fragments) => {
                problems.extend(contains_all(case.name, "stdout", &stdout, fragments))
            }
        }
        problems.extend(contains_all(case.name, "stderr", &stderr, case.stderr));
        if !problems.is_empty() {
            failures.push(format!("{}\n  stderr:\n{stderr}", problems.join("\n")));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
