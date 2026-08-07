// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end stderr / exit-code parity for the duplicate-rule guards.
//!
//! Parse time: `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) rejects a
//! second, DIFFERENT rule under an existing name via `addOpenProtoRule`
//! (OpenTheory.hs:691-702); batch mode's `handleError` `die`s on the
//! resulting `ParserError` (Main/Mode/Batch.hs:234) — parsec frame on stderr,
//! exit 1, no stdout.  An identical duplicate is accepted and appended again.
//!
//! Translate time: SAPIC's `translate` folds its generated rules through the
//! same guard (`foldM liftedAddProtoRule`, Sapic.hs:74), so a user rule named
//! like a generated one (`rule Init` alongside a `process:`) aborts AFTER the
//! `Theory translated` marker.  In HS the thrown `DuplicateItem` escapes to
//! GHC's runtime: the pinned oracle (Git revision ef3f0468) prints exactly
//! `tamarin-prover: duplicate rule: Init` after the markers and exits 1.
//!
//! The oracle emits the `maude tool:` banner and the `[Theory X] …` markers
//! on stderr even under `--quiet` (the flag is registered but never read —
//! TheoryLoader.hs:159-163, 414-416).  Expectations below are its `--quiet`
//! stderr minus the three banner lines, whose maude path and version are
//! machine-local.

use std::process::Command;

fn maude_available() -> bool {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return std::path::Path::new(&p).exists();
    }
    for c in ["/usr/local/bin/maude", "/usr/bin/maude"] {
        if std::path::Path::new(c).exists() {
            return true;
        }
    }
    false
}

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines that
/// follow it (Console.hs:150-155).
fn strip_maude_banner(stderr: &str) -> String {
    let rest = stderr
        .split_inclusive('\n')
        .skip_while(|l| l.starts_with("maude tool: '") || l.starts_with(" checking "))
        .collect::<String>();
    assert_ne!(
        rest, stderr,
        "expected a `maude tool:` banner on stderr; got:\n{stderr}"
    );
    rest
}

/// Run the built binary on `src` and return `(exit code, stderr minus the
/// maude banner)`.
fn run_binary(name: &str, src: &str) -> (i32, String) {
    let dir = std::env::temp_dir().join("tamarin_prover_dup_rule_names");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(name);
    std::fs::write(&path, src).expect("write theory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    let out = cmd
        .arg("--quiet")
        .arg(&path)
        .output()
        .expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        strip_maude_banner(&String::from_utf8(out.stderr).expect("utf-8 stderr")),
    )
}

/// Two different rules under one name: the parsec frame `die` prints — the
/// `SourcePos` name is the input path, so only the frame's tail is portable.
#[test]
fn duplicate_rule_prints_the_parsec_frame_and_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "dup.spthy",
        "theory T begin\n\n\
         rule R1: [ ] --> [ Out('a') ]\n\
         rule R1: [ ] --> [ Out('b') ]\n\n\
         end\n",
    );
    assert_eq!(code, 1);
    assert!(
        stderr.ends_with(
            "dup.spthy\" (line 6, column 1):\n\
             unexpected \"e\"\n\
             expecting \"variants\"\n\
             duplicate rule: R1\n"
        ),
        "unexpected stderr:\n{stderr}"
    );
}

/// An identical duplicate loads with exit 0 and renders BOTH copies.
#[test]
fn identical_duplicate_loads_and_renders_twice() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let dir = std::env::temp_dir().join("tamarin_prover_dup_rule_names");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join("ident.spthy");
    std::fs::write(
        &path,
        "theory T begin\n\nrule R1: [ ] --> [ ]\nrule R1: [ ] --> [ ]\n\nend\n",
    )
    .expect("write theory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    let out = cmd
        .arg("--quiet")
        .arg(&path)
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(0));
    let stdout = String::from_utf8(out.stdout).expect("utf-8 stdout");
    assert_eq!(
        stdout
            .matches("rule (modulo E) R1:\n   [ ] --> [ ]")
            .count(),
        2,
        "expected both R1 copies rendered:\n{stdout}"
    );
}

/// A user rule named like a SAPIC-generated one dies at translate time with
/// the oracle's stderr line `tamarin-prover: duplicate rule: Init`, after the
/// load/translate markers, with exit 1 and no theory on stdout (HS: the
/// `addProtoRule` exception escapes to GHC's runtime, which prints
/// `tamarin-prover: <show exception>` — the shape `run.rs`'s SAPIC error arm
/// reproduces).
#[test]
fn sapic_generated_name_clash_aborts_translation() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "sapic_clash.spthy",
        "theory T begin\n\n\
         rule Init: [ ] --> [ Out('a') ]\n\n\
         process:\nnew x; out(x)\n\n\
         end\n",
    );
    assert_eq!(code, 1);
    assert!(
        stderr.contains("tamarin-prover: duplicate rule: Init\n"),
        "expected the oracle's `tamarin-prover: duplicate rule: Init` line:\n{stderr}"
    );
    assert!(
        stderr.contains("[Theory T] Theory translated\n"),
        "the clash fires after the `Theory translated` marker:\n{stderr}"
    );
}
