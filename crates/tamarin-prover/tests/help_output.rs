//! Smoke tests for the clap-rendered help/version/usage-error surface.
//!
//! The CLI front end is canonical clap, deliberately NOT byte-matched to the
//! Haskell binary's `cmdargs` output (see the module doc in `src/cli.rs`).
//! These tests pin only the contract the port promises: help and version go
//! to stdout with rc 0, usage errors go to stderr with rc 2, and each mode
//! renders its own document.

use std::process::Command;

fn run(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("run tamarin-rs {args:?}: {e}"))
}

#[test]
fn help_is_stdout_rc_zero() {
    for argv in [&["--help"][..], &["-h"][..]] {
        let out = run(argv);
        assert_eq!(out.status.code(), Some(0), "{argv:?}");
        assert!(out.stderr.is_empty(), "{argv:?}");
        let text = String::from_utf8_lossy(&out.stdout);
        // One representative per flag family plus the subcommands, so an
        // accidental `hide = true` on a family is caught: optional-value
        // (--prove, --heuristic, --bound), repeatable (--lemma, --defines),
        // required-value (--output-json), bool (--auto-sources), batch
        // output (--output-module), tool path (--with-maude).
        for needle in [
            "--prove",
            "--heuristic",
            "--bound",
            "--lemma",
            "--defines",
            "--output-json",
            "--auto-sources",
            "--output-module",
            "--with-maude",
            "interactive",
            "variants",
            "test",
        ] {
            assert!(text.contains(needle), "{argv:?} help lacks {needle}");
        }
    }
}

#[test]
fn each_mode_renders_its_own_help() {
    let helps: Vec<String> = [
        &["--help"][..],
        &["interactive", "--help"][..],
        &["variants", "--help"][..],
        &["test", "--help"][..],
    ]
    .iter()
    .map(|argv| {
        let out = run(argv);
        assert_eq!(out.status.code(), Some(0), "{argv:?}");
        String::from_utf8_lossy(&out.stdout).into_owned()
    })
    .collect();
    for (i, a) in helps.iter().enumerate() {
        for b in &helps[i + 1..] {
            assert_ne!(a, b, "modes must render different help documents");
        }
    }
    // The interactive help carries the web flags the top level doesn't.
    assert!(helps[1].contains("--port"));
    assert!(!helps[0].contains("--port"));
}

#[test]
fn version_is_stdout_rc_zero() {
    // `-V` prints the short form; `--version` adds the build provenance.
    let out = run(&["-V"]);
    assert_eq!(out.status.code(), Some(0));
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains(env!("CARGO_PKG_VERSION")), "{text}");

    let out = run(&["--version"]);
    assert_eq!(out.status.code(), Some(0));
    assert!(out.stderr.is_empty());
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains(env!("CARGO_PKG_VERSION")), "{text}");
    assert!(text.contains("git revision"), "{text}");
    assert!(text.contains("compiled at"), "{text}");
}

#[test]
fn unknown_flag_is_stderr_rc_two() {
    let out = run(&["--frobnicate", "x.spthy"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(out.stdout.is_empty());
    let text = String::from_utf8_lossy(&out.stderr);
    assert!(text.contains("--frobnicate"), "{text}");
    assert!(text.contains("Usage"), "{text}");
}

#[test]
fn bare_invocation_shows_help_rc_two() {
    // `arg_required_else_help`: no files, no flags, no subcommand → the help
    // document as a usage error.
    let out = run(&[]);
    assert_eq!(out.status.code(), Some(2));
    let text = String::from_utf8_lossy(&out.stderr);
    assert!(text.contains("--prove"), "{text}");
}
