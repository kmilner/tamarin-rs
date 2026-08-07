// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end byte pins for `-m` / `--output-module` translate-only mode
//! (Batch.hs:101-113): per-module stdout (`prettyOpenTheoryByModule`,
//! TheoryLoader.hs:783-801, plus `withVersionAndReport`'s two trailing
//! comments), the six-marker stderr with NO `Theory closed`, the deferred
//! `-o`/`-O` write path, the `--quit-on-warning` abort shape, and the GHC
//! death for an unknown module value (`ArgumentError` forced at
//! Batch.hs:163:33).
//!
//! Every expectation below is verbatim oracle bytes from the pinned v1.13.0
//! binary (Git revision ef3f0468) on `examples/sapic/fast/basic/
//! replication.spthy` and `examples/sapic/not-suitable-for-regression/
//! issue331-warn-for-capture.spthy`, with only the build-local lines of the
//! `Generated from:` block normalized.
//!
//! MAUDE_PATH trap: [`maude_available`] probes ONLY `$MAUDE_PATH` and two
//! hardcoded absolute paths — never `$PATH`.  On machines whose maude lives
//! elsewhere (e.g. /home/linuxbrew/.linuxbrew/bin/maude) a bare `cargo test`
//! SKIPS every test here and reports green; run with
//! `MAUDE_PATH=/path/to/maude cargo test -p tamarin-prover`.
//! [`strip_maude_banner`] is the positive control: it panics when a run that
//! should have started maude produced no banner.

mod common;

use common::{joined, maude_available, normalize_stdout, strip_maude_banner};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_output_module";

/// `examples/sapic/fast/basic/replication.spthy`, verbatim.
const REPLICATION: &str = r#"/*
example illustrates replication (!)
*/

theory Replication
begin

process:
! new s; event Secret(s); out(s); 0

// only a single secret can be learned by the attacker
// lemma falsified by tamarin
lemma onlyOneSecret:
    exists-trace
      "Ex #i #j x y.  Secret(x)@i & Secret(y)@j & not (x = y)"

end
"#;

/// `examples/sapic/not-suitable-for-regression/issue331-warn-for-capture.spthy`
/// minus its long formal comment — the two variable-capture warnings are what
/// matters here.
const WF_WARN_THEORY: &str = r#"theory issue331

begin

process:
    insert 'bla', 'toto'
    |
    lookup 'bla' as counter in
     in(counter) // give warning before rewriting variable
    |
        in(x); in(x) // same error

end
"#;

/// `examples/sapic/fast/basic/patterns.spthy`, verbatim — an embedded MSR
/// whose premise pattern-matches an already-bound variable (`[In(=z)]`).
const PATTERNS: &str = r#"theory Patterns
begin

process:
in(x); // allowed
in(=x); // allowed
/* in(<=x,x>); // disallowed because ambigous */
/* in(x); // disallowed because x is bound in top-level process */
/* in(<y,y>); // disallowed, because unclear semantics... */
in(<=x,=x>); // allowed, because clear semantics...
[In(z)]-->[]; // allowed
/* [In(z)]-->[]; // disallowed because z is bound */
[In(=z)]-->[]; // allowed
0


end
"#;

/// Write `theory` to a per-stem temp file and run the binary on it with
/// `extra` flags; returns `(exit code, raw stdout, raw stderr)`.
fn run_raw(stem: &str, theory: &str, extra: &[&str]) -> (i32, String, String) {
    common::run_raw(TMP_DIR, stem, theory, extra)
}

/// [`run_raw`] + stdout normalization + banner strip.
fn run_translate(stem: &str, theory: &str, extra: &[&str]) -> (i32, String, String) {
    let (code, stdout, stderr) = run_raw(stem, theory, extra);
    (code, normalize_stdout(&stdout), strip_maude_banner(&stderr))
}

/// The oracle's stderr for every `-m spthy|spthytyped|msr` run on
/// [`REPLICATION`], after the banner: exactly six markers — NO
/// `[Theory Replication] Theory closed`, because translate mode goes through
/// `translateAndCheckTheory` (TheoryLoader.hs:768-780), which never reaches
/// `closeTranslatedTheory` and its `traceM` marker (:696).
const EXPECTED_STDERR: &[&str] = &[
    "[Theory Replication] Theory loaded",
    "[Theory Replication] Theory translated",
    "[Theory Replication] No Deconstruction Chain checks started",
    "[Theory Replication] No Deconstruction Chain checks ended",
    "[Theory Replication] Derivation checks started",
    "[Theory Replication] Derivation checks ended",
];

/// Oracle stdout for `-m=spthy` on [`REPLICATION`], normalized: the source
/// theory echoed untranslated (processes intact, no generated rules), then
/// the wellformedness comment and the `Generated from:` block.
const EXPECTED_SPTHY: &[&str] = &[
    "theory Replication",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "process:",
    "  !(new s;",
    "    event Secret( s );",
    "    out(s))",
    "",
    "lemma onlyOneSecret:",
    "  exists-trace",
    "  \"\u{2203} #i #j x y. ((Secret( x ) @ #i) \u{2227} (Secret( y ) @ #j)) \u{2227} (\u{ac}(x = y))\"",
    "/*",
    "guarded formula characterizing all satisfying traces:",
    "\"\u{2203} #i #j x y. (Secret( x ) @ #i) \u{2227} (Secret( y ) @ #j) \u{2227} \u{ac}(x = y)\"",
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
];

/// Oracle stdout for `-m=spthytyped`: variables renamed (`s` → `s.1`), and
/// the recomputed `function:` items appended after the lemma in DESCENDING
/// `UserDefinedSym` order (`Map.foldrWithKey` + append, Typing.hs:210,226).
/// The three trailing spaces on each `function:` line are HS's
/// `prettyTranslationElement` bytes.
const EXPECTED_SPTHYTYPED: &[&str] = &[
    "theory Replication",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "process:",
    "  !(new s.1;",
    "    event Secret( s.1 );",
    "    out(s.1))",
    "",
    "lemma onlyOneSecret:",
    "  exists-trace",
    "  \"\u{2203} #i #j x y. ((Secret( x ) @ #i) \u{2227} (Secret( y ) @ #j)) \u{2227} (\u{ac}(x = y))\"",
    "/*",
    "guarded formula characterizing all satisfying traces:",
    "\"\u{2203} #i #j x y. (Secret( x ) @ #i) \u{2227} (Secret( y ) @ #j) \u{2227} \u{ac}(x = y)\"",
    "*/",
    "by sorry",
    "",
    "function: snd (Any) : Any   ",
    "",
    "function: pair (Any, Any) : Any   ",
    "",
    "function: fst (Any) : Any   ",
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
];

/// Oracle stdout for `-m=msr`: every TranslationItem dropped (no `process:`),
/// `heuristic: p`, the SAPIC-generated rules WITHOUT AC-variant / loop-breaker
/// comments, and the `single_session` restriction with its `// safety
/// formula` but no `/* expanded formula */` block.
const EXPECTED_MSR: &[&str] = &[
    "theory Replication",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "heuristic: p",
    "",
    "lemma onlyOneSecret:",
    "  exists-trace",
    "  \"\u{2203} #i #j x y. ((Secret( x ) @ #i) \u{2227} (Secret( y ) @ #j)) \u{2227} (\u{ac}(x = y))\"",
    "/*",
    "guarded formula characterizing all satisfying traces:",
    "\"\u{2203} #i #j x y. (Secret( x ) @ #i) \u{2227} (Secret( y ) @ #j) \u{2227} \u{ac}(x = y)\"",
    "*/",
    "by sorry",
    "",
    "rule (modulo E) Init[color=#ffffff, process=\"!\", issapicrule,",
    "                     role='Process']:",
    "   [ ] --[ Init( ) ]-> [ State_( ) ]",
    "",
    "rule (modulo E) p_0_[color=#ffffff, process=\"!\", issapicrule,",
    "                     role='Process']:",
    "   [ State_( ) ] --> [ !Semistate_1( ) ]",
    "",
    "rule (modulo E) p_1_[color=#ffffff, process=\"!\", issapicrule,",
    "                     role='Process']:",
    "   [ !Semistate_1( ) ] --> [ State_1( ) ]",
    "",
    "rule (modulo E) news_0_1[color=#ffffff, process=\"new s.1;\", issapicrule,",
    "                         role='Process']:",
    "   [ State_1( ), Fr( s.1 ) ] --> [ State_11( s.1 ) ]",
    "",
    "rule (modulo E) eventSecrets_0_11[color=#ffffff,",
    "                                  process=\"event Secret( s.1 );\", issapicrule, role='Process']:",
    "   [ State_11( s.1 ) ] --[ Secret( s.1 ) ]-> [ State_111( s.1 ) ]",
    "",
    "rule (modulo E) outs_0_111[color=#ffffff, process=\"out(s.1);\",",
    "                           issapicrule, role='Process']:",
    "   [ State_111( s.1 ) ] --> [ State_1111( s.1 ), Out( s.1 ) ]",
    "",
    "rule (modulo E) p_0_1111[color=#ffffff, process=\"0\", issapicrule,",
    "                         role='Process']:",
    "   [ State_1111( s.1 ) ] --> [ ]",
    "",
    "restriction single_session:",
    "  \"\u{2200} #i #j. ((Init( ) @ #i) \u{2227} (Init( ) @ #j)) \u{21d2} (#i = #j)\"",
    "  // safety formula",
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
];

/// Oracle stdout for `-m=spthy` on [`PATTERNS`].  The `process:` block goes
/// through `prettyProcess = prettySapic' rulePrinter` (TheoryObject.hs:851-852,
/// Print.hs:34-53), which re-applies `unextractMatchingVariables mv` to an
/// embedded MSR's PREMISES: `[ In( =z ) ]` keeps the `=` pattern-match marker,
/// while the unmarked sibling rule stays `[ In( z ) ]`.
const EXPECTED_PATTERNS_SPTHY: &[&str] = &[
    "theory Patterns",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "process:",
    "  in(x);",
    "  in(=x);",
    "  in(<=x, =x>);",
    "   [ In( z ) ] --> [ ];",
    "   [ In( =z ) ] --> [ ]",
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
];

/// Oracle stdout for `-m=spthytyped` on [`PATTERNS`]: same markers, on the
/// renamed variables.
const EXPECTED_PATTERNS_SPTHYTYPED: &[&str] = &[
    "theory Patterns",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "process:",
    "  in(x.1);",
    "  in(=x.1);",
    "  in(<=x.1, =x.1>);",
    "   [ In( z.1 ) ] --> [ ];",
    "   [ In( =z.1 ) ] --> [ ]",
    "",
    "function: snd (Any) : Any   ",
    "",
    "function: pair (Any, Any) : Any   ",
    "",
    "function: fst (Any) : Any   ",
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
];

/// A theory whose `functions:` block re-declares both pair projections with an
/// attribute the builtin symbols do not carry, alongside a genuine user
/// destructor and a private constructor.
const FST_SND_ATTRS: &str = r#"theory FstSndAttrs
begin

functions: fst/1 [destructor], snd/1 [destructor], dec/2 [destructor],
           g/1 [private]

equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2, dec(g(x.1), x.2) = x.1

rule R: [ In( x ) ] --> [ Out( fst(x) ) ]

end
"#;

/// Oracle stdout for `-m=spthy` on [`FST_SND_ATTRS`], normalized.  `fst`/`snd`
/// print WITHOUT `[destructor]` while `dec` keeps it: HS's `function`
/// short-circuit for those two names returns `NoEqUser (f, kp')` — the
/// EXISTING pair-projection symbol `(1, Public, Constructor, NotNDC)` — so the
/// requested attributes never reach the `FunctionTypingInfo` item
/// (Theory/Text/Parser/Signature.hs:217, printed by TheoryObject.hs:820-838).
/// The signature echo agrees: `fst/1` and `snd/1` list no attributes there
/// either, because the short-circuit also skips `addFunSym`.
const EXPECTED_FST_SND_ATTRS_SPTHY: &[&str] = &[
    "theory FstSndAttrs",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: dec/2 [destructor], fst/1, g/1 [private,constructor], pair/2,",
    "           snd/1",
    "equations:",
    "    dec(g(x.1), x.2) = x.1,",
    "    fst(<x.1, x.2>) = x.1,",
    "    snd(<x.1, x.2>) = x.2",
    "",
    "function: fst (Any) : Any   ",
    "",
    "function: snd (Any) : Any   ",
    "",
    "function: dec (Any, Any) : Any   [destructor] ",
    "",
    "function: g (Any) : Any  [private]  ",
    "",
    "rule (modulo E) R:",
    "   [ In( x ) ] --> [ Out( fst(x) ) ]",
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
];

#[test]
fn spthy_module_drops_requested_attributes_from_redeclared_pair_projections() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("fst_snd_attrs", FST_SND_ATTRS, &["-m=spthy"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_FST_SND_ATTRS_SPTHY));
}

#[test]
fn spthy_module_keeps_msr_pattern_match_markers() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("patterns_spthy", PATTERNS, &["-m=spthy"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_PATTERNS_SPTHY));
}

#[test]
fn spthytyped_module_keeps_msr_pattern_match_markers() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("patterns_typed", PATTERNS, &["-m=spthytyped"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_PATTERNS_SPTHYTYPED));
}

/// The `process="..."` rule attribute uses the OTHER rule printer —
/// `prettyRuleAttribute`'s local `f l a r rest _` (Rule.hs:1324-1327) discards
/// the match-var set — so both embedded MSRs render their premise unmarked and
/// the two attributes are byte-identical.  Pins that the `=`-marking fix is
/// confined to the `prettySapic` path.
#[test]
fn msr_module_process_attribute_drops_pattern_match_markers() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("patterns_msr", PATTERNS, &["-m=msr"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let attrs: Vec<&str> = stdout
        .lines()
        .filter(|l| l.contains("process=\" ["))
        .collect();
    assert_eq!(
        attrs,
        vec![
            "                          process=\" [ In( z.1 ) ] --> [ ];\", issapicrule, role='Process']:",
            "                           process=\" [ In( z.1 ) ] --> [ ];\", issapicrule, role='Process']:",
        ],
        "stdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("=z"),
        "the attribute printer never marks match variables:\n{stdout}"
    );
}

#[test]
fn spthy_module_echoes_the_process_block() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("spthy", REPLICATION, &["-m=spthy"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_SPTHY));
}

#[test]
fn spthytyped_module_appends_function_type_lines() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("spthytyped", REPLICATION, &["-m=spthytyped"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_SPTHYTYPED));
}

#[test]
fn msr_module_emits_translated_rules_and_no_summary() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_translate("msr", REPLICATION, &["-m=msr"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_MSR));
    assert!(
        !stdout.contains("summary of summaries"),
        "translate mode must not print the summary block"
    );
}

#[test]
fn translate_only_stderr_has_no_theory_closed_marker() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    for m in ["-m=spthy", "-m=spthytyped", "-m=msr"] {
        let (code, _, stderr) = run_translate("stderr_markers", REPLICATION, &[m]);
        assert_eq!(code, 0, "{m} stderr: {stderr}");
        assert_eq!(stderr, joined(EXPECTED_STDERR), "{m}");
    }
}

/// `-m=bogus` (and `-m=` via the long form): `ArgumentError "output mode not
/// supported."` forced out of `mkTheoryLoadOptions` at Batch.hs:163:33 —
/// AFTER the banner, BEFORE any `[Theory …]` marker, stdout empty, rc 1.
#[test]
fn unsupported_module_dies_with_hs_bytes() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    for flag in ["-m=bogus", "--output-module="] {
        let (code, stdout, stderr) = run_raw("bogus", REPLICATION, &[flag]);
        assert_eq!(code, 1, "{flag}");
        assert!(
            stdout.is_empty(),
            "{flag}: stdout must be empty: {stdout:?}"
        );
        assert!(
            !stderr.contains("panicked at"),
            "{flag}: GHC-style death, not a Rust panic:\n{stderr}"
        );
        let rest = strip_maude_banner(&stderr);
        assert_eq!(
            rest,
            "tamarin-prover: output mode not supported.\n\
             CallStack (from HasCallStack):\n\
             \x20\x20error, called at src/Main/Mode/Batch.hs:163:33 in main:Main.Mode.Batch\n",
            "{flag}"
        );
    }
}

/// `--partial-evaluation=bogus` shares the Batch.hs:163:33 death
/// (`ArgumentError "partial-evaluation: unknown option"`,
/// TheoryLoader.hs:354-358), also after the banner.
#[test]
fn partial_evaluation_unknown_option_dies_with_hs_bytes() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_raw("pe_bogus", REPLICATION, &["--partial-evaluation=bogus"]);
    assert_eq!(code, 1);
    assert!(stdout.is_empty(), "stdout must be empty: {stdout:?}");
    let rest = strip_maude_banner(&stderr);
    assert_eq!(
        rest,
        "tamarin-prover: partial-evaluation: unknown option\n\
         CallStack (from HasCallStack):\n\
         \x20\x20error, called at src/Main/Mode/Batch.hs:163:33 in main:Main.Mode.Batch\n"
    );
}

/// The three export modules are valid values whose backends are unported:
/// they must NOT die with `output mode not supported.` but with the port's
/// own not-yet-ported error.
#[test]
fn proverif_module_still_errors_as_unported() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    for m in ["proverif", "proverifequiv", "deepsec"] {
        let (code, _, stderr) = run_raw("export", REPLICATION, &[&format!("-m={m}")]);
        assert_eq!(code, 1, "{m}");
        assert!(
            stderr.contains(&format!("--output-module={m}")) && stderr.contains("not yet ported"),
            "{m}: expected the not-ported error, got:\n{stderr}"
        );
        assert!(
            !stderr.contains("output mode not supported."),
            "{m} is a VALID module value; it must not hit the GHC death:\n{stderr}"
        );
    }
}

/// `--parse-only -m msr` behaves as plain `--parse-only` (Batch.hs guard
/// order :91-101): no maude banner, no wf/version comment blocks, no
/// translation.
#[test]
fn parse_only_wins_over_output_module() {
    let (code, stdout, stderr) = run_raw("parse_only", REPLICATION, &["--parse-only", "-m=msr"]);
    let (pcode, pstdout, _) = run_raw("parse_only_plain", REPLICATION, &["--parse-only"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(pcode, 0);
    assert_eq!(
        stdout, pstdout,
        "--parse-only -m msr must equal --parse-only"
    );
    assert!(
        !stderr.contains("maude tool:"),
        "parse-only never starts maude:\n{stderr}"
    );
    assert!(stdout.contains("process:"), "untranslated echo expected");
}

/// `-m=spthy -o=FILE`: stdout stays EMPTY, the doc goes to FILE verbatim —
/// `writeFileWithDirs o (renderDoc d)` has no `putStrLn`, so the file lacks
/// the stdout form's trailing newline (881 vs 882 bytes on typing4.spthy).
#[test]
fn output_file_gets_verbatim_doc_and_stdout_stays_empty() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let dir = std::env::temp_dir().join("tamarin_prover_output_module");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let out_file = dir.join("repl_out.spthy");
    let _ = std::fs::remove_file(&out_file);
    let (code, stdout, stderr) = run_raw(
        "ofile",
        REPLICATION,
        &["-m=spthy", &format!("-o={}", out_file.display())],
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert!(stdout.is_empty(), "stdout must be empty: {stdout:?}");
    strip_maude_banner(&stderr); // positive control: the run happened
    let written = std::fs::read_to_string(&out_file).expect("read -o file");
    assert!(
        !written.ends_with('\n'),
        "-o file is written verbatim, no trailing newline"
    );
    let mut expected = joined(EXPECTED_SPTHY);
    expected.pop(); // the stdout form's putStrLn newline
    assert_eq!(normalize_stdout(&written), normalize_stdout(&expected));
}

/// `-o` with an empty value (bare `-o`, no `-O`): every file is processed
/// (all six markers), then `die "Please specify a valid output
/// file/directory"` — stderr, rc 1, stdout empty (Batch.hs:106-110).
#[test]
fn empty_output_file_flag_dies_after_processing() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_raw("oempty", REPLICATION, &["-m=spthy", "-o"]);
    assert_eq!(code, 1);
    assert!(stdout.is_empty(), "stdout must be empty: {stdout:?}");
    let rest = strip_maude_banner(&stderr);
    let mut expected = joined(EXPECTED_STDERR);
    expected.push_str("Please specify a valid output file/directory\n");
    assert_eq!(rest, expected);
}

/// `--quit-on-warning` in translate mode (`withVersionAndReport`,
/// TheoryLoader.hs:656 + `handleError (WarningError …)`, Batch.hs:236-242):
/// stdout = blank line + WARNING header + blank + report + blank, stderr ends
/// with the `die` line, rc 1, NO theory output.
#[test]
fn quit_on_warning_prints_report_block_and_aborts() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_raw("qow", WF_WARN_THEORY, &["-m=spthy", "--quit-on-warning"]);
    assert_eq!(code, 1);
    assert_eq!(
        stdout,
        "\nWARNING: the following wellformedness checks failed!\n\n\
         Wellformedness-error in Process\n\
         \x20\x20Variable bound twice: x.\n\
         \x20\x20\n\
         \x20\x20Variable bound twice: counter.\n\n"
    );
    let rest = strip_maude_banner(&stderr);
    assert!(
        rest.ends_with("quit-on-warning mode selected - aborting on wellformedness errors.\n"),
        "stderr must end with the die line; got:\n{rest}"
    );
    assert!(
        !stdout.contains("theory issue331"),
        "no theory output on quit-on-warning"
    );
}
