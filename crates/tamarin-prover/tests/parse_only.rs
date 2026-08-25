// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--parse-only` end-to-end byte pins.
//!
//! HS `--parse-only` (Batch.hs:91-95) parses each input file (`loadTheory`,
//! which emits the `[Theory X] Theory loaded` traceM on stderr —
//! TheoryLoader.hs:451), then prints `prettyOpenTheory` for each via
//! `putStrLn . renderDoc` on STDOUT — no Maude banner, no wellformedness, no
//! `summary of summaries`, and NO output files (`-o`/`-O` are ignored by that
//! branch).  Every expected string below is the byte-exact stdout/stderr of
//! the pinned v1.13.0 oracle
//! (tamarin-prover-testing/.../bin/tamarin-prover) on the same input.
//!
//! Needs no Maude — `--parse-only` starts none (the oracle's
//! `toSignatureWithMaude` is output-inert there).

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

fn assert_transcript(
    test: &str,
    files: &[(&str, &str)],
    inputs: &[&str],
    want_stdout: &str,
    want_stderr: &str,
) {
    let (code, stdout, stderr) = run_parse_only(test, files, inputs);
    assert_eq!(code, 0, "exit code; stderr:\n{}", stderr);
    assert_eq!(stdout, want_stdout, "stdout must match the oracle bytes");
    assert_eq!(stderr, want_stderr, "stderr must match the oracle bytes");
}

/// Signature-heavy theory: `builtins:` enable-flag vs function-adding entries,
/// `builtin  <name>` items, `function:` typing lines (trailing-space layout),
/// `[private,constructor]` attrs, `macros:`, let-block rule.
#[test]
fn sig_builtins_functions_macros() {
    assert_transcript(
        "sig_builtins_functions_macros",
        &[(
            "p2_sig.spthy",
            r#"theory Sig
begin

builtins: symmetric-encryption, hashing, diffie-hellman
functions: f/2, g/1 [private], unwrap/1 [destructor], mac/2
equations: unwrap(f(x,y)) = x

macros: m1(x) = h(x)

rule A:
  let k2 = h(~k) in
  [ Fr(~k) ] --[ Key(k2) ]-> [ Out(senc(m1(~k), k2)) ]

end
"#,
        )],
        &["p2_sig.spthy"],
        r#"theory Sig

begin

// Function signature and definition of the equational theory E

builtins: diffie-hellman
functions: f/2, fst/1, g/1 [private,constructor], h/1, mac/2, pair/2,
           sdec/2, senc/2, snd/1, unwrap/1 [destructor]
equations:
    fst(<x.1, x.2>) = x.1,
    sdec(senc(x.1, x.2), x.2) = x.1,
    snd(<x.1, x.2>) = x.2,
    unwrap(f(x, y)) = x

builtin  symmetric-encryption

builtin  hashing

builtin  diffie-hellman

function: f (Any, Any) : Any   

function: g (Any) : Any  [private]  

function: unwrap (Any) : Any   [destructor] 

function: mac (Any, Any) : Any   

macros: m1( x ) =  h(x)

rule (modulo E) A:
   [ Fr( ~k ) ] --[ Key( h(~k) ) ]-> [ Out( senc(m1(~k), h(~k)) ) ]

end
"#,
        r#"[Theory Sig] Theory loaded
"#,
    );
}

/// `_restrict` lifting (Restr_A_1 inserted BEFORE the rule), rule attributes
/// attached without a space, restriction `// safety formula`, lemma guarded
/// blocks + `by sorry`.
#[test]
fn rules_restrict_lemmas() {
    assert_transcript(
        "rules_restrict_lemmas",
        &[(
            "p3_rules.spthy",
            r#"theory RulesAttrs
begin

rule A [color=#123456]:
  [ Fr(~k) ] --[ _restrict(Ex #i. B() @ i), S(~k) ]-> [ Out(~k) ]

rule B [issapicrule]:
  [ ] --[ B() ]-> [ ]

restriction unique:
  "All x #i #j. S(x) @ i & S(x) @ j ==> #i = #j"

lemma foo [sources, reuse]:
  all-traces
  "All k #i. S(k) @ i ==> Ex #j. B() @ j"

lemma bar:
  exists-trace
  "Ex k #i. S(k) @ i"

end
"#,
        )],
        &["p3_rules.spthy"],
        r#"theory RulesAttrs

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

restriction Restr_A_1:
  "∀ #NOW. (Restr_A_1( ) @ #NOW) ⇒ (∃ #i. B( ) @ #i)"

rule (modulo E) A[color=#123456]:
   [ Fr( ~k ) ] --[ S( ~k ), Restr_A_1( ) ]-> [ Out( ~k ) ]

rule (modulo E) B[issapicrule]:
   [ ] --[ B( ) ]-> [ ]

restriction unique:
  "∀ x #i #j. ((S( x ) @ #i) ∧ (S( x ) @ #j)) ⇒ (#i = #j)"
  // safety formula

lemma foo [sources, reuse]:
  all-traces "∀ k #i. (S( k ) @ #i) ⇒ (∃ #j. B( ) @ #j)"
/*
guarded formula characterizing all counter-examples:
"∃ k #i. (S( k ) @ #i) ∧ ∀ #j. (B( ) @ #j) ⇒ ⊥"
*/
by sorry

lemma bar:
  exists-trace "∃ k #i. S( k ) @ #i"
/*
guarded formula characterizing all satisfying traces:
"∃ k #i. (S( k ) @ #i)"
*/
by sorry

end
"#,
        r#"[Theory RulesAttrs] Theory loaded
"#,
    );
}

/// SAPIC theory: `--parse-only` does NOT translate — `let` defs and the
/// `process:` block are pretty-printed (prettySapic'), calls shown un-inlined.
#[test]
fn sapic_process_untranslated() {
    assert_transcript(
        "sapic_process_untranslated",
        &[(
            "p4_sapic.spthy",
            r#"theory SapicProc
begin

builtins: symmetric-encryption

let P(x) = out(x); 0

process:
new k; !(P(k) | in(y); event Recv(y))

lemma triv:
  exists-trace
  "Ex y #i. Recv(y) @ i"

end
"#,
        )],
        &["p4_sapic.spthy"],
        r#"theory SapicProc

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, sdec/2, senc/2, snd/1
equations:
    fst(<x.1, x.2>) = x.1,
    sdec(senc(x.1, x.2), x.2) = x.1,
    snd(<x.1, x.2>) = x.2

builtin  symmetric-encryption

let  P (x) = out(x)

process:
  new k;
  !(P(k) | in(y);
           event Recv( y ))

lemma triv:
  exists-trace "∃ y #i. Recv( y ) @ #i"
/*
guarded formula characterizing all satisfying traces:
"∃ y #i. (Recv( y ) @ #i)"
*/
by sorry

end
"#,
        r#"[Theory SapicProc] Theory loaded
"#,
    );
}

/// `configuration:` before `begin`, `heuristic:` hoisted to the header,
/// `predicate:` items, `section{* *}` formal comments, explicit `by sorry`.
#[test]
fn config_heuristic_predicate_comment() {
    assert_transcript(
        "config_heuristic_predicate_comment",
        &[(
            "p5_misc.spthy",
            r#"theory Misc
configuration: "--auto-sources"
begin

heuristic: p

predicates: Both(x,y) <=> Ex #i #j. A() @ i & A() @ j

section{* a formal comment *}

restriction rst:
  "All #i #j. A() @ i & A() @ j ==> #i = #j"

rule A:
  [ ] --[ A() ]-> [ ]

lemma withproof:
  exists-trace
  "Ex #i. A() @ i"
by sorry

end
"#,
        )],
        &["p5_misc.spthy"],
        r#"theory Misc

configuration: "--auto-sources"

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

heuristic: p

predicate: Both( x, y )<=>∃ #i #j. (A( ) @ #i) ∧ (A( ) @ #j)

section{* a formal comment *}

restriction rst:
  "∀ #i #j. ((A( ) @ #i) ∧ (A( ) @ #j)) ⇒ (#i = #j)"
  // safety formula

rule (modulo E) A:
   [ ] --[ A( ) ]-> [ ]

lemma withproof:
  exists-trace "∃ #i. A( ) @ #i"
/*
guarded formula characterizing all satisfying traces:
"∃ #i. (A( ) @ #i)"
*/
by sorry

end
"#,
        r#"[Theory Misc] Theory loaded
"#,
    );
}

/// Accountability: `test <name>:` case tests and `lemma acc:` with
/// `<idents> accounts for` — rendered raw (no translation).
#[test]
fn accountability_lemma_and_test() {
    assert_transcript(
        "accountability_lemma_and_test",
        &[(
            "p13_acc.spthy",
            r#"theory AccTest
begin

builtins: symmetric-encryption

test evid:
  "Ex #i. Evid() @ i"

lemma acc:
  evid accounts for
  "All #i. Bad() @ i ==> F"

process:
event Evid(); event Bad()

end
"#,
        )],
        &["p13_acc.spthy"],
        r#"theory AccTest

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, sdec/2, senc/2, snd/1
equations:
    fst(<x.1, x.2>) = x.1,
    sdec(senc(x.1, x.2), x.2) = x.1,
    snd(<x.1, x.2>) = x.2

builtin  symmetric-encryption

test evid:
  "∃ #i. Evid( ) @ #i"

lemma acc:
  evid accounts for
  "∀ #i. (Bad( ) @ #i) ⇒ (⊥)"

process:
  event Evid( );
  event Bad( )

end
"#,
        r#"[Theory AccTest] Theory loaded
"#,
    );
}

/// Embedded proof skeletons echo with cases in SORTED (Data.Map) order —
/// `case A` before `case Zed` despite source order — `solve(...)` goals
/// re-rendered, `by sorry /* comment */` reasons dropped, `SOLVED` gains
/// `// trace found`.
#[test]
fn proof_skeleton_cases_sorted() {
    assert_transcript(
        "proof_skeleton_cases_sorted",
        &[(
            "p14_cases.spthy",
            r#"theory CaseOrder
begin

rule A:
  [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]

rule Zed:
  [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]

lemma chain:
  exists-trace
  "Ex k #i. S(k) @ i"
simplify
solve( S( k ) @ #i )
  case Zed
  by sorry /* dropped-comment */
next
  case A
  SOLVED
qed

end
"#,
        )],
        &["p14_cases.spthy"],
        r#"theory CaseOrder

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

rule (modulo E) A:
   [ Fr( ~k ) ] --[ S( ~k ) ]-> [ Out( ~k ) ]

rule (modulo E) Zed:
   [ Fr( ~k ) ] --[ S( ~k ) ]-> [ Out( ~k ) ]

lemma chain:
  exists-trace "∃ k #i. S( k ) @ #i"
/*
guarded formula characterizing all satisfying traces:
"∃ k #i. (S( k ) @ #i)"
*/
simplify
solve( S( k ) @ #i )
  case A
  SOLVED // trace found
next
  case Zed
  by sorry
qed

end
"#,
        r#"[Theory CaseOrder] Theory loaded
"#,
    );
}

/// `tactic:` header block, `export:` item, user `[AC]` function typing line,
/// xor builtin, `hide_lemma=`/`heuristic={...}` lemma attributes.
#[test]
fn tactic_export_ac_function() {
    assert_transcript(
        "tactic_export_ac_function",
        &[(
            "p15_mixed.spthy",
            r#"theory Mixed
begin

builtins: xor
functions: uni/2 [AC], pw/1 [private]

export queries:
  "some export body"

tactic: mytac
presort: C
prio:
  regex ".*S\(.*"

lemma hid [hide_lemma=chain, heuristic={mytac}]:
  exists-trace
  "Ex k #i. S(k) @ i"

rule A:
  [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k XOR uni(~k, ~k)) ]

end
"#,
        )],
        &["p15_mixed.spthy"],
        r#"theory Mixed

begin

// Function signature and definition of the equational theory E

builtins: xor
functions: fst/1, pair/2, pw/1 [private,constructor], snd/1, uni/2 [AC]
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

tactic: mytac
presort: C
prio: {id}
  regex".*S\(.*"

builtin  xor

function: uni (Any, Any) : Any  [AC]   

function: pw (Any) : Any  [private]  

export:  queries "some export body"

lemma hid [hide_lemma=chain, heuristic={mytac}]:
  exists-trace "∃ k #i. S( k ) @ #i"
/*
guarded formula characterizing all satisfying traces:
"∃ k #i. (S( k ) @ #i)"
*/
by sorry

rule (modulo E) A:
   [ Fr( ~k ) ] --[ S( ~k ) ]-> [ Out( (~k⊕(~k uni ~k)) ) ]

end
"#,
        r#"[Theory Mixed] Theory loaded
"#,
    );
}

/// prettySapic's operand order for combinators (`then-branch if-cond
/// else-branch`), insert/lock/unlock/lookup actions.
#[test]
fn sapic_if_else_state_actions() {
    assert_transcript(
        "sapic_if_else_state_actions",
        &[(
            "p17_ifelse.spthy",
            r#"theory IfElse
begin

builtins: symmetric-encryption

process:
in(x); if x = 'a' then (event Yes(); out('y')) else event No(); insert 'st', x; lock 'st'; unlock 'st'; lookup 'st' as z in event Got(z) else 0

end
"#,
        )],
        &["p17_ifelse.spthy"],
        r#"theory IfElse

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, sdec/2, senc/2, snd/1
equations:
    fst(<x.1, x.2>) = x.1,
    sdec(senc(x.1, x.2), x.2) = x.1,
    snd(<x.1, x.2>) = x.2

builtin  symmetric-encryption

process:
  in(x);
   (event Yes( );
    out('y') if x='a' event No( );
                      insert 'st',x;
                      lock 'st';
                      unlock 'st';
                       (event Got( z ) lookup 'st' as z 0))

end
"#,
        r#"[Theory IfElse] Theory loaded
"#,
    );
}

/// Open restriction: macro form on top, NO `/* expanded formula: */` block
/// (parse-time `_rstrOriginalFormula` is Nothing; oracle-verified against the
/// closed print which HAS the block).
#[test]
fn macro_restriction_unexpanded() {
    assert_transcript(
        "macro_restriction_unexpanded",
        &[(
            "p18_macro_rst.spthy",
            r#"theory MacroRst
begin

functions: h/1
macros: m1(x) = h(x)

rule A:
  [ ] --[ A(m1('a')) ]-> [ ]

restriction rst:
  "All z #i. A(z) @ i ==> A(m1('a')) @ i"

end
"#,
        )],
        &["p18_macro_rst.spthy"],
        r#"theory MacroRst

begin

// Function signature and definition of the equational theory E

functions: fst/1, h/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

function: h (Any) : Any   

macros: m1( x ) =  h(x)

rule (modulo E) A:
   [ ] --[ A( m1('a') ) ]-> [ ]

restriction rst:
  "∀ z #i. (A( z ) @ #i) ⇒ (A( m1('a') ) @ #i)"
  // safety formula

end
"#,
        r#"[Theory MacroRst] Theory loaded
"#,
    );
}

/// Open lemma: the guarded-formula block keeps the MACRO form (`m1('a')`) —
/// macros are applied at translation, after `--parse-only` stops (the closed
/// print shows `h('a')`).
#[test]
fn macro_lemma_guarded_unexpanded() {
    assert_transcript(
        "macro_lemma_guarded_unexpanded",
        &[(
            "p19_macro_lem.spthy",
            r#"theory MacroLem
begin

functions: h/1
macros: m1(x) = h(x)

rule A:
  [ ] --[ A(m1('a')) ]-> [ ]

lemma lem:
  exists-trace
  "Ex z #i. A(z) @ i & A(m1('a')) @ i"

end
"#,
        )],
        &["p19_macro_lem.spthy"],
        r#"theory MacroLem

begin

// Function signature and definition of the equational theory E

functions: fst/1, h/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

function: h (Any) : Any   

macros: m1( x ) =  h(x)

rule (modulo E) A:
   [ ] --[ A( m1('a') ) ]-> [ ]

lemma lem:
  exists-trace "∃ z #i. (A( z ) @ #i) ∧ (A( m1('a') ) @ #i)"
/*
guarded formula characterizing all satisfying traces:
"∃ z #i. (A( z ) @ #i) ∧ (A( m1('a') ) @ #i)"
*/
by sorry

end
"#,
        r#"[Theory MacroLem] Theory loaded
"#,
    );
}

/// Multi-line `export` body: the whitespace right after the opening quote is
/// lexeme-skipped (HS `symbol "\""`), continuation lines stay at column 0.
#[test]
fn export_multiline_body() {
    assert_transcript(
        "export_multiline_body",
        &[(
            "p20_export.spthy",
            r#"theory ExportML
begin

builtins: symmetric-encryption

export queries:
  "
free c: channel.
query attacker(s).
"

process:
out('x')

end
"#,
        )],
        &["p20_export.spthy"],
        r#"theory ExportML

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, sdec/2, senc/2, snd/1
equations:
    fst(<x.1, x.2>) = x.1,
    sdec(senc(x.1, x.2), x.2) = x.1,
    snd(<x.1, x.2>) = x.2

builtin  symmetric-encryption

export:  queries "free c: channel.
query attacker(s).
"

process:
  out('x')

end
"#,
        r#"[Theory ExportML] Theory loaded
"#,
    );
}

/// `#include`d items splice inline and render at their spliced position.
#[test]
fn include_splices_items() {
    assert_transcript(
        "include_splices_items",
        &[
            (
                "p9_include.spthy",
                r#"theory WithInclude
begin

#include "inc_body.spthy"

rule Main:
  [ ] --[ M() ]-> [ ]

end
"#,
            ),
            (
                "inc_body.spthy",
                r#"rule Inc:
  [ ] --[ I() ]-> [ ]
"#,
            ),
        ],
        &["p9_include.spthy"],
        r#"theory WithInclude

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

rule (modulo E) Inc:
   [ ] --[ I( ) ]-> [ ]

rule (modulo E) Main:
   [ ] --[ M( ) ]-> [ ]

end
"#,
        r#"[Theory WithInclude] Theory loaded
"#,
    );
}

/// Two input files: one doc per file, each `putStrLn`-terminated, docs abut
/// with no extra blank line; the stderr markers all precede the stdout docs
/// (HS processes every file before printing — Batch.hs:91-95).
#[test]
fn multi_file_docs_concatenate() {
    assert_transcript(
        "multi_file",
        &[
            (
                "p1_minimal.spthy",
                r#"theory Minimal
begin

rule A:
  [ Fr(~k) ] --> [ Out(~k) ]

end
"#,
            ),
            (
                "p9_include.spthy",
                r#"theory WithInclude
begin

#include "inc_body.spthy"

rule Main:
  [ ] --[ M() ]-> [ ]

end
"#,
            ),
            (
                "inc_body.spthy",
                r#"rule Inc:
  [ ] --[ I() ]-> [ ]
"#,
            ),
        ],
        &["p1_minimal.spthy", "p9_include.spthy"],
        r#"theory Minimal

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

rule (modulo E) A:
   [ Fr( ~k ) ] --> [ Out( ~k ) ]

end
theory WithInclude

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

rule (modulo E) Inc:
   [ ] --[ I( ) ]-> [ ]

rule (modulo E) Main:
   [ ] --[ M( ) ]-> [ ]

end
"#,
        r#"[Theory Minimal] Theory loaded
[Theory WithInclude] Theory loaded
"#,
    );
}

/// Legacy `axiom` items: parsed as restrictions and echoed as `restriction`,
/// with HS's `Debug.Trace` deprecation warning on stderr ahead of the
/// `Theory loaded` markers (Theory/Text/Parser/Restriction.hs:88-92).  The
/// traced value is a shared CAF, so THREE axioms across TWO files still print
/// the line exactly once; a real `restriction` never prints it.
#[test]
fn legacy_axiom_deprecation_warning_once_per_process() {
    assert_transcript(
        "legacy_axiom",
        &[
            (
                "ax1.spthy",
                r#"theory AxOne
begin

axiom Ax1: "All x #i. A(x) @ i ==> F"

restriction R1: "All x #i. B(x) @ i ==> F"

axiom Ax2: "All x #i. C(x) @ i ==> F"

rule R: [ ] --[ A('x') ]-> [ ]

end
"#,
            ),
            (
                "ax2.spthy",
                r#"theory AxTwo
begin

axiom Bx1: "All x #i. D(x) @ i ==> F"

rule S: [ ] --[ D('y') ]-> [ ]

end
"#,
            ),
        ],
        &["ax1.spthy", "ax2.spthy"],
        r#"theory AxOne

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

restriction Ax1:
  "∀ x #i. (A( x ) @ #i) ⇒ (⊥)"
  // safety formula

restriction R1:
  "∀ x #i. (B( x ) @ #i) ⇒ (⊥)"
  // safety formula

restriction Ax2:
  "∀ x #i. (C( x ) @ #i) ⇒ (⊥)"
  // safety formula

rule (modulo E) R:
   [ ] --[ A( 'x' ) ]-> [ ]

end
theory AxTwo

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

restriction Bx1:
  "∀ x #i. (D( x ) @ #i) ⇒ (⊥)"
  // safety formula

rule (modulo E) S:
   [ ] --[ D( 'y' ) ]-> [ ]

end
"#,
        r#"Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.
[Theory AxOne] Theory loaded
[Theory AxTwo] Theory loaded
"#,
    );
}

/// `--Output=DIR` is ignored under `--parse-only` (the HS parseOnly branch
/// never consults `writeOutput`): the doc still goes to stdout and NO file
/// is created in DIR (oracle-verified).
#[test]
fn output_dir_flag_is_ignored() {
    let dir = std::env::temp_dir().join("tamarin_rs_parse_only_outdir");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("out")).expect("mkdir");
    std::fs::write(
        dir.join("p1_minimal.spthy"),
        r#"theory Minimal
begin

rule A:
  [ Fr(~k) ] --> [ Out(~k) ]

end
"#,
    )
    .expect("write");
    let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .current_dir(&dir)
        .args(["--parse-only", "--Output=out", "p1_minimal.spthy"])
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        r#"theory Minimal

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

rule (modulo E) A:
   [ Fr( ~k ) ] --> [ Out( ~k ) ]

end
"#
    );
    let entries: Vec<_> = std::fs::read_dir(dir.join("out")).unwrap().collect();
    assert!(entries.is_empty(), "--parse-only must write no -O files");
}

/// A `_restrict` action atom whose time point is FREE.  HS's `Traversable
/// (ProtoAtom s)` is `Action <$> f i <*> traverse f fa`
/// (Theory/Model/Atom.hs:139-140) and its `Foldable` folds in the same order
/// (Theory/Model/Atom.hs:130-131), so `rewrite` abstracts the time point into
/// the first fresh variable and `freesList` puts it first in the generated
/// fact: the restriction reads `Restr_A_1( x, x.1 )` over `B( x.1 ) @ x`, and
/// the rule's appended action reads `Restr_A_1( #i, f(x, y) )`.  A `_restrict`
/// whose time point is bound mints no fresh variable for it and cannot tell
/// the two orders apart.
#[test]
fn restrict_abstracts_the_timepoint_first() {
    assert_transcript(
        "restrict_abstracts_the_timepoint_first",
        &[(
            "p16_restrict_timepoint.spthy",
            r#"theory RestrictTimepoint
begin

functions: f/2

rule A:
  [ Fr(~k), In(x), In(y) ] --[ _restrict(B(f(x,y)) @ #i), S(~k) ]-> [ Out(~k) ]

end
"#,
        )],
        &["p16_restrict_timepoint.spthy"],
        r#"theory RestrictTimepoint

begin

// Function signature and definition of the equational theory E

functions: f/2, fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

function: f (Any, Any) : Any   

restriction Restr_A_1:
  "∀ x #NOW x.1. (Restr_A_1( x, x.1 ) @ #NOW) ⇒ (B( x.1 ) @ x)"
  // safety formula

rule (modulo E) A:
   [ Fr( ~k ), In( x ), In( y ) ]
  --[ S( ~k ), Restr_A_1( #i, f(x, y) ) ]->
   [ Out( ~k ) ]

end
"#,
        r#"[Theory RestrictTimepoint] Theory loaded
"#,
    );
}

/// A predicate use site whose argument names a variable the predicate body
/// also binds.  HS `expandFormula` (Theory/Syntactic/Predicate.hs:82-105)
/// splices the body under `compSubst`'s De Bruijn shift and renames nothing,
/// so the two stay apart — the body's binder is an index, the use-site `z` is
/// free — and the printer gives the binder the next display index, `z.1`.
/// The multiset `(<)` reaches the same expansion through the built-in
/// `Smaller` predicate (Theory/Text/Parser/Formula.hs:30-38), whose body binds
/// `z` as well.  Both the quoted lemma formula and its guarded block carry
/// that spelling.
#[test]
fn predicates_and_smaller_echo() {
    assert_transcript(
        "predicates_and_smaller_echo",
        &[(
            "p17_pred_capture.spthy",
            r#"theory S6PredCapture
begin

builtins: multiset

predicates: P(x) <=> Ex z #i. Act(x, z) @ #i

lemma cap:
  "All z #j. Start(z) @ #j ==> P(z)"

lemma mset:
  "All y #j. Start(y) @ #j ==> Smaller(z, y)"

end
"#,
        )],
        &["p17_pred_capture.spthy"],
        r#"theory S6PredCapture

begin

// Function signature and definition of the equational theory E

builtins: multiset
functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

builtin  multiset

predicate: P( x )<=>∃ z #i. Act( x, z ) @ #i

lemma cap:
  all-traces "∀ z #j. (Start( z ) @ #j) ⇒ (∃ z.1 #i. Act( z, z.1 ) @ #i)"
/*
guarded formula characterizing all counter-examples:
"∃ z #j. (Start( z ) @ #j) ∧ ∀ z.1 #i. (Act( z, z.1 ) @ #i) ⇒ ⊥"
*/
by sorry

lemma mset:
  all-traces "∀ y #j. (Start( y ) @ #j) ⇒ (∃ z.1. y = (z++z.1))"
/*
guarded formula characterizing all counter-examples:
"∃ y #j. (Start( y ) @ #j) ∧ ∀ z.1. (y = (z++z.1)) ⇒ ⊥"
*/
by sorry

end
"#,
        r#"[Theory S6PredCapture] Theory loaded
"#,
    );
}
