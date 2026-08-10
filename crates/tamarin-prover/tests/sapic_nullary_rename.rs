// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins that a declared 0-arity function symbol beats a same-named SAPIC
//! process binder.
//!
//! HS's term parser tries `nullaryApp` before the literal parser
//! (Theory/Text/Parser/Term.hs:151,158-163), so a declared 0-arity name in a
//! term position is resolved against the signature AT PARSE TIME.  A process
//! binder cannot shadow it: `new c` and `lookup t as c` take `sapicvar`
//! (Theory/Text/Parser/Sapic.hs:87,236) and do bind an `LVar` named `c`, but the `if` condition's
//! `c` — parsed through `standardFormula`'s `msetterm` — is the constant
//! `fApp c []`.
//!
//! `renameUnique` (Typing.hs:235-262) therefore renames the BINDER to `c.1`
//! while its `apply subst` leaves the condition's constant alone: the `Restr_`
//! restriction keeps `c`, takes no argument, and the `process=` attribute
//! reprints the bare `c`.
//!
//! No corpus theory names a process binder after a declared 0-arity symbol.
//!
//! The expected bytes below are the pinned oracle's (Git revision ef3f0468)
//! output for the two theories inlined here, run with `--derivcheck-timeout=0`.

mod common;

use common::maude_available;

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_sapic_nullary_rename";

/// Write `src` to a private temp file, load it with `--derivcheck-timeout=0`
/// and return the echoed theory.
fn load_theory(stem: &str, src: &str) -> String {
    let out_path = std::env::temp_dir()
        .join(TMP_DIR)
        .join(format!("{stem}_out.spthy"));

    // `-o`/`--output` is a cmdargs `flagOpt` whose value must be ATTACHED
    // (Batch.hs:44-84, see line 76).
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let (code, _, stderr) = common::run_raw(
        TMP_DIR,
        stem,
        src,
        &["--quiet", "--derivcheck-timeout=0", &output_arg],
    );
    assert_eq!(
        code, 0,
        "expected exit code 0, got {code}; stderr:\n{stderr}"
    );
    std::fs::read_to_string(&out_path).expect("output written")
}

fn assert_block(body: &str, expected: &[&str], what: &str) {
    let expected = expected.join("\n");
    assert!(
        body.contains(&expected),
        "{what}\nexpected:\n{expected}\ngot:\n{body}"
    );
}

/// The theory `new c` binds: `c/0` is declared, so the `if` condition's `c`
/// is the constant while the binder is a variable.
const THEORY_NEW: &str = r#"theory SapicNullaryNewRename
begin

functions: c/0

predicates: Eq(a, b) <=> a = b

process:
  new c;
  if Eq(c, 'x') then out('yes') else out('no')

end
"#;

/// Oracle bytes for [`THEORY_NEW`]: the `new` rule renames the binder to
/// `c.1`, while both `Restr_ifEqcx_…` restrictions keep the bare constant `c`
/// and take NO argument.
const EXPECTED_NEW: &[&str] = &[
    "rule (modulo E) newc_0_[color=#ffffff, process=\"new c.1;\", issapicrule,",
    "                        role='Process']:",
    "   [ State_( ), Fr( c.1 ) ] --> [ State_1( c.1 ) ]",
    "",
    "  /*",
    "  rule (modulo AC) newc_0_[color=#ffffff, process=\"new c.1;\", issapicrule,",
    "                           role='Process']:",
    "     [ State_( ), Fr( c ) ] --> [ State_1( c ) ]",
    "  */",
    "",
    "restriction Restr_ifEqcx_0_1_1:",
    "  \"∀ #NOW. (Restr_ifEqcx_0_1_1( ) @ #NOW) ⇒ (c = 'x')\"",
    "  // safety formula",
    "",
    "  /*",
    "  expanded formula:",
    "  \"∀ #NOW. (Restr_ifEqcx_0_1_1( ) @ #NOW) ⇒ (c = 'x')\"",
    "  */",
    "",
    "rule (modulo E) ifEqcx_0_1[color=#ffffff, process=\"if Eq( c, 'x' )\",",
    "                           issapicrule, role='Process']:",
    "   [ State_1( c.1 ) ] --[ Restr_ifEqcx_0_1_1( ) ]-> [ State_11( c.1 ) ]",
    "",
    "  /*",
    "  rule (modulo AC) ifEqcx_0_1[color=#ffffff, process=\"if Eq( c, 'x' )\",",
    "                              issapicrule, role='Process']:",
    "     [ State_1( c ) ] --[ Restr_ifEqcx_0_1_1( ) ]-> [ State_11( c ) ]",
    "  */",
    "",
    "restriction Restr_ifEqcx_1_1_1:",
    "  \"∀ #NOW. (Restr_ifEqcx_1_1_1( ) @ #NOW) ⇒ (¬(c = 'x'))\"",
    "  // safety formula",
    "",
    "  /*",
    "  expanded formula:",
    "  \"∀ #NOW. (Restr_ifEqcx_1_1_1( ) @ #NOW) ⇒ (¬(c = 'x'))\"",
    "  */",
    "",
    "rule (modulo E) ifEqcx_1_1[color=#ffffff, process=\"if Eq( c, 'x' )\",",
    "                           issapicrule, role='Process']:",
    "   [ State_1( c.1 ) ] --[ Restr_ifEqcx_1_1_1( ) ]-> [ State_12( c.1 ) ]",
    "",
    "  /*",
    "  rule (modulo AC) ifEqcx_1_1[color=#ffffff, process=\"if Eq( c, 'x' )\",",
    "                              issapicrule, role='Process']:",
    "     [ State_1( c ) ] --[ Restr_ifEqcx_1_1_1( ) ]-> [ State_12( c ) ]",
    "  */",
];

/// The same shape with a `lookup … as c` binder, whose scope is the `if`.
const THEORY_LOOKUP: &str = r#"theory SapicNullaryLookupRename
begin

functions: c/0

predicates: Eq(a, b) <=> a = b

process:
  lookup 'k' as c in
    if Eq(c, 'x') then out('yes') else out('no')
  else
    out('no')

end
"#;

/// Oracle bytes for [`THEORY_LOOKUP`]: `IsIn( 'k', c.1 )` binds the renamed
/// variable, and the restriction still reads `c` with an empty argument list.
const EXPECTED_LOOKUP: &[&str] = &[
    "rule (modulo E) lookupkasc_0_[color=#ffffff, process=\"lookup 'k' as c.1\",",
    "                              no_derivcheck, issapicrule, role='Process']:",
    "   [ State_( ) ] --[ IsIn( 'k', c.1 ) ]-> [ State_1( c.1 ) ]",
    "",
    "  /*",
    "  rule (modulo AC) lookupkasc_0_[color=#ffffff,",
    "                                 process=\"lookup 'k' as c.1\", no_derivcheck, issapicrule, role='Process']:",
    "     [ State_( ) ] --[ IsIn( 'k', c ) ]-> [ State_1( c ) ]",
    "  */",
    "",
    "rule (modulo E) lookupkasc_1_[color=#ffffff, process=\"lookup 'k' as c.1\",",
    "                              no_derivcheck, issapicrule, role='Process']:",
    "   [ State_( ) ] --[ IsNotSet( 'k' ) ]-> [ State_2( ) ]",
    "",
    "  /* has exactly the trivial AC variant */",
    "",
    "restriction Restr_ifEqcx_0_1_1:",
    "  \"∀ #NOW. (Restr_ifEqcx_0_1_1( ) @ #NOW) ⇒ (c = 'x')\"",
    "  // safety formula",
    "",
    "  /*",
    "  expanded formula:",
    "  \"∀ #NOW. (Restr_ifEqcx_0_1_1( ) @ #NOW) ⇒ (c = 'x')\"",
    "  */",
    "",
    "rule (modulo E) ifEqcx_0_1[color=#ffffff, process=\"if Eq( c, 'x' )\",",
    "                           issapicrule, role='Process']:",
    "   [ State_1( c.1 ) ] --[ Restr_ifEqcx_0_1_1( ) ]-> [ State_11( c.1 ) ]",
];

#[test]
fn nullary_constant_survives_new_binder_rename() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let body = load_theory("sapic_nullary_new", THEORY_NEW);
    assert_block(
        &body,
        EXPECTED_NEW,
        "a `new c` binder must not rename the condition's `c/0` constant",
    );
}

#[test]
fn nullary_constant_survives_lookup_binder_rename() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let body = load_theory("sapic_nullary_lookup", THEORY_LOOKUP);
    assert_block(
        &body,
        EXPECTED_LOOKUP,
        "a `lookup … as c` binder must not rename the condition's `c/0` constant",
    );
}
