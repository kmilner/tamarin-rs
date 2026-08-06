// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, jdreier, charlie-j, ValentinYuri, racoucho1u,
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Macro.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Parity for `macro`'s three rejections.
//!
//! HS `macro` (Theory/Text/Parser/Macro.hs:32-47) rejects a macro in three
//! ways: a GHC `error` on a `reservedBuiltins` name (line 34-35), a GHC
//! `error` on two equal arguments (line 37-38), and a parsec `fail` on a name
//! the signature already carries — `userDefinedFunSyms` (user +
//! enabled-theory symbols) or `macroNames` (line 43-44).  The port models the
//! two `error`s with the non-backtrackable [`ParseError::Abort`] and the
//! `fail` with [`ParseError::Custom`], both carrying HS's message verbatim.
//!
//! Every message below is the one the pinned Haskell oracle (Git revision
//! ef3f0468) prints for the same theory, minus the `HasCallStack` block GHC
//! appends to an `error` and the `tamarin-prover: ` prefix its top-level
//! handler adds; every accepted theory loads with exit 0 there.
//!
//! The `fail` positions are pinned too — they are the ones the oracle's frame
//! carries.  The oracle ALSO prints the expectation set parsec had
//! accumulated when the `fail` fired (the macro body's trailing `.`-index
//! attempt plus every enabled operator level's label); the port's `Custom`
//! variant carries a message only, so that set is no longer observable and no
//! longer pinned.

use tamarin_parser::{parse_theory, ParseError};

/// The message of the [`ParseError::Custom`] `src` fails with — HS's
/// `fail`ed string — together with its `(line, column)`.
#[track_caller]
fn custom(src: &str) -> (String, u32, u32) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let at = *e.location();
    let ParseError::Custom { message, .. } = e else {
        panic!("expected a `fail`-style error, got {e:?}");
    };
    (message, at.line, at.col)
}

/// The message of the [`ParseError::Abort`] `src` aborts with — the string
/// HS's GHC `error` carries.
#[track_caller]
fn abort(src: &str) -> String {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    match e {
        ParseError::Abort { message, .. } => message,
        other => panic!("{src:?} failed as a recoverable error, not an abort: {other:?}"),
    }
}

/// A theory whose single item is `macros: <decl>`.
fn macro_theory(decl: &str) -> String {
    format!("theory MacroT begin\nmacros: {decl}\nend\n")
}

/// Each of the nine `reservedBuiltins` (Term.hs:74-86) aborts the parse with
/// the `error` of Macro.hs:34-35 — `show` on the `ByteString` name puts a
/// second pair of quotes inside the backticks.
#[test]
fn reserved_builtin_macro_name_aborts() {
    for name in [
        "mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor",
    ] {
        assert_eq!(
            abort(&macro_theory(&format!("{name}(x) = x"))),
            format!("`\"{name}\"` is a reserved function name for builtins."),
            "case {name}"
        );
    }
}

/// The reserved-name abort fires right after the identifier, so it beats
/// everything the rest of the macro could raise: a malformed argument list, a
/// missing body, the duplicate-argument abort of Macro.hs:37-38, and the
/// name conflict the owning builtin's own symbol would otherwise produce
/// (Macro.hs:43-44).  It does not depend on any builtin being enabled.
#[test]
fn reserved_name_abort_precedes_every_later_macro_failure() {
    let expected = "`\"exp\"` is a reserved function name for builtins.";
    for src in [
        macro_theory("exp("),
        macro_theory("exp(x, x) = x"),
        macro_theory("exp(x)"),
        macro_theory("m(x) = x, exp(y) = y"),
        "theory MacroT begin\nbuiltins: diffie-hellman\nmacros: exp(x) = x\nend\n".to_string(),
        "theory MacroT begin\nbuiltins: bilinear-pairing\nmacros: exp(x) = x\nend\n".to_string(),
    ] {
        assert_eq!(abort(&src), expected, "case {src:?}");
    }
}

/// Two arguments that are the same full `LVar` abort with the `error` of
/// Macro.hs:37-38.  The check sits between the argument list and the `=`, so
/// it fires without a body, and a prefixless binder is `LSortMsg`
/// (Token.hs:424-433) — `m(x, x:msg)` is a duplicate.
#[test]
fn duplicate_macro_arguments_abort() {
    let expected = "\"m\" have two arguments with the same name.";
    for decl in [
        "m(x, x) = x",
        "m(x, x:msg) = x",
        "m(x:msg, x) = x",
        "m(x:pub, x:pub) = x",
        "m(x.1, y, x.1) = x",
        // `commaSep`'s trailing comma is consumed before the check.
        "m(x, x,) = x",
        // No `=` and no body: the arguments are all HS has parsed.
        "m(x, x)",
    ] {
        assert_eq!(abort(&macro_theory(decl)), expected, "case {decl}");
    }
}

/// `nub` compares name, sort AND index (`Eq LVar`, LTerm.hs:541-542), so
/// arguments that differ in any one of the three are distinct and the macro
/// parses (the oracle loads each of these with exit 0).
#[test]
fn macro_arguments_differing_in_sort_or_index_are_distinct() {
    for decl in [
        "m(x, y) = x",
        "m(x, x:pub) = x",
        "m(x.1, x) = x",
        "m(x.1, x.2) = x",
        "m(x:fresh, x:msg) = x",
        "m($x, ~x, #x) = x",
    ] {
        let src = macro_theory(decl);
        parse_theory(&src, &[]).unwrap_or_else(|e| panic!("{decl} rejected: {e}"));
    }
}

/// The parsec `fail`s stay recoverable errors — no abort is raised.
#[test]
fn parsec_failures_are_not_aborts() {
    for src in [
        "theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n",
        "theory MacroCF begin\nmacros: m(x) = \nend\n",
    ] {
        let e = parse_theory(src, &[]).expect_err("must fail to parse");
        assert!(
            !matches!(&e, ParseError::Abort { .. }),
            "case {src:?} aborted: {e:?}"
        );
    }
}

/// A macro named after a user-declared function conflicts
/// (`userDefinedFunSyms` via `stFunSyms`, Term/Maude/Signature.hs:163-164).
#[test]
fn macro_conflicts_with_user_function() {
    assert_eq!(
        custom("theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n"),
        ("Conflicting name for macro f".to_string(), 4, 1)
    );
}

/// A macro named after an EARLIER macro conflicts: each parsed macro is
/// registered under `macroNames` before the next one parses (Macro.hs:46).
#[test]
fn macro_conflicts_with_earlier_macro() {
    assert_eq!(
        custom("theory MacroCM begin\nmacros: m(x) = x, m(y) = y\nend\n"),
        ("Conflicting name for macro m".to_string(), 3, 1)
    );
}

/// A macro named after an enabled builtin's symbol conflicts: `builtins:
/// hashing` merges `h/1` into `stFunSyms` (Term/Builtin/Signature.hs:75-77),
/// which `userDefinedFunSyms` includes.
#[test]
fn macro_conflicts_with_enabled_builtin_symbol() {
    assert_eq!(
        custom("theory MacroCH begin\nbuiltins: hashing\nmacros: h(x) = x\nend\n"),
        ("Conflicting name for macro h".to_string(), 4, 1)
    );
}

/// The seeded pairing symbols (`fst`/`pair`/`snd`, `pairMaudeSig` —
/// Token.hs:260-261, Term/Term/FunctionSymbols.hs:299-300) conflict without
/// any declaration.
#[test]
fn macro_conflicts_with_seeded_pair_symbol() {
    assert_eq!(
        custom("theory MacroCP begin\nmacros: fst(x) = x\nend\n"),
        ("Conflicting name for macro fst".to_string(), 3, 1)
    );
}

/// `builtins: diffie-hellman` folds `dhFunSig`'s `NoEq` symbols (among them
/// `DH_neutral`) into `funSyms` (Term/Maude/Signature.hs:110-116), so the
/// name conflicts.
#[test]
fn macro_conflicts_with_dh_theory_symbol() {
    assert_eq!(
        custom("theory MacroCD begin\nbuiltins: diffie-hellman\nmacros: DH_neutral(x) = x\nend\n"),
        ("Conflicting name for macro DH_neutral".to_string(), 4, 1)
    );
    // Without the builtin the name is free (oracle loads the theory, exit 0).
    parse_theory(
        "theory MacroCDC begin\nmacros: DH_neutral(x) = x\nend\n",
        &[],
    )
    .expect("DH_neutral macro parses without diffie-hellman");
}

/// `bilinear-pairing` forces `enableDH` (`maudeSig`,
/// Term/Maude/Signature.hs:111-112), so it conflicts on `DH_neutral` too.
#[test]
fn macro_conflicts_under_bilinear_pairing() {
    assert_eq!(
        custom(
            "theory MacroCBP begin\nbuiltins: bilinear-pairing\nmacros: DH_neutral(x) = x\nend\n"
        ),
        ("Conflicting name for macro DH_neutral".to_string(), 4, 1)
    );
}

/// `natural-numbers` contributes `natOneSym` — whose name is `tone`
/// (Term/Term/FunctionSymbols.hs:236).
#[test]
fn macro_conflicts_with_nat_theory_symbol() {
    assert_eq!(
        custom("theory MacroCN begin\nbuiltins: natural-numbers\nmacros: tone(x) = x\nend\n"),
        ("Conflicting name for macro tone".to_string(), 4, 1)
    );
    parse_theory("theory MacroCNC begin\nmacros: tone(x) = x\nend\n", &[])
        .expect("tone macro parses without natural-numbers");
}

/// A user `[AC]` symbol conflicts (`acUserFunSyms` via `ACfctUser`,
/// Term/Maude/Signature.hs:158-164).
#[test]
fn macro_conflicts_with_user_ac_symbol() {
    assert_eq!(
        custom("theory MacroCA begin\nfunctions: f/2 [AC]\nmacros: f(x) = x\nend\n"),
        ("Conflicting name for macro f".to_string(), 4, 1)
    );
}

/// A second `[AC]` symbol does not change which name conflicts.
#[test]
fn a_second_ac_symbol_does_not_shadow_the_conflict() {
    assert_eq!(
        custom("theory MacroCA2 begin\nfunctions: f/2 [AC], g/2 [AC]\nmacros: f(x) = x\nend\n"),
        ("Conflicting name for macro f".to_string(), 4, 1)
    );
}

/// The conflict is reported the same way with the theory levels the builtins
/// open — `multiset`, `xor`, and all of them at once.
#[test]
fn enabled_theory_levels_do_not_change_the_conflict() {
    for (src, line) in [
        (
            "theory MacroCMS begin\nbuiltins: multiset\nfunctions: f/1\nmacros: f(x) = x\nend\n",
            5,
        ),
        (
            "theory MacroCX begin\nbuiltins: xor\nfunctions: f/1\nmacros: f(x) = x\nend\n",
            5,
        ),
        (
            "theory MacroCALL begin\n\
             builtins: diffie-hellman, xor, multiset, natural-numbers\n\
             functions: f/1\nmacros: f(x) = x\nend\n",
            5,
        ),
    ] {
        assert_eq!(
            custom(src),
            ("Conflicting name for macro f".to_string(), line, 1),
            "case {src:?}"
        );
    }
}

/// The conflict message and its position do not depend on the macro body's
/// last lexeme: an application's `)` (Term.hs:94), a nullary symbol matched
/// by `nullaryApp`'s `symbol` (Term.hs:158-163), a sort-suffixed variable
/// (Token.hs:413-418), a public-name literal, an explicit `.1` index, and a
/// grouping `(x)` all report at the item position after the macro list.
#[test]
fn body_shape_does_not_change_the_conflict() {
    assert_eq!(
        custom("theory T begin\nbuiltins: hashing\nfunctions: f/1\nmacros: f(x) = h(x)\nend\n"),
        ("Conflicting name for macro f".to_string(), 5, 1)
    );
    assert_eq!(
        custom("theory T begin\nfunctions: c/0, f/1\nmacros: f(x) = c\nend\n"),
        ("Conflicting name for macro f".to_string(), 4, 1)
    );
    for decl in ["f(x) = x:pub", "f(x) = 'a'", "f(x) = x.1", "f(x) = (x)"] {
        assert_eq!(
            custom(&format!(
                "theory T begin\nfunctions: f/1\nmacros: {decl}\nend\n"
            )),
            ("Conflicting name for macro f".to_string(), 4, 1),
            "case {decl}"
        );
    }
}

/// The same for bodies whose last lexeme IS a variable's identifier: a
/// `$`-prefixed variable, `binaryAlgApp`'s trailing `arg2` (Term.hs:109-121),
/// and a variable separated from the next token by a comment.
#[test]
fn a_variable_final_body_reports_the_same_conflict() {
    for thy in [
        "theory T begin\nfunctions: f/1\nmacros: f(x) = $y\nend\n",
        "theory T begin\nfunctions: g/2, f/1\nmacros: f(x) = g{x}x\nend\n",
        "theory T begin\nfunctions: f/1\nmacros: f(x) = x /* trailing */\nend\n",
    ] {
        assert_eq!(
            custom(thy),
            ("Conflicting name for macro f".to_string(), 4, 1),
            "case {thy:?}"
        );
    }
}

/// Non-conflicting macros still parse (oracle loads all of these, exit 0):
/// a fresh name, and the arguments HS's `nub` over full `LVar`s
/// (name+sort+index, Macro.hs:37) keeps apart by sort or index.
#[test]
fn non_conflicting_macros_parse() {
    for src in [
        "theory MacroOK begin\nmacros: m(x) = x\nend\n",
        "theory MacroBS begin\nmacros: m(x, x:pub) = x\nend\n",
        "theory MacroBI begin\nmacros: m(x.1, x) = x\nend\n",
    ] {
        parse_theory(src, &[]).unwrap_or_else(|e| panic!("{src:?} failed: {e}"));
    }
}
