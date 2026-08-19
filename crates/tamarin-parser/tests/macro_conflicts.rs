// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parity for `macro`'s three rejections.
//!
//! HS `macro` (Theory/Text/Parser/Macro.hs:32-47) rejects a macro in three
//! ways: a GHC `error` on a `reservedBuiltins` name (line 34-35), a GHC
//! `error` on two equal arguments (line 37-38), and a parsec `fail` on a name
//! the signature already carries — `userDefinedFunSyms` (user +
//! enabled-theory symbols) or `macroNames` (line 43-44).  The port reports
//! them as [`ParseError::UsedReservedBuiltin`],
//! [`ParseError::DuplicateMacroArg`] and
//! [`ParseError::ConflictingDeclarations`] (context
//! [`ParseContext::Macro`]) — the variants carry the offending spans, not
//! HS's message bytes (those end-to-end renderings are pinned in
//! `crates/tamarin-prover/tests/macro_conflicts.rs`).
//!
//! WHICH theories are rejected (and which load) is pinned to the Haskell
//! oracle (Git revision ef3f0468); every accepted theory loads with exit 0
//! there.  Positions are the port's own: the conflict spans the macro
//! declaration, the duplicate-argument rejection spans the two argument
//! sites.

use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError};

/// The `(name, first_at, second_at)` of the macro-context
/// [`ParseError::ConflictingDeclarations`] `src` fails with, positions
/// flattened to `(line, col)`.  `first_at` is `None` when the earlier owner
/// is a builtin with no declaration site.
#[track_caller]
fn conflict(src: &str) -> (String, Option<(u32, u32)>, (u32, u32)) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::ConflictingDeclarations {
        name,
        context: ParseContext::Macro,
        first_at,
        second_at,
    } = e
    else {
        panic!("expected the macro-conflict variant, got {e:?}");
    };
    (
        name,
        first_at.map(|at| (at.line, at.col)),
        (second_at.line, second_at.col),
    )
}

/// The `(arg, first_at, second_at)` of the [`ParseError::DuplicateMacroArg`]
/// `src` fails with — `arg` is the second occurrence's rendered variable,
/// the positions the two argument sites, flattened to `(line, col)`.
#[track_caller]
fn dup_arg(src: &str) -> (String, (u32, u32), (u32, u32)) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::DuplicateMacroArg {
        arg,
        first_at,
        second_at,
    } = e
    else {
        panic!("{src:?}: expected the duplicate-argument rejection, got {e:?}");
    };
    (
        arg,
        (first_at.line, first_at.col),
        (second_at.line, second_at.col),
    )
}

/// A theory whose single item is `macros: <decl>`.
fn macro_theory(decl: &str) -> String {
    format!("theory MacroT begin\nmacros: {decl}\nend\n")
}

/// The `f` of the macro-context [`ParseError::UsedReservedBuiltin`] `src`
/// fails with.
#[track_caller]
fn reserved(src: &str) -> String {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::UsedReservedBuiltin {
        f,
        context: ParseContext::Macro,
        ..
    } = e
    else {
        panic!("{src:?}: expected the reserved-builtin rejection, got {e:?}");
    };
    f
}

/// Each of the nine `reservedBuiltins` (Parser/Term.hs:74-85) is rejected —
/// HS's GHC `error` of Parser/Macro.hs:34-35, the port's
/// [`ParseError::UsedReservedBuiltin`] naming the macro.
#[test]
fn reserved_builtin_macro_name_is_rejected() {
    for name in [
        "mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor",
    ] {
        assert_eq!(
            reserved(&macro_theory(&format!("{name}(x) = x"))),
            name,
            "case {name}"
        );
    }
}

/// The reserved-name rejection fires right after the identifier, so it beats
/// everything the rest of the macro could raise: a malformed argument list, a
/// missing body, the duplicate-argument rejection of
/// Theory/Text/Parser/Macro.hs:37-38, and the name conflict the owning
/// builtin's own symbol would otherwise produce (Parser/Macro.hs:43-44).  It
/// does not depend on any builtin being enabled.
#[test]
fn reserved_name_rejection_precedes_every_later_macro_failure() {
    for src in [
        macro_theory("exp("),
        macro_theory("exp(x, x) = x"),
        macro_theory("exp(x)"),
        macro_theory("m(x) = x, exp(y) = y"),
        "theory MacroT begin\nbuiltins: diffie-hellman\nmacros: exp(x) = x\nend\n".to_string(),
        "theory MacroT begin\nbuiltins: bilinear-pairing\nmacros: exp(x) = x\nend\n".to_string(),
    ] {
        assert_eq!(reserved(&src), "exp", "case {src:?}");
    }
}

/// Two arguments that are the same full `LVar` are rejected — HS's `error`
/// of Parser/Macro.hs:37-38, the port's [`ParseError::DuplicateMacroArg`]
/// labelling both argument sites.  The check sits between the argument list
/// and the `=`, so it fires without a body, and a prefixless binder is
/// `LSortMsg` (Token.hs:424-433) — `m(x, x:msg)` is a duplicate.
#[test]
fn duplicate_macro_arguments_are_rejected() {
    for (decl, arg, first, second) in [
        ("m(x, x) = x", "x", (2, 11), (2, 14)),
        ("m(x, x:msg) = x", "x:msg", (2, 11), (2, 14)),
        ("m(x:msg, x) = x", "x", (2, 11), (2, 18)),
        ("m(x:pub, x:pub) = x", "x:pub", (2, 11), (2, 18)),
        ("m(x.1, y, x.1) = x", "x.1", (2, 11), (2, 19)),
        // `commaSep`'s trailing comma is consumed before the check.
        ("m(x, x,) = x", "x", (2, 11), (2, 14)),
        // No `=` and no body: the arguments are all HS has parsed.
        ("m(x, x)", "x", (2, 11), (2, 14)),
    ] {
        assert_eq!(
            dup_arg(&macro_theory(decl)),
            (arg.to_string(), first, second),
            "case {decl}"
        );
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

/// A macro with no body raises no rejection of its own: `term` claims the
/// next identifier as the body variable, and that identifier is the theory's
/// `end`.  The item alternation then runs out of input, so the failure is the
/// missing-`end` one at EOF rather than anything `macro` reports.
#[test]
fn a_bodyless_macro_swallows_end_and_dies_at_the_item_position() {
    let e = parse_theory("theory MacroCF begin\nmacros: m(x) = \nend\n", &[])
        .expect_err("must fail to parse");
    let ParseError::UnexpectedKeyword {
        found,
        expected,
        at,
    } = &e
    else {
        panic!("expected the missing-keyword variant, got {e:?}");
    };
    assert_eq!(*found, None);
    assert_eq!(expected, &["end".to_string()]);
    assert_eq!((at.line, at.col), (4, 1));
}

/// A macro named after a user-declared function conflicts
/// (`userDefinedFunSyms` via `stFunSyms`, Term/Maude/Signature.hs:163-164).
#[test]
fn macro_conflicts_with_user_function() {
    assert_eq!(
        conflict("theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n"),
        ("f".to_string(), Some((2, 12)), (3, 9))
    );
}

/// A macro named after an EARLIER macro conflicts: each parsed macro is
/// registered under `macroNames` before the next one parses (Parser/Macro.hs:46).
#[test]
fn macro_conflicts_with_earlier_macro() {
    assert_eq!(
        conflict("theory MacroCM begin\nmacros: m(x) = x, m(y) = y\nend\n"),
        ("m".to_string(), Some((2, 9)), (2, 19))
    );
}

/// A macro named after an enabled builtin's symbol conflicts: `builtins:
/// hashing` merges `h/1` into `stFunSyms` (Term/Builtin/Signature.hs:75-77),
/// which `userDefinedFunSyms` includes.
#[test]
fn macro_conflicts_with_enabled_builtin_symbol() {
    assert_eq!(
        conflict("theory MacroCH begin\nbuiltins: hashing\nmacros: h(x) = x\nend\n"),
        ("h".to_string(), None, (3, 9))
    );
}

/// The seeded pairing symbols (`fst`/`pair`/`snd`, `pairMaudeSig` —
/// Token.hs:260-261, Term/Term/FunctionSymbols.hs:299-300) conflict without
/// any declaration.
#[test]
fn macro_conflicts_with_seeded_pair_symbol() {
    assert_eq!(
        conflict("theory MacroCP begin\nmacros: fst(x) = x\nend\n"),
        ("fst".to_string(), None, (2, 9))
    );
}

/// `builtins: diffie-hellman` folds `dhFunSig`'s `NoEq` symbols (among them
/// `DH_neutral`) into `funSyms` (Term/Maude/Signature.hs:110-116), so the
/// name conflicts.
#[test]
fn macro_conflicts_with_dh_theory_symbol() {
    assert_eq!(
        conflict(
            "theory MacroCD begin\nbuiltins: diffie-hellman\nmacros: DH_neutral(x) = x\nend\n"
        ),
        ("DH_neutral".to_string(), None, (3, 9))
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
        conflict(
            "theory MacroCBP begin\nbuiltins: bilinear-pairing\nmacros: DH_neutral(x) = x\nend\n"
        ),
        ("DH_neutral".to_string(), None, (3, 9))
    );
}

/// `natural-numbers` contributes `natOneSym` — whose name is `tone`
/// (Term/Term/FunctionSymbols.hs:236).
#[test]
fn macro_conflicts_with_nat_theory_symbol() {
    assert_eq!(
        conflict("theory MacroCN begin\nbuiltins: natural-numbers\nmacros: tone(x) = x\nend\n"),
        ("tone".to_string(), None, (3, 9))
    );
    parse_theory("theory MacroCNC begin\nmacros: tone(x) = x\nend\n", &[])
        .expect("tone macro parses without natural-numbers");
}

/// A user `[AC]` symbol conflicts (`acUserFunSyms` via `ACfctUser`,
/// Term/Maude/Signature.hs:158-164).
#[test]
fn macro_conflicts_with_user_ac_symbol() {
    assert_eq!(
        conflict("theory MacroCA begin\nfunctions: f/2 [AC]\nmacros: f(x) = x\nend\n"),
        ("f".to_string(), Some((2, 12)), (3, 9))
    );
}

/// A second `[AC]` symbol does not change which name conflicts.
#[test]
fn a_second_ac_symbol_does_not_shadow_the_conflict() {
    assert_eq!(
        conflict("theory MacroCA2 begin\nfunctions: f/2 [AC], g/2 [AC]\nmacros: f(x) = x\nend\n"),
        ("f".to_string(), Some((2, 12)), (3, 9))
    );
}

/// The conflict is reported the same way with the theory levels the builtins
/// open — `multiset`, `xor`, and all of them at once.
#[test]
fn enabled_theory_levels_do_not_change_the_conflict() {
    for src in [
        "theory MacroCMS begin\nbuiltins: multiset\nfunctions: f/1\nmacros: f(x) = x\nend\n",
        "theory MacroCX begin\nbuiltins: xor\nfunctions: f/1\nmacros: f(x) = x\nend\n",
        "theory MacroCALL begin\n\
         builtins: diffie-hellman, xor, multiset, natural-numbers\n\
         functions: f/1\nmacros: f(x) = x\nend\n",
    ] {
        assert_eq!(
            conflict(src),
            ("f".to_string(), Some((3, 12)), (4, 9)),
            "case {src:?}"
        );
    }
}

/// The conflict and its span do not depend on the macro body's last lexeme:
/// an application's `)` (Theory/Text/Parser/Term.hs:94), a nullary symbol matched
/// by `nullaryApp`'s `symbol` (Theory/Text/Parser/Term.hs:158-163), a sort-suffixed variable
/// (Token.hs:413-418), a public-name literal, an explicit `.1` index, and a
/// grouping `(x)` all report the same macro-declaration span.
#[test]
fn body_shape_does_not_change_the_conflict() {
    assert_eq!(
        conflict("theory T begin\nbuiltins: hashing\nfunctions: f/1\nmacros: f(x) = h(x)\nend\n"),
        ("f".to_string(), Some((3, 12)), (4, 9))
    );
    assert_eq!(
        conflict("theory T begin\nfunctions: c/0, f/1\nmacros: f(x) = c\nend\n"),
        ("f".to_string(), Some((2, 17)), (3, 9))
    );
    for decl in ["f(x) = x:pub", "f(x) = 'a'", "f(x) = x.1", "f(x) = (x)"] {
        assert_eq!(
            conflict(&format!(
                "theory T begin\nfunctions: f/1\nmacros: {decl}\nend\n"
            )),
            ("f".to_string(), Some((2, 12)), (3, 9)),
            "case {decl}"
        );
    }
}

/// The same for bodies whose last lexeme IS a variable's identifier: a
/// `$`-prefixed variable, `binaryAlgApp`'s trailing `arg2` (Theory/Text/Parser/Term.hs:109-121),
/// and a variable separated from the next token by a comment.
#[test]
fn a_variable_final_body_reports_the_same_conflict() {
    for (thy, first) in [
        (
            "theory T begin\nfunctions: f/1\nmacros: f(x) = $y\nend\n",
            (2, 12),
        ),
        (
            "theory T begin\nfunctions: g/2, f/1\nmacros: f(x) = g{x}x\nend\n",
            (2, 17),
        ),
        (
            "theory T begin\nfunctions: f/1\nmacros: f(x) = x /* trailing */\nend\n",
            (2, 12),
        ),
    ] {
        assert_eq!(
            conflict(thy),
            ("f".to_string(), Some(first), (3, 9)),
            "case {thy:?}"
        );
    }
}
