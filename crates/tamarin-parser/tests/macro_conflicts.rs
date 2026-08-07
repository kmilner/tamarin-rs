// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for `macro`'s three rejections.
//!
//! HS `macro` (Theory/Text/Parser/Macro.hs:32-47) rejects a macro in three
//! ways: a GHC `error` on a `reservedBuiltins` name (line 34-35), a GHC
//! `error` on two equal arguments (line 37-38), and a parsec `fail` on a name
//! the signature already carries — `userDefinedFunSyms` (user +
//! enabled-theory symbols) or `macroNames` (line 43-44).  Every expected
//! string here is the stderr the pinned Haskell oracle (Git revision
//! ef3f0468) prints for the same theory, minus the three `maude tool:` banner
//! lines and, for the two `error`s, the `tamarin-prover: ` prefix GHC's
//! top-level handler adds; every accepted theory loads with exit 0 there.

use tamarin_parser::parse_theory;

/// The parse error for `src`, rendered with `file` as parsec's `SourcePos`
/// name — the same string HS's `show err` produces (and the RS CLI prints).
fn err(src: &str, file: &str) -> String {
    parse_theory(src, &[])
        .unwrap_err()
        .with_source(file)
        .to_string()
}

/// The GHC `error` `src` aborts with, as GHC's `displayException` renders it:
/// the message plus the `HasCallStack` block.
fn ghc(src: &str) -> String {
    let e = parse_theory(src, &[]).unwrap_err();
    match &e.ghc_error {
        Some(g) => g.display_exception(),
        None => panic!("{src:?} failed as a parsec error, not a GHC error: {e}"),
    }
}

/// The `HasCallStack` block of a `macro` `error` raised at `Macro.hs:<site>`,
/// with the pinned oracle's `tamarin-prover-theory` package id.
fn call_stack(site: &str) -> String {
    format!(
        "\nCallStack (from HasCallStack):\n  error, called at \
         src/Theory/Text/Parser/Macro.hs:{site} in \
         tamarin-prover-theory-1.13.0-8wixYaxm5uHCGl2uEzaKzP:Theory.Text.Parser.Macro"
    )
}

/// A theory whose single item is `macros: <decl>`.
fn macro_theory(decl: &str) -> String {
    format!("theory MacroT begin\nmacros: {decl}\nend\n")
}

/// Each of the nine `reservedBuiltins` (Term.hs:74-86) aborts the parse with
/// the `error` of Macro.hs:34-35 — `show` on the `ByteString` name puts a
/// second pair of quotes inside the backticks.
#[test]
fn reserved_builtin_macro_name_raises_ghc_error() {
    for name in [
        "mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor",
    ] {
        assert_eq!(
            ghc(&macro_theory(&format!("{name}(x) = x"))),
            format!(
                "`\"{name}\"` is a reserved function name for builtins.{}",
                call_stack("35:15")
            ),
            "case {name}"
        );
    }
}

/// The reserved-name `error` fires right after the identifier, so it beats
/// everything the rest of the macro could raise: a malformed argument list, a
/// missing body, the duplicate-argument `error` of Macro.hs:37-38, and the
/// name conflict the owning builtin's own symbol would otherwise produce
/// (Macro.hs:43-44).  It does not depend on any builtin being enabled.
#[test]
fn reserved_name_error_precedes_every_later_macro_failure() {
    let expected = format!(
        "`\"exp\"` is a reserved function name for builtins.{}",
        call_stack("35:15")
    );
    for src in [
        macro_theory("exp("),
        macro_theory("exp(x, x) = x"),
        macro_theory("exp(x)"),
        macro_theory("m(x) = x, exp(y) = y"),
        "theory MacroT begin\nbuiltins: diffie-hellman\nmacros: exp(x) = x\nend\n".to_string(),
        "theory MacroT begin\nbuiltins: bilinear-pairing\nmacros: exp(x) = x\nend\n".to_string(),
    ] {
        assert_eq!(ghc(&src), expected, "case {src:?}");
    }
}

/// Two arguments that are the same full `LVar` abort with the `error` of
/// Macro.hs:37-38.  The check sits between the argument list and the `=`, so
/// it fires without a body, and a prefixless binder is `LSortMsg`
/// (Token.hs:424-433) — `m(x, x:msg)` is a duplicate.
#[test]
fn duplicate_macro_arguments_raise_ghc_error() {
    let expected = format!(
        "\"m\" have two arguments with the same name.{}",
        call_stack("38:15")
    );
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
        assert_eq!(ghc(&macro_theory(decl)), expected, "case {decl}");
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

/// A GHC `error` carries no parsec frame: `Display` renders the bare message,
/// whatever `SourcePos` name a surface injects.  This is what the web load
/// path reports (`theory_io::load_from_source`), where the port deliberately
/// answers with a clean parse-error surface instead of HS's crashed handler.
#[test]
fn ghc_error_renders_without_a_parsec_frame() {
    assert_eq!(
        err(&macro_theory("exp(x) = x"), "g_reserved.spthy"),
        "`\"exp\"` is a reserved function name for builtins."
    );
    assert_eq!(
        err(&macro_theory("m(x, x) = x"), "g_dup.spthy"),
        "\"m\" have two arguments with the same name."
    );
}

/// The parsec `fail`s keep their frame — no `ghc_error` is attached.
#[test]
fn parsec_failures_carry_no_ghc_error() {
    for src in [
        "theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n",
        "theory MacroCF begin\nmacros: m(x) = \nend\n",
    ] {
        assert!(
            parse_theory(src, &[]).unwrap_err().ghc_error.is_none(),
            "case {src:?}"
        );
    }
}

/// A macro named after a user-declared function conflicts
/// (`userDefinedFunSyms` via `stFunSyms`, Term/Maude/Signature.hs:163-164).
/// The error merges the body's trailing-variable `.`-index attempt
/// (Token.hs:395-400) into the `fail`'s message.
#[test]
fn macro_conflicts_with_user_function() {
    assert_eq!(
        err(
            "theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n",
            "c_fun.spthy"
        ),
        "\"c_fun.spthy\" (line 4, column 1):\nunexpected \"e\"\nexpecting \".\"\n\
         Conflicting name for macro f"
    );
}

/// A macro named after an EARLIER macro conflicts: each parsed macro is
/// registered under `macroNames` before the next one parses (Macro.hs:46).
#[test]
fn macro_conflicts_with_earlier_macro() {
    assert_eq!(
        err(
            "theory MacroCM begin\nmacros: m(x) = x, m(y) = y\nend\n",
            "c_macro.spthy"
        ),
        "\"c_macro.spthy\" (line 3, column 1):\nunexpected \"e\"\nexpecting \".\"\n\
         Conflicting name for macro m"
    );
}

/// A macro named after an enabled builtin's symbol conflicts: `builtins:
/// hashing` merges `h/1` into `stFunSyms` (Term/Builtin/Signature.hs:75-77),
/// which `userDefinedFunSyms` includes.
#[test]
fn macro_conflicts_with_enabled_builtin_symbol() {
    assert_eq!(
        err(
            "theory MacroCH begin\nbuiltins: hashing\nmacros: h(x) = x\nend\n",
            "c_hash.spthy"
        ),
        "\"c_hash.spthy\" (line 4, column 1):\nunexpected \"e\"\nexpecting \".\"\n\
         Conflicting name for macro h"
    );
}

/// The seeded pairing symbols (`fst`/`pair`/`snd`, `pairMaudeSig` —
/// Token.hs:260-261, Term/Term/FunctionSymbols.hs:299-300) conflict without
/// any declaration.
#[test]
fn macro_conflicts_with_seeded_pair_symbol() {
    assert_eq!(
        err(
            "theory MacroCP begin\nmacros: fst(x) = x\nend\n",
            "c_pair.spthy"
        ),
        "\"c_pair.spthy\" (line 3, column 1):\nunexpected \"e\"\nexpecting \".\"\n\
         Conflicting name for macro fst"
    );
}

/// `builtins: diffie-hellman` folds `dhFunSig`'s `NoEq` symbols (among them
/// `DH_neutral`) into `funSyms` (Term/Maude/Signature.hs:110-116), so the
/// name conflicts — and the enabled `expterm`/`multterm` levels leave their
/// `^`/`*` labels in the error (Term.hs:176-185).
#[test]
fn macro_conflicts_with_dh_theory_symbol() {
    assert_eq!(
        err(
            "theory MacroCD begin\nbuiltins: diffie-hellman\nmacros: DH_neutral(x) = x\nend\n",
            "c_dh.spthy"
        ),
        "\"c_dh.spthy\" (line 4, column 1):\nunexpected \"e\"\n\
         expecting \".\", \"^\" or \"*\"\nConflicting name for macro DH_neutral"
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
        err(
            "theory MacroCBP begin\nbuiltins: bilinear-pairing\nmacros: DH_neutral(x) = x\nend\n",
            "c_bp.spthy"
        ),
        "\"c_bp.spthy\" (line 4, column 1):\nunexpected \"e\"\n\
         expecting \".\", \"^\" or \"*\"\nConflicting name for macro DH_neutral"
    );
}

/// `natural-numbers` contributes `natOneSym` — whose name is `tone`
/// (Term/Term/FunctionSymbols.hs:236) — and `natterm`'s `%+` label
/// (Term.hs:203-208).
#[test]
fn macro_conflicts_with_nat_theory_symbol() {
    assert_eq!(
        err(
            "theory MacroCN begin\nbuiltins: natural-numbers\nmacros: tone(x) = x\nend\n",
            "c_nat.spthy"
        ),
        "\"c_nat.spthy\" (line 4, column 1):\nunexpected \"e\"\n\
         expecting \".\" or \"%+\"\nConflicting name for macro tone"
    );
    parse_theory("theory MacroCNC begin\nmacros: tone(x) = x\nend\n", &[])
        .expect("tone macro parses without natural-numbers");
}

/// A user `[AC]` symbol conflicts (`acUserFunSyms` via `ACfctUser`,
/// Term/Maude/Signature.hs:158-164); its `chainl1` level (Term.hs:165-174)
/// leaves the symbol's own label.
#[test]
fn macro_conflicts_with_user_ac_symbol() {
    assert_eq!(
        err(
            "theory MacroCA begin\nfunctions: f/2 [AC]\nmacros: f(x) = x\nend\n",
            "c_ac.spthy"
        ),
        "\"c_ac.spthy\" (line 4, column 1):\nunexpected \"e\"\n\
         expecting \".\" or \"f\"\nConflicting name for macro f"
    );
}

/// Two `[AC]` symbols label the error in REVERSE `stACFunSyms` order: the
/// innermost `chainl1` level (the LAST symbol of `S.toList`) fails first
/// (`parseACSym`, Term.hs:171-173).
#[test]
fn ac_operator_labels_come_innermost_first() {
    assert_eq!(
        err(
            "theory MacroCA2 begin\nfunctions: f/2 [AC], g/2 [AC]\nmacros: f(x) = x\nend\n",
            "c_ac2.spthy"
        ),
        "\"c_ac2.spthy\" (line 4, column 1):\nunexpected \"e\"\n\
         expecting \".\", \"g\" or \"f\"\nConflicting name for macro f"
    );
}

/// `multiset` enables `msetterm`'s union level, whose `opUnion` tries both
/// spellings (`symbol_ "++" <|> symbol_ "+"`, Token.hs:551-552).
#[test]
fn mset_leaves_both_union_labels() {
    assert_eq!(
        err(
            "theory MacroCMS begin\nbuiltins: multiset\nfunctions: f/1\nmacros: f(x) = x\nend\n",
            "c_mset.spthy"
        ),
        "\"c_mset.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         expecting \".\", \"++\" or \"+\"\nConflicting name for macro f"
    );
}

/// `xor` enables `xorterm`, whose `opXor` tries both spellings
/// (`symbol_ "XOR" <|> symbol_ "⊕"`, Token.hs:555-556).
#[test]
fn xor_leaves_both_xor_labels() {
    assert_eq!(
        err(
            "theory MacroCX begin\nbuiltins: xor\nfunctions: f/1\nmacros: f(x) = x\nend\n",
            "c_xor.spthy"
        ),
        "\"c_xor.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         expecting \".\", \"XOR\" or \"⊕\"\nConflicting name for macro f"
    );
}

/// All theory levels enabled at once pin the full innermost-first label
/// order of the `msetterm → natterm → xorterm → multterm → expterm` nesting
/// (Term.hs:176-208).
#[test]
fn all_operator_levels_order() {
    assert_eq!(
        err(
            "theory MacroCALL begin\n\
             builtins: diffie-hellman, xor, multiset, natural-numbers\n\
             functions: f/1\nmacros: f(x) = x\nend\n",
            "c_all.spthy"
        ),
        "\"c_all.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         expecting \".\", \"^\", \"*\", \"XOR\", \"⊕\", \"%+\", \"++\" or \"+\"\n\
         Conflicting name for macro f"
    );
}

/// A body whose last lexeme is not a variable's identifier leaves no `.`
/// label: an application's `)` (Term.hs:94), a sort-suffixed variable
/// (Token.hs:413-418), a public-name literal, a nullary symbol matched by
/// `nullaryApp`'s `symbol` (Term.hs:158-163), an explicit `.1` index, and a
/// grouping `(x)`.
#[test]
fn no_dot_label_when_body_ends_in_non_identifier_lexeme() {
    for (name, src) in [
        (
            "c_paren_body.spthy",
            "theory T begin\nbuiltins: hashing\nfunctions: f/1\nmacros: f(x) = h(x)\nend\n",
        ),
        (
            "c_nullary_body.spthy",
            "theory T begin\nfunctions: c/0, f/1\nmacros: f(x) = c\nend\n",
        ),
    ] {
        let line = if src.matches('\n').count() == 5 { 5 } else { 4 };
        assert_eq!(
            err(src, name),
            format!(
                "\"{name}\" (line {line}, column 1):\nunexpected \"e\"\n\
                 Conflicting name for macro f"
            ),
            "case {name}"
        );
    }
    for (name, decl) in [
        ("c_suffix_body.spthy", "f(x) = x:pub"),
        ("c_pub_body.spthy", "f(x) = 'a'"),
        ("c_dotidx_body.spthy", "f(x) = x.1"),
        ("c_parengrp_body.spthy", "f(x) = (x)"),
    ] {
        assert_eq!(
            err(
                &format!("theory T begin\nfunctions: f/1\nmacros: {decl}\nend\n"),
                name
            ),
            format!(
                "\"{name}\" (line 4, column 1):\nunexpected \"e\"\n\
                 Conflicting name for macro f"
            ),
            "case {name}"
        );
    }
}

/// Bodies whose last lexeme IS a variable's identifier keep the `.` label:
/// a `$`-prefixed variable, `binaryAlgApp`'s trailing `arg2` (Term.hs:109-121),
/// and a variable separated from the next token by a comment (the label sits
/// at the post-whitespace position either way).
#[test]
fn dot_label_when_body_ends_in_variable_identifier() {
    for (name, thy) in [
        (
            "c_prefix_body.spthy",
            "theory T begin\nfunctions: f/1\nmacros: f(x) = $y\nend\n".to_string(),
        ),
        (
            "c_algapp_body.spthy",
            "theory T begin\nfunctions: g/2, f/1\nmacros: f(x) = g{x}x\nend\n".to_string(),
        ),
        (
            "c_comment_gap.spthy",
            "theory T begin\nfunctions: f/1\nmacros: f(x) = x /* trailing */\nend\n".to_string(),
        ),
    ] {
        assert_eq!(
            err(&thy, name),
            format!(
                "\"{name}\" (line 4, column 1):\nunexpected \"e\"\nexpecting \".\"\n\
                 Conflicting name for macro f"
            ),
            "case {name}"
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
