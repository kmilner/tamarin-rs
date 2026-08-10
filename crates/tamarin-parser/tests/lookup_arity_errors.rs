// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parse errors of `lookupArity`-driven prefix-application
//! resolution (Theory/Text/Parser/Term.hs:62-105) and the term-path frames
//! its backtrack leaves behind.
//!
//! HS resolves every prefix application through `lookupArity` over the
//! signature built SO FAR and parses the arity the lookup returns; on any
//! failure — unknown operator, arity mismatch, malformed argument list — the
//! try-wrapped application backtracks and the name reparses as a variable,
//! so the NEXT token breaks the enclosing grammar.  The user-visible frame is
//! that consumed failure, merged with the variable's `letter or digit`/`"."`
//! identifier hangovers and the enabled operator labels.
//!
//! Every expected string is the stderr frame the pinned Haskell oracle
//! (Git revision ef3f0468) prints for the same bytes, minus the three
//! `maude tool:` banner lines (probe files p02–p48 of the lookup-arity
//! probe matrix; sources here are byte-identical to the probes).

use tamarin_parser::parse_theory;

/// The frame `parse_theory` reports for `src`, rendered exactly as batch
/// mode prints it (`ParseError::with_source(<file>)`).
fn frame(src: &str, source_name: &str) -> String {
    parse_theory(src, &[])
        .unwrap_err()
        .with_source(source_name)
        .to_string()
}

/// Arity mismatch in a rule's fact argument: `g/3` applied to two arguments.
/// The application backtracks, `g` reparses as a variable, and `commaSep`'s
/// comma plus `parens`' close fail at the `(` together with the variable's
/// identifier hangovers.
#[test]
fn arity_mismatch_backtracks_to_variable_frame() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g('a','b')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p02_toofew.spthy"),
        "\"p02_toofew.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

/// An UNDECLARED name applied prefix is `lookupArity`'s `fail "unknown
/// operator …"` — same backtrack, same frame.
#[test]
fn undeclared_application_is_a_parse_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ Out(g('a')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p05_undeclared.spthy"),
        "\"p05_undeclared.spthy\" (line 5, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

/// Use BEFORE declaration: `lookupArity` reads the signature built so far,
/// so a later `functions:` item does not rescue an earlier use.
#[test]
fn use_before_declaration_is_a_parse_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ Out(g('a')) ]\n\nfunctions: g/1\n\nend\n";
    assert_eq!(
        frame(src, "p25_use_before_decl.spthy"),
        "\"p25_use_before_decl.spthy\" (line 5, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

/// A nullary symbol applied to arguments fails the arity check; the name is
/// then claimed by `nullaryApp`'s `symbol` (Parser/Term.hs:158-163), which leaves NO
/// identifier hangovers — only the fact-argument labels remain.
#[test]
fn nullary_applied_with_args_has_no_identifier_hangover() {
    let src =
        "theory T\nbegin\n\nfunctions: f/0\n\nrule r:\n  [ ] --> [ Out(f('a','b')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p07_nullary_args.spthy"),
        "\"p07_nullary_args.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting \",\" or \")\""
    );
}

/// `h()` for the unary hashing builtin: the `k == 1` branch parses ONE
/// `tupleterm`, which requires an operand — the empty argument list
/// backtracks the application.
#[test]
fn unary_empty_parens_backtracks() {
    let src = "theory T\nbegin\n\nbuiltins: hashing\n\nrule r:\n  [ ] --> [ Out(h()) ]\n\nend\n";
    assert_eq!(
        frame(src, "p15b_h_empty.spthy"),
        "\"p15b_h_empty.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

/// `h('a',)` — the `k == 1` branch's `tupleterm` is `chainr1`, which does
/// NOT admit a trailing comma (unlike `commaSep` for other arities).
#[test]
fn unary_trailing_comma_backtracks() {
    let src =
        "theory T\nbegin\n\nbuiltins: hashing\n\nrule r:\n  [ ] --> [ Out(h('a',)) ]\n\nend\n";
    assert_eq!(
        frame(src, "p27_unary_trailing.spthy"),
        "\"p27_unary_trailing.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

/// A malformed NESTED application (undeclared `k` inside a well-arity `g`)
/// fails the whole outer application: the error sits at the OUTER `(` and
/// the inner failure is discarded, exactly like parsec's `try`.
#[test]
fn nested_failure_reports_at_the_outer_application() {
    let src =
        "theory T\nbegin\n\nfunctions: g/2\n\nrule r:\n  [ ] --> [ Out(g(k('x'),'b')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p28_nested_bad.spthy"),
        "\"p28_nested_bad.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

/// Whitespace between the name and `(`: the `letter or digit` hangover sits
/// at the name's end and the error position (post-whitespace) has moved past
/// it, so only `"."` survives of the identifier's labels.
#[test]
fn whitespace_before_paren_drops_letter_or_digit() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g ('a','b')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p48_ws_before_paren.spthy"),
        "\"p48_ws_before_paren.spthy\" (line 7, column 19):\nunexpected \"(\"\nexpecting \".\", \",\" or \")\""
    );
}

/// `em` is ALWAYS in `lookupArity`'s list at arity 2 (appended after the
/// macro names, Parser/Term.hs:65); under bilinear-pairing a 3-argument use fails
/// the arity check and the DH operator labels (`^`, `*` — BP forces
/// `enableDH`) join the frame.
#[test]
fn em_wrong_arity_under_bp_shows_dh_operator_labels() {
    let src = "theory T\nbegin\n\nbuiltins: bilinear-pairing\n\nrule r:\n  [ ] --> [ Out(em('a','b','c')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p17_em_bp3.spthy"),
        "\"p17_em_bp3.spthy\" (line 7, column 19):\nunexpected \"(\"\nexpecting letter or digit, \".\", \"^\", \"*\", \",\" or \")\""
    );
}

/// A declared `[AC]` symbol adds its own infix-operator label between the
/// variable hangovers and the fact-argument labels (`acterm`'s per-symbol
/// `chainl1` level, Parser/Term.hs:165-172).
#[test]
fn user_ac_symbol_label_joins_the_frame() {
    let src =
        "theory T\nbegin\n\nfunctions: f/2 [AC]\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p33_ac_label.spthy"),
        "\"p33_ac_label.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \"f\", \",\" or \")\""
    );
}

/// `builtins: xor` opens the `XOR`/`⊕` chain level; both spellings' labels
/// appear (Parser/Term.hs:187-192, Token.hs:554-556).
#[test]
fn xor_operator_labels_join_the_frame() {
    let src = "theory T\nbegin\n\nbuiltins: xor\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p37_xor_label.spthy"),
        "\"p37_xor_label.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \"XOR\", \"⊕\", \",\" or \")\""
    );
}

/// `builtins: multiset` opens the `++`/`+` union level (Parser/Term.hs:195-200,
/// Token.hs:550-552).
#[test]
fn multiset_operator_labels_join_the_frame() {
    let src =
        "theory T\nbegin\n\nbuiltins: multiset\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p38_mset_label.spthy"),
        "\"p38_mset_label.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \"++\", \"+\", \",\" or \")\""
    );
}

/// `builtins: natural-numbers` opens the `%+` level (Parser/Term.hs:203-208).
#[test]
fn nat_operator_label_joins_the_frame() {
    let src = "theory T\nbegin\n\nbuiltins: natural-numbers\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p39_nat_label.spthy"),
        "\"p39_nat_label.spthy\" (line 7, column 18):\nunexpected \"(\"\nexpecting letter or digit, \".\", \"%+\", \",\" or \")\""
    );
}

/// Inside a tuple, the failed application's frame carries the tuple's own
/// close label (`chainr1` comma + `angled`'s `>`).
#[test]
fn tuple_close_labels_join_the_frame() {
    let src = "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(<g('a','b'), 'c'>) ]\n\nend\n";
    assert_eq!(
        frame(src, "p34_tuple.spthy"),
        "\"p34_tuple.spthy\" (line 7, column 19):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\" or \">\""
    );
}

/// Inside grouping parens there is no comma alternative — only the close.
#[test]
fn grouping_parens_frame_has_no_comma() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out((g('a','b'))) ]\n\nend\n";
    assert_eq!(
        frame(src, "p42_group_parens.spthy"),
        "\"p42_group_parens.spthy\" (line 7, column 19):\nunexpected \"(\"\nexpecting letter or digit, \".\" or \")\""
    );
}

/// `op{t1}t2` (`binaryAlgApp`, Parser/Term.hs:109-121) requires arity 2; a `g/3`
/// head backtracks the same way and the frame sits at the `{`.
#[test]
fn algapp_arity_mismatch_backtracks() {
    let src = "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g{'a'}'b') ]\n\nend\n";
    assert_eq!(
        frame(src, "p44_algapp_arity.spthy"),
        "\"p44_algapp_arity.spthy\" (line 7, column 18):\nunexpected \"{\"\nexpecting letter or digit, \".\", \",\" or \")\""
    );
}

// ---------------------------------------------------------------------------
// Formula contexts: `blatom`'s un-try'd node-equality alternative
// (Parser/Formula.hs:56) consumes the atom's leading identifier as a `nodevar` and
// its `opEqual` failure right after it is THE reported error.
// ---------------------------------------------------------------------------

/// A lowercase applied name in a lemma: `fact` refuses it (lowercase), the
/// term path backtracks to a variable, and the node-equality reparse puts the
/// frame at the char after the name.
#[test]
fn formula_lowercase_application_frame() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3(x) @ #i ==> F\"\n\nend\n";
    assert_eq!(
        frame(src, "p06_lemma_lower.spthy"),
        "\"p06_lemma_lower.spthy\" (line 8, column 16):\nunexpected \"(\"\nexpecting letter or digit, \".\" or \"=\""
    );
}

/// Whitespace variant: the `letter or digit` hangover is dropped, `"."`
/// survives at the post-whitespace position.
#[test]
fn formula_lowercase_application_frame_with_whitespace() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3 (x) @ #i ==> F\"\n\nend\n";
    assert_eq!(
        frame(src, "p23_lemma_ws.spthy"),
        "\"p23_lemma_ws.spthy\" (line 8, column 17):\nunexpected \"(\"\nexpecting \".\" or \"=\""
    );
}

/// Even a DECLARED, well-arity application errors when used where a fact is
/// needed: the node-equality reparse stops after the bare name, so the frame
/// sits at the `(` — not at the `@`.
#[test]
fn formula_declared_application_errors_after_the_name() {
    let src = "theory T\nbegin\n\nfunctions: g/1\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. g(x) @ #i ==> F\"\n\nend\n";
    assert_eq!(
        frame(src, "p29_formula_declared.spthy"),
        "\"p29_formula_declared.spthy\" (line 10, column 15):\nunexpected \"(\"\nexpecting letter or digit, \".\" or \"=\""
    );
}

/// A bare variable with no relational operator: same reparse, frame at the
/// `@` (whitespace dropped the `letter or digit`).
#[test]
fn formula_bare_variable_frame() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. x @ #i ==> F\"\n\nend\n";
    assert_eq!(
        frame(src, "p35_bare_var_at.spthy"),
        "\"p35_bare_var_at.spthy\" (line 8, column 16):\nunexpected \"@\"\nexpecting \".\" or \"=\""
    );
}

/// A non-identifier-headed atom (`'a' @ …`): `nodevar` consumes nothing, so
/// the empty failures merge instead — the `<?>` relabels of the try-wrapped
/// relational alternatives that consumed the term.
#[test]
fn formula_nonidentifier_atom_unions_relational_labels() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. 'a' @ #i ==> F\"\n\nend\n";
    assert_eq!(
        frame(src, "p40_nonident_atom.spthy"),
        "\"p40_nonident_atom.spthy\" (line 8, column 18):\nunexpected \"@\"\nexpecting subterm predicate or term equality"
    );
}

/// An undeclared UPPERCASE application before a relational operator: the
/// term-relational alternatives die at the `(`, the `Pred` fact alternative
/// then wins, and the leftover `= y` breaks the formula at its closing
/// quote — with the fact's `"["` annotation attempt and every formula
/// operator's labels.
#[test]
fn formula_undeclared_uppercase_relop_becomes_pred_then_close_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x y #i. P3(x) = y ==> F\"\n\nend\n";
    assert_eq!(
        frame(src, "p46_upper_eq.spthy"),
        "\"p46_upper_eq.spthy\" (line 8, column 22):\nunexpected \"=\"\nexpecting \"[\", \"&\", \"∧\", \"|\", \"∨\", \"==>\", \"⇒\", \"<=>\", \"⇔\" or \"\"\""
    );
}

// ---------------------------------------------------------------------------
// `equations:` context (eqn = True)
// ---------------------------------------------------------------------------

/// Arity mismatch inside an equation: the backtracked variable is followed by
/// `equalSign`'s failing `=`.
#[test]
fn equation_arity_mismatch_frame() {
    let src = "theory T\nbegin\n\nfunctions: g/2\n\nequations: g(x) = x\n\nend\n";
    assert_eq!(
        frame(src, "p21_eqn_arity.spthy"),
        "\"p21_eqn_arity.spthy\" (line 6, column 13):\nunexpected \"(\"\nexpecting letter or digit, \".\" or \"=\""
    );
}

/// A reserved builtin name in an equation is a GHC `error`, not a parsec
/// failure (Parser/Term.hs:90-92): the exception escapes every `try` and carries
/// the `HasCallStack` frame of `naryOpApp`'s call site.
#[test]
fn equation_reserved_builtin_is_a_ghc_error() {
    let src = "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n";
    let e = parse_theory(src, &[]).unwrap_err();
    let g = e.ghc_error.as_ref().expect("GHC error, not a parsec frame");
    assert_eq!(
        g.display_exception(),
        "`\"exp\"` is a reserved function name for builtins.\n\
         CallStack (from HasCallStack):\n  error, called at \
         src/Theory/Text/Parser/Term.hs:92:9 in \
         tamarin-prover-theory-1.13.0-8wixYaxm5uHCGl2uEzaKzP:Theory.Text.Parser.Term"
    );
}

/// The check fires on the identifier alone — even a BARE reserved name in an
/// equation operand aborts (naryOpApp runs before `nullaryApp`/`plit` for
/// every identifier-headed atom).
#[test]
fn equation_bare_reserved_builtin_is_a_ghc_error() {
    let src = "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n";
    let e = parse_theory(src, &[]).unwrap_err();
    let g = e.ghc_error.as_ref().expect("GHC error, not a parsec frame");
    assert_eq!(
        g.display_exception(),
        "`\"mun\"` is a reserved function name for builtins.\n\
         CallStack (from HasCallStack):\n  error, called at \
         src/Theory/Text/Parser/Term.hs:92:9 in \
         tamarin-prover-theory-1.13.0-8wixYaxm5uHCGl2uEzaKzP:Theory.Text.Parser.Term"
    );
}

// ---------------------------------------------------------------------------
// `macros:` body — the term ends the ITEM, so the frame is the top-level
// item alternation's, prefixed by the term's hangovers and the macro list's
// comma.
// ---------------------------------------------------------------------------

#[test]
fn macro_body_application_frame_is_the_item_position_error() {
    let src =
        "theory T\nbegin\n\nmacros: m(x) = k(x,'a')\n\nrule r:\n  [ ] --> [ Out(m('b')) ]\n\nend\n";
    assert_eq!(
        frame(src, "p36_macro_body.spthy"),
        "\"p36_macro_body.spthy\" (line 4, column 17):\nunexpected \"(\"\nexpecting letter or digit, \".\", \",\", \"heuristic\", \"tactic\", \"builtins\", \"options\", \"functions\", \"function\", \"equations\", \"macros\", \"restriction\", \"axiom\", \"test\", \"lemma\", \"rule\", letter, top-level process, \"let\", \"equivLemma\", \"diffEquivLemma\", predicate block, export block, \"#ifdef\", \"#define\", \"#include\" or \"end\""
    );
}
