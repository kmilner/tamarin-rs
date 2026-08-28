// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::atom::Unit2;
use crate::formula::BLNTerm;
use tamarin_parser::ast as p;
use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::term::f_app_no_eq;

/// A free variable leaf of a guarded formula's term.
fn bvar(name: &str, sort: LSort) -> BLNTerm {
    tamarin_term::vterm::var_term(tamarin_term::lterm::BVar::Free(
        tamarin_term::lterm::LVar::new(name, sort, 0),
    ))
}

/// A public-name leaf of a guarded formula's term.
fn bpub(name: &str) -> BLNTerm {
    tamarin_term::vterm::const_term(Name::new(NameTag::Pub, name))
}

/// A user-declared public constructor applied to `args`.
fn user_app(name: &str, args: Vec<BLNTerm>) -> BLNTerm {
    f_app_no_eq(
        NoEqSym::new(
            name.as_bytes().to_vec(),
            args.len(),
            Privacy::Public,
            Constructability::Constructor,
        ),
        args,
    )
}

#[test]
fn trivial_formulas() {
    let ltrue: LNFormula = ProtoFormula::ltrue();
    let lfalse: LNFormula = ProtoFormula::lfalse();
    assert_eq!(pretty_lnformula(&ltrue), "\u{22A4}");
    assert_eq!(pretty_lnformula(&lfalse), "\u{22A5}");
}

#[test]
fn unannotated_comment_renders_inline() {
    // `multiComment_ ["unannotated"]` → `/* unannotated */`.
    assert_eq!(unannotated_comment_doc().render(), "/* unannotated */");
}

#[test]
fn step_unann_inline_when_short() {
    // A short method + comment fit on one line: `sep` keeps the
    // `/* unannotated */` inline beside the method (HS ppStep,
    // ProofSkeleton.hs:80-84).
    use crate::pretty_hpj::Doc;
    let m = Doc::text("simplify");
    let out = step_line_with_unann(m, 2, /*annotated=*/ false, "");
    assert_eq!(out, "simplify /* unannotated */");
}

#[test]
fn step_annotated_omits_comment() {
    // When the step is annotated (psInfo = Just _), NO comment.
    use crate::pretty_hpj::Doc;
    let m = Doc::text("by sorry");
    let out = step_line_with_unann(m, 4, /*annotated=*/ true, "");
    assert_eq!(out, "by sorry");
}

#[test]
fn step_unann_breaks_past_ribbon() {
    // When the method line is so long that method + ` /* unannotated
    // */` exceeds the ribbon (73), `sep` drops the comment to its OWN
    // line at the step's base indent (here base_indent = 2).  The
    // method's own (single-line) text stays put; only the comment
    // moves.
    use crate::pretty_hpj::Doc;
    let long = "solve( (last(#k))  \u{2225} (something quite long here indeed yes) )";
    assert!(long.chars().count() + " /* unannotated */".chars().count() > 73);
    let out = step_line_with_unann(Doc::text(long), 2, /*annotated=*/ false, "");
    let lines: Vec<&str> = out.split('\n').collect();
    assert_eq!(
        lines.len(),
        2,
        "comment should drop to its own line: {out:?}"
    );
    assert_eq!(lines[0], long, "method line unchanged");
    // Dropped comment sits at the step's base indent (2 spaces).
    assert_eq!(lines[1], "  /* unannotated */");
}

#[test]
fn forall_with_action() {
    use crate::formula::from_parser;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    let f = parse_formula_str("All ni #i. Fa(ni) @ #i ==> F", &pair_maude_sig()).unwrap();
    let ln = from_parser(&f, &pair_maude_sig()).unwrap();
    // The output follows HS.  `Name( args )` keeps the internal spaces, and
    // `ppImp` puts parentheses on both sides of the `⇒`.  The expected bytes
    // come from the oracle (Git revision ef3f0468).
    assert_eq!(
        syntactic_lnformula_doc(&ln).render_with(FLAT_WIDTH, FLAT_WIDTH),
        "\u{2200} ni #i. (Fa( ni ) @ #i) \u{21D2} (\u{22A5})"
    );
}

#[test]
fn long_quantifier_varlist_wraps() {
    use crate::formula::from_parser;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    // HS `ppVars = fsep . map (text . show)` (Theory/Model/Formula.hs:503-511, see line 511): a long
    // bound-var list wraps across lines, the continuation aligned after
    // the `∃ ` prefix (column 2, the `<>` nesting offset).  Build an
    // existential with enough vars to overflow the ribbon, body `⊥`.
    let names = [
        "i1", "i2", "j1", "j2", "h1", "h2", "ss", "vote2", "fstcode1", "sndcode1", "fstcode2",
        "sndcode2", "ess", "hv1", "hv2", "hy1", "hy2", "x1", "x2", "adv1", "adv2", "ek", "bb",
        "sks", "y1", "y2", "aa", "ea", "el", "em",
    ];
    let src = format!("Ex {}. F", names.join(" "));
    let f = parse_formula_str(&src, &pair_maude_sig()).unwrap();
    let ln = from_parser(&f, &pair_maude_sig()).unwrap();
    let out = syntactic_lnformula_doc(&ln).render_at(
        crate::pretty_hpj::LINE_LENGTH,
        crate::pretty_hpj::RIBBON,
        0,
    );
    let lines: Vec<&str> = out.split('\n').collect();
    assert!(lines.len() >= 2, "long var list must wrap: {out:?}");
    // First line opens with the existential symbol and a space.
    assert!(
        lines[0].starts_with("\u{2203} "),
        "first line: {:?}",
        lines[0]
    );
    // Continuation lines are indented by 2 (aligned after `∃ `), i.e.
    // exactly the column where the first bound var landed.
    for cont in &lines[1..] {
        // Skip the final body-only line if it is just the nested `⊥`.
        if cont.trim_start() == "\u{22A5}" {
            continue;
        }
        assert!(
            cont.starts_with("  ") && !cont.starts_with("   "),
            "continuation var line should align at col 2: {cont:?}"
        );
    }
    // No bound var was dropped: the rendered text contains every name.
    for n in names {
        assert!(out.contains(n), "missing var {n} in {out:?}");
    }
}

#[test]
fn guarded_negation_shortcut() {
    // ∀ [] [Less(i,j)] ⊥  ⇒  rendered as `¬(i < j)`.
    let g = Guarded::GGuarded {
        qua: Quantifier::All,
        vars: vec![].into(),
        guards: vec![crate::atom::ProtoAtom::Less(
            bvar("i", LSort::Node),
            bvar("j", LSort::Node),
        )]
        .into(),
        body: std::sync::Arc::new(Guarded::Disj(vec![].into())),
    };
    // The expected bytes come from the oracle (Git revision ef3f0468).  The
    // `∀` without binders over `⊥` prints as the negated guard alone.  It
    // never prints as an `⇒ ⊥`.
    assert_eq!(pretty_guarded(&g), "\u{00AC}(#i < #j)");
}

/// Build the parser Term `<'1', g1> ++ <'2', g2> ++ <'3', g3>` where the
/// pair payloads are long enough that the flat AC chain exceeds the ribbon
/// and HS `prettyTerm` (Term/Term.hs:298-327, see line 305-309 `FApp (AC o) -> ppTerms ...`) must
/// wrap it with the `++` operator at line ends and each element `nest 1`'d.
fn ac_chain_bterm() -> BLNTerm {
    let pair = |n: &str, payload: &str| {
        f_app_no_eq(
            tamarin_term::function_symbols::pair_sym(),
            vec![bpub(n), bvar(payload, LSort::Fresh)],
        )
    };
    tamarin_term::term::f_app_ac(
        tamarin_term::function_symbols::AcSym::Union,
        vec![
            pair("1", "longPayloadNameNumberOne"),
            pair("2", "longPayloadNameNumberTwo"),
            pair("3", "longPayloadNameNumberThree"),
        ],
    )
}

#[test]
fn ac_union_chain_wraps_in_guarded_formula() {
    // The guarded path must wrap the SAME AC chain identically, since HS
    // uses ONE prettyTerm for both rule terms and formula terms.
    // Build `z = <chain>` as a guarded Eq atom and render wrapped.
    let g = Guarded::Atom(crate::atom::ProtoAtom::EqE(
        bvar("z", LSort::Msg),
        ac_chain_bterm(),
    ));
    // indent 12 (a proof-tree depth) forces the RHS chain to wrap.
    let s = pretty_guarded_wrapped(&g, 12);
    assert!(s.contains("++\n"), "guarded AC chain did not wrap:\n{s}");
    assert!(
        s.contains("~longPayloadNameNumberTwo"),
        "payload missing:\n{s}"
    );
    // The Eq's `=` is rendered (HS `sep [ppT l <-> opEqual, ppT r]`).
    assert!(s.contains("z ="), "Eq operator missing:\n{s}");
}

/// Regression: the AC `*` exponent inside an `exp` term must keep its
/// `fcat` break points.  HS `prettyTerm` (Term/Term.hs:298-327, see line 310) renders exp as
/// `ppTerm t1 <> "^" <> ppTerm t2`, so the exponent `t2 = (~a*~b)` stays a
/// breakable `fcat`: `hmac('g'^(~a*~b), ...)` must wrap the `*`-operands
/// like HS rather than run past LINE_LENGTH=110.  Mirrors the spdm
/// `hmac('g'^(~newPrivKey*~respPrivKey), ...)` proof-line divergence.
#[test]
fn exp_with_ac_exponent_wraps_inside_fun() {
    use tamarin_term::function_symbols::{exp_sym, AcSym};
    use tamarin_term::lterm::LVar;
    use tamarin_term::pretty::pretty_nterm;
    use tamarin_term::term::{f_app_ac, f_app_no_eq};
    use tamarin_term::vterm::{const_term, var_term};

    let fresh = |n: &str| var_term(LVar::new(n, LSort::Fresh, 0));
    // hmac('g'^(~longFreshPrivKeyOne*~longFreshPrivKeyTwo), ~longSaltArgument)
    let exp = f_app_no_eq(
        exp_sym(),
        vec![
            const_term(Name::new(NameTag::Pub, "g")),
            f_app_ac(
                AcSym::Mult,
                vec![fresh("longFreshPrivKeyOne"), fresh("longFreshPrivKeyTwo")],
            ),
        ],
    );
    let t = f_app_no_eq(
        NoEqSym::new(
            b"hmac".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        ),
        vec![exp.clone(), fresh("longSaltArgumentName")],
    );
    // Deep indent (col 30) so the flat term overruns and the `*`-operands
    // must each break onto their own line at `nest 1` (HS layout).
    let s = pretty_nterm(&t).render_at(LINE_LENGTH, RIBBON, 30);
    assert!(
        s.contains("*\n"),
        "AC `*` exponent inside exp did not wrap:\n{s}"
    );
    // exp's `^` and `'g'` stay on the first line (exp never breaks at `^`).
    assert!(
        s.lines().next().unwrap().contains("'g'^("),
        "exp head should stay flat as `'g'^(`:\n{s}"
    );
    // No flat line exceeds the page width.
    for line in s.lines() {
        assert!(
            line.chars().count() <= LINE_LENGTH,
            "line overruns LINE_LENGTH:\n{line}"
        );
    }
    // The plain (well-fitting) exp still renders flat with no wrap.
    let flat = pretty_nterm(&exp).render_at(LINE_LENGTH, RIBBON, 0);
    assert_eq!(flat, "'g'^(~longFreshPrivKeyOne*~longFreshPrivKeyTwo)");
}

#[test]
fn algapp_renders_function_form_flat_guarded_term() {
    let g = user_app(
        "sdec",
        vec![bvar("body", LSort::Msg), bvar("key", LSort::Msg)],
    );
    // The guarded printer reaches a term through its atom, so read the
    // application off the left side of an equality.
    let a = Guarded::Atom(crate::atom::ProtoAtom::EqE(g, bpub("z")));
    assert_eq!(pretty_guarded(&a), "sdec(body, key) = 'z'");
}

#[test]
fn algapp_pair_arg_renders_function_form_doc_guarded_term() {
    // senc{a,b}k as a guarded term -> senc(<a, b>, k) via the Doc renderer
    let g = user_app(
        "senc",
        vec![
            f_app_no_eq(
                tamarin_term::function_symbols::pair_sym(),
                vec![bvar("a", LSort::Msg), bvar("b", LSort::Msg)],
            ),
            bvar("k", LSort::Msg),
        ],
    );
    let a = Guarded::Atom(crate::atom::ProtoAtom::EqE(g, bpub("z")));
    assert_eq!(guarded_doc(&a).render(), "senc(<a, b>, k) = 'z'");
}

// =============================================================================
// Locally-nameless printer
// =============================================================================

/// Every sample printed through both locally-nameless printers, pinned to
/// the oracle's `--parse-only` render of the lemma-header shape (probe
/// `S0_printer_samples.spthy`), and the two printers compared through the
/// nested restriction-body wrapper as well.
#[test]
fn lnformula_doc_renders_the_lemma_header_samples() {
    use crate::formula::{from_parser, to_lnformula};
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::{mset_maude_sig, pair_maude_sig};

    // The union sample needs the signature bit `builtins: multiset` sets, the
    // one that opens `msetterm`'s `+` level (Theory/Text/Parser/Term.hs:195-200).
    let msig = pair_maude_sig().merge(mset_maude_sig());

    let samples: &[(&str, &[&str])] = &[
        ("T", &["  all-traces \"⊤\""]),
        ("F", &["  all-traces \"⊥\""]),
        (
            "(A(x) @ #i & B(x) @ #j) | C(x) @ #k",
            &["  all-traces \"((A( x ) @ #i) ∧ (B( x ) @ #j)) ∨ (C( x ) @ #k)\""],
        ),
        (
            "(not (D(x) @ #l) ==> E(x) @ #m) <=> C(x) @ #n",
            &["  all-traces \"((¬(D( x ) @ #l)) ⇒ (E( x ) @ #m)) ⇔ (C( x ) @ #n)\""],
        ),
        (
            "not (Ex x. A(x) @ #i)",
            &["  all-traces \"¬(∃ x. A( x ) @ #i)\""],
        ),
        (
            "All x y #i. A(x, y) @ #i",
            &["  all-traces \"∀ x y #i. A( x, y ) @ #i\""],
        ),
        (
            "All x. Ex #i. A(x) @ #i",
            &["  all-traces \"∀ x. ∃ #i. A( x ) @ #i\""],
        ),
        // The inner binder shadows the outer one: `x` and `x.1`.
        (
            "All x. Ex x. A(x) @ #i",
            &["  all-traces \"∀ x. ∃ x.1. A( x.1 ) @ #i\""],
        ),
        // Closed, the union is `[Bound 0, Bound 1]` = `y, x`; opening
        // rebuilds it through `f_app`, which re-sorts under the display
        // `LVar`s.
        (
            "All x y. (x + y) = z",
            &["  all-traces \"∀ x y. (x++y) = z\""],
        ),
        // A predicate atom and one with a bound argument; `to_lnformula`
        // is `None` for these.
        ("All x. P(x, y)", &["  all-traces \"∀ x. P( x, y )\""]),
        (
            "All x. Ex y. P(x, y)",
            &["  all-traces \"∀ x. ∃ y. P( x, y )\""],
        ),
        (
            "All x #i #j. OnlyOnce(x) @ i & OnlyOnce(x) @ j ==> #i = #j",
            &[
                "  all-traces",
                "  \"∀ x #i #j. ((OnlyOnce( x ) @ #i) ∧ (OnlyOnce( x ) @ #j)) ⇒ (#i = #j)\"",
            ],
        ),
        // The `_restrict` lifting shape: `#NOW` and an `x.1` binder.
        (
            "All x #NOW x.1. Restr_C_2_1(x, x.1) @ NOW ==> x = x.1",
            &["  all-traces \"∀ x #NOW x.1. (Restr_C_2_1( x, x.1 ) @ #NOW) ⇒ (x = x.1)\""],
        ),
        // Twelve conjuncts: the body wraps at the 110-column page width.
        (
            "All x #i1 #i2 #i3 #i4 #i5 #i6 #i7 #i8 #i9 #i10 #i11 #i12. \
             A(x) @ #i1 & A(x) @ #i2 & A(x) @ #i3 & A(x) @ #i4 & A(x) @ #i5 & \
             A(x) @ #i6 & A(x) @ #i7 & A(x) @ #i8 & A(x) @ #i9 & A(x) @ #i10 & \
             A(x) @ #i11 & A(x) @ #i12 ==> F",
            &[
                "  all-traces",
                "  \"∀ x #i1 #i2 #i3 #i4 #i5 #i6 #i7 #i8 #i9 #i10 #i11 #i12.",
                "    ((((((((((((A( x ) @ #i1) ∧ (A( x ) @ #i2)) ∧ (A( x ) @ #i3)) ∧",
                "             (A( x ) @ #i4)) ∧",
                "            (A( x ) @ #i5)) ∧",
                "           (A( x ) @ #i6)) ∧",
                "          (A( x ) @ #i7)) ∧",
                "         (A( x ) @ #i8)) ∧",
                "        (A( x ) @ #i9)) ∧",
                "       (A( x ) @ #i10)) ∧",
                "      (A( x ) @ #i11)) ∧",
                "     (A( x ) @ #i12)) ⇒",
                "    (⊥)\"",
            ],
        ),
    ];
    for (src, expected_lines) in samples {
        let expected = expected_lines.join("\n");
        let f = parse_formula_str(src, &msig).unwrap();
        let ln = from_parser(&f, &msig).unwrap();
        assert_eq!(
            lemma_header_line_doc("all-traces", syntactic_lnformula_doc(&ln)),
            expected,
            "syntactic_lnformula_doc on {src}"
        );
        if let Some(plain) = to_lnformula(&ln) {
            assert_eq!(
                lemma_header_line_doc("all-traces", lnformula_doc(&plain)),
                expected,
                "lnformula_doc on {src}"
            );
            assert_eq!(
                doublequoted_nested_doc(lnformula_doc(&plain), 2),
                doublequoted_nested_doc(syntactic_lnformula_doc(&ln), 2),
                "nested body on {src}"
            );
        }
    }
}

/// The atom shapes and binder scopes the samples above leave out, pinned
/// to the oracle's `--parse-only` render of the probe
/// `S0_tests_extra_samples.spthy` (`builtins: hashing, multiset`,
/// `functions: zero/0`): sorted binders, a merged block of same-kind
/// quantifiers with a shadowed name, the binder supply restored after each
/// quantifier block, the `⊏`, `last` and `<` atoms, a pair, a hash and a
/// nullary user symbol inside a fact, and a binder whose source index is not
/// its display index.
#[test]
fn lnformula_doc_renders_the_atom_and_scope_samples() {
    use crate::formula::{from_parser, to_lnformula};
    use tamarin_parser::parser::{parse_formula_str, parse_theory};

    let thy = parse_theory(
        "theory T begin\nbuiltins: hashing, multiset\nfunctions: zero/0\nend",
        &[],
    )
    .unwrap();
    let msig = crate::elaborate::elaborate(&thy)
        .unwrap()
        .signature
        .maude_sig;

    let samples: &[(&str, &[&str])] = &[
        (
            "All ~k $p #i. K(~k, $p) @ #i",
            &["  all-traces \"∀ ~k $p #i. K( ~k, $p ) @ #i\""],
        ),
        (
            "All x. All x. A(x) @ #i",
            &["  all-traces \"∀ x x.1. A( x.1 ) @ #i\""],
        ),
        (
            "All x. All y. P(x, y) @ #i",
            &["  all-traces \"∀ x y. P( x, y ) @ #i\""],
        ),
        (
            "(All x. A(x) @ #i) & (All x. B(x) @ #j)",
            &["  all-traces \"(∀ x. A( x ) @ #i) ∧ (∀ x. B( x ) @ #j)\""],
        ),
        (
            "All x. ((Ex y. A(y) @ #i) & (Ex y. B(y) @ #j)) ==> A(x) @ #k",
            &[
                "  all-traces",
                "  \"∀ x. ((∃ y. A( y ) @ #i) ∧ (∃ y. B( y ) @ #j)) ⇒ (A( x ) @ #k)\"",
            ],
        ),
        ("All x y. x << y", &["  all-traces \"∀ x y. x ⊏ y\""]),
        ("All #i. last(#i)", &["  all-traces \"∀ #i. last(#i)\""]),
        ("All #i #j. #i < #j", &["  all-traces \"∀ #i #j. #i < #j\""]),
        (
            "All x y. P(<x, y>, h(x)) @ #i",
            &["  all-traces \"∀ x y. P( <x, y>, h(x) ) @ #i\""],
        ),
        (
            "All x. P(x, zero) @ #i",
            &["  all-traces \"∀ x. P( x, zero ) @ #i\""],
        ),
        (
            "All x. A(x) @ #i ==> Ex x.1. B(x.1) @ #i",
            &["  all-traces \"∀ x. (A( x ) @ #i) ⇒ (∃ x.1. B( x.1 ) @ #i)\""],
        ),
        (
            "All x.1. A(x.1) @ #i ==> Ex x. B(x) @ #i",
            &["  all-traces \"∀ x. (A( x ) @ #i) ⇒ (∃ x.1. B( x.1 ) @ #i)\""],
        ),
    ];
    for (src, expected_lines) in samples {
        let expected = expected_lines.join("\n");
        let f = parse_formula_str(src, &msig).unwrap();
        let ln = from_parser(&f, &msig).unwrap();
        assert_eq!(
            lemma_header_line_doc("all-traces", syntactic_lnformula_doc(&ln)),
            expected,
            "syntactic_lnformula_doc on {src}"
        );
        let plain = to_lnformula(&ln).unwrap();
        assert_eq!(
            lemma_header_line_doc("all-traces", lnformula_doc(&plain)),
            expected,
            "lnformula_doc on {src}"
        );
    }
}

/// A bare name under a `#`-binder, pinned to the oracle's `--parse-only`
/// render of the probe `S0_bare_name_under_node_binder.spthy`: the right
/// operand of a node equality is a `nodevar` and binds to the `#l` binder,
/// while a fact argument is a `msgvar` that stays free and renames the
/// binder to `#l.1`.  Both printers render every sample alike.
#[test]
fn lnformula_doc_bare_name_under_node_binder() {
    use crate::formula::{from_parser, to_lnformula};
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    let samples: &[(&str, &str, &[&str])] = &[
        (
            "all-traces",
            "All y z #k #l. Alive(y) @ k & Alive(z) @ l ==> #k = l",
            &[
                "  all-traces",
                "  \"∀ y z #k #l. ((Alive( y ) @ #k) ∧ (Alive( z ) @ #l)) ⇒ (#k = #l)\"",
            ],
        ),
        (
            "all-traces",
            "All y z #k #l. Alive(y) @ k & Alive(z) @ l ==> k:node = l",
            &[
                "  all-traces",
                "  \"∀ y z #k #l. ((Alive( y ) @ #k) ∧ (Alive( z ) @ #l)) ⇒ (#k = #l)\"",
            ],
        ),
        (
            "all-traces",
            "All y z #k #l.1. Alive(y) @ k & Alive(z) @ l.1 ==> #k = l.1",
            &[
                "  all-traces",
                "  \"∀ y z #k #l. ((Alive( y ) @ #k) ∧ (Alive( z ) @ #l)) ⇒ (#k = #l)\"",
            ],
        ),
        (
            "all-traces",
            "All l #l. Alive(l) @ l ==> #l = l",
            &["  all-traces \"∀ l #l.1. (Alive( l ) @ #l.1) ⇒ (#l.1 = #l.1)\""],
        ),
        (
            "all-traces",
            "All #l. Alive(l) @ l ==> F",
            &["  all-traces \"∀ #l.1. (Alive( l ) @ #l.1) ⇒ (⊥)\""],
        ),
        (
            "exists-trace",
            "Ex #j1 #l1. Once('a') @ #j1 & Once('b') @ #l1 & #j1 < #l1 \
             & (All a #k. Once(a) @ k ==> (#k = #j1 | #k = l1))",
            &[
                "  exists-trace",
                "  \"∃ #j1 #l1.",
                "    (((Once( 'a' ) @ #j1) ∧ (Once( 'b' ) @ #l1)) ∧ (#j1 < #l1)) ∧",
                "    (∀ a #k. (Once( a ) @ #k) ⇒ ((#k = #j1) ∨ (#k = #l1)))\"",
            ],
        ),
    ];
    for (quant, src, expected_lines) in samples {
        let expected = expected_lines.join("\n");
        let f = parse_formula_str(src, &pair_maude_sig()).unwrap();
        let ln = from_parser(&f, &pair_maude_sig()).unwrap();
        let plain = to_lnformula(&ln).unwrap();
        assert_eq!(
            lemma_header_line_doc(quant, syntactic_lnformula_doc(&ln)),
            expected,
            "syntactic_lnformula_doc on {src}"
        );
        assert_eq!(
            lemma_header_line_doc(quant, lnformula_doc(&plain)),
            expected,
            "lnformula_doc on {src}"
        );
    }
}

/// `prettyAtom = prettyProtoAtom (const emptyDoc)` (Atom.hs:226-229): the
/// sugar-free atom renders as the empty document.
#[test]
fn lnformula_doc_prints_unit2_syntactic_as_empty() {
    let atom: LNFormula = ProtoFormula::Atom(ProtoAtom::Syntactic(Unit2));
    assert_eq!(lnformula_doc(&atom).render(), "");
    let conj: LNFormula =
        ProtoFormula::ltrue().and(ProtoFormula::Atom(ProtoAtom::Syntactic(Unit2)));
    assert_eq!(lnformula_doc(&conj).render(), "(⊤) ∧ ()");
}

/// A `Bound` index with no enclosing binder is HS `extractFree`'s error
/// (Theory/Model/Formula.hs:481-482).
#[test]
#[should_panic(expected = "prettyFormula: illegal bound variable '0'")]
fn lnformula_doc_panics_on_unbound_index() {
    use tamarin_term::lterm::BVar;
    use tamarin_term::vterm::var_term;

    let f: LNFormula = ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Bound(0))));
    let _ = lnformula_doc(&f);
}

// =============================================================================
// Display names bind by the whole variable identity
// =============================================================================

/// `avoidPrecise fm = avoidPreciseVars (frees fm)` (LTerm.hs:714-715) counts a
/// body occurrence as free unless a binder closes it, and `quantify` closes
/// only what equals its `LVar` in name, sort AND index (`v == x`,
/// Theory/Model/Formula.hs:347-352).  A message-sorted `k` under a `~k` or a
/// `$k` binder is therefore free, seeds the display supply for the name `k`,
/// and pushes the binder's own display name to `k.1`.
///
/// Oracle bytes (pinned build): probe `S1_binder_sort_capture.spthy`.
#[test]
fn binder_does_not_capture_a_different_sort() {
    use crate::formula::from_parser;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    for (src, want) in [
        ("Ex ~k #i. Made(k) @ i", "∃ ~k.1 #i. Made( k ) @ #i"),
        ("Ex $k #i. Made(k) @ i", "∃ $k.1 #i. Made( k ) @ #i"),
    ] {
        let f = parse_formula_str(src, &pair_maude_sig()).unwrap();
        let ln = from_parser(&f, &pair_maude_sig()).unwrap();
        assert_eq!(
            syntactic_lnformula_doc(&ln).render_with(FLAT_WIDTH, FLAT_WIDTH),
            want,
            "on {src}"
        );
        assert_eq!(syntactic_lnformula_doc(&ln).render(), want, "on {src}");
    }
}

/// The argument of `last` and the operand after `@` are timepoints, so the
/// bare `x` of `All x y. Alive(y) @ x ==> last(x)` is a node variable that no
/// message binder closes: it stays free and renames the binder to `x.1`.
///
/// Oracle bytes (pinned build): fixture `s1_temporal_positions`.
#[test]
fn bare_binder_used_as_timepoint_is_renamed() {
    use crate::formula::from_parser;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    let f = parse_formula_str("All x y. Alive(y) @ x ==> last(x)", &pair_maude_sig()).unwrap();
    let ln = from_parser(&f, &pair_maude_sig()).unwrap();
    assert_eq!(
        syntactic_lnformula_doc(&ln).render_with(FLAT_WIDTH, FLAT_WIDTH),
        "∀ x.1 y. (Alive( y ) @ #x) ⇒ (last(#x))"
    );
}

/// The `dif` binder and the `seq1` operand of
/// examples/sapic/fast/SCADA/opc_ua_secure_conversation.spthy's
/// `A_Counter_Increases` restriction are both message-sorted variables at
/// index 0, so `Ord LVar` (idx, sort, name — LTerm.hs:546-548) orders the
/// union's operands by name and both printers write `(dif++seq1)`.
///
/// Oracle bytes (pinned build): probe `S1_ac_binder_operand_order.spthy`.
#[test]
fn existential_binder_keeps_ac_operand_order() {
    use crate::elaborate::formula_to_guarded_parsed;
    use crate::formula::from_parser;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::{mset_maude_sig, pair_maude_sig};

    let want = "  \"∀ A B seq1 seq2 #i #j.\n    \
        (((Seq_Sent( A, B, seq1 ) @ #i) ∧ (Seq_Sent( A, B, seq2 ) @ #j)) ∧\n     \
        (#i < #j)) ⇒\n    (∃ dif. seq2 = (dif++seq1))\"";
    // That theory declares `builtins: multiset`, the bit `msetterm`'s `+`
    // level needs (Theory/Text/Parser/Term.hs:195-200).
    let sig = pair_maude_sig().merge(mset_maude_sig());
    let f = parse_formula_str(
        "All A B seq1 seq2 #i #j.(Seq_Sent(A, B, seq1) @ #i \
         & Seq_Sent(A, B, seq2) @ #j & #i < #j ==> Ex dif. seq2 = seq1 + dif )",
        &sig,
    )
    .unwrap();
    let ln = from_parser(&f, &sig).unwrap();
    assert_eq!(
        doublequoted_nested_doc(syntactic_lnformula_doc(&ln), 2),
        want
    );
    // `formulaToGuarded` on the negation is what the solver stores and what
    // the probe prints as the counter-example characterisation; the guard
    // reorders the implication but keeps the union's operands.
    let g =
        formula_to_guarded_parsed(&p::Formula::Not(Box::new(f)), &sig).expect("guarded conversion");
    assert_eq!(
        pretty_guarded_doublequoted(&g),
        "\"∃ A B seq1 seq2 #i #j.\n  \
         (Seq_Sent( A, B, seq1 ) @ #i) ∧ (Seq_Sent( A, B, seq2 ) @ #j)\n \
         ∧\n  (#i < #j) ∧ (∀ dif. (seq2 = (dif++seq1)) ⇒ ⊥)\""
    );
}
