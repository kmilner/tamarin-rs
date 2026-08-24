// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

fn v(name: &str, sort: LSort) -> p::VarSpec {
    p::VarSpec {
        name: name.into(),
        idx: 0,
        sort,
        typ: None,
    }
}

#[test]
fn trivial_formulas() {
    assert_eq!(pretty_formula(&p::Formula::True), "\u{22A4}");
    assert_eq!(pretty_formula(&p::Formula::False), "\u{22A5}");
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
    // ∀ ni #i. F(ni)@#i ⇒ ⊥
    let fa = p::Fact {
        persistent: false,
        name: "F".into(),
        args: vec![p::Term::Var(v("ni", LSort::Msg))],
        annotations: vec![],
    };
    let body = p::Formula::Implies(
        Box::new(p::Formula::Atom(p::Atom::Action(
            fa,
            p::Term::Var(v("i", LSort::Node)),
        ))),
        Box::new(p::Formula::False),
    );
    let f = p::Formula::Forall(
        vec![v("ni", LSort::Msg), v("i", LSort::Node)],
        Box::new(body),
    );
    // The output follows HS.  `Name( args )` keeps the internal spaces, and
    // `ppImp` puts parentheses on both sides of the `⇒`.  The expected bytes
    // come from the oracle (Git revision ef3f0468).
    assert_eq!(
        pretty_formula(&f),
        "\u{2200} ni #i. (F( ni ) @ #i) \u{21D2} (\u{22A5})"
    );
}

#[test]
fn long_quantifier_varlist_wraps() {
    // HS `ppVars = fsep . map (text . show)` (Theory/Model/Formula.hs:503-511, see line 511): a long
    // bound-var list wraps across lines, the continuation aligned after
    // the `∃ ` prefix (column 2, the `<>` nesting offset).  Build an
    // existential with enough vars to overflow the ribbon, body `⊥`.
    let names = [
        "i1", "i2", "j1", "j2", "h1", "h2", "ss", "vote2", "fstcode1", "sndcode1", "fstcode2",
        "sndcode2", "ess", "hv1", "hv2", "hy1", "hy2", "x1", "x2", "adv1", "adv2", "ek", "bb",
        "sks", "y1", "y2", "aa", "ea", "el", "em",
    ];
    let vs: Vec<p::VarSpec> = names.iter().map(|n| v(n, LSort::Msg)).collect();
    let f = p::Formula::Exists(vs, Box::new(p::Formula::False));
    let out = pretty_formula_wrapped(&f, 0);
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
fn pair_term() {
    let t = p::Term::Pair(vec![
        p::Term::Var(v("a", LSort::Msg)),
        p::Term::Var(v("b", LSort::Msg)),
    ]);
    assert_eq!(pretty_term(&t), "<a, b>");
}

/// HS `prettyTerm` renders a user-declared `[AC]` symbol INFIX:
/// `FApp (AC (ACfct (f,_))) ts -> ppTerms (" " ++ BC.unpack f ++ " ") 1
/// "(" ")" ts` (Term/Term.hs:305), so `add(x, y)` prints as `(x add y)`.
/// `lnterm_to_parser` must therefore project it onto the AC-BinOp path,
/// not onto a prefix `App`.
#[test]
fn user_ac_symbol_renders_infix() {
    use tamarin_term::function_symbols::{AcFctSym, AcSym, Constructability, NdcState, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::f_app_ac;
    use tamarin_term::vterm::var_term;

    let sym = AcFctSym::new(
        b"add".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let t = f_app_ac(AcSym::AcFct(sym), vec![x, y]);

    let ast = crate::pretty_theory::lnterm_to_parser(&t);
    assert_eq!(term_to_doc(&ast, &[]).render(), "(x add y)");

    // The same infix form must reach a rendered fact.
    let fa = p::Fact {
        persistent: false,
        name: "F".to_string(),
        args: vec![ast],
        annotations: Vec::new(),
    };
    assert_eq!(fact_to_doc(&fa, &[]).render(), "F( (x add y) )");
}

/// A NULLARY user-AC symbol is HS `FApp (AC (ACfct (f,_))) [] ->
/// text (BC.unpack f)` (Term/Term.hs:304) — the bare name.
#[test]
fn user_ac_symbol_nullary_renders_bare_name() {
    use tamarin_term::function_symbols::{
        AcFctSym, AcSym, Constructability, FunSym, NdcState, Privacy,
    };
    use tamarin_term::term::Term;

    let sym = AcFctSym::new(
        b"add".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let t = Term::App(FunSym::Ac(AcSym::AcFct(sym)), Vec::new().into());
    let ast = crate::pretty_theory::lnterm_to_parser(&t);
    assert_eq!(term_to_doc(&ast, &[]).render(), "add");
}

/// HS `prettyTerm` renders an AC operand list with the operator between the
/// arguments.  It puts the complete application in parentheses
/// (Term/Term.hs:305-309).  `a XOR b` is therefore `(a⊕b)`, with no spaces and
/// with the outer parentheses kept.  The expected bytes come from the oracle
/// (Git revision ef3f0468).
#[test]
fn binop_xor() {
    let t = p::Term::BinOp(
        p::BinOp::Xor,
        Box::new(p::Term::Var(v("a", LSort::Msg))),
        Box::new(p::Term::Var(v("b", LSort::Msg))),
    );
    assert_eq!(pretty_term(&t), "(a\u{2295}b)");
}

#[test]
fn guarded_negation_shortcut() {
    // ∀ [] [Less(i,j)] ⊥  ⇒  rendered as `¬(i < j)`.
    let g = Guarded::GGuarded {
        qua: Quant::All,
        vars: vec![].into(),
        guards: vec![crate::guarded::atom_to_gatom_free(&p::Atom::Less(
            p::Term::Var(v("i", LSort::Node)),
            p::Term::Var(v("j", LSort::Node)),
        ))]
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
fn ac_chain_term() -> p::Term {
    let pair = |n: &str, payload: &str| {
        p::Term::Pair(vec![
            p::Term::PubLit(n.into()),
            p::Term::Var(v(payload, LSort::Fresh)),
        ])
    };
    // ((p1 ++ p2) ++ p3) — binary, same-op; renderer flattens to n-ary.
    p::Term::BinOp(
        p::BinOp::Union,
        Box::new(p::Term::BinOp(
            p::BinOp::Union,
            Box::new(pair("1", "longPayloadNameNumberOne")),
            Box::new(pair("2", "longPayloadNameNumberTwo")),
        )),
        Box::new(pair("3", "longPayloadNameNumberThree")),
    )
}

#[test]
fn ac_union_chain_wraps_in_rule_term() {
    // term_to_doc routes AC ops through ac_op_doc (fcat).  Rendered at a
    // deep indent the chain must break; HS puts `++` at the end of each
    // non-last element's lines and `(`-wraps the whole chain.
    let t = ac_chain_term();
    let doc = term_to_doc(&t, &[]);
    // place at column 20 (a typical proof-tree/rule indent) so it wraps.
    let s = doc.render_at(LINE_LENGTH, RIBBON, 20);
    assert!(
        s.contains("++\n"),
        "AC chain did not wrap with ++ at line end:\n{s}"
    );
    assert!(s.starts_with('('), "AC chain missing leading paren:\n{s}");
    assert!(
        s.trim_end().ends_with(')'),
        "AC chain missing trailing paren:\n{s}"
    );
    // Each pair element renders fully (its payload var appears).
    assert!(s.contains("~longPayloadNameNumberOne"));
    assert!(s.contains("~longPayloadNameNumberThree"));
}

#[test]
fn ac_union_chain_wraps_in_guarded_formula() {
    // gterm_to_doc (guarded path) must wrap the SAME AC chain identically,
    // since HS uses ONE prettyTerm for both rule terms and formula terms.
    // Build `z = <chain>` as a guarded Eq atom and render wrapped.
    let eq = p::Atom::Eq(p::Term::Var(v("z", LSort::Msg)), ac_chain_term());
    let g = Guarded::Atom(crate::guarded::atom_to_gatom_free(&eq));
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
    // hmac('g'^(~longFreshPrivKeyOne*~longFreshPrivKeyTwo), ~longSaltArgument)
    let exp = p::Term::BinOp(
        p::BinOp::Exp,
        Box::new(p::Term::PubLit("g".into())),
        Box::new(p::Term::BinOp(
            p::BinOp::Mult,
            Box::new(p::Term::Var(v("longFreshPrivKeyOne", LSort::Fresh))),
            Box::new(p::Term::Var(v("longFreshPrivKeyTwo", LSort::Fresh))),
        )),
    );
    let t = p::Term::App(
        "hmac".into(),
        vec![
            exp.clone(),
            p::Term::Var(v("longSaltArgumentName", LSort::Fresh)),
        ],
    );
    let doc = term_to_doc(&t, &[]);
    // Deep indent (col 30) so the flat term overruns and the `*`-operands
    // must each break onto their own line at `nest 1` (HS layout).
    let s = doc.render_at(LINE_LENGTH, RIBBON, 30);
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
    let flat = term_to_doc(&exp, &[]).render_at(LINE_LENGTH, RIBBON, 0);
    assert_eq!(flat, "'g'^(~longFreshPrivKeyOne*~longFreshPrivKeyTwo)");
}

// The curly-brace form `name{a}b` in the source is parser-only sugar (the
// `{` branch of `atom_term` in `parser.rs`); HS `prettyTerm`/`ppFun`
// (Term/Term.hs:298-327) has no brace case
// and re-emits these NoEq applications in function form
// `name(a, b)`.  Every term renderer (flat + Doc, parser-AST + GTerm) must
// match that.
#[test]
fn algapp_renders_function_form_flat_term() {
    // sdec{body}key  ->  sdec(body, key)
    let t = p::Term::AlgApp(
        "sdec".into(),
        Box::new(p::Term::Var(v("body", LSort::Msg))),
        Box::new(p::Term::Var(v("key", LSort::Msg))),
    );
    assert_eq!(pretty_term(&t), "sdec(body, key)");
}

#[test]
fn algapp_pair_arg_renders_function_form_flat_term() {
    // senc{a,b}k  ->  AlgApp(senc, <a, b>, k)  ->  senc(<a, b>, k)
    let t = p::Term::AlgApp(
        "senc".into(),
        Box::new(p::Term::Pair(vec![
            p::Term::Var(v("a", LSort::Msg)),
            p::Term::Var(v("b", LSort::Msg)),
        ])),
        Box::new(p::Term::Var(v("k", LSort::Msg))),
    );
    assert_eq!(pretty_term(&t), "senc(<a, b>, k)");
}

#[test]
fn algapp_renders_function_form_doc_term() {
    let t = p::Term::AlgApp(
        "sdec".into(),
        Box::new(p::Term::Var(v("body", LSort::Msg))),
        Box::new(p::Term::Var(v("key", LSort::Msg))),
    );
    assert_eq!(term_to_doc(&t, &[]).render(), "sdec(body, key)");
}

#[test]
fn algapp_renders_function_form_flat_gterm() {
    let g = crate::guarded::GTerm::AlgApp(
        "sdec".into(),
        std::sync::Arc::new(crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
            "body",
            LSort::Msg,
        )))),
        std::sync::Arc::new(crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
            "key",
            LSort::Msg,
        )))),
    );
    let mut s = String::new();
    pp_gterm(&g, &[], &mut s);
    assert_eq!(s, "sdec(body, key)");
}

#[test]
fn algapp_pair_arg_renders_function_form_doc_gterm() {
    // senc{a,b}k as a GTerm -> senc(<a, b>, k) via the Doc renderer
    let g = crate::guarded::GTerm::AlgApp(
        "senc".into(),
        std::sync::Arc::new(crate::guarded::GTerm::Pair(
            vec![
                crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v("a", LSort::Msg))),
                crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v("b", LSort::Msg))),
            ]
            .into(),
        )),
        std::sync::Arc::new(crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
            "k",
            LSort::Msg,
        )))),
    );
    assert_eq!(gterm_to_doc(&g, &[]).render(), "senc(<a, b>, k)");
}

#[test]
fn fact_annotations_render_in_ord_order() {
    // HS `ppAnn` iterates `S.toList ann`, i.e. `FactAnnotation` Ord order
    // (SolveFirst < SolveLast < NoSources), regardless of input order.
    // Supply the annotations scrambled and assert the rendered suffix is
    // sorted (and deduped).
    let fa = p::Fact {
        persistent: false,
        name: "F".into(),
        args: vec![p::Term::Var(v("a", LSort::Msg))],
        annotations: vec![
            p::FactAnnotation::NoSources,
            p::FactAnnotation::SolveFirst,
            p::FactAnnotation::NoSources, // duplicate: deduped like S.fromList
        ],
    };
    assert_eq!(fact_to_doc(&fa, &[]).render(), "F( a )[+, no_precomp]");
}

// =============================================================================
// Locally-nameless printer
// =============================================================================

/// The AST printer's `Doc` for a formula, as the production renderers build
/// it.
fn ast_doc(f: &p::Formula) -> Doc {
    formula_to_doc(f, &[], &mut avoid_precise_formula(f))
}

/// Every sample printed through the AST printer and through the
/// locally-nameless printers, compared through both production wrappers
/// and pinned to the oracle's `--parse-only` render of the lemma-header
/// shape (probe `S0_printer_samples.spthy`).
#[test]
fn lnformula_doc_matches_ast_doc_on_samples() {
    use crate::formula::{from_parser, to_lnformula};
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

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
        let f = parse_formula_str(src, &pair_maude_sig()).unwrap();
        let ln = from_parser(&f).unwrap();
        assert_eq!(
            lemma_header_line_doc("all-traces", ast_doc(&f)),
            expected,
            "AST printer on {src}"
        );
        assert_eq!(
            lemma_header_line_doc("all-traces", syntactic_lnformula_doc(&ln)),
            expected,
            "syntactic_lnformula_doc on {src}"
        );
        assert_eq!(
            doublequoted_nested_doc(syntactic_lnformula_doc(&ln), 2),
            doublequoted_nested_doc(ast_doc(&f), 2),
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
                doublequoted_nested_doc(ast_doc(&f), 2),
                "lnformula_doc on {src}"
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
fn lnformula_doc_matches_ast_doc_on_atom_and_scope_samples() {
    use crate::formula::{from_parser, to_lnformula};
    use tamarin_parser::parser::{parse_formula_str, parse_theory};
    use tamarin_term::maude_sig::pair_maude_sig;

    let thy = parse_theory(
        "theory T begin\nbuiltins: hashing, multiset\nfunctions: zero/0\nend",
        &[],
    )
    .unwrap();
    let _guard = crate::elaborate::set_user_funs_for_theory(&thy);

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
        let f = parse_formula_str(src, &pair_maude_sig()).unwrap();
        let ln = from_parser(&f).unwrap();
        assert_eq!(
            lemma_header_line_doc("all-traces", ast_doc(&f)),
            expected,
            "AST printer on {src}"
        );
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
/// binder to `#l.1`.  All three printers render every sample alike.
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
        let ln = from_parser(&f).unwrap();
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
        assert_eq!(
            lemma_header_line_doc(quant, ast_doc(&f)),
            expected,
            "AST printer on {src}"
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
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    for (src, want) in [
        ("Ex ~k #i. Made(k) @ i", "∃ ~k.1 #i. Made( k ) @ #i"),
        ("Ex $k #i. Made(k) @ i", "∃ $k.1 #i. Made( k ) @ #i"),
    ] {
        let f = parse_formula_str(src, &pair_maude_sig()).unwrap();
        assert_eq!(pretty_formula(&f), want, "on {src}");
        assert_eq!(ast_doc(&f).render(), want, "on {src}");
    }
}

/// The argument of `last` and the operand after `@` are timepoints, so the
/// bare `x` of `All x y. Alive(y) @ x ==> last(x)` is a node variable that no
/// message binder closes: it stays free and renames the binder to `x.1`.
///
/// Oracle bytes (pinned build): fixture `s1_temporal_positions`.
#[test]
fn bare_binder_used_as_timepoint_is_renamed() {
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    let f = parse_formula_str("All x y. Alive(y) @ x ==> last(x)", &pair_maude_sig()).unwrap();
    assert_eq!(
        pretty_formula(&f),
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
    use crate::elaborate::canonicalize_ac_in_formula;
    use crate::guarded::formula_to_guarded;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    let want = "  \"∀ A B seq1 seq2 #i #j.\n    \
        (((Seq_Sent( A, B, seq1 ) @ #i) ∧ (Seq_Sent( A, B, seq2 ) @ #j)) ∧\n     \
        (#i < #j)) ⇒\n    (∃ dif. seq2 = (dif++seq1))\"";
    let f = parse_formula_str(
        "All A B seq1 seq2 #i #j.(Seq_Sent(A, B, seq1) @ #i \
         & Seq_Sent(A, B, seq2) @ #j & #i < #j ==> Ex dif. seq2 = seq1 + dif )",
        &pair_maude_sig(),
    )
    .unwrap();
    assert_eq!(
        formula_doublequoted_nested(&canonicalize_ac_in_formula(&f), 2),
        want
    );
    // `formulaToGuarded` on the negation is what the solver stores and what
    // the probe prints as the counter-example characterisation; the guard
    // reorders the implication but keeps the union's operands.
    let g = formula_to_guarded(&p::Formula::Not(Box::new(f))).expect("guarded conversion");
    assert_eq!(
        pretty_guarded_doublequoted(&g),
        "\"∃ A B seq1 seq2 #i #j.\n  \
         (Seq_Sent( A, B, seq1 ) @ #i) ∧ (Seq_Sent( A, B, seq2 ) @ #j)\n \
         ∧\n  (#i < #j) ∧ (∀ dif. (seq2 = (dif++seq1)) ⇒ ⊥)\""
    );
}
