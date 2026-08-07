// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

fn v(name: &str, sort: p::SortHint) -> p::VarSpec {
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
        args: vec![p::Term::Var(v("ni", p::SortHint::Untagged))],
        annotations: vec![],
    };
    let body = p::Formula::Implies(
        Box::new(p::Formula::Atom(p::Atom::Action(
            fa,
            p::Term::Var(v("i", p::SortHint::Node)),
        ))),
        Box::new(p::Formula::False),
    );
    let f = p::Formula::Forall(
        vec![v("ni", p::SortHint::Untagged), v("i", p::SortHint::Node)],
        Box::new(body),
    );
    let s = pretty_formula(&f);
    assert!(s.contains("\u{2200}"));
    // HS-faithful: `Name( args )` with internal spaces.
    assert!(s.contains("F( ni )"));
    assert!(s.contains("@ #i"));
    assert!(s.contains("\u{21D2}"));
}

#[test]
fn long_quantifier_varlist_wraps() {
    // HS `ppVars = fsep . map (text . show)` (Formula.hs:471-511, see line 508): a long
    // bound-var list wraps across lines, the continuation aligned after
    // the `∃ ` prefix (column 2, the `<>` nesting offset).  Build an
    // existential with enough vars to overflow the ribbon, body `⊥`.
    let names = [
        "i1", "i2", "j1", "j2", "h1", "h2", "ss", "vote2", "fstcode1", "sndcode1", "fstcode2",
        "sndcode2", "ess", "hv1", "hv2", "hy1", "hy2", "x1", "x2", "adv1", "adv2", "ek", "bb",
        "sks", "y1", "y2", "aa", "ea", "el", "em",
    ];
    let vs: Vec<p::VarSpec> = names.iter().map(|n| v(n, p::SortHint::Untagged)).collect();
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
        p::Term::Var(v("a", p::SortHint::Untagged)),
        p::Term::Var(v("b", p::SortHint::Untagged)),
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

#[test]
fn binop_xor() {
    let t = p::Term::BinOp(
        p::BinOp::Xor,
        Box::new(p::Term::Var(v("a", p::SortHint::Untagged))),
        Box::new(p::Term::Var(v("b", p::SortHint::Untagged))),
    );
    let s = pretty_term(&t);
    assert!(s.contains("\u{2295}"));
}

#[test]
fn guarded_negation_shortcut() {
    // ∀ [] [Less(i,j)] ⊥  ⇒  rendered as `¬(i < j)`.
    let g = Guarded::GGuarded {
        qua: Quant::All,
        vars: vec![].into(),
        guards: vec![crate::guarded::atom_to_gatom_free(&p::Atom::Less(
            p::Term::Var(v("i", p::SortHint::Node)),
            p::Term::Var(v("j", p::SortHint::Node)),
        ))]
        .into(),
        body: std::sync::Arc::new(Guarded::Disj(vec![].into())),
    };
    let s = pretty_guarded(&g);
    assert!(s.starts_with("\u{00AC}"));
    assert!(s.contains("#i < #j"));
}

/// Build the parser Term `<'1', g1> ++ <'2', g2> ++ <'3', g3>` where the
/// pair payloads are long enough that the flat AC chain exceeds the ribbon
/// and HS `prettyTerm` (Term/Term.hs:298-327, see line 305-309 `FApp (AC o) -> ppTerms ...`) must
/// wrap it with the `++` operator at line ends and each element `nest 1`'d.
fn ac_chain_term() -> p::Term {
    let pair = |n: &str, payload: &str| {
        p::Term::Pair(vec![
            p::Term::PubLit(n.into()),
            p::Term::Var(v(payload, p::SortHint::Fresh)),
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
    let eq = p::Atom::Eq(p::Term::Var(v("z", p::SortHint::Msg)), ac_chain_term());
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
            Box::new(p::Term::Var(v("longFreshPrivKeyOne", p::SortHint::Fresh))),
            Box::new(p::Term::Var(v("longFreshPrivKeyTwo", p::SortHint::Fresh))),
        )),
    );
    let t = p::Term::App(
        "hmac".into(),
        vec![
            exp.clone(),
            p::Term::Var(v("longSaltArgumentName", p::SortHint::Fresh)),
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
        Box::new(p::Term::Var(v("body", p::SortHint::Untagged))),
        Box::new(p::Term::Var(v("key", p::SortHint::Untagged))),
    );
    assert_eq!(pretty_term(&t), "sdec(body, key)");
}

#[test]
fn algapp_pair_arg_renders_function_form_flat_term() {
    // senc{a,b}k  ->  AlgApp(senc, <a, b>, k)  ->  senc(<a, b>, k)
    let t = p::Term::AlgApp(
        "senc".into(),
        Box::new(p::Term::Pair(vec![
            p::Term::Var(v("a", p::SortHint::Untagged)),
            p::Term::Var(v("b", p::SortHint::Untagged)),
        ])),
        Box::new(p::Term::Var(v("k", p::SortHint::Untagged))),
    );
    assert_eq!(pretty_term(&t), "senc(<a, b>, k)");
}

#[test]
fn algapp_renders_function_form_doc_term() {
    let t = p::Term::AlgApp(
        "sdec".into(),
        Box::new(p::Term::Var(v("body", p::SortHint::Untagged))),
        Box::new(p::Term::Var(v("key", p::SortHint::Untagged))),
    );
    assert_eq!(term_to_doc(&t, &[]).render(), "sdec(body, key)");
}

#[test]
fn algapp_renders_function_form_flat_gterm() {
    let g = crate::guarded::GTerm::AlgApp(
        "sdec".into(),
        std::sync::Arc::new(crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
            "body",
            p::SortHint::Untagged,
        )))),
        std::sync::Arc::new(crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
            "key",
            p::SortHint::Untagged,
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
                crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
                    "a",
                    p::SortHint::Untagged,
                ))),
                crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
                    "b",
                    p::SortHint::Untagged,
                ))),
            ]
            .into(),
        )),
        std::sync::Arc::new(crate::guarded::GTerm::Var(crate::guarded::BVar::Free(v(
            "k",
            p::SortHint::Untagged,
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
        args: vec![p::Term::Var(v("a", p::SortHint::Untagged))],
        annotations: vec![
            p::FactAnnotation::NoSources,
            p::FactAnnotation::SolveFirst,
            p::FactAnnotation::NoSources, // duplicate: deduped like S.fromList
        ],
    };
    assert_eq!(fact_to_doc(&fa, &[]).render(), "F( a )[+, no_precomp]");
}
