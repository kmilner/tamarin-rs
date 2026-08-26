// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use tamarin_parser::ast as p;
use tamarin_parser::parse_theory;

use super::super::{check_wellformedness, topics};
use super::*;

fn parse(src: &str) -> p::Theory {
    parse_theory(src, &["diff"]).expect("parse")
}

/// The elaborated theory for `src`, as a loader holds it before translation.
fn elaborated(src: &str) -> Theory {
    crate::elaborate::elaborate(&parse(src)).expect("elaborate")
}

/// The whole wellformedness report of a parsed theory, elaborated the way
/// the drivers elaborate it.
fn check(parsed: &p::Theory) -> WfReport {
    check_wellformedness(&crate::elaborate::elaborate(parsed).expect("elaborate"))
}

/// Return the single `WfError` whose topic matches `topic`.
fn only(report: &WfReport, topic: &str) -> String {
    let hits: Vec<&WfError> = report.iter().filter(|e| e.topic == topic).collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one {:?} entry, got {:?}",
        topic,
        report
    );
    hits[0].message.clone()
}

/// The report's bodies joined the way `prettyWfErrorReport` joins a topic
/// group — `intersperse (text "")` under one header, which at the group's
/// 2-space nest is a two-space line (Wellformedness.hs:118-125).
fn bodies(report: &[WfError]) -> String {
    assert!(!report.is_empty(), "empty report");
    report
        .iter()
        .map(|e| e.message.clone())
        .collect::<Vec<_>>()
        .join("\n  \n")
}

/// The parser inlines a rule's `let` bindings into the body it builds
/// (`apply subst (ps0,as0,cs0,rs0)`, Theory/Text/Parser/Rule.hs:119), so the
/// checks read the substituted facts: `Fr(m)` passes the fresh-argument check
/// as a message variable and fails it as `Fr( h(~k) )`.  The end-to-end pin
/// is `scripts/divergence_fixtures/s6_let_conclusion_var`.
#[test]
fn let_inlining_reaches_the_fresh_fact_check() {
    let t = parse(
        r#"theory T begin
            builtins: hashing
            rule Reuse: let m = h(~k) in [Fr(m)] --[ ]-> [Out(m)]
        end"#,
    );
    let r = check(&t);
    assert!(
        topics(&r).contains("Fr facts must only use a fresh- or a msg-variable"),
        "report: {r:?}"
    );
}

/// Rule conclusions also feed the arity table.  The tests that pin the arity
/// body clash on premises (`nullary_fact_keeps_only_the_sep_space`) or on an
/// action/lemma-fact pair (`wf_lemma_fact_show_form_nests_pairs_right`).
#[test]
fn fact_arity_clash_detected() {
    let t = parse(
        r#"theory T begin
            rule R1: [Fr(~x)] --[ ]-> [Foo(~x)]
            rule R2: [Fr(~x), Fr(~y)] --[ ]-> [Foo(~x, ~y)]
        end"#,
    );
    let r = check(&t);
    assert!(topics(&r).contains("Fact arity issues"));
}

/// `KU` in a conclusion is a reserved name.  The sibling test that pins the
/// reserved-name body (`wf_entry_fills_comma_lists_at_the_report_ribbon`)
/// reaches the check through action facts ("on the middle").
#[test]
fn reserved_name_detected() {
    let t = parse(
        r#"theory T begin
            rule R: [Fr(~k)] --[ ]-> [KU(~k)]
        end"#,
    );
    let r = check(&t);
    assert!(topics(&r).contains("Reserved names"));
}

/// A top-level `rule (modulo AC)` block is an intruder rule.  The parser puts
/// it in the theory's intruder-rule cache (`addIntrRuleACs`,
/// Theory/Text/Parser.hs:287) and `theoryRules` folds over the theory items
/// only (TheoryObject.hs:304-306), so the checks read the protocol rules and
/// the `!KU`/`!KD` facts of the block raise nothing.  The end-to-end pin is
/// `scripts/divergence_fixtures/s7_intruder_rule_block`.
#[test]
fn intruder_rule_block_reaches_no_check() {
    let t = parse(
        r#"theory T begin
            builtins: symmetric-encryption
            rule (modulo AC) d_0_sdec:
              [ !KD( senc(m, k) ), !KU( k ) ] --> [ !KD( m ) ]
        end"#,
    );
    let r = check(&t);
    assert!(r.is_empty(), "report: {r:?}");
}

/// The fact lists of `specialFactsUsage'` and `reservedFactNameRules'` are
/// HS `fsep` paragraph fills, which break before any cell that would pass
/// the 67-column ribbon measured from the 4-space nesting.  Every cell here
/// fits inside that ribbon, so the bodies equal the pinned oracle's bytes
/// (ef3f0468).  The whole `/* WARNING … */` block, including the descent
/// into an over-wide cell, is pinned by
/// `tamarin-theory/tests/wf_fact_fill_layout.rs`.
#[test]
fn wf_entry_fills_comma_lists_at_the_report_ribbon() {
    let list = |n: usize, f: &dyn Fn(usize) -> String| -> String {
        (1..=n).map(f).collect::<Vec<_>>().join(", ")
    };
    // 20 uniform 11-column facts: five cells (5*12 + 4 spaces = 64) fit,
    // a sixth (77) does not.
    let t = parse(&format!(
        "theory T begin rule R: [ {} ] --[ ]-> [] end",
        list(20, &|i| format!("Out( a{i:02} )"))
    ));
    assert_eq!(
        only(&check(&t), "Special facts"),
        "  rule `R' uses disallowed facts on left-hand-side:\n\
             \x20   Out( a01 ), Out( a02 ), Out( a03 ), Out( a04 ), Out( a05 ),\n\
             \x20   Out( a06 ), Out( a07 ), Out( a08 ), Out( a09 ), Out( a10 ),\n\
             \x20   Out( a11 ), Out( a12 ), Out( a13 ), Out( a14 ), Out( a15 ),\n\
             \x20   Out( a16 ), Out( a17 ), Out( a18 ), Out( a19 ), Out( a20 )"
    );
    // The same 20 names as `K` action facts: 10-column cells, six fit at 65
    // and seven would need 76.
    let t = parse(&format!(
        "theory T begin rule R: [] --[ {} ]-> [] end",
        list(20, &|i| format!("K( a{i:02} )"))
    ));
    assert_eq!(
        only(&check(&t), "Reserved names"),
        "  Rule `R' contains facts with reserved names on the middle:\n\
             \x20   K( a01 ), K( a02 ), K( a03 ), K( a04 ), K( a05 ), K( a06 ),\n\
             \x20   K( a07 ), K( a08 ), K( a09 ), K( a10 ), K( a11 ), K( a12 ),\n\
             \x20   K( a13 ), K( a14 ), K( a15 ), K( a16 ), K( a17 ), K( a18 ),\n\
             \x20   K( a19 ), K( a20 )"
    );
    // The ribbon boundary itself: `Out( a ),` (9) + space + a 57-column
    // fact is exactly 67 and stays on the line; one column more breaks.
    let boundary = |n: usize| -> String {
        let t = parse(&format!(
            "theory T begin rule R: [ Out( a ), Out( '{}' ) ] --[ ]-> [] end",
            "b".repeat(n)
        ));
        only(&check(&t), "Special facts")
    };
    assert_eq!(
        boundary(48),
        format!(
            "  rule `R' uses disallowed facts on left-hand-side:\n    Out( a ), Out( '{}' )",
            "b".repeat(48)
        )
    );
    assert_eq!(
        boundary(49),
        format!(
            "  rule `R' uses disallowed facts on left-hand-side:\n    Out( a ),\n    Out( '{}' )",
            "b".repeat(49)
        )
    );
    // The fill is greedy, not balanced: alternating 13- and 27-column
    // cells pack 3 then 2-per-line.
    let wide = "z".repeat(15);
    let t = parse(&format!(
        "theory T begin rule R: [ {} ] --[ ]-> [] end",
        (0..6)
            .flat_map(|i| [format!("Out( 'c{i}z' )"), format!("Out( 'w{i}{wide}' )")])
            .collect::<Vec<_>>()
            .join(", ")
    ));
    assert_eq!(
        only(&check(&t), "Special facts"),
        format!(
            "  rule `R' uses disallowed facts on left-hand-side:\n\
                 \x20   Out( 'c0z' ), Out( 'w0{wide}' ), Out( 'c1z' ),\n\
                 \x20   Out( 'w1{wide}' ), Out( 'c2z' ),\n\
                 \x20   Out( 'w2{wide}' ), Out( 'c3z' ),\n\
                 \x20   Out( 'w3{wide}' ), Out( 'c4z' ),\n\
                 \x20   Out( 'w4{wide}' ), Out( 'c5z' ),\n\
                 \x20   Out( 'w5{wide}' )"
        )
    );
}

/// A filled entry hands the layout engine one document per cell, with the
/// fact's arguments still separate documents, so a cell that overruns the
/// ribbon breaks INSIDE itself: `nestShort'`'s enclosing `sep` drops the
/// closing `)` — and the `punctuate comma` comma beside it — onto the
/// following line at the fill's indent.  A single flat cell per line could
/// only give the fact a line of its own.  The end-to-end pin against the
/// oracle is `tamarin-theory/tests/wf_fact_fill_layout.rs`.
#[test]
fn filled_entries_break_inside_an_over_wide_cell() {
    let wide = "c".repeat(58);
    let t = parse(&format!(
        "theory T begin rule R: [ Out( '{wide}' ), Out( a ) ] --[ ]-> [] end"
    ));
    assert_eq!(
        only(&check(&t), "Special facts"),
        format!(
            "  rule `R' uses disallowed facts on left-hand-side:\n\
                 \x20   Out( '{wide}'\n\
                 \x20   ),\n\
                 \x20   Out( a )"
        )
    );
}

/// HS `ppFact n ts = nestShort' (n ++ "(") ")" (fsep …)`
/// (Model/Fact.hs:567-572) = `sep [text lead $$ nest n body, text ")"]`
/// (Text/PrettyPrint/Class.hs:218-223).  With NO arguments the `$$` has
/// nothing to overlap onto the lead's line, so only the `sep` space
/// survives — the oracle
/// (ef3f0468) prints the nullary fact `A( )`, not `A(  )`.
#[test]
fn nullary_fact_keeps_only_the_sep_space() {
    let t = parse(
        "theory T begin rule R1: [ A( ) ] --[ ]-> [] \
             rule R2: [ A( x ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check(&t), "Fact arity issues"),
        "Fact arity issues\n=================\n\n\
             Same fact is used with different arities, i.e., Fact('A','B') is \
             different from Fact('A'). \nCheck the arguments of your facts.\n  \n\n\
             \x20 Fact `a':\n\n\
             \x20   1. Rule `R1', arity 0\n\
             \x20        A( )\n    \n\
             \x20   2. Rule `R2', arity 1\n\
             \x20        A( x )\n  \n"
    );
}

/// A `functions: add/2 [AC]` symbol is an HS `ACfct`, so `prettyTerm`
/// renders it INFIX and parenthesised over the flattened, sorted operand
/// list, and `Ord FunSym` ranks it in the `AC` tier — after every `NoEq`
/// head and after the four builtin AC operators.  Both source spellings
/// (`add(p, q)` and `p add q`) build the same `fAppAC` term.  Every body
/// is byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn wf_entry_renders_user_ac_symbols_infix_like_haskell() {
    let facts = |src: &str| -> String {
        let t = parse(&format!(
            "theory T begin builtins: multiset, xor, diffie-hellman, natural-numbers \
                 functions: add/2 [AC], mix/2 [AC], zz/1 \
                 rule Test: [ Out( {src} ) ] --[ ]-> [] end"
        ));
        only(&check(&t), "Special facts")
            .strip_prefix("  rule `Test' uses disallowed facts on left-hand-side:\n    ")
            .expect("Special facts body")
            .to_string()
    };
    // Oracle `Out( (z++(p add q)) )` for both spellings of the same term.
    assert_eq!(facts("add(p,q) ++ z"), "Out( (z++(p add q)) )");
    assert_eq!(facts("(p add q) ++ z"), "Out( (z++(p add q)) )");
    // HS `naryOpApp` skips the arity check for an `IsAC` symbol, so a
    // ternary application is legal and renders as a three-operand chain;
    // oracle `Out( (z++(p add q add r)) )`.
    assert_eq!(facts("add(p,q,r) ++ z"), "Out( (z++(p add q add r)) )");
    // `fAppAC _ [a] = a`: oracle `Out( (x++z) )` — no `add` node survives.
    assert_eq!(facts("add(x) ++ z"), "Out( (x++z) )");
    // Same-head nesting is flattened and the operands sorted; oracle
    // `Out( (z++(a add b add c)) )`.
    assert_eq!(facts("add(add(b,a),c) ++ z"), "Out( (z++(a add b add c)) )");
    // Two `ACfct` heads separate by name; oracle
    // `Out( (z++(p add q)++(r mix s)) )`.
    assert_eq!(
        facts("add(q,p) ++ mix(s,r) ++ z"),
        "Out( (z++(p add q)++(r mix s)) )"
    );
    // Inside an `add` chain a `NoEq`-headed operand still precedes an
    // AC-headed one; oracle `Out( (zz(c) add (a mix b)) )`.
    assert_eq!(
        facts("add( mix(a,b), zz(c) )"),
        "Out( (zz(c) add (a mix b)) )"
    );
    // Full tier order `NoEq < Union < Mult < Xor < NatPlus < ACfct`, with
    // the two `ACfct` heads by name; oracle
    // `Out( (c^d++zz(u)++(x*y)++(a⊕b)++(%e%+%f)++(p add q)++(r mix s)) )`.
    assert_eq!(
        facts("(x*y) ++ (a XOR b) ++ (c^d) ++ (%e %+ %f) ++ add(p,q) ++ mix(r,s) ++ zz(u)"),
        "Out( (c^d++zz(u)++(x*y)++(a⊕b)++(%e%+%f)++(p add q)++(r mix s)) )"
    );
}

/// HS `prettyTerm`'s pair arm keys on the term SHAPE, so the source
/// spellings `pair(a, b)` and `<a, b>` — which the parser AST keeps apart —
/// both render `<a, b>`, and `split` flattens the right spine across both.
/// Every body is byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn wf_entry_renders_pair_headed_terms_in_angle_form() {
    // Oracle: `Out( (fst(<e, f>)++<a, b>++<c, d>) )` — a `pair(a, b)`
    // operand renders `<a, b>` and sorts as the `pair` head it is.
    let t = parse(
        "theory T begin builtins: multiset \
            rule Test: [ Out( pair(a,b) ++ <c,d> ++ fst(<e,f>) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (fst(<e, f>)++<a, b>++<c, d>) )"
    );
    // Oracle: `Out( <<a, b>, c> ), Out( <a, b, c> ), Out( <<a, b>, c> )`
    //   — a LEFT-nested pair keeps its `<…>` nesting whichever spelling
    //   builds it, while a right-nested one flattens.
    let t = parse(
        "theory T begin \
            rule Test: [ Out( pair(pair(a,b),c) ), Out( <a, <b,c>> ), \
            Out( <pair(a,b), c> ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( <<a, b>, c> ), Out( <a, b, c> ), Out( <<a, b>, c> )"
    );
    // Oracle: `Out( <a, b, c> ), Out( <a, b, c> ), Out( <a, b> )` — the
    // right spine flattens across a change of spelling in either direction.
    let t = parse(
        "theory T begin \
            rule Test: [ Out( pair(a, <b,c>) ), Out( <a, pair(b,c)> ), \
            Out( pair(a,b) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( <a, b, c> ), Out( <a, b, c> ), Out( <a, b> )"
    );
}

/// The `Fr`-argument check renders the whole fact with `prettyLNFact`, which
/// carries the shape-keyed pair arm.  Byte-pinned to the pinned oracle
/// (ef3f0468).
#[test]
fn wf_pair_headed_terms_render_in_angle_form() {
    // Oracle: `rule `Test' fact: Fr( <a, b> )`.
    let t = parse("theory T begin rule Test: [ Fr( pair(a,b) ) ] --[ ]-> [] end");
    assert_eq!(
        only(
            &check(&t),
            "Fr facts must only use a fresh- or a msg-variable"
        ),
        "rule `Test' fact: Fr( <a, b> )"
    );
}

/// The De Bruijn `show` form HS prints for a LEMMA fact is the derived
/// `Show`, which has NO pair arm — every node prints `pair(_,_)`.  Oracle
/// (ef3f0468) prints `factTerms = [pair(Free x,pair(Free y,Free z))]`.
#[test]
fn wf_lemma_fact_show_form_nests_pairs_right() {
    let t = parse(
        "theory T begin rule Test: [ ] --[ A(x, y) ]-> [ ] \
            lemma L: exists-trace \"Ex #i. A(<x,y,z>) @ i\" end",
    );
    let r = check(&t);
    let arity = only(&r, "Fact arity issues");
    assert!(
        arity.contains(
            "Fact {factTag = ProtoFact Linear \"A\" 1, factAnnotations = fromList [], \
                 factTerms = [pair(Free x,pair(Free y,Free z))]}"
        ),
        "arity report: {:?}",
        arity
    );
}

/// The lemma-fact `show` form prints an AC head over the FLATTENED,
/// SORTED operand list and a `C` head (`em`) over the sorted one, because
/// HS's terms are built by `fAppAC`/`fAppC` (Term/Term/Raw.hs:118-134).
///
/// The sort key is the POST-De-Bruijn `Ord`: `quantify`'s `mapLits`
/// rebuilds every node with `fApp` after substituting `Bound i`
/// (Model/Formula.hs:288-291,347-352), so `Bound` precedes `Free` and `Bound i`
/// orders by `i` — the reverse of the source order of the binders.  Every
/// expected string is byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn wf_lemma_fact_show_form_canonicalises_ac_and_c_heads() {
    let terms = |binders: &str, src: &str| -> String {
        let t = parse(&format!(
            "theory T begin \
                 builtins: multiset, xor, bilinear-pairing, natural-numbers \
                 functions: add/2 [AC], zz/1 \
                 rule Test: [ Fr(~n) ] --[ A(~n) ]-> [ Out(~n) ] \
                 lemma L: all-traces \"All {binders} #i. A({src}, 'p') @ i ==> F\" end"
        ));
        let arity = only(&check(&t), "Fact arity issues");
        let head = "factTerms = [";
        let at = arity.find(head).expect("factTerms") + head.len();
        let rest = &arity[at..];
        rest[..rest.find(",'p']}").expect("term end")].to_string()
    };
    // `a` is the OUTER binder, so it is `Bound 2` and `b` is `Bound 1`:
    // sorting by index reverses the source order.
    assert_eq!(terms("a b", "a*b"), "Mult(Bound 1,Bound 2)");
    // Same-head nesting flattens, whichever way it was spelled.
    assert_eq!(terms("a b c", "(a*b)*c"), "Mult(Bound 1,Bound 2,Bound 3)");
    assert_eq!(
        terms("a b c", "add(add(b,a),c)"),
        "add(Bound 1,Bound 2,Bound 3)"
    );
    // `fAppAC _ [a] = a`: no `add` node survives a unary application.
    assert_eq!(terms("a", "add(a)"), "Bound 1");
    // A `Bound` operand precedes a `Free` one, and a `Con` precedes both.
    assert_eq!(terms("a", "x*a"), "Mult(Bound 1,Free x)");
    assert_eq!(terms("a", "'c'*a"), "Mult('c',Bound 1)");
    assert_eq!(terms("a", "~'f'*a*'c'"), "Mult(~'f','c',Bound 1)");
    // Every LIT precedes every FAPP, and `NoEq` heads precede `AC` ones.
    assert_eq!(terms("a", "a*1"), "Mult(Bound 1,one)");
    assert_eq!(terms("a b", "zz(a)*b"), "Mult(Bound 1,zz(Bound 2))");
    assert_eq!(
        terms("a b", "(a*b) ++ (a XOR b)"),
        "Union(Mult(Bound 1,Bound 2),Xor(Bound 1,Bound 2))"
    );
    // `em` sorts (but does not flatten) its two arguments.
    assert_eq!(terms("a b", "em(a,b)"), "em(Bound 1,Bound 2)");
    assert_eq!(terms("a b", "em(zz(a),b)"), "em(Bound 1,zz(Bound 2))");
    // `pair` and `exp` are `NoEq`: their argument order is positional.
    assert_eq!(
        terms("a b", "<b,a>*a"),
        "Mult(Bound 2,pair(Bound 1,Bound 2))"
    );
    assert_eq!(
        terms("a b", "(a^b)*a"),
        "Mult(Bound 2,exp(Bound 2,Bound 1))"
    );
}

/// HS `freshFactArguments'` renders the offending premise with
/// `prettyLNFact` (Wellformedness.hs:569-576, see line 576), so the body
/// carries `prettyLVar`'s `.idx` suffix and `prettyTerm`'s AC/C
/// canonicalisation.  Byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn fresh_fact_argument_renders_the_whole_fact_like_prettylnfact() {
    let body = |src: &str| -> String {
        let t = parse(&format!(
            "theory T begin \
                 builtins: multiset, xor, bilinear-pairing, natural-numbers \
                 functions: add/2 [AC], zz/1 \
                 rule R: [ In(<a,b,c>), Fr( {src} ) ] --> [ ] end"
        ));
        let msg = only(
            &check(&t),
            "Fr facts must only use a fresh- or a msg-variable",
        );
        let at = msg.find("fact: ").expect("fact:") + "fact: ".len();
        msg[at..].to_string()
    };
    assert_eq!(body("(a*b)*c"), "Fr( (a*b*c) )");
    assert_eq!(body("add(add(b,a),c)"), "Fr( (a add b add c) )");
    assert_eq!(body("zz(b*a)"), "Fr( zz((a*b)) )");
    assert_eq!(body("em(b,a)"), "Fr( em(a, b) )");
    assert_eq!(body("$y.2"), "Fr( $y.2 )");
    assert_eq!(body("zz(x.1)"), "Fr( zz(x.1) )");
}

/// HS's `mkProtoFact` dispatches on `map toUpper f`
/// (Theory/Text/Parser/Fact.hs:56-63), so every source spelling of `Ku`
/// carries the `KUFact` tag and no `.spthy` file reaches `reservedFactName`'s
/// `ProtoFact _ name _` pattern (Wellformedness.hs:621-624).  The tag is set
/// here directly.  The expected bytes are HS's `wrappedText header $--$
/// nest 2 (ppFa $-$ text ("show:" ++ show info))` under
/// `prettyWfErrorReport`'s `nest 2`.
#[test]
fn reserved_report_groups_by_origin() {
    use crate::theory::TheoryItem;

    let mut thy = elaborated("theory T begin rule Bad: [ Fr( ~k ) ] --[ ]-> [ Foo( ~k ) ] end");
    for item in &mut thy.items {
        if let TheoryItem::Rule(opr) = item {
            opr.rule.conclusions = opr
                .rule
                .conclusions
                .iter()
                .map(|fa| {
                    Fact::fresh(
                        FactTag::Proto(
                            Multiplicity::Linear,
                            tamarin_term::intern::intern_str("Ku"),
                            1,
                        ),
                        fa.terms.to_vec(),
                    )
                })
                .collect();
        }
    }
    let report = reserved_report(&theory_facts(&thy));
    assert_eq!(report.len(), 1, "report: {report:?}");
    assert_eq!(report[0].topic, "Reserved names");
    assert_eq!(
        report[0].message,
        "  The Rule `Bad' contains facts with reserved names:\n  \n    \
         Ku( ~k )\n    show:(ProtoFact Linear \"Ku\" 1,1,Linear)"
    );
}

/// HS reads a lemma's facts off `_lFormula`, which `applyMacroInLemma` only
/// rewrites in `closeTheoryItem` (CloseRule.hs:85) — after
/// `checkWellformedness`.  `Lemma::original_formula` holds that pre-macro
/// formula, so the cell shows the macro application rather than its body.
#[test]
fn lemma_action_facts_come_from_the_pre_macro_formula() {
    let thy = elaborated(
        "theory T begin builtins: hashing \
             macros: MAC(x) = h(x) \
             rule One: [ ] --[ A(x) ]-> [ ] \
             rule Two: [ ] --[ A(x, y) ]-> [ ] \
             lemma L: exists-trace \"Ex x #i. A(MAC(x)) @ i\" end",
    );
    let lemma = thy.lemmas().next().expect("lemma");
    assert_eq!(
        show_bl_fact(formula_facts(lemma.original_formula.as_ref().expect("original"))[0]),
        "Fact {factTag = ProtoFact Linear \"A\" 1, factAnnotations = fromList [], \
         factTerms = [MAC(Bound 1)]}"
    );
    assert_eq!(
        show_bl_fact(formula_facts(&lemma.formula)[0]),
        "Fact {factTag = ProtoFact Linear \"A\" 1, factAnnotations = fromList [], \
         factTerms = [h(Bound 1)]}"
    );
    let report = fact_usage(&theory_facts(&thy));
    assert!(
        only(&report, "Fact arity issues").contains("factTerms = [MAC(Bound 1)]"),
        "report: {report:?}"
    );
}
/// This is `underlineTopic` of HS's source-literal topic plus the `$-$`
/// blank line that opens the body.  The title is 65 characters long, its
/// trailing space included, so the rule below it is 65 `=` characters.
const LHS_NO_RHS_HEADER: &str =
    "Facts occur in the left-hand-side but not in any right-hand-side \n\
     =================================================================\n\n";

/// The suggestion arm picks the right-hand-side fact with the smallest
/// name distance, not the first one.  `Sesion` is 1 edit from `Session`
/// and 2 from `Section`, which the source lists earlier.  Byte-pinned to
/// the pinned oracle (ef3f0468).
#[test]
fn fact_lhs_no_rhs_suggests_the_smallest_edit_distance_not_the_first() {
    let thy = elaborated(
        r#"theory T begin
        rule A: [ Sesion(x) ] --[ ]-> [ ]
        rule B: [ ] --[ ]-> [ Section(x) ]
        rule C: [ ] --[ ]-> [ Session(x) ]
    end"#,
    );
    assert_eq!(
        bodies(&fact_lhs_occur_no_rhs(&thy)),
        format!(
            "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Sesion' arity: 1 \
             multiplicity: Linear. Perhaps you want to use the fact in rule \"C\":  \
             factName `Session' arity: 1 multiplicity: Linear\n"
        )
    );
}

/// HS `isSimilar` keeps the nearest right-hand-side name only at distance
/// `<= 3` (Wellformedness.hs:192-196).  `Abc` is 4 edits from `Abcdefg`,
/// the only such name, so the line carries no suggestion.  Byte-pinned to
/// the pinned oracle (ef3f0468).
#[test]
fn fact_lhs_no_rhs_drops_the_suggestion_past_distance_three() {
    let thy = elaborated(
        r#"theory T begin
        rule A: [ Abc(x) ] --[ ]-> [ ]
        rule B: [ ] --[ ]-> [ Abcdefg(x) ]
    end"#,
    );
    assert_eq!(
        bodies(&fact_lhs_occur_no_rhs(&thy)),
        format!(
            "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Abc' arity: 1 \
             multiplicity: Linear\n"
        )
    );
}

/// Both right-hand-side names are 1 edit from `Aaa`, and the tie goes to
/// the first of them: HS `minimalEdFact` takes `listToMaybe . sortOn snd`
/// (Wellformedness.hs:200-201), a stable sort.  Byte-pinned to the pinned
/// oracle (ef3f0468).
#[test]
fn fact_lhs_no_rhs_breaks_distance_ties_by_rhs_source_order() {
    let thy = elaborated(
        r#"theory T begin
        rule A: [ Aaa(x) ] --[ ]-> [ ]
        rule B: [ ] --[ ]-> [ Aax(x) ]
        rule C: [ ] --[ ]-> [ Aay(x) ]
    end"#,
    );
    assert_eq!(
        bodies(&fact_lhs_occur_no_rhs(&thy)),
        format!(
            "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Aaa' arity: 1 \
             multiplicity: Linear. Perhaps you want to use the fact in rule \"B\":  \
             factName `Aax' arity: 1 multiplicity: Linear\n"
        )
    );
}
