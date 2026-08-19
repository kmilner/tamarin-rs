// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::{parse_theory, parser::DUMMY_LOCATION};

fn parse(src: &str) -> Theory {
    parse_theory(src, &["diff"]).expect("parse")
}

/// A fresh variable that occurs only in a conclusion is unbound.  The sibling
/// checks that pin the body of the unbound-variable report reach that check
/// through action facts (`wf_entry_fills_comma_lists_at_the_report_ribbon`)
/// or through a premise-bound rule (`lookup_binder_is_not_unbound`).  This
/// test covers the conclusion-side fresh-variable branch.
#[test]
fn unbound_var_detected() {
    let t = parse("theory T begin rule R: [] --[ ]-> [ Out(~k) ] end");
    let r = check_theory(&t);
    assert!(topics(&r).contains("Unbound variables"), "report: {:?}", r);
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
    let r = check_theory(&t);
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
    let r = check_theory(&t);
    assert!(topics(&r).contains("Reserved names"));
}

/// The cross-operator order `binop_rank` gives AC operands is the one
/// `tamarin_theory::guarded::funsym_key` encodes from HS's `Ord FunSym`:
/// `Exp < Union < Mult < Xor < NatPlus < AcFct`, with two `AcFct` heads
/// separated by name.  `funsym_key` is the source of truth — `binop_rank`
/// restates the order because `tamarin-parser` is dependency-free and
/// cannot call into `tamarin-theory` — so this test spells the order out
/// for the copy that lives here.
#[test]
fn binop_rank_matches_funsym_key_order() {
    use crate::ast::BinOp as B;
    let ordered = [
        B::Exp,
        B::Union,
        B::Mult,
        B::Xor,
        B::NatPlus,
        B::AcFct("add"),
    ];
    for w in ordered.windows(2) {
        assert!(
            binop_rank(&w[0]) < binop_rank(&w[1]),
            "{:?} must rank before {:?}",
            w[0],
            w[1]
        );
    }
    assert!(binop_rank(&B::AcFct("add")) < binop_rank(&B::AcFct("mix")));
}

/// A FAPP-class operand is ordered by its HS `FunSym` NAME, so `exp` sorts
/// before `pair` and `em` (the sole `C` symbol) after every `NoEq` one.
/// Each body is byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn wf_entry_sorts_fapp_operands_by_funsym_name_like_haskell() {
    // Oracle: `Out( (c^d++h(e)++one++<a, b>++zz(f)) )`
    //   — exp < h < one < pair < zz.
    let t = parse(
        "theory T begin builtins: multiset, diffie-hellman, hashing \
            functions: zz/1 \
            rule Test: [ Out( <a,b> ++ (c^d) ++ h(e) ++ zz(f) ++ 1 ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (c^d++h(e)++one++<a, b>++zz(f)) )"
    );
    // Oracle: `Out( (aenc(m, pk)++c^d++h(e)++<a, b>++(u⊕v)) )`
    //   — the four NoEq heads by name, then the AC-headed operand.
    let t = parse(
        "theory T begin builtins: multiset, diffie-hellman, hashing, xor, \
            asymmetric-encryption \
            rule Test: [ Out( <a,b> ++ (c^d) ++ h(e) ++ (u XOR v) ++ aenc{m}pk ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (aenc(m, pk)++c^d++h(e)++<a, b>++(u⊕v)) )"
    );
    // Oracle: `Out( (DH_neutral++h(c)++one++zz(d)++em(a, b)) )`
    //   — `em` is `C EMap`, which outranks every `NoEq` head.
    let t = parse(
        "theory T begin builtins: multiset, bilinear-pairing, hashing \
            functions: zz/1 \
            rule Test: [ Out( em(a,b) ++ h(c) ++ zz(d) ++ 1 ++ DH_neutral ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (DH_neutral++h(c)++one++zz(d)++em(a, b)) )"
    );
    // Oracle: `Out( (h(c)++<a, b>++%1++zz(d)) )` — `%1` is `tone`.
    let t = parse(
        "theory T begin builtins: multiset, natural-numbers, hashing \
            functions: zz/1 \
            rule Test: [ Out( <a,b> ++ h(c) ++ zz(d) ++ %1 ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (h(c)++<a, b>++%1++zz(d)) )"
    );
}

/// Two same-head operands compare their HS argument lists, which for an AC
/// head is the flattened+sorted multiset and for `pair` the right-nested
/// `pair(a, pair(b, c))` shape.  Both bodies are byte-pinned to the pinned
/// oracle (ef3f0468).
#[test]
fn wf_entry_compares_same_head_operands_on_hs_argument_lists() {
    // Oracle: `Out( ((a*b*c)++(b*z)) )` — the `*` operands compare as the
    // sorted lists [a,b,c] vs [b,z], not as their parser binary trees.
    let t = parse(
        "theory T begin builtins: multiset, diffie-hellman \
            rule Test: [ Out( ((b*c)*a) ++ (b*z) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( ((a*b*c)++(b*z)) )"
    );
    // Oracle: `Out( (<a, z>++<a, b, c>) )` — `<a, b, c>` is
    // `pair(a, pair(b, c))`, whose second argument is a FAPP term and so
    // sorts after the variable `z`.
    let t = parse(
        "theory T begin builtins: multiset \
            rule Test: [ Out( <a,b,c> ++ <a,z> ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (<a, z>++<a, b, c>) )"
    );
}

/// The fact/variable lists of `specialFactsUsage'`,
/// `reservedFactNameRules'` and `unboundCheck` are HS `fsep` paragraph
/// fills, which break before any cell that would pass column
/// [`WF_FILL_RIBBON`] measured from the 4-space nesting.  This is
/// [`WfError::message`]'s flat-cell rendering; every cell here fits inside
/// the ribbon, so it equals the pinned oracle's bytes (ef3f0468).  The
/// layout that ships — including the descent into an over-wide cell —
/// is pinned by `tamarin-theory/tests/wf_fact_fill_layout.rs`.
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
        only(&check_theory(&t), "Special facts"),
        "  rule `R' uses disallowed facts on left-hand-side:\n\
             \x20   Out( a01 ), Out( a02 ), Out( a03 ), Out( a04 ), Out( a05 ),\n\
             \x20   Out( a06 ), Out( a07 ), Out( a08 ), Out( a09 ), Out( a10 ),\n\
             \x20   Out( a11 ), Out( a12 ), Out( a13 ), Out( a14 ), Out( a15 ),\n\
             \x20   Out( a16 ), Out( a17 ), Out( a18 ), Out( a19 ), Out( a20 )"
    );
    // The same 20 names as `K` action facts (10-column cells: six fit at
    // 65, seven would need 76) and as unbound variables (4-column cells:
    // thirteen fit at 64, fourteen would need 69).
    let t = parse(&format!(
        "theory T begin rule R: [] --[ {} ]-> [] end",
        list(20, &|i| format!("K( a{i:02} )"))
    ));
    let report = check_theory(&t);
    assert_eq!(
        only(&report, "Reserved names"),
        "  Rule `R' contains facts with reserved names on the middle:\n\
             \x20   K( a01 ), K( a02 ), K( a03 ), K( a04 ), K( a05 ), K( a06 ),\n\
             \x20   K( a07 ), K( a08 ), K( a09 ), K( a10 ), K( a11 ), K( a12 ),\n\
             \x20   K( a13 ), K( a14 ), K( a15 ), K( a16 ), K( a17 ), K( a18 ),\n\
             \x20   K( a19 ), K( a20 )"
    );
    assert_eq!(
        only(&report, "Unbound variables"),
        "  rule `R' has unbound variables: \n\
             \x20   a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13,\n\
             \x20   a14, a15, a16, a17, a18, a19, a20"
    );
    // The ribbon boundary itself: `Out( a ),` (9) + space + a 57-column
    // fact is exactly 67 and stays on the line; one column more breaks.
    let boundary = |n: usize| -> String {
        let t = parse(&format!(
            "theory T begin rule R: [ Out( a ), Out( '{}' ) ] --[ ]-> [] end",
            "b".repeat(n)
        ));
        only(&check_theory(&t), "Special facts")
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
        only(&check_theory(&t), "Special facts"),
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

/// A filled entry hands its cells to the layout engine as [`WfDoc`]
/// skeletons: one per `prettyLNFact` / `prettyLVar`, with the fact's
/// arguments still separate documents so an over-wide fact can break
/// inside itself.  `message` keeps the flat fill, which can only give such
/// a fact a line of its own.
#[test]
fn filled_entries_carry_their_cells_for_the_layout_engine() {
    let wide = "c".repeat(58);
    let t = parse(&format!(
        "theory T begin rule R: [ Out( '{wide}' ), Out( a ) ] --[ ]-> [] end"
    ));
    let report = check_theory(&t);
    let entry = report
        .iter()
        .find(|e| e.topic == "Special facts")
        .expect("Special facts entry");
    let Some(WfFill::Paragraph { info, cells }) = entry.fill.as_ref() else {
        panic!("fact list carries its cells");
    };
    assert_eq!(info, "rule `R' uses disallowed facts on left-hand-side:");
    assert_eq!(
        *cells,
        vec![
            WfDoc::Fact {
                lead: "Out(".to_string(),
                args: vec![WfDoc::Text(format!("'{wide}'"))],
            },
            WfDoc::Fact {
                lead: "Out(".to_string(),
                args: vec![WfDoc::Text("a".to_string())],
            },
        ]
    );
    assert_eq!(
        entry.message,
        format!(
            "  rule `R' uses disallowed facts on left-hand-side:\n\
                 \x20   Out( '{wide}' ),\n\
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
        only(&check_theory(&t), "Fact arity issues"),
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
        only(&check_theory(&t), "Special facts")
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

/// `cmp_wf_term` only consults `binop_rank` when two operands of one AC
/// chain are headed by DIFFERENT operators, which a wellformedness entry
/// reaches through `pp_wf_fact`.  Both bodies are byte-pinned to the
/// pinned oracle (ef3f0468; the 1.12.0 release emits the same bytes),
/// which reports `Out( ((a++b)⊕(x*y)) )` and
/// `Out( (c^d++(x*y)++(a⊕b)++(%e%+%f)) )` for the two rules below.
#[test]
fn wf_entry_sorts_cross_operator_ac_operands_like_haskell() {
    let t = parse(
        "theory T begin builtins: multiset, xor, diffie-hellman \
            rule Test: [ Out( (x*y) XOR (a++b) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( ((a++b)⊕(x*y)) )"
    );
    let t = parse(
        "theory T begin builtins: multiset, xor, diffie-hellman, natural-numbers \
            rule Test: [ Out( (x*y) ++ (a XOR b) ++ (c^d) ++ (%e %+ %f) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( (c^d++(x*y)++(a⊕b)++(%e%+%f)) )"
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
        only(&check_theory(&t), "Special facts"),
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
        only(&check_theory(&t), "Special facts"),
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
        only(&check_theory(&t), "Special facts"),
        "  rule `Test' uses disallowed facts on left-hand-side:\n    \
             Out( <a, b, c> ), Out( <a, b, c> ), Out( <a, b> )"
    );
}

/// The `Fr`-argument, nat-sort and subterm-convergence checks reach the
/// terms through their own printers, each of which is HS `prettyLNTerm`
/// and so carries the same shape-keyed pair arm.  Byte-pinned to the
/// pinned oracle (ef3f0468).
#[test]
fn wf_pair_headed_terms_render_in_angle_form_in_every_check() {
    // Oracle: `rule `Test' fact: Fr( <a, b> )`.
    let t = parse("theory T begin rule Test: [ Fr( pair(a,b) ) ] --[ ]-> [] end");
    assert_eq!(
        only(
            &check_theory(&t),
            "Fr facts must only use a fresh- or a msg-variable"
        ),
        "rule `Test' fact: Fr( <a, b> )"
    );
    // Oracle:
    //   `  x in term (x%+<a, b>) must be of sort nat`
    //   `  <a, b> in term (x%+<a, b>) must be of sort nat`
    let t = parse(
        "theory T begin builtins: natural-numbers \
            rule Test: [ In( x %+ pair(a,b) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        group_bodies(&check_theory(&t), "Nat Sorts"),
        "  x in term (x%+<a, b>) must be of sort nat\n  \n  \
             <a, b> in term (x%+<a, b>) must be of sort nat"
    );
    // Oracle: `    ff(x, y) = <x, y>`.
    let t = parse(
        "theory T begin functions: ff/2 equations: ff(x,y) = pair(x,y) \
            rule Test: [ ] --[ ]-> [] end",
    );
    let msg = only(&check_theory(&t), "Subterm Convergence Warning");
    assert!(msg.contains("\n    ff(x, y) = <x, y>\n"), "report: {msg:?}");
}

/// The De Bruijn `show` form HS prints for a LEMMA fact is the derived
/// `Show`, which has NO pair arm — every node prints `pair(_,_)`, so the
/// flat parser tuple must be re-nested.  Oracle (ef3f0468) prints
/// `factTerms = [pair(Free x,pair(Free y,Free z))]`.
#[test]
fn wf_lemma_fact_show_form_nests_pairs_right() {
    let t = parse(
        "theory T begin rule Test: [ ] --[ A(x, y) ]-> [ ] \
            lemma L: exists-trace \"Ex #i. A(<x,y,z>) @ i\" end",
    );
    let r = check_theory(&t);
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
        let arity = only(&check_theory(&t), "Fact arity issues");
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

/// The `Nat Sorts` bodies render `prettyLNTerm` over the canonical term,
/// and `nonWellSorted` walks the canonical operand list — so both the
/// offender `err` and the enclosing term `t` print flattened and sorted,
/// and MULTIPLE offenders of one term are reported in that same order.
/// Byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn nat_sorts_renders_ac_terms_canonically() {
    let bodies = |src: &str| -> String {
        let t = parse(&format!(
            "theory T begin \
                 builtins: multiset, xor, bilinear-pairing, natural-numbers \
                 functions: add/2 [AC], zz/1 \
                 rule R: [ In(<a,b,c>) ] --> [ Out( {src} ) ] end"
        ));
        group_bodies(&check_theory(&t), "Nat Sorts")
    };
    assert_eq!(
        bodies("(a*b)*c %+ %1"),
        "  (a*b*c) in term (%1%+(a*b*c)) must be of sort nat"
    );
    assert_eq!(
        bodies("add(add(b,a),c) %+ %1"),
        "  (a add b add c) in term (%1%+(a add b add c)) must be of sort nat"
    );
    assert_eq!(
        bodies("em(b,a) %+ %1"),
        "  em(a, b) in term (%1%+em(a, b)) must be of sort nat"
    );
    assert_eq!(
        bodies("zz(b*a) %+ %1"),
        "  zz((a*b)) in term (%1%+zz((a*b))) must be of sort nat"
    );
    // `fAppAC _ [a] = a`: the offender is `a`, not `add(a)`.
    assert_eq!(
        bodies("add(a) %+ %1"),
        "  a in term (a%+%1) must be of sort nat"
    );
    // `exp` is `NoEq`, so it renders unparenthesised.
    assert_eq!(
        bodies("(a^b) %+ %1"),
        "  a^b in term (a^b%+%1) must be of sort nat"
    );
    // Two offenders under one `%+`: reported in canonical operand order
    // (the LIT `c` before the `Mult`-headed FAPP), not source order.
    assert_eq!(
        bodies("(a*b) %+ c %+ %1"),
        "  c in term (c%+%1%+(a*b)) must be of sort nat\n  \n  \
             (a*b) in term (c%+%1%+(a*b)) must be of sort nat"
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
            &check_theory(&t),
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

/// The bodies of every `topic` entry joined the way `prettyWfErrorReport`
/// joins a topic group (`intersperse (text "")` under one header,
/// Wellformedness.hs:118-125).  For the topics that emit ONE `WfError` per
/// finding, so `report.len()` keeps HS's `N wellformedness check failed` count.
fn group_bodies(report: &WfReport, topic: &str) -> String {
    let hits: Vec<&str> = report
        .iter()
        .filter(|e| e.topic == topic)
        .map(|e| e.message.as_str())
        .collect();
    assert!(!hits.is_empty(), "no {topic:?} entry in {report:?}");
    hits.join("\n  \n")
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

/// Probed against tamarin-prover ef3f0468 on `Out(%a %+ ~x)`:
///   `~x in term (~x%+%a) must be of sort nat`
/// The only operand that the check rejects is the fresh var `~x`.  The check
/// accepts the nat-sorted `%a`.  This matches HS `notOnlyNat`/`isNatVar`,
/// which accepts `NatOne` and nat-sorted *variables*.  The message has no
/// rule name.  `t` is the complete fact-arg term.  The `%+` operands print in
/// `Ord LVar` order (`~x` is `LSortFresh`, `%a` is `LSortNat`,
/// LTerm.hs:165-170) rather than in the source order.  HS's `fAppAC` sorts
/// them at construction.
#[test]
fn nat_sorts_message_format() {
    let t = parse(
        "theory T begin builtins: natural-numbers \
            rule R: [ Fr(~x) ] --[ ]-> [ Out(%a %+ ~x) ] end",
    );
    // One `WfError` per (t, err), body 2-space-nested, header supplied by
    // `prettyWfErrorReport`'s topic group.
    assert_eq!(
        group_bodies(&check_theory(&t), "Nat Sorts"),
        "  ~x in term (~x%+%a) must be of sort nat"
    );
}

/// The check flags a nat *literal* `%'a'`, which is a `Con` name and not a
/// var.  It does not flag the nat var `%y` beside it.  This matches HS
/// `isNatVar`, which is true only for `Lit (Var ..)` with LSortNat.  The
/// single body is pinned byte for byte to the pinned oracle (ef3f0468).
#[test]
fn nat_sorts_flags_nat_literal() {
    let t = parse(
        "theory T begin builtins: natural-numbers \
            rule R: [ Fr(~x) ] --[ ]-> [ Out(%'a' %+ %y) ] end",
    );
    assert_eq!(
        group_bodies(&check_theory(&t), "Nat Sorts"),
        "  %'a' in term (%'a'%+%y) must be of sort nat"
    );
}

/// Probed against tamarin-prover v1.13.0 on `Out(<~k, ~'foo'>)`:
///   rule name uses the HS `quote` form (backtick + apostrophe) and the
///   fresh constant renders via `show (Name FreshName ..)` = `~'foo'`.
#[test]
fn fresh_public_constants_message_format() {
    let t = parse(
        "theory T begin \
            rule R: [ Fr(~k) ] --[ ]-> [ Out(<~k, ~'foo'>) ] end",
    );
    let msg = only(&check_theory(&t), "Fresh public constants");
    assert_eq!(
        msg,
        "Fresh public constants\n======================\n\n  \
             rule `R': fresh public constants are not allowed: ~'foo'"
    );
}

/// A free variable literally named `True` IS reported as unbound — there
/// is no builtin `True` nullary (only `true`), so HS does not suppress it.
/// (Regression for removing `"True"` from `is_known_nullary_constant_name`.)
#[test]
fn variable_named_true_is_unbound() {
    let t = parse("theory T begin rule R: [ ] --[ ]-> [ Out(True) ] end");
    assert!(
        topics(&check_theory(&t)).contains("Unbound variables"),
        "True must be reported as unbound"
    );
}

/// HS `originatesFromLookup` (Wellformedness.hs:501-503, 506-510): the
/// variable a SAPIC `lookup t as v` combinator binds reaches its generated
/// rule through the `IsIn( t, v )` action, so it is not unbound — while an
/// otherwise identical rule without the `process=` attribute is.  The
/// parser never mints [`RuleAttr::Process`] (HS's rule-attribute parser
/// discards a written one), so the generated shape is built by attaching
/// the attribute the SAPIC translation writes.
#[test]
fn lookup_binder_is_not_unbound() {
    let src = "theory T begin \
                   rule L: [ State_1(m.1) ] --[ IsIn(m.1, v.1) ]-> [ State_11(m.1, v.1) ] \
                   end";
    let mut t = parse(src);
    assert_eq!(
        unbound_report(&t).len(),
        1,
        "without the lookup attribute v.1 is unbound"
    );
    for it in t.items.iter_mut() {
        if let TheoryItem::Rule(r) = it {
            r.attributes.push(RuleAttr {
                kind: RuleAttrKind::Process("lookup m.1 as v.1".into()),
                location: DUMMY_LOCATION,
            });
        }
    }
    assert!(
        unbound_report(&t).is_empty(),
        "the lookup binder must be suppressed: {:?}",
        unbound_report(&t)
    );

    // A DIFFERENT free variable in the same lookup rule is still reported:
    // HS compares the offender against the binder, it does not exempt the
    // whole rule.
    let mut t2 = parse(
        "theory T begin \
             rule L: [ State_1(m.1) ] --[ IsIn(m.1, v.1) ]-> [ State_11(m.1, v.1, w.2) ] \
             end",
    );
    for it in t2.items.iter_mut() {
        if let TheoryItem::Rule(r) = it {
            r.attributes.push(RuleAttr {
                kind: RuleAttrKind::Process("lookup m.1 as v.1".into()),
                location: DUMMY_LOCATION,
            });
        }
    }
    let rep = unbound_report(&t2);
    assert_eq!(rep.len(), 1);
    let Some(WfFill::Paragraph { cells, .. }) = rep[0].fill.as_ref() else {
        panic!("unbound entry carries its cells: {rep:?}");
    };
    assert_eq!(
        *cells,
        vec![WfDoc::Text("w.2".to_string())],
        "only the non-binder variable is reported: {rep:?}"
    );
}

/// `equations [convergent]` as the LAST equations block suppresses the
/// whole Subterm Convergence Warning (HS `isUserMarkedConvergent`,
/// last-write-wins), even with a non-convergent regular block present.
#[test]
fn subterm_convergence_global_convergent_guard() {
    let t = parse(
        "theory T begin functions: f/1, g/1, a/0, b/0 \
            equations: f(x) = g(x) \
            equations [convergent]: g(y) = a end",
    );
    assert!(
        !topics(&check_theory(&t)).contains("Subterm Convergence Warning"),
        "global convergent flag (last-write-wins) must suppress the check"
    );
}

/// A `[convergent]` block FIRST followed by a regular block LAST does NOT
/// suppress (last-write-wins => flag false), so the non-convergent
/// equation is reported.
#[test]
fn subterm_convergence_last_write_wins() {
    let t = parse(
        "theory T begin functions: f/1, g/1, a/0, b/0 \
            equations [convergent]: g(y) = a \
            equations: f(x) = g(x) end",
    );
    assert!(
        topics(&check_theory(&t)).contains("Subterm Convergence Warning"),
        "regular block last => flag false => warning fires"
    );
}

/// This is HS's source-literal topic string.  It includes the trailing space
/// (Wellformedness.hs:221#topic).
const LHS_NO_RHS_TOPIC: &str = "Facts occur in the left-hand-side but not in any right-hand-side ";

/// This is `underlineTopic LHS_NO_RHS_TOPIC` plus the `$-$` blank line that
/// opens the body.  The title is 65 characters long, and its trailing space
/// counts.  Below the title is a rule of 65 `=` characters.
const LHS_NO_RHS_HEADER: &str =
    "Facts occur in the left-hand-side but not in any right-hand-side \n\
     =================================================================\n\n";

/// The suggestion arm of `fact_lhs_occur_no_rhs` is the only caller of the
/// live `edit_distance`.  It picks the RHS fact with the smallest name
/// distance.  It does not pick the first one.  `Sesion` is 1 edit from
/// `Session` and 2 edits from `Section`, which the source lists earlier.  So
/// the report suggests `Session`.  A wrong cost term in `edit_distance` makes
/// `Section` win here.
///
/// The body bytes follow HS `showRuleAndFact`/`showFactInfo`
/// (Wellformedness.hs:239-251#showRuleAndFact).  They come from a probe
/// against the pinned oracle (ef3f0468).
#[test]
fn fact_lhs_no_rhs_suggests_the_smallest_edit_distance_not_the_first() {
    let t = parse(
        r#"theory T begin
            rule A: [ Sesion(x) ] --[ ]-> [ ]
            rule B: [ ] --[ ]-> [ Section(x) ]
            rule C: [ ] --[ ]-> [ Session(x) ]
        end"#,
    );
    assert_eq!(
        only(&fact_lhs_occur_no_rhs(&t), LHS_NO_RHS_TOPIC),
        format!(
            "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Sesion' arity: 1 \
             multiplicity: Linear. Perhaps you want to use the fact in rule \"C\":  \
             factName `Session' arity: 1 multiplicity: Linear\n"
        )
    );
}

/// HS `isSimilar` keeps the nearest RHS name only at distance `<= 3`
/// (Wellformedness.hs:192-196#isSimilar).  `Abc` is 4 edits from `Abcdefg`,
/// the only RHS name.  So the line has no "Perhaps you want to use" suffix.
/// The body comes from a probe against the pinned oracle (ef3f0468).
#[test]
fn fact_lhs_no_rhs_drops_the_suggestion_past_distance_three() {
    let t = parse(
        r#"theory T begin
            rule A: [ Abc(x) ] --[ ]-> [ ]
            rule B: [ ] --[ ]-> [ Abcdefg(x) ]
        end"#,
    );
    assert_eq!(
        only(&fact_lhs_occur_no_rhs(&t), LHS_NO_RHS_TOPIC),
        format!(
            "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Abc' arity: 1 \
             multiplicity: Linear\n"
        )
    );
}

/// Both RHS names are 1 edit from `Aaa`.  The tie goes to the first name in
/// RHS source order.  HS `minimalEdFact` takes `listToMaybe . sortOn snd`
/// (Wellformedness.hs:200-201#minimalEdFact), and that sort is stable.  The
/// port's `min_by_key` copies this behaviour.  The body comes from a probe
/// against the pinned oracle (ef3f0468).
#[test]
fn fact_lhs_no_rhs_breaks_distance_ties_by_rhs_source_order() {
    let t = parse(
        r#"theory T begin
            rule A: [ Aaa(x) ] --[ ]-> [ ]
            rule B: [ ] --[ ]-> [ Aax(x) ]
            rule C: [ ] --[ ]-> [ Aay(x) ]
        end"#,
    );
    assert_eq!(
        only(&fact_lhs_occur_no_rhs(&t), LHS_NO_RHS_TOPIC),
        format!(
            "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Aaa' arity: 1 \
             multiplicity: Linear. Perhaps you want to use the fact in rule \"B\":  \
             factName `Aax' arity: 1 multiplicity: Linear\n"
        )
    );
}
