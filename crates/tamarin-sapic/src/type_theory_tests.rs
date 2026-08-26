// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

use tamarin_theory::pretty_theory::{
    pretty_open_theory_by_module, pretty_open_translated_theory_by_module, BuildInfo,
};
use tamarin_theory::theory::remove_translation_items;

/// The pinned oracle build's `Generated from:` facts (Git revision ef3f0468),
/// so the byte expectations below match the captured stdout verbatim.
fn oracle_build_info() -> BuildInfo {
    BuildInfo {
        tamarin_version: "1.13.0".to_string(),
        maude_version: "3.5.1".to_string(),
        git_revision: "ef3f0468f6f12b81f43289aa64f5d1b9e53eaf59".to_string(),
        git_branch: "HEAD".to_string(),
        compiled_at: "2026-07-31 12:54:17.256348115 UTC".to_string(),
    }
}

fn build(input: &str) -> Theory {
    let parsed = tamarin_parser::parse_theory(input, &[]).unwrap();
    tamarin_theory::elaborate::elaborate(&parsed).unwrap()
}

/// `prettyOpenTheoryByModule`'s `spthy`/`spthytyped` arm.
fn render(thy: &Theory) -> String {
    pretty_open_theory_by_module(
        thy,
        "test.spthy",
        "/* All wellformedness checks were successful. */",
        &oracle_build_info(),
    )
}

/// `prettyOpenTheoryByModule`'s `msr` arm.
fn render_msr(thy: &Theory) -> String {
    pretty_open_translated_theory_by_module(
        &remove_translation_items(thy),
        "test.spthy",
        "/* All wellformedness checks were successful. */",
        &oracle_build_info(),
    )
}

/// `Sapic.typeTheory` on the theory the `spthytyped` print then renders.
fn typed(input: &str) -> Theory {
    let mut thy = build(input);
    type_theory_env(&mut thy).unwrap();
    thy
}

/// `examples/sapic/fast/basic/typing4.spthy`.
const TYPING4: &str = r#"theory Typing
begin
functions: f(bitstring):bitstring, g(lol):lol,
            h/1 // implicitely typed
builtins: multiset
process:
        new x:lol;
        out(x) |         new x:lol; new x.1:lol; event Run(x,x.1);
        out(<x,x.1>)
lemma sanity:
 exists-trace
 "Ex x y #i. Run(x,y)@i & not(x=y)"
end
"#;

/// `-m spthytyped` on typing4 — oracle stdout (pinned build ef3f0468), minus
/// `putStrLn`'s trailing newline.  Exercises: typed/renamed processes
/// (`x.2:lol`…), source-positioned `function:` items DELETED, the six
/// recomputed items appended after the lemma in REVERSE-alphabetical
/// (descending `UserDefinedSym`) order, then the wf + version comments.
#[test]
fn spthytyped_typing4_bytes() {
    let thy = typed(TYPING4);
    let expected = "theory Typing

begin

// Function signature and definition of the equational theory E

builtins: multiset
functions: f/1, fst/1, g/1, h/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

builtin  multiset

process:
  new x.2:lol;
  out(x.2:lol) | new x.3:lol;
                 new x.4:lol;
                 event Run( x.3:lol, x.4:lol );
                 out(<x.3:lol, x.4:lol>)

lemma sanity:
  exists-trace \"\u{2203} x y #i. (Run( x, y ) @ #i) \u{2227} (\u{ac}(x = y))\"
/*
guarded formula characterizing all satisfying traces:
\"\u{2203} x y #i. (Run( x, y ) @ #i) \u{2227} \u{ac}(x = y)\"
*/
by sorry

function: snd (Any) : Any  \u{20}

function: pair (Any, Any) : Any  \u{20}

function: h (Any) : Any  \u{20}

function: g (lol) : lol  \u{20}

function: fst (Any) : Any  \u{20}

function: f (bitstring) : bitstring  \u{20}

/* All wellformedness checks were successful. */

/*
Generated from:
Tamarin version 1.13.0
Maude version 3.5.1
Git revision: ef3f0468f6f12b81f43289aa64f5d1b9e53eaf59, branch: HEAD
Compiled at: 2026-07-31 12:54:17.256348115 UTC
*/

end";
    assert_eq!(render(&thy), expected);
}

/// `examples/sapic/fast/basic/channels4.spthy`.
const CHANNELS4: &str = r#"theory ChannelsTestOne
begin

let P = new a; event Secret(a); out (c, a)
let Q = in(c, x); event Received(x)

process:
new c; (P || Q)

lemma secret :
      "All x #i. ( Secret(x) @ i ==> not (Ex #j. K(x) @ j) )"

lemma received : exists-trace
      "Ex x #i. Received(x) @ i"

end
"#;

/// `-m spthytyped` on channels4 — oracle stdout (pinned build ef3f0468).
/// Exercises `typeAndRenameProcessDef`'s `_pVars` inference: both defs were
/// written WITHOUT formals, and the free `c` of each body becomes the
/// (renamed) formal `(c.1)`; bodies rename `a.1`/`x.1`.
#[test]
fn spthytyped_channels4_bytes() {
    let thy = typed(CHANNELS4);
    let expected = "theory ChannelsTestOne

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

let  P (c.1) = new a.1;
               event Secret( a.1 );
               out(c.1,a.1)

let  Q (c.1) = in(c.1,x.1);
               event Received( x.1 )

process:
  new c.1;
   (P() | Q())

lemma secret:
  all-traces \"\u{2200} x #i. (Secret( x ) @ #i) \u{21d2} (\u{ac}(\u{2203} #j. K( x ) @ #j))\"
/*
guarded formula characterizing all counter-examples:
\"\u{2203} x #i. (Secret( x ) @ #i) \u{2227} \u{2203} #j. (K( x ) @ #j)\"
*/
by sorry

lemma received:
  exists-trace \"\u{2203} x #i. Received( x ) @ #i\"
/*
guarded formula characterizing all satisfying traces:
\"\u{2203} x #i. (Received( x ) @ #i)\"
*/
by sorry

function: snd (Any) : Any  \u{20}

function: pair (Any, Any) : Any  \u{20}

function: fst (Any) : Any  \u{20}

/* All wellformedness checks were successful. */

/*
Generated from:
Tamarin version 1.13.0
Maude version 3.5.1
Git revision: ef3f0468f6f12b81f43289aa64f5d1b9e53eaf59, branch: HEAD
Compiled at: 2026-07-31 12:54:17.256348115 UTC
*/

end";
    assert_eq!(render(&thy), expected);
}

/// `-m msr` on typing4 — oracle stdout (pinned build ef3f0468).  The full
/// SAPIC translation runs (`apply_sapic`, as in normal mode), then the open
/// print drops the whole `TranslationElement` set: no `builtin  multiset`, no
/// `function:` items, no `process:` — but `heuristic: p`, the generated
/// rules, and `single_session` render.
#[test]
fn msr_typing4_bytes() {
    let parsed = tamarin_parser::parse_theory(TYPING4, &[]).unwrap();
    let mut elaborated = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
    let wf = crate::apply::apply_sapic(&mut elaborated, false).unwrap();
    assert!(wf.is_empty());
    let expected = "theory Typing

begin

// Function signature and definition of the equational theory E

builtins: multiset
functions: f/1, fst/1, g/1, h/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

heuristic: p

lemma sanity:
  exists-trace \"\u{2203} x y #i. (Run( x, y ) @ #i) \u{2227} (\u{ac}(x = y))\"
/*
guarded formula characterizing all satisfying traces:
\"\u{2203} x y #i. (Run( x, y ) @ #i) \u{2227} \u{ac}(x = y)\"
*/
by sorry

rule (modulo E) Init[color=#ffffff, process=\"|\", issapicrule,
                     role='Process']:
   [ ] --[ Init( ) ]-> [ State_( ) ]

rule (modulo E) p_0_[color=#ffffff, process=\"|\", issapicrule,
                     role='Process']:
   [ State_( ) ] --> [ State_1( ), State_2( ) ]

rule (modulo E) newxlol_0_1[color=#ffffff, process=\"new x.2:lol;\",
                            issapicrule, role='Process']:
   [ State_1( ), Fr( x.2 ) ] --> [ State_11( x.2 ) ]

rule (modulo E) outxlol_0_11[color=#ffffff, process=\"out(x.2:lol);\",
                             issapicrule, role='Process']:
   [ State_11( x.2 ) ] --> [ State_111( x.2 ), Out( x.2 ) ]

rule (modulo E) p_0_111[color=#ffffff, process=\"0\", issapicrule,
                        role='Process']:
   [ State_111( x.2 ) ] --> [ ]

rule (modulo E) newxlol_0_2[color=#ffffff, process=\"new x.3:lol;\",
                            issapicrule, role='Process']:
   [ State_2( ), Fr( x.3 ) ] --> [ State_21( x.3 ) ]

rule (modulo E) newxlol_0_21[color=#ffffff, process=\"new x.4:lol;\",
                             issapicrule, role='Process']:
   [ State_21( x.3 ), Fr( x.4 ) ] --> [ State_211( x.3, x.4 ) ]

rule (modulo E) eventRunxlolxlol_0_211[color=#ffffff,
                                       process=\"event Run( x.3:lol, x.4:lol );\", issapicrule, role='Process']:
   [ State_211( x.3, x.4 ) ]
  --[ Run( x.3, x.4 ) ]->
   [ State_2111( x.3, x.4 ) ]

rule (modulo E) outxlolxlol_0_2111[color=#ffffff,
                                   process=\"out(<x.3:lol, x.4:lol>);\", issapicrule, role='Process']:
   [ State_2111( x.3, x.4 ) ]
  -->
   [ State_21111( x.3, x.4 ), Out( <x.3, x.4> ) ]

rule (modulo E) p_0_21111[color=#ffffff, process=\"0\", issapicrule,
                          role='Process']:
   [ State_21111( x.3, x.4 ) ] --> [ ]

restriction single_session:
  \"\u{2200} #i #j. ((Init( ) @ #i) \u{2227} (Init( ) @ #j)) \u{21d2} (#i = #j)\"
  // safety formula

/* All wellformedness checks were successful. */

/*
Generated from:
Tamarin version 1.13.0
Maude version 3.5.1
Git revision: ef3f0468f6f12b81f43289aa64f5d1b9e53eaf59, branch: HEAD
Compiled at: 2026-07-31 12:54:17.256348115 UTC
*/

end";
    assert_eq!(render_msr(&elaborated), expected);
}

/// `examples/sapic/fast/basic/let-blocks3.spthy` shape: a parameterless
/// `let P = …` def gets `_pVars: None -> Some([])` — the `()` in
/// `let  P () =` — and the recomputed `function:` set is `snd, pair, hash,
/// fst` (descending key order).
#[test]
fn parameterless_def_gets_some_empty_vars() {
    let src = r#"theory LetBlockCharlyTwo
begin
functions: hash/1
let P =
   new a;
   let h=a in
   out(h)
process: P
end
"#;
    let thy = typed(src);
    // The `Some(vec![])` rule (Typing.hs:224 — always `Just`).
    let defs: Vec<&ProcessDef> = thy.process_defs().collect();
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].vars, Some(Vec::new()));
    // Reverse-BTreeMap emission order (`foldrWithKey` + append).
    let names: Vec<String> = thy
        .function_typing_infos()
        .map(|fti| String::from_utf8_lossy(fti.sym.name()).to_string())
        .collect();
    assert_eq!(names, ["snd", "pair", "hash", "fst"]);
    // Rendered def carries the empty parens and the renamed body (oracle
    // §`let-blocks3`: `let  P () = new a.1; …`).
    let out = render(&thy);
    assert!(
        out.contains("let  P () = new a.1;"),
        "missing typed def header in:\n{out}"
    );
}

/// A `let` binder written `cnext:nat` inside a process.  HS `sapicvar`
/// (Token.hs:506-510) is `lvarNoSuffix` — PREFIX sorts only — plus
/// `option Nothing (colon *> typep)`, so the `:nat` names a SAPIC TYPE and
/// `cnext` stays msg-sorted; the same text in a rule would be the nat-sorted
/// `%cnext`.  Reading it as a sort suffix instead makes the binder a
/// DIFFERENT `LVar` from every later msg-sorted use, so `renameUnique` leaves
/// those uses at index 0 and `typeProcess`'s variable case throws
/// `WFUnbound` — the whole theory dies where HS types it
/// (`examples/sapic/export/5G_AKA/5G_AKA.spthy`,
/// `examples/sapic/export/States/canauth.spthy`).
///
/// Oracle stdout for `-m spthytyped` (pinned build ef3f0468).
#[test]
fn spthytyped_let_binder_typed_nat_stays_msg_sorted() {
    let src = r#"theory T1
begin

builtins: natural-numbers

process:
  in(%c);
  let cnext:nat = %c %+ %1 in
  event E(cnext);
  0

end
"#;
    let thy = typed(src);
    let expected = "theory T1

begin

// Function signature and definition of the equational theory E

builtins: natural-numbers
functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

builtin  natural-numbers

process:
  in(%c.1);
   (event E( cnext.1:nat ) let cnext.1:nat=(%c.1%+%1) 0)

function: snd (Any) : Any  \u{20}

function: pair (Any, Any) : Any  \u{20}

function: fst (Any) : Any  \u{20}

/* All wellformedness checks were successful. */

/*
Generated from:
Tamarin version 1.13.0
Maude version 3.5.1
Git revision: ef3f0468f6f12b81f43289aa64f5d1b9e53eaf59, branch: HEAD
Compiled at: 2026-07-31 12:54:17.256348115 UTC
*/

end";
    assert_eq!(render(&thy), expected);
}

/// A SAPIC condition's variables are `SapicLVar`s, so a process definition
/// written without formals takes their type tags into `_pVars`
/// (`pvars = S.toList (varsProc pr) \\ accBindings pr`, Sapic/Typing.hs:219,
/// over `varsProc = foldMap Data.Set.singleton`,
/// Theory/Sapic/Process.hs:361-362), and `-m=spthytyped` prints each formal
/// with `show :: SapicLVar` (TheoryObject.hs:791-799,
/// Theory/Sapic/Term.hs:108-110).  A timepoint operand of `<` is read by
/// `sapicnodevar` and so carries `node`
/// (Theory/Sapic/Term.hs:99-100#defaultSapicNodeType), while a predicate
/// argument takes `sapicvar` and stays untagged.
///
/// Oracle bytes (pinned build, Git revision ef3f0468; fixture
/// `sapic_cond_type_tag`).
#[test]
fn a_process_def_formal_from_a_condition_keeps_its_type_tag() {
    let src = r#"theory T
begin

predicates: Eq(a, b) <=> a = b, Pred(a, b) <=> a = a

let P = if Eq(x:foo, 'a') then out('yes') else out('no')
let S = if #k < #l then out('yes') else out('no')
let V = if Pred(#p, y) then out('yes') else out('no')

process:
  out('done')

end
"#;
    let thy = typed(src);
    let out = render(&thy);
    for line in [
        "let  P (x.1:foo) = out('yes') if Eq( x.1, 'a' ) out('no')",
        "let  S (#k.1:node,#l.1:node) = out('yes') if #k.1 < #l.1 out('no')",
        "let  V (y.1,#p.1) = out('yes') if Pred( #p.1, y.1 ) out('no')",
    ] {
        assert!(out.contains(line), "missing `{line}` in:\n{out}");
    }
}
