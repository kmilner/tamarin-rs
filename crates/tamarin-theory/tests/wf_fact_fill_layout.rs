// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-parity of the wellformedness report's paragraph fills — HS
//! `text info $-$ nest 2 (fsep $ punctuate comma cells)` for
//! `specialFactsUsage'` (Wellformedness.hs:563), `reservedFactNameRules'`
//! (Wellformedness.hs:546) and `unboundCheck` (Wellformedness.hs:497-498),
//! laid out by `tamarin_theory::wf_fill` at `addComment`'s 100/67
//! (TheoryObject.hs:717-718).
//!
//! Every expected block is the pinned oracle's (`ef3f0468`) `/* WARNING … */`
//! comment verbatim, so the fill's break points — between cells, and INSIDE a
//! cell that overruns the ribbon — are pinned to HughesPJ's own decisions.

use tamarin_theory::pretty_theory::format_wf_block;

/// The `/* WARNING … */` comment the load pipelines render, i.e. the block the
/// theory output carries between the source body and the summary: the
/// parser-level pass, then the translated-theory splice that carries
/// `unboundReport` and its siblings.
///
/// The dynamic "Message Derivation Checks" entries both pipelines append are
/// absent here: `--derivcheck-timeout=0` — how the expected blocks below were
/// captured — produces none of them.
fn wf_block(src: &str) -> String {
    let parsed = tamarin_parser::parse_theory(src, &[]).expect("probe parses");
    let mut report = tamarin_theory::wellformedness::pre_translation_wf_report(&parsed);
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("probe elaborates");
    let maude_sig = elaborated.signature.maude_sig.clone();
    tamarin_theory::wellformedness::splice_translated_wf_reports(
        &elaborated,
        &maude_sig,
        &mut report,
    );
    format_wf_block(&report)
}

/// Cells that each fit the 67-column ribbon: `fsep` packs them greedily and
/// breaks BETWEEN cells, re-applying the 4-space nesting.  `fs67`/`fs68` are
/// the one-column boundary — a 67-wide line stays, a 68-wide one breaks.
#[test]
fn fill_breaks_between_cells_that_pass_the_ribbon() {
    assert_eq!(
        wf_block(
            r#"theory FsA
begin

rule R:
  [ Out( a01 ), Out( a02 ), Out( a03 ), Out( a04 ), Out( a05 ), Out( a06 ), Out( a07 ), Out( a08 ), Out( a09 ), Out( a10 ), Out( a11 ), Out( a12 ), Out( a13 ), Out( a14 ), Out( a15 ), Out( a16 ), Out( a17 ), Out( a18 ), Out( a19 ), Out( a20 ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( a01 ), Out( a02 ), Out( a03 ), Out( a04 ), Out( a05 ),
    Out( a06 ), Out( a07 ), Out( a08 ), Out( a09 ), Out( a10 ),
    Out( a11 ), Out( a12 ), Out( a13 ), Out( a14 ), Out( a15 ),
    Out( a16 ), Out( a17 ), Out( a18 ), Out( a19 ), Out( a20 )
*/"#,
        "fsA"
    );
    assert_eq!(
        wf_block(
            r#"theory fs67
begin

rule R:
  [ Out( a ), Out( 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( a ), Out( 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' )
*/"#,
        "fs67"
    );
    assert_eq!(
        wf_block(
            r#"theory fs68
begin

rule R:
  [ Out( a ), Out( 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( a ),
    Out( 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' )
*/"#,
        "fs68"
    );
    assert_eq!(
        wf_block(
            r#"theory fsL57
begin

rule R:
  [ Out( 'ccccccccccccccccccccccccccccccccccccccccccccccccccccccccc' ), Out( a ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( 'ccccccccccccccccccccccccccccccccccccccccccccccccccccccccc' ),
    Out( a )
*/"#,
        "fsL57"
    );
    assert_eq!(
        wf_block(
            r#"theory FsD
begin

rule R:
  [ Out( 'c0z' ), Out( 'c1zzzzzzzzzzzzzzz' ), Out( 'c2z' ), Out( 'c3zzzzzzzzzzzzzzz' ), Out( 'c4z' ), Out( 'c5zzzzzzzzzzzzzzz' ), Out( 'c6z' ), Out( 'c7zzzzzzzzzzzzzzz' ), Out( 'c8z' ), Out( 'c9zzzzzzzzzzzzzzz' ), Out( 'c10' ), Out( 'c11zzzzzzzzzzzzzz' ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( 'c0z' ), Out( 'c1zzzzzzzzzzzzzzz' ), Out( 'c2z' ),
    Out( 'c3zzzzzzzzzzzzzzz' ), Out( 'c4z' ),
    Out( 'c5zzzzzzzzzzzzzzz' ), Out( 'c6z' ),
    Out( 'c7zzzzzzzzzzzzzzz' ), Out( 'c8z' ),
    Out( 'c9zzzzzzzzzzzzzzz' ), Out( 'c10' ),
    Out( 'c11zzzzzzzzzzzzzz' )
*/"#,
        "fsD"
    );
    assert_eq!(
        wf_block(
            r#"theory T
begin

rule R:
  [ Out( 'c0z' ), Out( 'w0zzzzzzzzzzzzzzz' ), Out( 'c1z' ), Out( 'w1zzzzzzzzzzzzzzz' ), Out( 'c2z' ), Out( 'w2zzzzzzzzzzzzzzz' ), Out( 'c3z' ), Out( 'w3zzzzzzzzzzzzzzz' ), Out( 'c4z' ), Out( 'w4zzzzzzzzzzzzzzz' ), Out( 'c5z' ), Out( 'w5zzzzzzzzzzzzzzz' ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( 'c0z' ), Out( 'w0zzzzzzzzzzzzzzz' ), Out( 'c1z' ),
    Out( 'w1zzzzzzzzzzzzzzz' ), Out( 'c2z' ),
    Out( 'w2zzzzzzzzzzzzzzz' ), Out( 'c3z' ),
    Out( 'w3zzzzzzzzzzzzzzz' ), Out( 'c4z' ),
    Out( 'w4zzzzzzzzzzzzzzz' ), Out( 'c5z' ),
    Out( 'w5zzzzzzzzzzzzzzz' )
*/"#,
        "fsG"
    );
}

/// A cell wider than the ribbon is laid out by its own `prettyLNFact` Doc:
/// `nestShort'`'s enclosing `sep` breaks, leaving the closing `)` — and the
/// `punctuate comma` comma beside it — on the following line at the fill's
/// indent.  `fsL58` overruns by a single column, `fs70` by thirteen.
#[test]
fn overwide_fact_drops_its_closing_paren_to_the_next_line() {
    assert_eq!(
        wf_block(
            r#"theory fsL58
begin

rule R:
  [ Out( 'cccccccccccccccccccccccccccccccccccccccccccccccccccccccccc' ), Out( a ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( 'cccccccccccccccccccccccccccccccccccccccccccccccccccccccccc'
    ),
    Out( a )
*/"#,
        "fsL58"
    );
    assert_eq!(
        wf_block(
            r#"theory Fs70
begin

rule R:
  [ Out( 'cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc' ), Out( a ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( 'cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc'
    ),
    Out( a )
*/"#,
        "fs70"
    );
}

/// The descent is the fact's WHOLE layout, not just its parentheses: a pair
/// argument keeps its `ppTerms ", " 1 "<" ">"` `fcat` break points and refills
/// at the `nestShort'` indent (lead width + 1), each broken line keeping the
/// trailing space of the `", "` separator it breaks after.
#[test]
fn overwide_fact_refills_its_own_argument_list() {
    assert_eq!(
        wf_block(
            r#"theory FsE
begin

rule R:
  [ Out( <v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30> ), Out( a ), Out( b ), Out( c ) ]
  --[ ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Special facts
=============

  rule `R' uses disallowed facts on left-hand-side:
    Out( <v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, 
          v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, 
          v26, v27, v28, v29, v30>
    ),
    Out( a ), Out( b ), Out( c )
*/"#,
        "fsE"
    );
}

/// `prettyVarList`'s cells are bare `prettyLVar` texts — no layout of their
/// own — and `reservedFactNameRules'` fills its facts exactly like the
/// `specialFactsUsage'` sibling.  Both topics come from one theory here, so
/// the per-topic grouping is pinned along with the fills.
#[test]
fn variable_and_reserved_name_lists_fill_at_the_same_ribbon() {
    assert_eq!(
        wf_block(
            r#"theory FsC
begin

rule R:
  [ ]
  --[ K( a01 ), K( a02 ), K( a03 ), K( a04 ), K( a05 ), K( a06 ), K( a07 ), K( a08 ), K( a09 ), K( a10 ), K( a11 ), K( a12 ), K( a13 ), K( a14 ), K( a15 ), K( a16 ), K( a17 ), K( a18 ), K( a19 ), K( a20 ) ]->
  [ ]

end
"#
        ),
        r#"/*
WARNING: the following wellformedness checks failed!

Unbound variables
=================

  rule `R' has unbound variables: 
    a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19, a20

Reserved names
==============

  Rule `R' contains facts with reserved names on the middle:
    K( a01 ), K( a02 ), K( a03 ), K( a04 ), K( a05 ), K( a06 ),
    K( a07 ), K( a08 ), K( a09 ), K( a10 ), K( a11 ), K( a12 ),
    K( a13 ), K( a14 ), K( a15 ), K( a16 ), K( a17 ), K( a18 ),
    K( a19 ), K( a20 )
*/"#,
        "fsC"
    );
}
