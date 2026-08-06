use super::*;

/// Regression for the `sepNB`/`fillNBE` `nilAboveNest` column
/// behaviour.
///
/// HS `sepNB g Empty k ys` builds its wrapped tail via
/// `nilAboveNest False k ...` — the flag is `False` (GHC's bundled
/// pretty-1.1.3.6 settled on `False`; see the matching comment on
/// the `sep_nb` `Empty` arm).  `nilAboveNest`'s flag governs where
/// the wrapped tail item lands: this test pins that the second
/// disjunct keeps its expected column rather than being inlined and
/// dropped one column to the left.
///
/// This case mirrors NSPK3 injective_agree's all-counterexamples
/// guarded formula: a GDisj whose disjuncts are GGuarded with
/// recursive `∀`-bodies that themselves wrap.  The expected output is
/// byte-identical to `Text.PrettyPrint.HughesPJ` (verified against the
/// real library at width 50 / ribbon 33).
#[test]
fn nested_sep_disjunct_second_item_column() {
    let opp = |d: Doc| Doc::text("(").beside(d).beside(Doc::text(")"));
    let fa = |atom: &str| {
        let quant = Doc::text("F.");
        let dante = opp(Doc::text(atom)).nest(1);
        let conn = Doc::text("=>");
        let dsucc = Doc::text("RHS").nest(1);
        sep(vec![quant, sep(vec![dante, conn, dsucc])])
    };
    let mkdj = |label: &str| {
        let quant = Doc::text(format!("Q{}.", label));
        let dante = opp(Doc::text("DANTE")).nest(1);
        let conn = Doc::text("C");
        let g1 = opp(fa("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")).beside(Doc::text(" &"));
        let g2 = opp(fa("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"));
        let dsucc = sep(vec![g1, g2]).nest(1);
        sep(vec![quant, sep(vec![dante, conn, dsucc])])
    };
    let mp = punctuate(Doc::text(" |"), vec![opp(mkdj("x")), opp(mkdj("y"))]);
    let out = Doc::text("(")
        .beside(sep(mp))
        .beside(Doc::text(")"))
        .render_with(50, 33);
    let expected = "\
((Qx.
   (DANTE)
  C
   (F.
     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)
    =>
     RHS) &
   (F.
     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)
    =>
     RHS)) |
 (Qy.
   (DANTE)
  C
   (F.
     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)
    =>
     RHS) &
   (F.
     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)
    =>
     RHS)))";
    assert_eq!(out, expected, "got:\n{out}");
}
