use super::*;

/// Regression for the column a wrapped `sep` tail lands in when the
/// break happens inside a `sep` whose own first item already wrapped.
///
/// This case mirrors NSPK3 injective_agree's all-counterexamples
/// guarded formula: a GDisj whose disjuncts are GGuarded with
/// recursive `∀`-bodies that themselves wrap.  The expected output is
/// byte-identical to `Text.PrettyPrint.HughesPJ` (pretty-1.1.3.6,
/// verified against the real library at width 50 / ribbon 33).
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

/// Pins the `False` in `sepNB g Empty k ys`'s
/// `nilAboveNest False k (reduceDoc (vcat ys))`
/// (pretty-1.1.3.6 HughesPJ.hs:760-766 — GHC's bundled `pretty` settled on
/// `False` where the upstream XXX comment wavered).
///
/// `nilAboveNest g k q` only branches on that flag when `k > 0`
/// (`not g && k > 0` inlines `k` spaces instead of breaking the line), and on
/// this call site `k` is the leading item's nest offset MINUS its text width.
/// Every `sep` a theory produces has a non-negative nest, so `k` there is
/// always `<= 0` and both flag values agree — which is why the corpus gates
/// and the layout pin above cannot see the flag at all.  A NEGATIVE nest on
/// the first item is the one shape that drives `k` positive: `nest (-5)` less
/// the 2-column `ab` leaves `k = 3`, so the wrapped tail is inlined after
/// three spaces rather than moved to its own line.
///
/// Expected bytes from `Text.PrettyPrint.HughesPJ` (pretty-1.1.3.6) at
/// lineLength 4 / ribbon 4.  Flipping the flag to `True` breaks the line
/// instead and re-nests by `k`, which the outer `nest (-5)` then cancels —
/// yielding `"ab\ncd\nef"`.
#[test]
fn sep_nb_empty_arm_inlines_the_wrapped_tail_at_a_positive_nest() {
    let d = sep(vec![
        Doc::text("ab").nest(-5),
        Doc::text("cd"),
        Doc::text("ef"),
    ]);
    assert_eq!(d.render_with(4, 4), "ab   cd\nef");
}
