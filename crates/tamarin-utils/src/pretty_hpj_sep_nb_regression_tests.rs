use super::*;

/// Checks the column that a wrapped `sep` tail goes to. The break here
/// happens inside a `sep` whose own first item already wraps.
///
/// This case mirrors NSPK3 injective_agree's all-counterexamples
/// guarded formula: a GDisj whose disjuncts are GGuarded with
/// recursive `∀`-bodies that themselves wrap.  The expected output is
/// the same, byte for byte, as the output of `Text.PrettyPrint.HughesPJ`
/// (pretty-1.1.3.6). A run against the real library at width 50 and
/// ribbon 33 verifies these bytes.
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
/// (pretty-1.1.3.6 HughesPJ.hs:760-766). The `pretty` package that GHC
/// bundles settles on `False`. The XXX comment upstream does not settle the
/// choice.
///
/// `nilAboveNest g k q` branches on that flag only when `k > 0`. In that
/// case `not g && k > 0` inlines `k` spaces instead of a line break. At this
/// call site `k` is the nest offset of the leading item minus the text width
/// of that item. Every `sep` that a theory produces has a non-negative nest.
/// `k` there is therefore always `<= 0`, and both values of the flag give
/// the same output. For that reason the corpus gates and the layout pin
/// above cannot see the flag at all. A negative nest on the first item is
/// the one shape that makes `k` positive. Here `nest (-5)` minus the
/// 2-column `ab` leaves `k = 3`. The wrapped tail therefore goes inline
/// after three spaces, and not onto its own line.
///
/// The expected bytes come from `Text.PrettyPrint.HughesPJ`
/// (pretty-1.1.3.6) at lineLength 4 / ribbon 4. A flag value of `True`
/// breaks the line instead and nests again by `k`. The outer `nest (-5)`
/// then cancels that nest, and the output is `"ab\ncd\nef"`.
#[test]
fn sep_nb_empty_arm_inlines_the_wrapped_tail_at_a_positive_nest() {
    let d = sep(vec![
        Doc::text("ab").nest(-5),
        Doc::text("cd"),
        Doc::text("ef"),
    ]);
    assert_eq!(d.render_with(4, 4), "ab   cd\nef");
}
