// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HS `checkEquationsSubtermConvergence` (Wellformedness.hs:1222-1232) — the
//! "Subterm Convergence Warning" over the elaborated signature's subterm-rule
//! Set.

use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::pretty::pretty_nterm;
use tamarin_term::subterm_rule::{is_subterm_convergent, CtxtStRule};

use crate::pretty_hpj::{self as hpj, Doc};

use super::{underline_topic, WfError};

/// Port of HS `checkEquationsSubtermConvergence` (Wellformedness.hs:1222-1232).
///
/// HS works on `thyEquations thy = S.toList (stRules sig)` — the SIGNATURE's
/// subterm-rule Set, NOT the parser-AST `equations:` blocks — and this
/// function reproduces it byte-for-byte from the elaborated `MaudeSig` and
/// the ported HughesPJ printer:
///
///   * order = `sig.st_rules` `BTreeSet` iteration = HS `S.toList` (derived
///     `Ord CtxtStRule`), so e.g. `f1, f2, f3, g` rather than source order
///     `f1, g, f2, f3`;
///   * each equation = `prettyCtxtStRule r = sep [nest 2 lhs, "=" <-> rhs]`
///     (SubtermRule.hs:122-126, see line 125), each side rendered via
///     `pretty_nterm` so a wide RHS wraps (HS `prettyTerm`'s `fsep` ppFun,
///     Term/Term.hs:326-327);
///   * suppressed entirely when `eqConvergent (sig thy)` is set
///     (`isUserMarkedConvergent`, Wellformedness.hs:1211-1214/1285).
///
/// Both drivers reach it through
/// [`super::append_subterm_convergence_report`].
pub fn subterm_convergence_report(sig: &MaudeSig) -> Vec<WfError> {
    // HS: `if not (isUserMarkedConvergent thy) then checkEqs else []`
    // (Wellformedness.hs:1270-1286, see line 1285); `isUserMarkedConvergent thy = eqConvergent (sig thy)`.
    if sig.eq_convergent {
        return Vec::new();
    }
    // HS: `nonSubtermEquations = filterNonSubtermCtxtRule (thyEquations thy)`
    // = filter (not . isSubtermConvergentCtxtRule) (S.toList (stRules sig)).
    let non_conv: Vec<&CtxtStRule> = sig
        .st_rules
        .iter()
        .filter(|r| !is_subterm_convergent(r))
        .collect();
    if non_conv.is_empty() {
        return Vec::new();
    }

    // Equation list: `vcat (map prettyCtxtStRule nonSubtermEquations)`, each
    // `sep [nest 2 lhs, "=" <-> rhs]`, all rendered inside prettyWfErrorReport's
    // outer `nest 2`.  Build it as one HughesPJ Doc so the wrap decision +
    // indentation are HS-exact.
    //
    // WIDTH: the WF report Doc is rendered by HS `addComment c = ... TextItem
    // ("", render c)` (TheoryObject.hs:717-718, see line 718), where `render = P.render` uses the
    // HughesPJ DEFAULT style (`lineLength = 100`, `ribbonsPerLine = 1.5`,
    // `ribbon = round (100 / 1.5) = 67`) — NOT the theory body's
    // `renderDoc` width of 110/73 (Console.hs:242-243,398-399).  The pre-rendered
    // string is then emitted verbatim inside the `/* ... */` comment.  So the
    // equation list wraps at the 100/67 budget, e.g. `f3`/`f6` (inline width 73
    // from column 4) wrap while `f2` (66) stays inline.  This is a SEPARATE
    // width from the `equations:` block, which is part of the theory body and
    // renders at 110/73.
    const WF_LINE_LENGTH: usize = 100;
    const WF_RIBBON: usize = 67; // round(100 / 1.5)
    let eq_lines = {
        let docs: Vec<Doc> = non_conv
            .iter()
            .map(|r| {
                let lhs = pretty_nterm(&r.lhs).nest(2);
                let rhs = pretty_nterm(&r.rhs.term);
                let eq_doc = Doc::text("=").beside_sp(rhs);
                hpj::sep(vec![lhs, eq_doc])
            })
            .collect();
        // Outer `nest 2` from prettyWfErrorReport `(nest 2 . vcat ...)`.
        let mut s = hpj::vcat(docs)
            .nest(2)
            .render_with(WF_LINE_LENGTH, WF_RIBBON);
        s.push('\n');
        s
    };

    // Assemble the full message block (topic header + intro + equations +
    // footer) — byte-identical to the parser-level version, only `eq_lines`
    // differs (proper order + width-wrap).
    let mut msg = String::new();
    msg.push_str(&underline_topic("Subterm Convergence Warning"));
    msg.push('\n'); // blank line before intro (HS `$-$`)
    msg.push_str("  User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue \n");
    msg.push('\n'); // blank line after intro (HS `$-$` before vcat)
    msg.push_str(&eq_lines);
    // HS: `$-$ text " \n For more information..."` — note the leading space.
    msg.push_str("   \n For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html ");

    vec![WfError::new("Subterm Convergence Warning", msg)]
}
