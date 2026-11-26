//! The generator of Maude's `get variants` replies in the algebra library
//! (`tamarin_maude_variants`), on the query of a Maude `get variants`
//! command and the equations of the module the Maude backend writes, under
//! Maude's ranks ([`crate::maude_ranks`]), with its reply as the
//! substitutions Maude's reply parses to.
//!
//! The export is a proposer: nothing is proved about its reply. The caller
//! uses the family only once the certificate checker has accepted it.
//!
//! The request is the command's term as the Maude backend writes it (a fact's
//! arguments `list(cons(t1, cons(t2, … nil)))` as one row of its arguments),
//! and the module's equations in the order the module text lists them, each
//! with the variables the text gives it. The reply lists, for each variant in
//! Maude's order, the binding of every query variable in Maude's order; the
//! variant's variable `k` is Maude's `#(k+1)` (or `%(k+1)`), which the reply
//! parser reads as `FreshVar(k + 1, sort)`. It is read here into the parsed
//! form of Maude's reply, so that the Maude backend's own decoding takes it
//! from there.
use super::maude_unify::{read_unifiers, Rows, Scope};
use super::total::{reply_words, rows_of};
use crate::lean_unification::LEAN_THREAD;
use crate::lean_unification::{initialize, Error, MatchRows, Theory, Watch, WordSlice};
use crate::maude_ranks::MaudeRanks;
use crate::maude_sig::MaudeSig;
use crate::maude_types::{lterm_to_mterm_global, ConvCtx, MSubst, MTerm};
use tamarin_algebra_sys::tamarin_lean_maude_variants;

/// What the generator made of a request.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum VariantsReply {
    /// Maude's variants, in Maude's order, as its reply parses.
    Variants(Vec<MSubst>),
    /// The search gave up: it ran out of fuel or of its work bound, or a
    /// variant does not fit in words.
    GaveUp,
    /// A term is outside the theory's operators.
    Unencodable,
}

/// The equations of the module of `sig` in the order the module text lists
/// them, each side converted as the text writes it (`emit_rrule`: one
/// context for both sides, left side first).
pub(crate) fn module_equations(sig: &MaudeSig) -> Vec<(MTerm, MTerm)> {
    sig.rrules()
        .iter()
        .map(|rule| {
            let mut ctx = ConvCtx::new();
            let lhs = lterm_to_mterm_global(&rule.lhs, &mut ctx);
            let rhs = lterm_to_mterm_global(&rule.rhs, &mut ctx);
            (lhs, rhs)
        })
        .collect()
}

/// Run the generator on the term `query` of a `get variants` command, with
/// the module's `equations` ([`module_equations`]). `fuel` bounds every
/// recursion of the search and its number of layers; `work` bounds the
/// questions of the call (zero for no bound), past which it gives up.
pub(crate) fn maude_variants(
    theory: &Theory,
    ranks: &MaudeRanks,
    equations: &[(MTerm, MTerm)],
    query: &MTerm,
    fuel: u64,
    work: u64,
) -> Result<VariantsReply, Error> {
    let mut rows = Rows {
        lists: true,
        ..Rows::default()
    };
    let mut roots = Vec::with_capacity(1 + 2 * equations.len());
    let Some(root) = rows.term(theory, query) else {
        return Ok(VariantsReply::Unencodable);
    };
    roots.push(root);
    // The bindings are of the query's variables; every variable of a
    // binding is a variable of the variant, `#(k+1)` for `k`.
    let scope = Scope {
        fresh: 0,
        ..Scope::of(&rows)
    };
    for (lhs, rhs) in equations {
        for side in [lhs, rhs] {
            let Some(root) = rows.term(theory, side) else {
                return Ok(VariantsReply::Unencodable);
            };
            roots.push(root);
        }
    }
    let rank_rows = ranks.rows(theory);
    let list_row = ranks.list_row();
    let rank_slices: Vec<_> = rank_rows
        .iter()
        .chain(std::iter::once(&list_row))
        .map(|r| WordSlice::new(r))
        .collect();
    let node_slices: Vec<_> = rows.nodes.iter().map(|r| WordSlice::new(r)).collect();
    initialize()?;
    let mut watch = Watch::new("Maude variants", work);
    let words = LEAN_THREAD.with(|_| {
        // SAFETY: the shim copies every slice, which outlives the call, and
        // writes the watch, which outlives it too. MatchRows owns the single
        // output reference and releases it on every exit.
        let raw = unsafe {
            tamarin_lean_maude_variants(
                theory.flags(),
                WordSlice::new(theory.free()),
                theory.ac(),
                rank_slices.as_ptr(),
                rank_slices.len(),
                fuel,
                node_slices.as_ptr(),
                node_slices.len(),
                WordSlice::new(&roots),
                watch.raw(),
            )
        };
        // A stopped call returned no reply. A call stopped by its work
        // bound gave up; a cancelled one is the caller's to report.
        match watch.finish() {
            Err(Error::SearchBudget { .. }) => return Ok(None),
            other => other?,
        }
        reply_words(&MatchRows::new(raw)?).map(Some)
    })?;
    let Some(words) = words else {
        return Ok(VariantsReply::GaveUp);
    };
    match rows_of(&words).next() {
        Some(Some([1])) => Ok(VariantsReply::Variants(read_unifiers(
            theory, &words, &scope,
        )?)),
        Some(Some([3])) => Ok(VariantsReply::GaveUp),
        // 0 is a malformed request, which the rows above never are.
        Some(Some([status])) => Err(Error::InvalidStatus(*status as u8)),
        _ => Err(Error::InvalidStatus(255)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{fst_sym, pair_sym, pmult_sym, CSym, FunSym};
    use crate::lterm::LSort;
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, minimal_maude_sig, pair_maude_sig};
    use crate::maude_types::MaudeLit;
    use crate::term::Term;
    use std::sync::Arc;

    fn module(sig: &MaudeSig) -> (Arc<Theory>, MaudeRanks, Vec<(MTerm, MTerm)>) {
        (
            Arc::new(Theory::new(sig).unwrap()),
            MaudeRanks::new(sig),
            module_equations(sig),
        )
    }

    fn var(id: u64) -> MTerm {
        Term::Lit(MaudeLit::MaudeVar(id, LSort::Msg))
    }

    fn app(f: FunSym, args: Vec<MTerm>) -> MTerm {
        Term::App(f, args.into())
    }

    /// A command of a captured Maude 3.5.1 session (the Tutorial theory) and
    /// Maude's reply: the generator's reply parses to the same substitutions.
    ///
    /// ```text
    /// get variants in MSG : list(cons(x0:Msg,cons(tamXCFUfst(x0:Msg),cons(tamXCFUfst(x0:Msg),nil)))) .
    /// ```
    #[test]
    fn a_pairing_query_reads_as_maudes_reply() {
        let sig = minimal_maude_sig(false).merge(pair_maude_sig()).refresh();
        let (theory, ranks, equations) = module(&sig);
        let fst = || app(FunSym::NoEq(fst_sym()), vec![var(0)]);
        let query = app(FunSym::List, vec![var(0), fst(), fst()]);
        let reply = maude_variants(&theory, &ranks, &equations, &query, 1 << 20, 0).unwrap();
        let maude = crate::maude_parse::parse_variants_reply_with_sig(
            b"\nVariant 1\nrewrites: 0\n\
              TOP: list(cons(#1:Msg, cons(tamXCFUfst(#1:Msg), cons(tamXCFUfst(#1:Msg), nil))))\n\
              x0:Msg --> #1:Msg\n\nVariant 2\nrewrites: 2\n\
              TOP: list(cons(tamXCFUpair(%1:Msg, %2:Msg), cons(%1:Msg, cons(%1:Msg, nil))))\n\
              x0:Msg --> tamXCFUpair(%1:Msg, %2:Msg)\n\nNo more variants.\nrewrites: 2\n",
            &sig,
        )
        .unwrap();
        assert_eq!(reply, VariantsReply::Variants(maude));
    }

    /// A product of the reply comes back as the reply parser builds it, and
    /// a term outside the theory is not sent.
    #[test]
    fn a_bilinear_query_lists_its_variants() {
        let sig = minimal_maude_sig(false)
            .merge(dh_maude_sig())
            .merge(bp_maude_sig())
            .refresh();
        let (theory, ranks, equations) = module(&sig);
        let pmult = app(FunSym::NoEq(pmult_sym()), vec![var(1), var(2)]);
        let em = app(FunSym::C(CSym::EMap), vec![var(0), pmult]);
        let query = app(FunSym::List, vec![em]);
        match maude_variants(&theory, &ranks, &equations, &query, 1 << 20, 0).unwrap() {
            VariantsReply::Variants(variants) => assert!(variants.len() > 1, "{variants:?}"),
            other => panic!("{other:?}"),
        }
        let foreign = app(FunSym::NoEq(pair_sym()), vec![var(0), var(1)]);
        assert_eq!(
            maude_variants(&theory, &ranks, &equations, &foreign, 1 << 20, 0),
            Ok(VariantsReply::Unencodable)
        );
    }
}
