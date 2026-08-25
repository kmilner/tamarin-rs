// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Faithful port of HS `checkTerms` (the "Formula terms" wellformedness
//! check) from `lib/theory/src/Theory/Tools/Wellformedness.hs:960-985`.
//!
//! `checkTerms header maudeSig fm` collects the terms appearing in the ATOMS
//! of `fm` (`crate::formula::formula_terms`, HS `formulaTerms`), then keeps
//! as offenders every term that is not `allowed`:
//!
//! ```text
//! allowed (Lit (Var (Bound _)))        = True   -- bound (quantified) variable
//! allowed (Lit (Con (Name PubName _))) = True   -- public constant 'c'
//! allowed (FUnion args)                = all allowed args  -- multiset union ++
//! allowed (FApp o args) | o `member` irreducible = all allowed args
//! allowed _                            = False
//!   where irreducible = irreducibleFunSyms maudeSig
//! ```
//!
//! Everything else — free variables, fresh/nat name literals, applications
//! of REDUCIBLE function symbols (sdec/adec/fst/snd/verify/...) — is an
//! offender.  Offenders are rendered with HS's `show` of the `VTerm Name
//! (BVar LVar)` ([`show_term`], e.g. `snd(sdec(Bound 3,Bound 2))`,
//! `Free #i`), not with the pretty-printer.
//!
//! The formula is the internal one, so its AC and C applications are already
//! in the argument order HS's `fApp` gives them: `from_parser` closes each
//! binder with `quantify`, whose `mapLits` rebuild re-sorts every node it
//! passes (Theory/Model/Formula.hs:347-352), and the outermost binder's pass
//! runs last — so the terms this check inspects are sorted under the ordering
//! in which `Bound` precedes every `Free` and `Bound i` orders by `i`.

use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_term::function_symbols::{AcSym, FunSym};
use tamarin_term::lterm::{BVar, NameTag};
use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::term::{show_term, Term};
use tamarin_term::vterm::Lit;

use crate::formula::{BLNTerm, LNProtoFormula};
use crate::pretty_hpj::{fsep, punctuate, Doc};

/// The fixed render budget for the formula-report WF blocks, determined
/// empirically from HS output: HS lays the whole `/* WARNING ... */`
/// comment at `lineLength = 110` / `ribbon = 73` (see
/// [`crate::pretty_hpj::LINE_LENGTH`] / [`crate::pretty_hpj::RIBBON`]), but
/// the topic body is rendered already indented inside the surrounding
/// `/* ... */` warning frame, so the effective wrap column for the body is
/// 41 columns narrower than `lineLength`, i.e. 110 - 41 = 69. Boundary
/// verified against the real binary: an offender ending at column 69 stays
/// on the header line, at column 70 it wraps.
///
/// CAVEAT: this is a precomputed effective budget, NOT HS's own lineLength.
/// We do not reproduce the outer warning-frame nesting in the `Doc`
/// renderer, so if HS's `lineWidth` (Console.hs:242-243) or the WARNING-frame
/// indentation ever changes, this constant (used at both `render_with`
/// call sites in `render_block` and by
/// [`crate::formula_reports`]'s "Quantifier sorts" block, which HS lays out
/// inside the same frame) must be re-derived against the new binary.
pub(crate) const WF_WIDTH: usize = 69;

/// The constant explanatory paragraph (HS `wrappedText "..."`).  The text
/// never varies, so its wrapped form (at `WF_WIDTH`) is constant too.
const ALLOWED_PARAGRAPH: &str = "The only allowed terms are public constants \
    and bound node and message variables. If you encounter free message \
    variables, then you might have forgotten a #-prefix. Sort prefixes can \
    only be dropped where this is unambiguous. Moreover, reducible function \
    symbols are disallowed.";

/// The signature HS `checkTerms` closes over, for the `irreducibleFunSyms`
/// classification of its `allowed` predicate (Wellformedness.hs:975).
/// [`TermChecker::check`] runs the `checkTerms` arm of HS `formulaReports`
/// (Wellformedness.hs:1003) for one annotated formula, so the combined
/// per-formula pass in [`crate::formula_reports`] can interleave it with the
/// other two arms.
pub struct TermChecker<'a> {
    sig: &'a MaudeSig,
}

impl<'a> TermChecker<'a> {
    pub fn new(sig: &'a MaudeSig) -> Self {
        TermChecker { sig }
    }

    /// The `checkTerms` finding for one annotated formula, if it has
    /// offenders.  `header` is HS's `"Lemma `n'"` / `"Restriction `n'"`.
    pub fn check<S>(&self, header: &str, fm: &LNProtoFormula<S>) -> Option<WfError> {
        let offenders: Vec<String> = crate::formula::formula_terms(fm)
            .into_iter()
            .filter(|t| !self.allowed(t))
            .map(show_term)
            .collect();
        if offenders.is_empty() {
            return None;
        }
        Some(WfError::new(
            "Formula terms",
            render_block(header, &offenders),
        ))
    }

    /// HS `allowed` (Wellformedness.hs:978-985).  `FUnion` is the multiset
    /// union `viewTerm2` gives an `AC Union` head (Term/Term/Raw.hs:185), and
    /// it is allowed whether or not the signature holds it; every other head
    /// has to be a member of `irreducibleFunSyms`.
    fn allowed(&self, t: &BLNTerm) -> bool {
        match t {
            Term::Lit(Lit::Var(BVar::Bound(_))) => true,
            Term::Lit(Lit::Con(n)) => n.tag == NameTag::Pub,
            Term::Lit(_) => false,
            Term::App(FunSym::Ac(AcSym::Union), args) => args.iter().all(|a| self.allowed(a)),
            Term::App(sym, args) => {
                self.sig.irreducible_fun_syms_fast.contains(sym)
                    && args.iter().all(|a| self.allowed(a))
            }
        }
    }
}

/// Port of HS `formulaReports`'s `checkTerms` arm (Wellformedness.hs:1003),
/// run on its own over every lemma + restriction formula (HS `annFormulas`
/// order: all lemmas in theory order, then all restrictions).  Macros and
/// predicates must already be expanded by the caller, as HS's formulas are by
/// the time `formulaReports` reads them.
///
/// The batch / web load pipelines instead go through
/// [`crate::formula_reports::formula_reports`], which interleaves this arm
/// with the other two per formula as HS's `msum` does; this entry point
/// serves callers that want the `checkTerms` findings alone.
pub fn check_terms_wf(thy: &p::Theory, sig: &MaudeSig) -> Vec<WfError> {
    let checker = TermChecker::new(sig);
    crate::formula_reports::ann_formulas(thy)
        .into_iter()
        .filter_map(|(header, fm)| {
            let fm = crate::formula::from_parser(fm, sig).ok()?;
            checker.check(&header, &fm)
        })
        .collect()
}

// =============================================================================
// Block rendering (matches HS prettyWfErrorReport per-topic body)
// =============================================================================

/// Build the full "Formula terms" topic block (underline header + offender
/// fsep line + blank `$--$` line + wrapped paragraph), byte-identical to HS.
fn render_block(header: &str, offenders: &[String]) -> String {
    // fsep $ (text "<header> uses terms of the wrong form:")
    //       : punctuate comma (map (nest 2 . text . quote . show) offenders)
    let mut items = vec![Doc::text(format!(
        "{} uses terms of the wrong form:",
        header
    ))];
    let off_docs: Vec<Doc> = offenders
        .iter()
        .map(|o| Doc::text(format!("`{}'", o)).nest(2))
        .collect();
    items.extend(punctuate(Doc::text(","), off_docs));
    let line1 = fsep(items).nest(2).render_with(WF_WIDTH, WF_WIDTH);

    let words: Vec<Doc> = ALLOWED_PARAGRAPH
        .split_whitespace()
        .map(Doc::text)
        .collect();
    let para = fsep(words).nest(2).render_with(WF_WIDTH, WF_WIDTH);

    let mut out = String::new();
    out.push_str("Formula terms\n=============\n");
    out.push('\n'); // HS `$-$` blank line before the nest-2 body
    out.push_str(&line1);
    out.push('\n');
    out.push_str("  \n"); // HS `$--$` blank line (nest-2 `text ""`)
    out.push_str(&para);
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "check_terms_tests.rs"]
mod tests;
