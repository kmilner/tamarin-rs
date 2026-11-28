// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! HS `ClosedTheory` (ClosedTheory.hs): a theory whose protocol rules went
//! through the loader's closing step. Closing validates explicit variants,
//! removes zero-variant rules and annotates loop breakers.

use std::sync::Arc;

use tamarin_term::function_symbols::{FunSym, NdcState};
use tamarin_term::maude_proc::{MaudeHandle, MaudePool};

use crate::theory::Theory;
use crate::tools::rule_variants::VariantsError;
use crate::wellformedness::WfReport;

/// A closed theory. It derefs to the underlying [`Theory`]; the operations
/// that change it after closing keep the rules closed.
#[derive(Debug, Clone)]
pub struct ClosedTheory(Arc<Theory>);

impl std::ops::Deref for ClosedTheory {
    type Target = Theory;

    fn deref(&self) -> &Theory {
        &self.0
    }
}

/// A theory whose rule variants have passed the checks required for closing.
/// Loaders can inspect the open rules for derivation checks before closing.
pub struct PreparedTheory(Theory);

impl PreparedTheory {
    pub fn prepare(
        mut theory: Theory,
        maude: &MaudeHandle,
        pool: Option<&MaudePool>,
    ) -> Result<(Self, WfReport), VariantsError> {
        let report =
            crate::tools::rule_variants::prepare_theory_rules(&mut theory, maude, pool, true)?;
        Ok((Self(theory), report))
    }

    pub fn theory(&self) -> &Theory {
        &self.0
    }

    pub fn close(mut self, maude: &MaudeHandle) -> Result<ClosedTheory, VariantsError> {
        crate::tools::rule_variants::finish_theory_rules(&mut self.0, maude)?;
        Ok(ClosedTheory(Arc::new(self.0)))
    }
}

/// Validate and close the protocol rules, returning the wellformedness report.
pub fn close_theory(
    theory: Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
) -> Result<(ClosedTheory, WfReport), VariantsError> {
    let (prepared, report) = PreparedTheory::prepare(theory, maude, pool)?;
    Ok((prepared.close(maude)?, report))
}

impl ClosedTheory {
    fn theory_mut(&mut self) -> &mut Theory {
        Arc::make_mut(&mut self.0)
    }

    /// HS `removeLemma` (ClosedTheory.hs): the theory without the named
    /// lemma, or `None` when there is no such lemma.
    pub fn without_lemma(&self, name: &str) -> Option<Self> {
        let mut theory = (*self.0).clone();
        theory
            .remove_lemma(name)
            .then(|| ClosedTheory(Arc::new(theory)))
    }

    /// Adopt `checkCloseIntrRule`'s NDC verdict for `fun_sym` in the
    /// theory's signature (`sign'` of `checkTranslatedTheory`).
    pub fn join_ndc_in_sig(&mut self, fun_sym: FunSym, ndc_state: NdcState) {
        let theory = self.theory_mut();
        let sig = std::mem::take(&mut theory.signature);
        theory.signature = sig.join_ndc_in_sig(fun_sym, ndc_state);
    }

    /// `--auto-sources` on the closed theory
    /// ([`crate::auto_sources::apply_auto_sources`]).
    pub fn apply_auto_sources(
        &mut self,
        maude: MaudeHandle,
        pool: Option<Arc<MaudePool>>,
        ndc_cache: Option<&crate::constraint::solver::context::IntrRuleCache>,
        parameters: crate::constraint::solver::sources::IntegerParameters,
    ) -> Result<bool, crate::prove::ProveError> {
        crate::auto_sources::apply_auto_sources(
            self.theory_mut(),
            maude,
            pool,
            ndc_cache,
            parameters,
        )
    }

    /// HS `applyPartialEvaluation` (Prover.hs) up to its auto-sources step:
    /// refine the rules, then close the refined rules again (the second
    /// `closeTheoryWithMaude`). Returns the evaluation's trace. On an error
    /// the theory is unchanged, since the refined rules are open until the
    /// re-close succeeds.
    pub fn apply_partial_evaluation(
        &mut self,
        maude: &MaudeHandle,
        pool: Option<&MaudePool>,
        style: crate::tools::EvaluationStyle,
    ) -> Result<String, VariantsError> {
        let mut theory = (*self.0).clone();
        let trace = crate::tools::apply_partial_evaluation(&mut theory, maude, style)?;
        crate::tools::rule_variants::reprepare_theory_rules(&mut theory, maude, pool)?;
        self.0 = Arc::new(theory);
        Ok(trace)
    }
}
