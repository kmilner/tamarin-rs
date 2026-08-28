// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The substitution a whole-system pass applies, as
//! `instance Apply LNSubst System` (System.hs:1815-1822) reaches the parts of
//! a constraint system.
//!
//! Haskell threads a bare `LNSubst` through those instances.  The port's pass
//! carries three more things with it — the hashed leaf view it probes, the
//! domain bloom the cached fact fingerprints are tested against, and the
//! rewrite it performs on a disjunction's alternatives — so
//! [`SystemSubst`] is what the constraint-system instances take.  The
//! `Apply` instances themselves sit beside their types: [`crate::fact`],
//! [`crate::rule`], [`crate::constraint::constraints`] and
//! [`crate::tools::subterm_store`].

use std::sync::atomic::Ordering::Relaxed;

use tamarin_term::apply::LeafSubst;
use tamarin_term::lterm::{LVar, Name};
use tamarin_term::subst::SubstView;
use tamarin_term::vterm::VTerm;

use crate::fact::LNFact;
use crate::guarded::Guarded;
use crate::tools::equation_store::LNSubst;

/// Fact descents the [`Apply`] instance reaches, under `TAM_RS_FP_STATS`;
/// `constraint::solver::reduction` prints them.
pub(crate) static FP_FACT_DESCENTS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Descents the bloom fast path skipped (`bloom & dom_bloom == 0`).
pub(crate) static FP_FACT_SKIPS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// One whole-system substitution pass.
///
/// `subst_system_once` (`constraint::solver::reduction`) applies the equation
/// store's substitution; `rename_precise_system`
/// (`constraint::solver::rename_precise`) applies the variable-to-variable
/// renaming it has just allocated.  Both fix their substitution for the whole
/// pass and touch every node, goal, edge and stored term with it, which is
/// what the hashed [`SubstView`] and the domain bloom are for.
pub struct SystemSubst<'a> {
    view: SubstView<'a, Name, LVar>,
    /// OR of [`crate::fact::var_bit`] over the domain variables — the same
    /// bit assignment the cached fact bloom carries.
    dom_bloom: u64,
    /// Whether a fact whose bloom shares no bit with `dom_bloom` may be
    /// returned unchanged without descending into its terms.
    fact_skip: bool,
    /// `TAM_RS_VERIFY_FP`: run the real descent behind every bloom skip and
    /// panic if it finds a change.
    verify_fact_skip: bool,
    /// `TAM_RS_FP_STATS`: count fact descents and bloom skips.
    count_fact_descents: bool,
    /// The rewrite of a `Disj` goal's alternatives, `None` when it leaves the
    /// list unchanged.
    disj: &'a dyn Fn(&[Guarded]) -> Option<Vec<Guarded>>,
}

impl<'a> SystemSubst<'a> {
    /// The pass over `subst`.  `fact_skip` enables the cached-bloom fact fast
    /// path; `disj` rewrites a `Disj` goal's alternatives.
    pub fn new(
        subst: &'a LNSubst,
        fact_skip: bool,
        disj: &'a dyn Fn(&[Guarded]) -> Option<Vec<Guarded>>,
    ) -> Self {
        SystemSubst {
            view: SubstView::new(subst),
            dom_bloom: subst.dom().fold(0u64, |b, v| b | crate::fact::var_bit(v)),
            fact_skip,
            verify_fact_skip: tamarin_utils::env_gate!("TAM_RS_VERIFY_FP"),
            count_fact_descents: tamarin_utils::env_gate!("TAM_RS_FP_STATS"),
            disj,
        }
    }

    /// Whether `fa` contains no domain variable, so the `Apply` instance may
    /// answer `None` without walking its terms.  The cached fact bloom is a
    /// superset of the fact's free variables' bits, so a bloom that shares no
    /// bit with `dom_bloom` proves the substitution touches nothing in `fa`.
    pub(crate) fn skips_fact(&self, fa: &LNFact) -> bool {
        if self.count_fact_descents {
            FP_FACT_DESCENTS.fetch_add(1, Relaxed);
        }
        if !self.fact_skip || fa.bloom() & self.dom_bloom != 0 {
            return false;
        }
        if self.verify_fact_skip {
            self.verify_fact_unchanged(fa);
        }
        if self.count_fact_descents {
            FP_FACT_SKIPS.fetch_add(1, Relaxed);
        }
        true
    }

    /// The pass's rewrite of a `Disj` goal's alternatives.
    pub(crate) fn apply_disj(&self, alts: &[Guarded]) -> Option<Vec<Guarded>> {
        (self.disj)(alts)
    }

    /// Oracle for one bloom skip: descend into `fa` anyway and panic if a
    /// term actually changes, i.e. if the fingerprint missed a domain
    /// variable.  Probes the view directly, so it is independent of the bloom
    /// decision it checks.
    fn verify_fact_unchanged(&self, fa: &LNFact) {
        for t in fa.terms.iter() {
            if let Some(c) = self.view.apply_changed(t) {
                if c != *t {
                    panic!(
                        "TAM_RS_VERIFY_FP: bloom-skip dropped a real change \
                            (fact contained a domain var the fingerprint missed) \
                            — unsound bit assignment"
                    );
                }
            }
        }
    }
}

impl LeafSubst for SystemSubst<'_> {
    type Const = Name;
    type Var = LVar;

    fn image_of(&self, v: &LVar) -> Option<&VTerm<Name, LVar>> {
        self.view.image_of(v)
    }

    fn is_empty(&self) -> bool {
        self.view.is_empty()
    }
}
