// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The substitution a whole-system pass applies, as
//! `instance Apply LNSubst System` (System.hs) reaches the parts of
//! a constraint system.
//!
//! Haskell threads a bare `LNSubst` through those instances.  The port's pass
//! carries three more things with it — the hashed leaf map it probes, the
//! domain bloom the cached fact fingerprints are tested against, and the
//! rewrite it performs on a disjunction's alternatives — so
//! [`SystemSubst`] is what the constraint-system instances take.  The
//! `Apply` instances themselves sit beside their types: [`crate::fact`],
//! [`crate::rule`], [`crate::constraint::constraints`] and
//! [`crate::tools::subterm_store`].

use tamarin_term::apply::LeafSubst;
use tamarin_term::lterm::{LVar, Name};
use tamarin_term::vterm::VTerm;

use crate::fact::LNFact;
use crate::guarded::Guarded;
use crate::tools::equation_store::LNSubst;

/// One whole-system substitution pass.
///
/// `subst_system_once` (`constraint::solver::reduction`) applies the equation
/// store's substitution; `rename_precise_system`
/// (`constraint::solver::rename_precise`) applies the variable-to-variable
/// renaming it has just allocated.  Both fix their substitution for the whole
/// pass and touch every node, goal, edge and stored term with it, which is
/// what the hashed leaf map and the domain bloom are for.
pub struct SystemSubst<'a> {
    /// The substitution's entries, borrowed into a hash map so each leaf costs
    /// one hash probe instead of a `BTreeMap` descent.  Only probed by key,
    /// never iterated, so the hash order cannot reach output.
    images: tamarin_utils::FastMap<&'a LVar, &'a VTerm<Name, LVar>>,
    /// OR of [`crate::fact::var_bit`] over the domain variables — the same
    /// bit assignment the cached fact bloom carries.
    dom_bloom: u64,
    /// Whether a fact whose bloom shares no bit with `dom_bloom` may be
    /// returned unchanged without descending into its terms.
    fact_skip: bool,
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
            images: subst.iter().collect(),
            dom_bloom: subst.dom().fold(0u64, |b, v| b | crate::fact::var_bit(v)),
            fact_skip,
            disj,
        }
    }

    /// Whether `fa` contains no domain variable, so the `Apply` instance may
    /// answer `None` without walking its terms.  The cached fact bloom is a
    /// superset of the fact's free variables' bits, so a bloom that shares no
    /// bit with `dom_bloom` proves the substitution touches nothing in `fa`.
    pub(crate) fn skips_fact(&self, fa: &LNFact) -> bool {
        self.fact_skip && fa.bloom() & self.dom_bloom == 0
    }

    /// The pass's rewrite of a `Disj` goal's alternatives.
    pub(crate) fn apply_disj(&self, alts: &[Guarded]) -> Option<Vec<Guarded>> {
        (self.disj)(alts)
    }
}

impl LeafSubst for SystemSubst<'_> {
    type Const = Name;
    type Var = LVar;

    fn image_of(&self, v: &LVar) -> Option<&VTerm<Name, LVar>> {
        self.images.get(v).copied()
    }

    fn is_empty(&self) -> bool {
        self.images.is_empty()
    }
}
