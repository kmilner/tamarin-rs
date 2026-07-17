// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Robert Künnemann, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Model/Signature.hs

//! Port of `Theory.Model.Signature` from
//! `lib/theory/src/Theory/Model/Signature.hs`.
//!
//! In Haskell the type is parameterised over the Maude attachment
//! (`Signature MaudeSig` vs `Signature MaudeHandle`).  The Rust port
//! carries the running handle (`tamarin_term::maude_proc::MaudeHandle`)
//! separately on the `ProofContext`, so this module models only the
//! pure `MaudeSig`-carrying variant.

use tamarin_term::maude_sig::{minimal_maude_sig, MaudeSig};

/// A theory signature carrying a Maude signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignaturePure {
    pub maude_sig: MaudeSig,
}

impl SignaturePure {
    pub fn empty(diff: bool) -> Self {
        SignaturePure { maude_sig: minimal_maude_sig(diff) }
    }

    pub fn maude_sig(&self) -> &MaudeSig { &self.maude_sig }
}
