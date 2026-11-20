import Tamarin.MaudeOperations
import Tamarin.MixedUnification
import Tamarin.VariantReconstruction
import Tamarin.StableVariants
import Tamarin.NarrowingFrontier

namespace Tamarin.MaudeOperations
open Rewriting
variable {s : Signature}

/-- Constructor, exclusion and staged normalization proofs which establish a
stable representative for every component all implement this reply contract. -/
theorem stableTuple (rules : List (Equation s))
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (q : List (Term s)) (n : Term s → Term s)
    (cert : ∀ t ∈ q, StableVariants.Representative (ruleRoot rules) t (n t))
    (avoid : List Variable) :
    VariantReply (ruleRoot rules) q avoid [⟨.identity, q.map n⟩] :=
  VariantReply.singleton_iff.mpr (StableVariants.tuple rules apps q n cert avoid)

/-- A closed narrowing frontier for one term supplies a complete Maude reply
once the decoded answers respect the caller's scope. A reducer for the same
presentation justifies dropping the returned normal values. -/
theorem frontierReply {rules : List (Equation s)} {t : Term s} {states kept answers avoid}
    (frontier : RootNarrowing.Certificate rules t states kept answers)
    (r : VerifiedReducer (ruleRoot rules)) (vars : Normalized (ruleRoot rules) .identity)
    (safe : ∀ a ∈ answers, a.Safe [t] avoid) : VariantReply (ruleRoot rules) [t] avoid answers :=
  .ofCanonical r vars (frontier.complete vars) safe

private theorem emptyStable (t : Term s) : StableVariants.Stable (ruleRoot []) t :=
  StableVariants.constructors [] (by simp) t (fun _ _ hm => List.not_mem_nil hm)

/-- With no active equations, every free/C/AC term is already a normal form
modulo B. This also applies to kind-level application trees. -/
def emptyReducer (s : Signature) : VerifiedReducer (ruleRoot (sig := s) []) where
  reduce := id
  correct t := by
    have vars := (ConstructorVariants.constructor_normal (sig := s) [] (by simp)).1
    have hn : Normal (ruleRoot []) t := by simpa using emptyStable t .identity vars
    exact ⟨⟨.basis (.refl _), hn, fun _ h => h⟩, fun _ nf => (normal_reduces_equiv nf.1 hn).symm⟩

def emptyVariants (s : Signature) : VerifiedVariantGenerator (ruleRoot (sig := s) []) where
  variants q _ := [⟨.identity, q⟩]
  correct q avoid := by
    simpa using stableTuple [] (by simp) q id
      (fun t _ => StableVariants.stableRepresentative (emptyStable t)) avoid

/-- All four source operations for modules with free/C/AC declarations and
an empty rewrite table. Ordinary unification has the same contract when a
module also declares rewrite rules. -/
def emptyReference (s : Signature) [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] : Reference s [] where
  unify := MixedUnification.verified
  matchTerms := ReferenceMatching.matcher s
  reduce := emptyReducer s
  variants := emptyVariants s

/-- The existing two-projection reference normalizer also meets the total
reduction target for its abstract pairing relation. -/
def pairingReducer : VerifiedReducer Pairing.root :=
  .ofNormalizer Pairing.referenceNormalizer (fun _ _ _ hu hv =>
    Pairing.normal_unique_modulo (Pairing.rewriting_reducesModulo hu.1) (Pairing.rewriting_reducesModulo hv.1)
      ((Pairing.normal_iff_rewriting _).mpr hu.2.1) ((Pairing.normal_iff_rewriting _).mpr hv.2.1))

end Tamarin.MaudeOperations
