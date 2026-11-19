import Tamarin.XorVariants
import TamarinRuntime.Candidate

namespace Tamarin.Rewriting.FreshXor

/-- On the fragment the mask records the identity and diagonal branches.
A proof is required for either possible equality of the two input names. -/
def BranchCorrect (run : Bool → UInt8) : Prop :=
  ∀ same, run same = if same then 2 else 3

theorem candidate_correct : BranchCorrect RuntimeCandidate.xorBranches := by
  intro same; rfl

theorem selected_normalForm {sig : Signature} (T : Table sig) {a b : Term sig}
    (ha : HasSort a .fresh) (hb : HasSort b .fresh) (na : Normal T.R a) (nb : Normal T.R b)
    {run} (hc : BranchCorrect run) (same : Bool) (he : same = true ↔ a = b) :
    NormalForm T.R (.ac T.f a b) (if run same &&& 1 == 0 then T.zero else .ac T.f a b) := by
  cases same
  · have ne : a ≠ b := fun h => Bool.noConfusion (he.mpr h)
    simpa [hc false, show (3 : UInt8) &&& 1 = 1 by decide] using
      (show NormalForm T.R (.ac T.f a b) (.ac T.f a b) from
        ⟨.basis (.refl _), T.distinct_normal ha hb na nb ne, fun _ hs => hs⟩)
  · obtain rfl := he.mp rfl
    simpa [hc true, show (2 : UInt8) &&& 1 = 0 by decide] using T.duplicate_nf ha

end Tamarin.Rewriting.FreshXor
