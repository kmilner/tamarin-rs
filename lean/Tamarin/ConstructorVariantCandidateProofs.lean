import Tamarin.ConstructorVariants
import TamarinRuntime.Candidate

namespace Tamarin.ConstructorVariantCandidateProofs

theorem correct : Rewriting.ConstructorVariants.DecisionCorrect RuntimeCandidate.constructorVariant := by
  intro roots used
  unfold RuntimeCandidate.constructorVariant
  rw [Array.all_eq_true_iff_forall_mem]
  simp

end Tamarin.ConstructorVariantCandidateProofs
