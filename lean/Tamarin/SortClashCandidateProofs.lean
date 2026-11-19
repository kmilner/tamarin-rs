import Tamarin.SortClash
import TamarinRuntime.Candidate

namespace Tamarin.SortClashCandidateProofs

theorem correct : SortClash.Correct RuntimeCandidate.sortClash := by
  intro a b
  unfold RuntimeCandidate.sortClash
  simp only [Bool.or_eq_true, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  simp

end Tamarin.SortClashCandidateProofs
