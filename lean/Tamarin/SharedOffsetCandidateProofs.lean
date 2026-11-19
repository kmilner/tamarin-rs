import Tamarin.SharedOffset
import TamarinRuntime.Candidate

namespace Tamarin.SharedOffsetCandidateProofs

theorem correct : SharedOffset.PacketCorrect RuntimeCandidate.sharedOffset := by
  intro a b _
  exact ⟨0, List.Perm.swap _ _ []⟩

end Tamarin.SharedOffsetCandidateProofs
