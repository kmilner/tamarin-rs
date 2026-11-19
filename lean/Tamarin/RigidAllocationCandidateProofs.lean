import Tamarin.RigidAllocationPacket
import TamarinRuntime.Candidate

namespace Tamarin.RigidAllocationCandidateProofs

theorem correct : RigidAllocation.PacketCorrect RuntimeCandidate.rigidAllocation := by
  intro _
  exact ⟨1, 1, 1, 2, 1, 2, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, List.Perm.refl _⟩

end Tamarin.RigidAllocationCandidateProofs
