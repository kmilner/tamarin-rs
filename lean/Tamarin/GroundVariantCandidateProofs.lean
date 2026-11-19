import Tamarin.GroundVariantDecision
import TamarinRuntime.Candidate

namespace Tamarin.GroundVariantCandidateProofs
open Rewriting.GroundVariantDecision

theorem correct : Correct RuntimeCandidate.groundVariant := by
  intro holes anchors deps rigid
  unfold RuntimeCandidate.groundVariant
  have he : (rigid && decide holes.toList.Nodup && decide anchors.toList.Nodup &&
      holes.all (fun v => !(deps.contains v))) = true ↔ Admitted holes anchors deps rigid := by
    rw [Admitted]
    rw [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
    simp [and_assoc, and_comm, and_left_comm]
  by_cases h : Admitted holes anchors deps rigid
  · rw [ite_eq_left (he.mpr h)]; simp [h]
  · rw [ite_eq_right (fun ok => h (he.mp ok))]; simp [h]

end Tamarin.GroundVariantCandidateProofs
