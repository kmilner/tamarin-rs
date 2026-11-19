import Tamarin.CandidateProofs
import Tamarin.SharedOffset

namespace Tamarin.BackendContractChecks

open Executable

/-- A different executable decision procedure: decidable list permutation
instead of the candidate's sort-and-compare implementation. This is a proof
acceptance test, not a benchmark or a selected production implementation. -/
private def permutationBackend : FlatACBackend where
  equal := fun lhs rhs =>
    if lhs.toList.isEmpty || rhs.toList.isEmpty then 0
    else if lhs.toList.Perm rhs.toList then 2 else 1
  residual := RuntimeCandidate.backend.residual

example : FlatACBackend.Correct permutationBackend := by
  have same : permutationBackend = RuntimeCandidate.backend := by
    unfold permutationBackend RuntimeCandidate.backend
    congr 1
    funext lhs rhs
    simp only [classify, sameMultiset_iff]
  rw [same]
  exact CandidateProofs.correct

private def alwaysUnsupported : FlatACBackend where
  equal := fun _ _ => 0
  residual := fun _ _ => #[0]

/-- Safe empty partial answers do not satisfy the completion obligation. -/
example : ¬ FlatACBackend.Correct alwaysUnsupported := by
  intro h
  have complete := h.equal_completes #[7] #[7] (by decide) (by decide)
  simp [alwaysUnsupported] at complete

/-- Empty arrays have no AC denotation. Equal sentinel terms cannot justify
accepting a successful packet at the numeric boundary. -/
private def acceptsEmptyPair : FlatACBackend where
  equal := fun lhs rhs => if lhs.isEmpty && rhs.isEmpty then 2 else RuntimeCandidate.backend.equal lhs rhs
  residual := RuntimeCandidate.backend.residual

example : ¬ FlatACBackend.Correct acceptsEmptyPair := by
  intro h
  have bad := (h.empty_inputs #[] #[] (Or.inl rfl)).1
  contradiction

private def invalidStatus : FlatACBackend where
  equal := fun _ _ => 255
  residual := fun _ _ => #[]

/-- Numeric packet validity is required even outside the supported fragment. -/
example : ¬ FlatACBackend.Correct invalidStatus := by
  intro h
  have packet := h.equal_status #[] #[]
  simp [invalidStatus] at packet

/-- Reversing branch order and selecting a full-width slot ID are valid
optimizations under the same shared-offset packet contract. -/
example : SharedOffset.PacketCorrect (fun a b =>
    #[#[#[b, UInt64.ofNat (2^64-1)], #[a, UInt64.ofNat (2^64-1)]], #[#[b], #[a]]]) := by
  intro a b _
  exact ⟨_, List.Perm.swap _ _ []⟩

end Tamarin.BackendContractChecks
