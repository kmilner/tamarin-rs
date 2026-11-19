import Tamarin.Executable
import Tamarin.BackendContract

namespace Tamarin.CandidateProofs

open Executable

/-- Candidate-owned proof, checked against the fixed contract by TamarinCI.
No reference algorithm equality is required: another representation or search
strategy may supply its own proofs of these same semantic obligations. -/
theorem correct : FlatACBackend.Correct RuntimeCandidate.backend where
  equal_status := by
    intro lhs rhs
    change classify lhs.toList rhs.toList = 0 ∨
      classify lhs.toList rhs.toList = 1 ∨ classify lhs.toList rhs.toList = 2
    unfold classify
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  empty_inputs := flatAC_empty_inputs
  equal_correct := flatACEqual_correct
  equal_completes := flatACEqual_completes
  equal_words := by
    intro lhs rhs hl hr
    change classify _ _ = 2 ↔ _
    simp only [classify, List.isEmpty_eq_false_iff.mpr hl, List.isEmpty_eq_false_iff.mpr hr,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    by_cases h : sameMultiset lhs.toList rhs.toList <;> simp [h, ← sameMultiset_iff]
  residual_admits := by
    intro small big excess hs hx hp
    have hb : big.toList ≠ [] := by
      intro h; rw [h] at hp
      exact hx (List.append_eq_nil_iff.mp (List.Perm.nil_eq hp).symm).1
    change ∃ rest, (residual small.toList big.toList).toArray = (2 :: rest).toArray
    cases he : difference small.toList big.toList with
    | none =>
      obtain ⟨a, ha⟩ := difference_failure _ _ he
      rw [hp.count_eq a, List.count_append] at ha
      omega
    | some rest =>
      have perm := difference_sound _ _ _ he
      cases rest with
      | nil =>
        have len := hp.length_eq.symm.trans perm.length_eq
        simp only [List.length_append, List.length_nil, Nat.zero_add] at len
        exact False.elim (hx (List.length_eq_zero_iff.mp (by omega)))
      | cons a rest =>
        exact ⟨a :: rest, by simp only [residual, List.isEmpty_eq_false_iff.mpr hs,
          List.isEmpty_eq_false_iff.mpr hb, Bool.false_or, Bool.false_eq_true, ↓reduceIte, he]⟩
  residual_packet := by
    intro tail rhs
    by_cases ht : tail.toList = []
    · apply Or.inl
      change (residual tail.toList rhs.toList).toArray = #[0]
      rw [ht]
      rfl
    by_cases hr : rhs.toList = []
    · apply Or.inl
      change (residual tail.toList rhs.toList).toArray = #[0]
      rw [hr]
      simp [residual]
    exact Or.inr (flatACResidual_completes tail rhs ht hr)
  residual_difference := by
    intro tail rhs rest h
    have he : residual tail.toList rhs.toList = 2 :: rest := by
      simpa only [RuntimeCandidate.backend, List.toList_toArray] using congrArg Array.toList h
    exact (residual_success tail.toList rhs.toList rest he).2.2.2
  residual_success := flatACResidual_complete
  residual_failure := flatACResidual_empty_complete
  residual_completes := flatACResidual_completes

end Tamarin.CandidateProofs
