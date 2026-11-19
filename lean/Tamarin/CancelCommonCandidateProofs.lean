import Tamarin.CommonCancellation
import TamarinRuntime.Candidate

namespace Tamarin.CancelCommonCandidateProofs
open RuntimeCandidate

private theorem merge_correct (lhs rhs leftRev rightRev : List UInt64)
    (sl : lhs.Pairwise (· ≤ ·)) (sr : rhs.Pairwise (· ≤ ·)) :
    ∃ common left right : List UInt64,
      cancelSorted lhs rhs leftRev rightRev = (leftRev.reverseAux left, rightRev.reverseAux right) ∧
      lhs.Perm (common ++ left) ∧ rhs.Perm (common ++ right) ∧ ∀ w ∈ left, w ∉ right := by
  cases lhs with
  | nil =>
    refine ⟨[], [], rhs, ?_, .refl _, .refl _, ?_⟩
    · simp [cancelSorted]
    · simp
  | cons x xs =>
    cases rhs with
    | nil =>
      refine ⟨[], x :: xs, [], ?_, .refl _, .refl _, ?_⟩
      · simp [cancelSorted]
      · simp
    | cons y ys =>
      rw [cancelSorted]
      by_cases he : x = y
      · subst y
        rw [ite_eq_left rfl]
        obtain ⟨c, l, r, out, hl, hr, hd⟩ := merge_correct xs ys leftRev rightRev sl.of_cons sr.of_cons
        exact ⟨x :: c, l, r, out, .cons x hl, .cons x hr, hd⟩
      · rw [ite_eq_right he]
        by_cases lt : x < y
        · rw [ite_eq_left lt]
          obtain ⟨c, l, r, out, hl, hr, hd⟩ :=
            merge_correct xs (y :: ys) (x :: leftRev) rightRev sl.of_cons sr
          refine ⟨c, x :: l, r, out, (hl.cons x).trans List.perm_middle.symm, hr, ?_⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hm
          · intro hw
            have h := hr.mem_iff.mpr (List.mem_append_right _ hw)
            rcases List.mem_cons.mp h with h | h
            · exact he h
            · exact (UInt64.not_le.mpr lt) ((List.pairwise_cons.mp sr).1 _ h)
          · exact hd _ hm
        · rw [ite_eq_right lt]
          obtain ⟨c, l, r, out, hl, hr, hd⟩ :=
            merge_correct (x :: xs) ys leftRev (y :: rightRev) sl sr.of_cons
          refine ⟨c, l, y :: r, out, hl, (hr.cons y).trans List.perm_middle.symm, ?_⟩
          intro w hw hy
          rcases List.mem_cons.mp hy with rfl | hm
          · have h := hl.mem_iff.mpr (List.mem_append_right _ hw)
            rcases List.mem_cons.mp h with h | h
            · exact he h.symm
            · have hle := (List.pairwise_cons.mp sl).1 _ h
              exact he (UInt64.le_antisymm hle (UInt64.not_lt.mp lt))
          · exact hd w hw hm
termination_by lhs.length + rhs.length

private theorem sorted (xs : List UInt64) : (xs.mergeSort Executable.atomLE).Pairwise (· ≤ ·) := by
  have trans (a b c : UInt64) : Executable.atomLE a b → Executable.atomLE b c → Executable.atomLE a c := by
    simpa only [Executable.atomLE, decide_eq_true_eq] using @UInt64.le_trans a b c
  have total (a b : UInt64) : Executable.atomLE a b || Executable.atomLE b a := by
    simpa only [Executable.atomLE, Bool.or_eq_true, decide_eq_true_eq] using UInt64.le_total a b
  simpa only [Executable.atomLE, decide_eq_true_eq] using List.pairwise_mergeSort trans total xs

theorem correct : CommonCancellation.Correct RuntimeCandidate.cancelCommon := by
  intro lhs rhs
  obtain ⟨common, left, right, out, hl, hr, hd⟩ :=
    merge_correct _ _ [] [] (sorted lhs.toList) (sorted rhs.toList)
  refine ⟨common, left, right, ?_, (List.mergeSort_perm _ _).symm.trans hl,
    (List.mergeSort_perm _ _).symm.trans hr, hd⟩
  simp only [RuntimeCandidate.cancelCommon, out, List.reverseAux_nil]

end Tamarin.CancelCommonCandidateProofs
