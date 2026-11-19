import Tamarin.CandidateProofs

namespace Tamarin.ExecutableChecks

open Executable

example : flatACEqual #[3, 1, 3] #[3, 3, 1] = 2 := by
  exact (CandidateProofs.correct.equal_words _ _ (by decide) (by decide)).mpr (by decide)
example : flatACEqual #[3, 1, 3] #[3, 1, 1] = 1 := by
  apply (CandidateProofs.correct.equal_completes _ _ (by decide) (by decide)).resolve_right
  rw [CandidateProofs.correct.equal_words _ _ (by decide) (by decide)]
  decide
example : flatACEqual #[] #[1] = 0 := by
  exact (CandidateProofs.correct.empty_inputs _ _ (.inl rfl)).1
example : flatACEqual #[18446744073709551615, 0] #[0, 18446744073709551615] = 2 := by
  exact (CandidateProofs.correct.equal_words _ _ (by decide) (by decide)).mpr (by decide)

private theorem residual_represents (small big : Array UInt64) (excess : List UInt64)
    (hs : small.toList ≠ []) (hx : excess ≠ []) (hp : big.toList.Perm (excess ++ small.toList)) :
    ∃ rest, flatACResidual small big = (2 :: rest).toArray ∧ rest.Perm excess := by
  obtain ⟨rest, h⟩ := CandidateProofs.correct.residual_admits small big excess hs hx hp
  have diff := CandidateProofs.correct.residual_difference small big rest h
  exact ⟨rest, h, (List.perm_append_right_iff _).mp (diff.symm.trans hp)⟩

example : ∃ rest, flatACResidual #[2, 4] #[4, 3, 2] = (2 :: rest).toArray ∧ rest.Perm [3] :=
  residual_represents _ _ _ (by decide) (by decide) (by decide)
example : ∃ rest, flatACResidual #[2] #[4, 3, 2] = (2 :: rest).toArray ∧ rest.Perm [3, 4] :=
  residual_represents _ _ _ (by decide) (by decide) (by decide)

private theorem residual_same_size (small big : Array UInt64)
    (hs : small.toList ≠ []) (hb : big.toList ≠ []) (size : big.size = small.size) :
    flatACResidual small big = #[1] := by
  apply (CandidateProofs.correct.residual_completes small big hs hb).resolve_right
  rintro ⟨rest, hn, h⟩
  have length := (CandidateProofs.correct.residual_difference small big rest h).length_eq
  simp [size] at length
  exact hn length

example : flatACResidual #[2, 2] #[4, 2] = #[1] :=
  residual_same_size _ _ (by decide) (by decide) rfl
example : flatACResidual #[2, 4] #[4, 2] = #[1] :=
  residual_same_size _ _ (by decide) (by decide) rfl
example : flatACResidual #[] #[2] = #[0] := by
  exact (CandidateProofs.correct.empty_inputs _ _ (.inl rfl)).2

end Tamarin.ExecutableChecks
