import Tamarin.MultisetDifference

namespace Tamarin.Executable

private theorem not_mem_below_head (x a : UInt64) (xs : List UInt64)
    (hs : List.Pairwise (fun x y => x ≤ y) (x :: xs)) (ha : a < x) :
    a ∉ x :: xs := by
  intro hm
  rcases List.mem_cons.mp hm with he | he
  · subst a
    exact UInt64.lt_irrefl x ha
  · have hxa := (List.pairwise_cons.mp hs).1 a he
    exact UInt64.lt_irrefl a (UInt64.lt_of_lt_of_le ha hxa)

/-- Failure of linear subtraction on sorted lists exhibits a missing atom
with its multiplicity. This justifies an unsatisfiable result rather than
merely reporting an unsupported query. -/
theorem subtractSorted_failure (need available : List UInt64)
    (hn : List.Pairwise (fun x y => x ≤ y) need)
    (ha : List.Pairwise (fun x y => x ≤ y) available)
    (h : subtractSorted need available = none) :
    ∃ a, available.count a < need.count a := by
  induction available generalizing need with
  | nil =>
    cases need with
    | nil => simp [subtractSorted] at h
    | cons x xs =>
      refine ⟨x, ?_⟩
      simp
  | cons y ys ih =>
    cases need with
    | nil => simp [subtractSorted] at h
    | cons x xs =>
      have hys : List.Pairwise (fun x y => x ≤ y) ys := (List.pairwise_cons.mp ha).2
      simp only [subtractSorted] at h
      split at h
      · next heq =>
        subst x
        obtain ⟨a, hac⟩ := ih xs (List.pairwise_cons.mp hn).2 hys h
        refine ⟨a, ?_⟩
        simp only [List.count_cons]
        exact Nat.add_lt_add_right hac _
      · next hne =>
        split at h
        · next hlt =>
          have hnone : subtractSorted (x :: xs) ys = none := by
            cases hr : subtractSorted (x :: xs) ys with
            | none => rfl
            | some rest => simp [hr] at h
          obtain ⟨a, hac⟩ := ih (x :: xs) hn hys hnone
          have hcount : (x :: xs).count y = 0 :=
            List.count_eq_zero.mpr (not_mem_below_head x y xs hn hlt)
          have hay : a ≠ y := by
            intro heq
            subst a
            rw [hcount] at hac
            exact Nat.not_lt_zero _ hac
          refine ⟨a, ?_⟩
          simpa [List.count_cons, Ne.symm hay] using hac
        · next hlt =>
          have hxy : x < y := UInt64.lt_of_le_of_ne (UInt64.not_lt.mp hlt) hne
          have hcount : (y :: ys).count x = 0 :=
            List.count_eq_zero.mpr (not_mem_below_head y x ys ha hxy)
          refine ⟨x, ?_⟩
          rw [hcount]
          simp

end Tamarin.Executable
