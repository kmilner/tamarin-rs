import TamarinRuntime.Whole

namespace Tamarin.Whole
namespace Tree

mutual
  theorem emit_injective (a b : Tree) (xs ys : List UInt64)
      (h : a.emit xs = b.emit ys) : a = b ∧ xs = ys := by
    cases a <;> cases b <;> simp only [emit, List.cons.injEq] at h
    · obtain ⟨hk, hi, hs, ht⟩ := h.2
      exact ⟨by simp [hk, hi, hs], ht⟩
    · simp at h
    · simp at h
    · obtain ⟨hk, hi, ht⟩ := h.2
      obtain ⟨ha, ht⟩ := emitArgs_injective _ _ _ _ ht
      exact ⟨by simp [hk, hi, ha], ht⟩
  theorem emitArgs_injective (as bs : List Tree) (xs ys : List UInt64)
      (h : emitArgs as (2 :: xs) = emitArgs bs (2 :: ys)) : as = bs ∧ xs = ys := by
    cases as with
    | nil =>
      cases bs with
      | nil => exact ⟨rfl, (List.cons.inj h).2⟩
      | cons b bs => cases b <;> simp [emitArgs, emit] at h
    | cons a as =>
      cases bs with
      | nil => cases a <;> simp [emitArgs, emit] at h
      | cons b bs =>
        obtain ⟨hab, hr⟩ := emit_injective a b _ _ h
        obtain ⟨he, ht⟩ := emitArgs_injective as bs _ _ hr
        exact ⟨by simp [hab, he], ht⟩
end

theorem key_injective : Function.Injective key := fun a b h => (emit_injective a b [] [] h).1

instance : LawfulBEq Tree where
  rfl := by intro a; change (a.key == a.key) = true; simp
  eq_of_beq := by intro a b h; change (a.key == b.key) = true at h; exact key_injective (beq_iff_eq.mp h)

end Tree

theorem order_perm (xs : List Tree) : (order xs).Perm xs := List.mergeSort_perm ..

theorem order_eq_of_perm {xs ys : List Tree} (h : xs.Perm ys) : order xs = order ys := by
  let le := fun (a b : Tree) => decide (a.key ≤ b.key)
  have trans (a b c : Tree) : le a b = true → le b c = true → le a c = true := by
    simp only [le, decide_eq_true_eq]
    exact Std.le_trans
  have total (a b : Tree) : (le a b || le b a) = true := by
    simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using List.le_total a.key b.key
  apply List.Perm.eq_of_pairwise (le := fun a b => le a b = true)
  · intro a b _ _ ha hb
    apply Tree.key_injective
    exact List.le_antisymm (of_decide_eq_true ha) (of_decide_eq_true hb)
  · exact List.pairwise_mergeSort trans total xs
  · exact List.pairwise_mergeSort trans total ys
  · exact (order_perm xs).trans (h.trans (order_perm ys).symm)

end Tamarin.Whole
