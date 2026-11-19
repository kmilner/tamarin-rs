import Tamarin.ACPlane

/-! Capping each plane coordinate keeps exactly the corresponding reference
vectors, including their relative order. -/
namespace Tamarin.ACBasis

private theorem filter_range_cap (v cap : Nat) :
    (List.range (v+1)).filter (fun h => decide (h ≤ cap)) = List.range (min v cap + 1) := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [List.range_succ,List.filter_append,ih]
    by_cases h : v+1 ≤ cap
    · simp [h,Nat.min_eq_left h,Nat.min_eq_left (Nat.le_trans (Nat.le_succ _) h),List.range_succ]
    · simp [h,Nat.min_eq_right (show cap ≤ v by omega),Nat.min_eq_right (show cap ≤ v+1 by omega)]

theorem box_cap (n : Nat) (limits : Vec n) (cap : Nat) :
    box n (fun i => min (limits i) cap) =
      (box n limits).filter (fun v => decide (∀ i, v i ≤ cap)) := by
  induction n with
  | zero => simp [box]
  | succ n ih =>
    let tail (i : Fin n) := limits i.succ
    let prepend (h : Nat) (t : Vec n) : Vec (n+1) := Fin.cases h t
    have head (h : Nat) : ((box n tail).map (prepend h)).filter (fun v => decide (∀ i, v i ≤ cap)) =
        if h ≤ cap then ((box n tail).filter (fun v => decide (∀ i, v i ≤ cap))).map (prepend h) else [] := by
      rw [List.filter_map]
      by_cases hcap : h ≤ cap <;> simp [Function.comp_def,Fin.forall_fin_succ,hcap,prepend]
      apply congrArg (List.map _)
      apply List.filter_congr
      intro t _
      apply Bool.eq_iff_iff.mpr
      exact ⟨fun h => decide_eq_true (of_decide_eq_true h), fun h => decide_eq_true (of_decide_eq_true h)⟩
    have heads (xs : List Nat) :
        (xs.filter fun h => decide (h ≤ cap)).flatMap (fun h =>
          ((box n tail).filter (fun v => decide (∀ i, v i ≤ cap))).map (prepend h)) =
        (xs.flatMap fun h => (box n tail).map (prepend h)).filter (fun v => decide (∀ i, v i ≤ cap)) := by
      induction xs with
      | nil => rfl
      | cons h xs ih =>
        by_cases ok : h ≤ cap <;> simp [ok,head,ih]
    unfold box
    rw [← filter_range_cap,ih tail]
    exact heads _

theorem Row.compactGenerators_eq {n} (r : Row n) :
    r.compactGenerators = r.generators.filter (fun v => decide (∀ i, v i ≤ 2 * r.cap)) := by
  unfold Row.compactGenerators Row.generators Row.compactLimits
  rw [balancedBox_eq _ _ _ _ r.disjoint,box_cap]
  simp only [List.filter_filter,Nat.zero_add]
  apply List.filter_congr
  intro v _
  simp only [Bool.and_comm,Bool.and_left_comm,Bool.and_assoc]

end Tamarin.ACBasis
