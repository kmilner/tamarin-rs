import TamarinRuntime.ACPlane

namespace Tamarin.ACBasis

private theorem forcedHead_eq (l w a b : Nat) (pos : 0 < w) :
    forcedHead l w a b = (List.range (l+1)).filter (fun h => a + w*h == b) := by
  let k := (b-a)/w
  have unique (h) (eq : a + w*h = b) : h = k := by
    simp [k, ← eq, Nat.mul_div_cancel_left _ pos]
  by_cases ok : k ≤ l ∧ a + w*k = b
  · have pred (h : Nat) : (a + w*h == b) = (h == k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact ⟨unique h, fun e => e ▸ ok.2⟩
    simp only [pred, List.filter_beq, List.count_range]
    change (if decide (k ≤ l) && (a + w*k == b) then [k] else []) = _
    simp [ok.1, ok.2, Nat.lt_succ_of_le ok.1]
  · have empty : (List.range (l+1)).filter (fun h => a + w*h == b) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h mem eq
      have e := beq_iff_eq.mp eq
      obtain rfl := unique h e
      exact ok ⟨Nat.le_of_lt_succ (List.mem_range.mp mem), e⟩
    rw [empty]
    change (if decide (k ≤ l) && (a + w*k == b) then [k] else []) = []
    simp [ok]

private theorem flatMap_filtered {α β} (xs : List α) (p : α → Bool) (g : α → List β) :
    (xs.filter p).flatMap g = xs.flatMap (fun x => if p x then g x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h, ih]

private theorem filter_const {α} (xs : List α) (b : Bool) :
    xs.filter (fun _ => b) = if b then xs else [] := by
  cases b <;> induction xs <;> simp_all

theorem balancedBox_eq (n : Nat) (lim p q : Vec n)
    (disjoint : ∀ i, p i = 0 ∨ q i = 0) (a b : Nat) :
    balancedBox n lim p q a b = (box n lim).filter (fun x => a + dot p x == b + dot q x) := by
  induction n generalizing a b with
  | zero => simp [balancedBox, box, dot, total]; split <;> simp_all
  | succ n ih =>
    let l := fun i : Fin n => lim i.succ
    let u := fun i : Fin n => p i.succ
    let v := fun i : Fin n => q i.succ
    let prepend (h : Nat) (t : Vec n) : Vec (n+1) := Fin.cases h t
    have expand (h : Nat) :
        ((box n l).map (prepend h)).filter (fun x => a + dot p x == b + dot q x) =
        ((box n l).filter (fun t => a + p 0 * h + dot u t == b + q 0 * h + dot v t)).map (prepend h) := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro t _
      simp [prepend, dot, total, List.ofFn_succ, u, v, Nat.add_assoc]
    rw [box, List.filter_flatMap]
    change balancedBox (n+1) lim p q a b = (List.range (lim 0 + 1)).flatMap _
    rw [funext expand]
    dsimp only [prepend]
    unfold balancedBox
    dsimp only
    split
    · rename_i h
      have hz : ∀ i, u i = 0 ∧ v i = 0 := by
        simpa [neutral, u, v] using (Bool.and_eq_true_iff.mp h).1
      have du (t : Vec n) : dot u t = 0 := by
        simp [dot, total, fun i => (hz i).1, List.sum_eq_zero_iff_forall_eq_nat]
      have dv (t : Vec n) : dot v t = 0 := by
        simp [dot, total, fun i => (hz i).2, List.sum_eq_zero_iff_forall_eq_nat]
      simp only [du, dv, Nat.add_zero]
      by_cases hp : 0 < p 0
      · have hq := (disjoint 0).resolve_left (Nat.ne_of_gt hp)
        simp [hp,hq,forcedHead_eq _ _ _ _ hp,flatMap_filtered,l]
        apply congrArg (List.flatMap · _)
        funext z
        split <;> simp_all [filter_const]
      · have hp' := Nat.eq_zero_of_not_pos hp
        have hq : 0 < q 0 := by simpa [hp'] using (Bool.and_eq_true_iff.mp h).2
        simp [hp',forcedHead_eq _ _ _ _ hq,flatMap_filtered,l]
        apply congrArg (List.flatMap · _)
        funext z
        by_cases e : b + q 0 * z = a
        · simp [e, filter_const]
        · simp [e, Ne.symm e, filter_const]
    · apply congrArg (List.flatMap · _)
      funext z
      rw [ih _ _ _ (fun i => disjoint i.succ)]

theorem Row.planeGenerators_eq {n} (r : Row n) : r.planeGenerators = r.generators := by
  unfold Row.planeGenerators Row.generators
  rw [balancedBox_eq _ _ _ _ r.disjoint, List.filter_filter]
  simp [Bool.and_comm]

end Tamarin.ACBasis
