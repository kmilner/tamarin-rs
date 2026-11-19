import TamarinRuntime.ACPlane

/-! Shrinking a coordinate box preserves any previously admitted search
budget, also when the projected coordinate itself gets smaller. -/
namespace Tamarin.ACBasis
variable {n : Nat}

def gridSize (limits : Vec n) := (List.ofFn fun i => limits i + 1).prod

def GridBudget (r : Row n) (limits : Vec n) (budget : Nat) : Prop :=
  gridSize limits ≤ budget ∨
    ∃ i, (0 < r.pos i ∨ 0 < r.neg i) ∧ gridSize limits ≤ budget * (limits i + 1)

private def volume (limits : Vec n) (indices : List (Fin n)) :=
  (indices.map fun i => limits i + 1).prod

private theorem volume_perm (lim : Vec n) {xs ys : List (Fin n)} (p : xs.Perm ys) :
    volume lim xs = volume lim ys := by
  induction p with
  | nil => rfl
  | cons x _ ih => exact congrArg ((lim x + 1) * ·) ih
  | swap => simp [volume,Nat.mul_left_comm]
  | trans _ _ ih kh => exact ih.trans kh

private theorem volume_mono {lo hi : Vec n} (xs : List (Fin n)) (le : ∀ i, lo i ≤ hi i) :
    volume lo xs ≤ volume hi xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons i _ ih => exact Nat.mul_le_mul (Nat.succ_le_succ (le i)) ih

private theorem size_eq (lim : Vec n) : gridSize lim = volume lim (List.finRange n) := by
  simp [gridSize,volume,List.finRange,List.map_ofFn,Function.comp_def]

theorem GridBudget.shrink {r : Row n} {hi lo : Vec n} {b : Nat}
    (fits : GridBudget r hi b) (le : ∀ i, lo i ≤ hi i) : GridBudget r lo b := by
  rcases fits with whole | ⟨i,active,cap⟩
  · exact .inl (Nat.le_trans (by rw [size_eq,size_eq]; exact volume_mono _ le) whole)
  · let rest := (List.finRange n).erase i
    have factor (lim : Vec n) : gridSize lim = volume lim rest * (lim i + 1) := by
      rw [size_eq,volume_perm lim (List.perm_cons_erase (List.mem_finRange i)),Nat.mul_comm]
      rfl
    rw [factor] at cap
    have small := Nat.le_trans (volume_mono rest le) (Nat.le_of_mul_le_mul_right cap (Nat.zero_lt_succ _))
    exact .inr ⟨i,active,by rw [factor]; exact Nat.mul_le_mul_right _ small⟩

end Tamarin.ACBasis
