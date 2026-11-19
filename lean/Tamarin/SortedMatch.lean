import TamarinRuntime.SortedMatch

namespace Tamarin.SortedMatch

def Admitted (ac : UInt64) (vs ats occ tail rhs : Array UInt64) : Prop :=
  ac ≤ 4 ∧ vs.size < UInt64.size ∧
  (∀ s ∈ vs, s ≤ 4 ∧ Whole.subsort s ac = true) ∧
  (∀ s ∈ ats, s ≤ 4 ∧ Whole.subsort s ac = true) ∧
  (∀ i ∈ occ, i.toNat < vs.size) ∧
  (∀ j ∈ tail, j.toNat < ats.size) ∧ (∀ j ∈ rhs, j.toNat < ats.size)

def RowFits (ac v : UInt64) (ats : Array UInt64) : List UInt64 → Prop
  | [] => False
  | [j] => ∃ s, ats[j.toNat]? = some s ∧ Whole.subsort s v = true
  | _ :: _ :: _ => Whole.subsort ac v = true

def Fits (ac : UInt64) (vs ats : Array UInt64) (arm : Array (Array UInt64)) : Prop :=
  arm.size = vs.size ∧ ∀ i : Fin vs.size, ∃ row, arm[i.val]? = some row ∧ RowFits ac vs[i] ats row.toList

/-- On valid packets keep exactly the flat answers whose images have the declared
sort of every bound variable. Membership permits any order and redundant arms. -/
structure Correct (run : Kernel) (flat : Flat) : Prop where
  completes : ∀ ac vs ats occ tail rhs,
    (run ac vs ats occ tail rhs).isSome ↔ Admitted ac vs ats occ tail rhs
  rows : ∀ ac vs ats occ tail rhs out, run ac vs ats occ tail rhs = some out →
    ∀ arm, arm ∈ out ↔ arm ∈ flat vs.size.toUInt64 occ tail rhs ∧ Fits ac vs ats arm

private theorem valid_iff {ac vs ats occ tail rhs} :
    valid ac vs ats occ tail rhs = true ↔ Admitted ac vs ats occ tail rhs := by
  simp only [valid, Admitted, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem, and_assoc]

private theorem checkRow_iff {ac v ats row} : checkRow ac v ats row = true ↔ RowFits ac v ats row.toList := by
  rcases row with ⟨xs⟩
  cases xs with
  | nil => simp [checkRow, RowFits]
  | cons j js =>
    cases js with
    | nil => simp [checkRow, RowFits, Option.any_eq_true]
    | cons k ks => simp [checkRow, RowFits]

private theorem checkArm_iff {ac vs ats arm} : checkArm ac vs ats arm = true ↔ Fits ac vs ats arm := by
  simp only [checkArm, Fits, Bool.and_eq_true, beq_iff_eq, Nat.all_eq_finRange_all,
    List.all_eq_true, List.mem_finRange, forall_const, Option.any_eq_true, checkRow_iff]
  rfl

theorem run_correct (flat : Flat) : Correct (runWith flat) flat := by
  constructor
  · intro ac vs ats occ tail rhs
    unfold runWith
    split <;> simp_all [valid_iff]
  · intro ac vs ats occ tail rhs out returned
    unfold runWith at returned
    split at returned
    · cases returned
      simp only [Array.mem_filter, checkArm_iff, implies_true]
    · contradiction

end Tamarin.SortedMatch
