import TamarinRuntime.Homogeneous
import Tamarin.FlatMatchSearch

namespace Tamarin.Homogeneous.Coverage

variable {α : Type} {n : Nat} (mask : α → BitVec n)

/-- A prefix and the selected generators together cover every coordinate. -/
private def Covered (seen : BitVec n) (xs : List α) : Prop :=
  ∀ i : Fin n, seen.getLsbD i = true ∨ ∃ x ∈ xs, (mask x).getLsbD i = true

private instance (seen : BitVec n) (xs : List α) : Decidable (Covered mask seen xs) :=
  inferInstanceAs (Decidable (∀ i : Fin n, seen.getLsbD i = true ∨ ∃ x ∈ xs, (mask x).getLsbD i = true))

private theorem full_iff (v : BitVec n) :
    v = BitVec.allOnes n ↔ ∀ i : Fin n, v.getLsbD i = true := by
  constructor
  · rintro rfl i
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa [hi] using h ⟨i, hi⟩

private theorem available_bit (xs : List α) (i : Fin n) :
    (prepare mask xs).available.getLsbD i = true ↔ ∃ x ∈ xs, (mask x).getLsbD i = true := by
  induction xs with
  | nil => simp [prepare, Plan.available]
  | cons x xs ih =>
    change ((mask x ||| (prepare mask xs).available).getLsbD i = true) ↔ _
    simp only [BitVec.getLsbD_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]

private theorem possible_iff (seen : BitVec n) (xs : List α) :
    seen ||| (prepare mask xs).available = BitVec.allOnes n ↔ Covered mask seen xs := by
  simp only [full_iff, Covered, BitVec.getLsbD_or, Bool.or_eq_true, available_bit]

private theorem include_iff (seen : BitVec n) (x : α) (xs : List α) :
    Covered mask seen (x :: xs) ↔ Covered mask (seen ||| mask x) xs := by
  simp [Covered, or_assoc]

private theorem enumerate_eq (xs : List α) (seen : BitVec n) :
    enumerate (BitVec.allOnes n) (prepare mask xs) seen =
      (FlatMatchSearch.sublists xs).filter (fun ys => decide (Covered mask seen ys)) := by
  induction xs generalizing seen with
  | nil => simp [prepare, enumerate, FlatMatchSearch.sublists, Covered, full_iff, List.filter_cons]
  | cons x xs ih =>
    by_cases possible : seen ||| (prepare mask (x :: xs)).available = BitVec.allOnes n
    · change seen ||| (mask x ||| (prepare mask xs).available) = _ at possible
      simp only [prepare, enumerate, possible, ite_true, ih, FlatMatchSearch.sublists,
        List.filter_append, List.filter_map, Function.comp_def, include_iff]
    · have dead := mt (possible_iff mask seen _).mpr possible
      rw [List.filter_eq_nil_iff.mpr (by
        intro ys hy accepted
        apply dead
        have small := (FlatMatchSearch.mem_sublists _ _).mp hy
        intro i
        exact ((of_decide_eq_true accepted) i).imp_right fun ⟨y, mem, bit⟩ => ⟨y, small.subset mem, bit⟩)]
      change ¬ seen ||| (mask x ||| (prepare mask xs).available) = _ at possible
      simp only [prepare, enumerate, possible, ite_false]

theorem support_bit (v : ACBasis.Vec n) (i : Fin n) :
    (support v).getLsbD i = decide (0 < v i) := by
  simp only [support, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

/-- The optimized traversal returns the same arms in the same order for every
basis, including zero columns, repeated supports and the empty problem. -/
theorem coveringSelections_eq (gs : List (ACBasis.Vec n)) :
    coveringSelections gs = selections gs := by
  unfold coveringSelections selections
  rw [enumerate_eq]
  apply List.filter_congr
  intro xs _
  simp only [Covered, covers, support_bit, decide_eq_true_eq]
  simp

end Tamarin.Homogeneous.Coverage
