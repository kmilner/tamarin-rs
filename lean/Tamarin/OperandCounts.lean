import TamarinRuntime.OperandCounts
import Tamarin.GraphMatrix

namespace Tamarin.OperandCounts

/-- The sides alternate left and right. The per-side word bound ensures that
even a side consisting of a single repeated operand has exact word counts. -/
def Admitted (width : UInt64) (sides : Array (Array UInt64)) : Prop :=
  0 < width ∧ width ≤ 32 ∧ sides.size ≤ 128 ∧ sides.size % 2 = 0 ∧
    ∀ row ∈ sides, 0 < row.size ∧ row.size < UInt64.size ∧ ∀ k ∈ row, k < width

/-- In row order, each coefficient is the multiplicity of its column ID.
The counter is defined exactly on the stated input domain. -/
def Correct (count : Kernel) : Prop :=
  ∀ width sides m, count width sides = some m ↔
    Admitted width sides ∧ m = sides.map (fun row => GraphMatrix.counts width row.toList)

theorem run_correct : Correct run := by
  intro width sides m
  have eq : GraphMatrix.histogram width = fun row => GraphMatrix.counts width row.toList :=
    funext (GraphMatrix.histogram_counts width)
  simp only [run, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Array.all_eq_true_iff_forall_mem, eq, and_assoc]
  split
  · next h => change Admitted width sides at h; simp [h, eq_comm]
  · next h => change ¬Admitted width sides at h; simp [h]

/-- Reading a coefficient as an unbounded natural recovers all occurrences,
without modular reduction. -/
theorem coefficient {counter : Kernel} (contract : Correct counter) {width sides m}
    (h : counter width sides = some m) (r : Fin sides.size) (c : Fin width.toNat) :
    m[r.val]![c.val]!.toNat = sides[r].toList.count c.val.toUInt64 := by
  obtain ⟨ok, rfl⟩ := (contract ..).mp h
  have bound := (ok.2.2.2.2 _ (Array.getElem_mem r.isLt)).2.1
  have le := List.count_le_length (l := sides[r].toList) (a := c.val.toUInt64)
  have small : sides[r].toList.count c.val.toUInt64 < 2^64 := by
    simpa using Nat.lt_of_le_of_lt le (show sides[r].toList.length < UInt64.size by simpa using bound)
  have eq : ∀ xs : List UInt64, xs.count c.val.toUInt64 < 2^64 →
      (GraphMatrix.counts width xs)[c.val]!.toNat = xs.count c.val.toUInt64 := by
    intro xs hx
    simp [GraphMatrix.counts, getElem!_pos, Nat.toUInt64, Nat.mod_eq_of_lt hx]
  simpa [getElem!_pos, r.isLt] using eq _ small

end Tamarin.OperandCounts
