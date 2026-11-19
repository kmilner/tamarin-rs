import Tamarin.ACDirectFeasibility
import Tamarin.ACRationalCone
/-! Strict positive homogeneous feasibility as a single nonnegative cone-membership
problem. A common positive denominator keeps every certificate integral. -/
namespace Tamarin.ACFeasibility.ColumnCone
open ACBasis

/-- With signed column matrix A, the equation for a correction is
A z = d (-A · 1). The full positive witness then has coordinates d + zᵢ. -/
def Correction {n} (rs : List (Row n)) (d : Nat) (z : Vec n) : Prop :=
  ∀ r ∈ rs, d * total r.pos + dot r.pos z = d * total r.neg + dot r.neg z

private theorem dot_shift {n} (v : Vec n) (d : Nat) (z : Vec n) :
    dot v (fun i => d + z i) = d * total v + dot v z := by
  have shift : dot v (fun _ => d) = d * total v := by
    simpa [Cone.scale, dot] using Cone.dot_scale v d (fun _ => 1)
  simp only [dot, Nat.mul_add, total_add] at shift ⊢
  rw [shift]

theorem correction_iff {n} (rs : List (Row n)) (d : Nat) (z : Vec n) :
    Correction rs d z ↔ SystemHolds rs (fun i => d + z i) := by
  simp only [Correction,SystemHolds,Row.Holds,dot_shift]

theorem feasible_iff_correction {n} (rs : List (Row n)) :
    Feasible rs ↔ ∃ d > 0, ∃ z : Vec n, Correction rs d z := by
  constructor
  · rintro ⟨x, sol, live⟩
    refine ⟨1, by decide, fun i => x i - 1, (correction_iff ..).mpr ?_⟩
    have eq : (fun i => 1 + (x i - 1)) = x := funext fun i => by have := live i; omega
    rwa [eq]
  · rintro ⟨d, hd, z, cert⟩
    exact ⟨_, (correction_iff ..).mp cert, fun i => Nat.add_pos_left hd _⟩
end Tamarin.ACFeasibility.ColumnCone
