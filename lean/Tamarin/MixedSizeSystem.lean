import Tamarin.UnifierSize
import Tamarin.ACCertificate

namespace Tamarin.MixedSizeSystem
open ACBasis FiniteOccurs ACFeasibility

variable {sig : Signature} {n : Nat}

/-- The first coordinate homogenizes the fixed part of each equation's size.
Adding the opposite side's variable count cancels the single node already
included for each occurrence in the unsubstituted term. -/
def row (names : Fin n → Variable) (e : Equation sig) : Row (n+1) :=
  Row.ofWeights
    (prepend (nodes e.lhs + e.rhs.variables.length) (coefficients names e.lhs.variables))
    (prepend (nodes e.rhs + e.lhs.variables.length) (coefficients names e.rhs.variables))

private theorem nodes_pos (t : Term sig) : 0 < nodes t := by
  cases t with
  | var | atom => exact Nat.zero_lt_one
  | free _ _ | ac | comm => exact Nat.zero_lt_succ _

private theorem sum_sizes (σ : Substitution sig) (xs : List Variable) :
    (xs.map (fun v => nodes (σ.image v))).sum =
      (xs.map (fun v => nodes (σ.image v) - 1)).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have := nodes_pos (σ.image v)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem dot_prepend (c : Nat) (v x : Vec n) :
    dot (prepend c v) (prepend 1 x) = c + dot v x := by
  simp [dot,total,List.ofFn_succ,prepend]

/-- Any unifier of the whole mixed conjunction supplies one strictly positive
size for each variable image, shared across every constructor and equation. -/
theorem feasible_of_solves (p : Problem sig) (names : Fin n → Variable)
    (unique : ∀ i j, names i = names j → i = j)
    (live : ∀ e ∈ p, ∀ v ∈ e.lhs.variables ++ e.rhs.variables, ∃ i, names i = v)
    (σ : Substitution sig) (sol : p.Solves σ) :
    Feasible (p.map (row names)) := by
  let size := fun v => nodes (σ.image v)
  refine ⟨prepend 1 (fun i => size (names i)), ?_, Fin.cases (show 0 < 1 from Nat.zero_lt_one) (fun i => nodes_pos _)⟩
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  rw [row, Row.ofWeights_holds, dot_prepend, dot_prepend, weight_eq names unique, weight_eq names unique]
  · have eq := nodes_equiv (sol e he)
    rw [UnifierSize.substituted,UnifierSize.substituted] at eq
    have l := sum_sizes σ e.lhs.variables
    have r := sum_sizes σ e.rhs.variables
    dsimp only [size]
    omega
  · exact fun v hv => live e he v (List.mem_append_right _ hv)
  · exact fun v hv => live e he v (List.mem_append_left _ hv)

/-- A checked negative size certificate refutes the original term equations.
A positive size assignment alone makes no claim about term unifiability. -/
theorem refutes (p : Problem sig) (names : Fin n → Variable)
    (unique : ∀ i j, names i = names j → i = j)
    (live : ∀ e ∈ p, ∀ v ∈ e.lhs.variables ++ e.rhs.variables, ∃ i, names i = v)
    {c} (no : checkCertificate (p.map (row names)) c = some false) : ¬ p.Satisfiable := by
  rintro ⟨σ,sol⟩
  exact Bool.noConfusion ((checkCertificate_sound _ _ no).mpr (feasible_of_solves p names unique live σ sol))

end Tamarin.MixedSizeSystem
