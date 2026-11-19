import TamarinRuntime.OperandUnification
import Tamarin.OperandCounts
import Tamarin.GraphUnification

namespace Tamarin.OperandUnification
open Homogeneous

def matrix (width : UInt64) (sides : Array (Array UInt64)) : Matrix :=
  sides.map fun row => GraphMatrix.counts width row.toList

/-- Acceptance and deferral of the compound-operand export, independently
of how it builds the numeric matrix or how the matrix solver searches. -/
def Refines (run : Kernel) (solve : UInt64 → Matrix → Option Answers) : Prop :=
  ∀ width sides raw, run width sides = some raw ↔ OperandCounts.Admitted width sides ∧
    GraphUnification.Nontrivial (matrix width sides).toList ∧
    solve width (matrix width sides) = some raw

theorem run_refines {count} (h : OperandCounts.Correct count)
    (solve : UInt64 → Matrix → Option Answers) : Refines (runWith count solve) solve := by
  intro width sides raw
  rw [← GraphUnification.hasConstraint_iff]
  cases hc : count width sides with
  | none =>
    have invalid : ¬ OperandCounts.Admitted width sides := by
      intro adm
      have := (h width sides (matrix width sides)).mpr ⟨adm,rfl⟩
      simp_all
    simp [runWith,hc,invalid]
  | some m =>
    obtain ⟨admitted,rfl⟩ := (h ..).mp hc
    by_cases active : GraphUnification.hasConstraint (matrix width sides).toList = true <;>
      simp_all [runWith, matrix, guard, failure]

end Tamarin.OperandUnification
