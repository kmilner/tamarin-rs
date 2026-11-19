import Tamarin.MixedCancellationShape
import TamarinRuntime.BinaryCancellation

namespace Tamarin.Rewriting.MixedCancellation

/-- Bit positions refer to the same two Fresh witnesses and Msg witness
throughout one row, including its normal value. -/
def mask (left right residual : Bool) : UInt64 :=
  (if left then 1 else 0) + (if right then 2 else 0) + (if residual then 4 else 0)

def Shape.packet : Shape → Array UInt64
  | .diagonal => #[1,1,4,4]
  | .separate l r tail => #[1,2,mask l r tail,mask (!l) (!r) tail]

/-- A candidate can choose its own enumeration order and repeat rows. -/
def RowsCorrect (rows : Array (Array UInt64)) :=
  ∀ row, row ∈ rows ↔ ∃ sh : Shape, row = sh.packet

theorem candidate_rows : RowsCorrect BinaryCancellationCandidate.mixedRows := by
  let flags := [false,true]
  let shapes := Shape.diagonal :: flags.flatMap fun l =>
    flags.flatMap fun r => flags.map fun tail => Shape.separate l r tail
  have covered (sh : Shape) : sh ∈ shapes := by
    cases sh with
    | diagonal => decide
    | separate l r tail => cases l <;> cases r <;> cases tail <;> decide
  have all : ∀ sh ∈ shapes, sh.packet ∈ BinaryCancellationCandidate.mixedRows.toList := by decide
  have only : ∀ row ∈ BinaryCancellationCandidate.mixedRows.toList, row ∈ shapes.map Shape.packet := by decide
  intro row
  constructor
  · intro mem
    obtain ⟨sh,_,eq⟩ := List.mem_map.mp (only row (Array.mem_def.mp mem))
    exact ⟨sh,eq.symm⟩
  · rintro ⟨sh,rfl⟩
    exact Array.mem_def.mpr (all sh (covered sh))

end Tamarin.Rewriting.MixedCancellation
