import TamarinRuntime.Homogeneous
import Std.Data.HashMap

namespace Tamarin.AnswerProjection
open Homogeneous

abbrev Kernel := UInt64 → Answers → Option Answers

def insertSlot (seen : Std.HashMap UInt64 Nat) (slot : UInt64) : Std.HashMap UInt64 Nat :=
  seen.insertIfNew slot seen.size

/-- The same slot can occur in several columns and several answers. -/
def indexSlots (answers : Answers) : Std.HashMap UInt64 Nat :=
  answers.foldl (fun seen arm => arm.foldl (fun seen row => row.foldl insertSlot seen) seen) ∅

def project (width : UInt64) (answers : Answers) : Option Answers := do
  guard (0 < width ∧ width ≤ 65)
  guard (answers.all fun arm => arm.size == width.toNat && arm.all (fun row => !row.isEmpty))
  let indices := indexSlots answers
  guard (indices.size ≤ UInt64.size)
  return answers.map fun arm => Array.ofFn fun i : Fin arm.size =>
    let row := arm[i]
    row.foldl (fun acc slot => acc.push ((indices[slot]?.getD indices.size).toUInt64))
      ((Array.emptyWithCapacity (row.size + 1)).push i.val.toUInt64)

end Tamarin.AnswerProjection
