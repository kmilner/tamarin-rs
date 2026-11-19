import Tamarin.ACBagSearch
open Tamarin.Matching

/-- Enumerate ordinary bag-valued assignments directly. Small reference
targets use only 7 and 9, with at most two copies of either. -/
private def reference (rows : ACBagSearch.Rows) : Bool :=
  let images : List (List UInt64) := ((List.range 3).flatMap fun i =>
    (List.range 3).map fun j => List.replicate i 7 ++ List.replicate j 9).filter (!·.isEmpty)
  images.any fun x => images.any fun y => rows.all fun (pattern,subject) =>
    decide ((pattern.flatMap fun k => if k == 17 then x else y).Perm subject)

private def samples : List (List UInt64 × List UInt64) :=
  let patterns : List (List UInt64) := [[],[17],[17,17],[17,23],[17,17,23],[17,23,23]]
  let subjects : List (List UInt64) := [[],[7],[9],[7,9],[7,7,9],[7,7,9,9],[9,9,7]]
  patterns.flatMap fun p => subjects.map (p,·)

private def items (copies : Nat) : List UInt64 :=
  (List.range 65).flatMap fun i => List.replicate copies i.toUInt64

def main : IO Unit := do
  for r in samples do
    for s in samples do
      let rows := [r,s]
      let expected := reference rows
      unless ACBagSearch.run rows == some expected do
        throw (IO.userError s!"Incorrect simultaneous match decision on {rows}")
  let patterns : List UInt64 × List UInt64 := ([17,17,23], [17,23,23])
  let query : ACBagSearch.Rows := [(patterns.1,items 3),(patterns.2,items 3)]
  unless ACBagSearch.run query == some true do
    throw (IO.userError "Each of the 65 frozen factors can occur once in each capture")
  unless ACBagSearch.run [(patterns.1,items 3),(patterns.2,items 2)] == some false do
    throw (IO.userError "Two feasible equations require incompatible multiplicities")
  unless ACBagSearch.run [([17,23], [7])] == some false do
    throw (IO.userError "Separate alternatives cannot jointly supply two nonempty captures")
  unless ACBagSearch.run [([17,23], [7,9]),([17,17,23], [9,7,9])] == some true do
    throw (IO.userError "Sharing across rows admits x=[9], y=[7]")
