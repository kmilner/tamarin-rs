import Tamarin.OperandCounts

namespace Tamarin.OperandCountsTests
open OperandCounts

#guard run 2 #[#[1,1,0,1], #[0,1], #[0], #[0]] ==
  some #[#[1,3], #[1,1], #[1,0], #[1,0]]
#guard run 2 #[#[0], #[0]] == some #[#[1,0], #[1,0]]
#guard run 1 #[] == some #[]
#guard run 0 #[] == none
#guard run 33 #[] == none
#guard run 1 #[#[0]] == none
#guard run 1 #[#[], #[0]] == none
#guard run 32 #[#[31], #[32]] == none
#guard run 32 #[#[18446744073709551615], #[0]] == none
#guard (run 32 (Array.replicate 128 #[31])).isSome
#guard run 32 (Array.replicate 130 #[31]) == none
#guard run 1 #[Array.replicate 4097 0, #[0]] == some #[#[4097], #[1]]

-- Enumerate every side up to length three, including empty sides, out-of-range
-- columns, repeated columns, and both possible orders of each pair.
private def sideWords : Nat → List (List UInt64)
  | 0 => [[]]
  | n+1 => [] :: ([0,1,2] : List UInt64).flatMap (fun i => (sideWords n).map (i :: ·))

private def stress : Bool := Id.run do
  for w in [1,2,3] do
    for l in sideWords 3 do
      for r in sideWords 3 do
        let sides := [l,r]
        let valid := sides.all (fun row => !row.isEmpty && row.all (· < w))
        let expected := sides.map fun row => (List.range w.toNat).toArray.map
          fun i => (row.filter (· == i.toUInt64)).length.toUInt64
        if run w (sides.map List.toArray).toArray != (if valid then some expected.toArray else none) then
          return false
  return true
#guard stress

end Tamarin.OperandCountsTests
