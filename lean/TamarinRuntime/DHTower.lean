import TamarinRuntime.FlatMatch

namespace Tamarin.DHTowerCandidate

/-- Postfix bytecode. Slots starting at 9 are occurrences in the list of
positive exponent factors. Repeated occurrences retain their own slot. -/
def cancellation : List Nat → List (Array UInt64)
  | [] => []
  | i :: is =>
    let product := (9+i).toUInt64 :: is.flatMap (fun j => [(9+j).toUInt64, 7])
    [([2,3] ++ product ++ [6,7,8]).toArray, ([2] ++ product ++ [6,8]).toArray,
     ([2,3,4] ++ product ++ [7,6,7,8]).toArray, ([2,4] ++ product ++ [7,6,8]).toArray]

def images (size : UInt64) : Option (Array (Array UInt64)) :=
  if 2 ≤ size.toNat ∧ size.toNat ≤ 8 then
    some (([#[0], #[5], #[2,3,8]] ++
      (FlatMatchSearch.sublists (List.range size.toNat)).flatMap cancellation).toArray)
  else none

end Tamarin.DHTowerCandidate
