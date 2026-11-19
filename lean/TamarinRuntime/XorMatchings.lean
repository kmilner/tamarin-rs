namespace Tamarin.XorMatchingCandidate

/-- Fixed points denote unmatched positions. Swap two previously fixed
positions in the partner map to record one cancellation pair. -/
def pair (f : Nat → Nat) (a b i : Nat) : Nat :=
  if i = a then b else if i = b then a else f i

/-- The new position either stays unmatched or pairs with exactly one
previously unmatched position. The empty matching occurs at every width. -/
def enumerate : Nat → List (Nat → Nat)
  | 0 => [id]
  | n+1 => (enumerate n).flatMap fun f =>
    f :: (((List.range n).filter fun i => f i == i).map fun i => pair f n i)

def run (width : UInt64) : Option (Array (Array UInt64)) :=
  if 1 ≤ width.toNat ∧ width.toNat ≤ 9 then
    some (((enumerate width.toNat).map fun f =>
      Array.ofFn fun (i : Fin width.toNat) => (f i).toUInt64).toArray)
  else none

end Tamarin.XorMatchingCandidate
