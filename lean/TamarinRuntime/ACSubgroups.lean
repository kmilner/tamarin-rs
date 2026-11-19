import TamarinRuntime.FlatMatch

namespace Tamarin.ACSubgroups

/-- Enumerate positions, keeping equal operand occurrences distinct. -/
def run (n : UInt64) : Option (Array (Array UInt64)) :=
  if n.toNat ≤ 10 then
    some (((FlatMatchSearch.sublists ((List.range n.toNat).map Nat.toUInt64)).filter
      (fun row => 2 ≤ row.length)).map List.toArray).toArray
  else none

end Tamarin.ACSubgroups
