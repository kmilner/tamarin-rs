import Std

namespace Tamarin.OpenMatchSelect

abbrev Packet := Array (Array UInt64)
abbrev Kernel := UInt64 → UInt64 → Option Packet

/-- Number of ordered selections without replacement. -/
def ways (n : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => n * ways (n-1) k

def picks (pool : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k+1 => pool.flatMap fun i => (picks (pool.erase i) k).map (i :: ·)

/-- Each arm supplies the positions of the rigid factors in pattern order,
then the remaining subject positions in input order. -/
def run : Kernel := fun k n =>
  if n < k then some #[]
  else if n ≤ 64 && ways n.toNat k.toNat ≤ 4096 then
    let pool := List.range n.toNat
    some ((picks pool k.toNat).toArray.map fun picked =>
      (picked ++ pool.filter (fun i => !picked.contains i)).toArray.map Nat.toUInt64)
  else none

end Tamarin.OpenMatchSelect
