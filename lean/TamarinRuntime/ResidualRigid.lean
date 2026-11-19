import Std

namespace Tamarin.ResidualRigid

abbrev Kernel := UInt8 → UInt64 → Array UInt64 → UInt8 → UInt64 → Array UInt64 → UInt8

def shape (k : UInt8) (n : Nat) : Bool :=
  match k with
  | 1 => n == 0
  | 2 => true
  | 3 => n == 2
  | 4 => n ≥ 2
  | _ => false

/-- Root IDs are compared only within a kind. Child references are ordered,
including the repeated occurrences of a flat AC node. -/
def run : Kernel := fun lk lh ls rk rh rs =>
  if !(shape lk ls.size && shape rk rs.size) then 255
  else if lk != rk || lh != rh then 1
  else if lk == 2 && ls.size != rs.size then 255
  else if ls == rs then 2
  else if lk == 2 then 5
  else if lk == 3 then 6
  else 0

end Tamarin.ResidualRigid
