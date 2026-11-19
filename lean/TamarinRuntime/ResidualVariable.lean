import TamarinRuntime.Residual
import TamarinWire

namespace Tamarin.ResidualVariable

abbrev Kernel := Bool → UInt64 → UInt64 → UInt8 → UInt64 → Array UInt64 → UInt8

def swap (action : UInt8) : UInt8 :=
  if action == 3 then 4 else if action == 4 then 3 else action

def shape (kind : UInt8) (ids : Array UInt64) : Bool :=
  if kind == 0 then ids.size == 1 else if kind == 1 then ids.isEmpty else true

/-- A variable operand and the root kind, root sort and variable identities of its
opposite operand. A root variable has exactly one identity, an atom has none. -/
def run : Kernel := fun right key keySort kind valueSort ids =>
  if keySort ≤ 4 && valueSort ≤ 4 && kind ≤ 4 && shape kind ids then
    let rootVar := kind == 0
    let member := ids.contains key
    if rootVar && member && keySort != valueSort then 255
    else
      let action := Residual.step 0 kind (rootVar && member) false
        (Whole.subsort valueSort keySort) (rootVar && Whole.subsort keySort valueSort)
        (!rootVar && member)
      if right then swap action else action
  else 255

end Tamarin.ResidualVariable
