import TamarinRuntime.GraphMatrix

namespace Tamarin.OperandCounts

abbrev Kernel := UInt64 → Array (Array UInt64) → Option Homogeneous.Matrix

/-- Each side lists column IDs in flattened operand order. Repeated references
are distinct occurrences, including references to the same compound term. -/
def run : Kernel := fun width sides =>
  if 0 < width && width ≤ 32 && sides.size ≤ 128 && sides.size % 2 == 0 &&
      sides.all (fun row => 0 < row.size && row.size < UInt64.size && row.all (· < width)) then
    some (sides.map (GraphMatrix.histogram width))
  else none

end Tamarin.OperandCounts
