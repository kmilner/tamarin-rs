import TamarinRuntime.OperandCounts
import TamarinRuntime.GraphUnification

namespace Tamarin.OperandUnification
open Homogeneous

abbrev Kernel := UInt64 → Array (Array UInt64) → Option Answers

/-- The worklist retains each compound term locally. Repeated references to
the same column contribute their full multiplicity in every equation. -/
def runWith (count : UInt64 → Array (Array UInt64) → Option Matrix)
    (solve : UInt64 → Matrix → Option Answers) : Kernel :=
  fun width sides => do
    let matrix ← count width sides
    guard (GraphUnification.hasConstraint matrix.toList)
    solve width matrix

end Tamarin.OperandUnification
