import TamarinRuntime.GraphMatrix
import TamarinRuntime.ACGraphAnswers

namespace Tamarin.GraphUnification
open Homogeneous

abbrev Kernel := UInt64 → UInt64 → UInt64 → Array UInt64 → Array (Array UInt64) →
  Array UInt64 → Option Answers

/-- Identity systems use the whole-graph identity reply, which needs no witnesses. -/
def hasConstraint : List (Array UInt64) → Bool
  | lhs :: rhs :: tail => lhs != rhs || hasConstraint tail
  | _ => false

def runWith (build : UInt64 → UInt64 → UInt64 → Array UInt64 → Array (Array UInt64) →
    Array UInt64 → Option Matrix) (solve : UInt64 → Matrix → Option Answers) : Kernel :=
  fun width symbol sort decls nodes roots => do
    let m ← build width symbol sort decls nodes roots
    guard (hasConstraint m.toList)
    solve width m

abbrev buildMatrix := GraphMatrix.buildUpTo RayPacket.maxWidth

def run : Kernel := runWith buildMatrix GraphAnswers.solve

end Tamarin.GraphUnification
