import TamarinRuntime.Homogeneous

namespace Tamarin.Homogeneous.RayPacket
open ACBasis

abbrev Candidate := {n : Nat} → List (Row n) → Option (Vector Nat n)

/-- At most 64 equations are admitted by the graph decoder. A positive
one-dimensional kernel can have at most one more column than independent rows. -/
def maxWidth : UInt64 := 65

/-- One reusable slot represents the primitive ray at every coordinate.
Budget the arm, the tags and row headers before expanding any multiplicities. -/
def fallback (ray : Candidate) (width : UInt64) (m : Matrix) : Option Answers := do
  guard (0 < width ∧ width ≤ maxWidth ∧ m.size ≤ 128)
  let rows ← readRows width.toNat m.toList
  let generator ← ray rows
  let g := coordinates generator
  guard (1 + 2*width.toNat + total g ≤ 65536)
  return emit [g]

def solve (ray : Candidate) (width : UInt64) (m : Matrix) : Option Answers :=
  Homogeneous.solve width m <|> fallback ray width m

end Tamarin.Homogeneous.RayPacket
