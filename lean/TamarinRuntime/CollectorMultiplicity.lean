import Std.Data.HashMap

namespace Tamarin.CollectorMultiplicity

abbrev Kernel := Array UInt64 → Array UInt64 → Bool

structure Tally where
  counts : Std.HashMap UInt64 Nat
  largest : Nat

def increment (state : Tally) (key : UInt64) : Tally :=
  let n := state.counts.getD key 0 + 1
  ⟨state.counts.insert key n,max state.largest n⟩

def largestCount (xs : Array UInt64) : Nat :=
  (xs.foldl increment ⟨∅,0⟩).largest

/-- Every collector needs at least one factor in its image. A repeated
collector thus needs a residual class with at least that many occurrences. -/
def run : Kernel := fun occurrences residual =>
  let required := largestCount occurrences
  if required > residual.size then false
  else required ≤ 1 || required ≤ largestCount residual

end Tamarin.CollectorMultiplicity
