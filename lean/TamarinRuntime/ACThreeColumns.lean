import TamarinRuntime.ACLowRank

namespace Tamarin.ACFeasibility.ThreeColumns
open ACBasis

/-- A positive solution in three dimensions puts every row in a common
plane. A third independent row therefore decides infeasibility. -/
def decide (rs : List (Row 3)) : Bool := (LowRank.run rs).getD false

def run {n} (rs : List (Row n)) : Option Bool :=
  if h : n = 3 then some (decide (h ▸ rs)) else none

end Tamarin.ACFeasibility.ThreeColumns
