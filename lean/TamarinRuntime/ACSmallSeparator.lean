import TamarinRuntime.ACSeparation

namespace Tamarin.ACFeasibility.SmallSeparator
open ACBasis
variable {n : Nat}

/-- Try sparse certificates early while visiting the entire signed box. -/
def digits (radius : Nat) : List Int :=
  0 :: (List.range radius).flatMap fun i => [(i+1 : Nat),-((i+1 : Nat) : Int)]

def search (choices : List Int) : Nat → (List Int → Bool) → Bool
  | 0, test => test []
  | k+1, test => choices.any fun w => search choices k (fun tail => test (w::tail))

def radiusFor (width height : Nat) : Nat :=
  -- At 13 rows even the smallest nontrivial box has more than 524288 points.
  if height > 12 then 0 else
  let cost := fun radius => (2*radius+1)^height * max 1 height * max 1 width
  if cost 3 ≤ 524288 then 3 else if cost 2 ≤ 524288 then 2 else if cost 1 ≤ 524288 then 1 else 0

/-- Failure to find a separator within the budget gives no feasibility verdict. -/
def run (rows : List (Row n)) : Option Bool :=
  let radius := radiusFor n rows.length
  if radius = 0 then none else
  if search (digits radius) rows.length (Separation.separates rows) then some false else none

end Tamarin.ACFeasibility.SmallSeparator
