import Tamarin.ACColumnSupport

open Tamarin Tamarin.ACBasis Tamarin.ACFeasibility Tamarin.ACFeasibility.ColumnSupport

-- Thirty-eight columns share the same positive contribution. The final two
-- columns can pay either row independently, or both at an incompatible ratio.
private def common (i : Fin 40) : Nat := if i.val < 38 then 1 else 0
private def separate : List (Row 40) :=
  [Row.ofWeights common (fun i => if i.val == 38 then 1 else 0),
   Row.ofWeights common (fun i => if i.val == 39 then 1 else 0)]
private def forcedRatio : List (Row 40) :=
  [Row.ofWeights common (fun i => if i.val < 38 then 0 else 1),
   Row.ofWeights common (fun i => if i.val < 38 then 0 else 2)]

#guard direct separate == none
#guard direct forcedRatio == none
#guard run separate 3 == none
#guard run separate 4 == some true
#guard run forcedRatio 820 == none
#guard run forcedRatio 821 == some false
#guard run (n := 40) [] 0 == none
#guard run (n := 40) [] 1 == some true

-- Small semantic cases include an empty denominator support and zero columns.
#guard run ([] : List (Row 0)) 1 == some true
#guard run [Row.ofWeights (fun _ : Fin 3 => 1) (fun _ => 0)] 4 == some false
#guard run [Row.ofWeights (fun _ : Fin 3 => 0) (fun _ => 0)] 1 == some true
