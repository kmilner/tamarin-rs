import TamarinRuntime.ACThreeColumns

namespace Tamarin.ACFeasibility.PairCorrection
open ACBasis
variable {n : Nat}

structure Prepared (n : Nat) where
  row : Row n
  left : Nat
  right : Nat

def prepare (r : Row n) : Prepared n := ⟨r,total r.pos,total r.neg⟩

/-- With one exceptional coordinate the second group is empty. -/
def counts (v : Vec n) (sum : Nat) (j k : Fin n) : Vector Nat 3 :=
  let x := v j
  let y := if j = k then 0 else v k
  #v[x,y,sum-x-y]

def project (j k : Fin n) (p : Prepared n) : Row 3 :=
  let left := counts p.row.pos p.left j k
  let right := counts p.row.neg p.right j k
  Row.ofWeights (fun i => left[i]) (fun i => right[i])

/-- Collapse all ordinary coordinates to one common value. A negative
three-column result rules out only that choice of exceptional coordinates. -/
def run (rs : List (Row n)) : Option Bool :=
  if n*n*max 1 rs.length > 200000 then none else
  if n = 0 then some true else
  let prepared := rs.map prepare
  let indices := List.finRange n
  if indices.any (fun j => indices.any (fun k => j ≤ k && ThreeColumns.decide (prepared.map (project j k)))) then
    some true else none

end Tamarin.ACFeasibility.PairCorrection
