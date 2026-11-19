import TamarinRuntime.ACBasis

namespace Tamarin.ACFeasibility.Separation
open ACBasis
variable {n : Nat}

/-- Compute one coefficient of the weighted sum of signed rows. -/
def column (pairs : List (Int × Row n)) (i : Fin n) : Int :=
  pairs.foldl (fun acc (w,r) => acc + w * ((r.pos i : Int) - r.neg i)) 0

/-- Evaluate each combined coefficient once. A negative entry invalidates
the certificate immediately; strict positivity must occur in some column. -/
def scan (pairs : List (Int × Row n)) : List (Fin n) → Bool → Bool
  | [], seen => seen
  | i :: rest, seen =>
    let c := column pairs i
    if c < 0 then false else scan pairs rest (seen || 0 < c)

def separates (rows : List (Row n)) (weights : List Int) : Bool :=
  weights.length == rows.length &&
    scan ((weights.zip rows).filter (fun (w,_) => w != 0)) (List.finRange n) false

end Tamarin.ACFeasibility.Separation
