import TamarinRuntime.ACReducedFeasibility
import TamarinRuntime.ACRationalProjection

namespace Tamarin.ACBasis.PrincipalRay
open ACFeasibility
variable {n : Nat}

def leading (r : Row n) := (List.finRange n).find? (fun i => r.pos i != r.neg i)

def freeColumns (rows : List (Row n)) : List (Fin n) :=
  let pivots := rows.filterMap leading
  (List.finRange n).filter fun i => !pivots.contains i

/-- Starting from the sole free coordinate, a positive witness and the leading
row at every other coordinate certify all solutions lie on one rational ray. -/
def check (rows : List (Row n)) : Option (Vector Nat n) := do
  guard ((freeColumns rows).length = 1)
  let trial ← rows.foldrM adjust (Vector.replicate n 1)
  let ray := RationalProjection.primitive (fun i => trial[i])
  if positiveCertificate rows ray && ray.toList.foldr Nat.gcd 0 == 1 then return ray else none

def run (rows : List (Row n)) : Option (Vector Nat n) := do
  guard (n > 0 ∧ n * max 1 rows.length * max 1 rows.length ≤ 524288)
  check rows <|> (RowReduction.echelon rows.length rows >>= check)

end Tamarin.ACBasis.PrincipalRay
