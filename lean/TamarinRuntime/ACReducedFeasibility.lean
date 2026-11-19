import TamarinRuntime.ACRowReduction
import TamarinRuntime.ACDirectFeasibility

namespace Tamarin.ACFeasibility
open ACBasis

/-- Solve a pivot coordinate while scaling the whole vector to clear its
denominator. A failed trial says nothing about alternative free coordinates. -/
def adjust {n} (r : Row n) (x : Vector Nat n) : Option (Vector Nat n) := do
  let left := dot r.pos (fun i => x[i])
  let right := dot r.neg (fun i => x[i])
  if left = right then return x
  let j ← (List.finRange n).find? (fun i => 0 < r.pos i || 0 < r.neg i)
  let a := r.pos j + r.neg j
  let (wanted, spent) := if r.neg j = 0 then (right,left) else (left,right)
  let gap := (wanted+a*x[j]) - spent
  guard (0 < gap)
  let g := a.gcd gap
  let scale := a / g
  let pivot := gap / g
  let y := Vector.ofFn fun i => if i = j then pivot else scale*x[i]
  guard (y.all (· < 2^128))
  return y

def positiveCertificate {n} (rs : List (Row n)) (x : Vector Nat n) : Bool :=
  x.all (0 < ·) && rs.all fun r => dot r.pos (fun i => x[i]) == dot r.neg (fun i => x[i])

def reducedFeasible {n} (rs : List (Row n)) : Option Bool := do
  guard (n*rs.length*rs.length ≤ 524288)
  let out ← RowReduction.echelon rs.length rs
  if let some b := direct out then return b
  let trial ← out.foldrM adjust (Vector.replicate n 1)
  guard (positiveCertificate rs trial)
  return true

end Tamarin.ACFeasibility
