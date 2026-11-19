import TamarinRuntime.ACTwoRowFeasibility

namespace Tamarin.ACFeasibility.LowRank
open ACBasis
variable {n : Nat}

def coeff (p : Row n) (i : Fin n) : Int := (p.pos i : Int) - p.neg i

def minor (p q : Row n) (j k : Fin n) : Int :=
  coeff p j * coeff q k - coeff p k * coeff q j

def pivot (rows : List (Row n)) (weight : Row n → Fin n → Int) : Option (Row n × Fin n) :=
  let indices := List.finRange n
  rows.findSome? fun row => (indices.find? (fun i => weight row i != 0)).map (row,·)

inductive Basis (n : Nat) where
  | zero
  | line (p : Row n)
  | plane (p q : Row n)

/-- Find independent input rows and certify all remaining rows by cross
multiplication in the two pivot columns. Scans the existing coefficients with
linear work in the matrix size, retaining two rows and one index list. -/
def select (rows : List (Row n)) : Option (Basis n) := do
  let some (p,j) := pivot rows coeff | return .zero
  let some (q,k) := pivot rows (fun r => minor p r j) | return .line p
  let d := minor p q j k
  let indices := List.finRange n
  guard (rows.all fun r =>
    let u := minor r q j k
    let v := minor p r j k
    indices.all fun i => d * coeff r i == u * coeff p i + v * coeff q i)
  return .plane p q

def Basis.verdict : Basis n → Bool
  | .zero => true
  | .line p => TwoRow.decidePair p p
  | .plane p q => TwoRow.decidePair p q

def run (rows : List (Row n)) := (select rows).map Basis.verdict

end Tamarin.ACFeasibility.LowRank
