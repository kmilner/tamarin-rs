import TamarinRuntime.ACSpanCertificate

namespace Tamarin.ACBasis.ForcedCoordinates
open SpanCertificate ACFeasibility
variable {n : Nat}

abbrev Step (n : Nat) := ZRow n × Fin n

/-- Single shared fraction-free elimination plan. Each pivot acts on every
subsequent row and, later, on just the coordinate units that use a pivot. -/
def prepare : Nat → List (ZRow n) → Option (List (Step n))
  | 0, [] | _+1, [] => some []
  | 0, _::_ => none
  | k+1, p::rs => do
    guard (bounded p && rs.all bounded)
    match pivot p with
    | none => prepare k rs
    | some j =>
      return (p,j) :: (← prepare k (rs.map (eliminate p j)))

def unit (j : Fin n) : ZRow n := Vector.ofFn fun i => if i = j then 1 else 0

def project (steps : List (Step n)) (v : ZRow n) : ZRow n :=
  steps.foldl (fun t (p,j) => eliminate p j t) v

def scale (steps : List (Step n)) : Int := (steps.map fun (p,j) => p[j]).prod

abbrev Key (n : Nat) := List (Fin n × Int)

def sparse (v : ZRow n) : Key n :=
  (List.finRange n).filterMap fun j => if v[j] = 0 then none else some (j,v[j])

def signatures (steps : List (Step n)) : Vector (Key n) n :=
  let pivots := steps.map Prod.snd
  let common := scale steps
  Vector.ofFn fun i =>
    if i ∈ pivots then sparse (project steps (unit i)) else [(i,common)]

def origins (ks : Vector (Key n) n) (is : List (Fin n)) : Std.HashMap (Key n) (Fin n) :=
  is.foldr (fun i tab => tab.insert ks[i] i) ∅

def labels (ks : Vector (Key n) n) : Vector Nat n :=
  let idx := origins ks (List.finRange n)
  Vector.ofFn fun i => (idx[ks[i]]?).elim n Fin.val

def equation (i j : Fin n) : Row n := Row.ofWeights (spike i 1) (spike j 1)

/-- Equal labels denote exactly those coordinate pairs whose difference
lies in the rational span. A free (nonpivot) column uses one sparse entry.
There is no square table of units or pairwise search over coordinates. -/
def run (rs : List (Row n)) : Option (Vector Nat n) := do
  guard (dimensions n rs.length)
  let steps ← prepare rs.length (rs.map signed)
  return labels (signatures steps)

end Tamarin.ACBasis.ForcedCoordinates
