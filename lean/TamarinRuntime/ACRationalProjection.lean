import TamarinRuntime.Homogeneous

namespace Tamarin.ACBasis.RationalProjection
open Homogeneous
variable {n k : Nat}

/-- A graph has at most 32 variables and 64 equations. Each stage stores at
most 256 dense rays with at most 128 bits per coordinate. -/
def maxRays := 256
def maxCoeff := 2^128 - 1

def neutralIds (p : Row k) := (List.finRange k).filter fun i => p.pos i == 0 && p.neg i == 0
def positiveIds (p : Row k) := (List.finRange k).filter fun i => 0 < p.pos i
def negativeIds (p : Row k) := (List.finRange k).filter fun i => 0 < p.neg i

def combine (g : Fin k → Vec n) (p : Row k) (i j : Fin k) : Vec n :=
  fun t => p.neg j * g i t + p.pos i * g j t

def images (g : Fin k → Vec n) (p : Row k)
    (neutrals positives negatives : List (Fin k)) : List (Vec n) :=
  neutrals.map g ++ positives.flatMap fun i => negatives.map (combine g p i)

/-- Remove the gcd before comparing rays. The all-zero vector uses divisor 1. -/
def primitive (x : Vec n) : Vector Nat n :=
  let v := Vector.ofFn x
  let d := max 1 (v.toList.foldr Nat.gcd 0)
  if d == 1 then v else v.map (· / d)

def compact (xs : List (Vec n)) := ((xs.map primitive).eraseDups).map coordinates

def cached (p : Row k) : Row k :=
  let a := Vector.ofFn p.pos
  let b := Vector.ofFn p.neg
  ⟨coordinates a,coordinates b, by simpa [a,b,coordinates] using p.disjoint⟩

def project (r : Row n) (gs : List (Vec n)) : Option (List (Vec n)) := do
  let store := gs.toArray
  let get := fun j : Fin gs.length => store[j.val]'(by simp [store])
  let p := cached (r.pullback get)
  let zs := neutralIds p
  let ps := positiveIds p
  let ns := negativeIds p
  -- Charge the entire cross product before allocating its first vector.
  guard (zs.length + ps.length * ns.length ≤ maxRays)
  guard (∀ i, p.pos i ≤ maxCoeff ∧ p.neg i ≤ maxCoeff)
  let next := compact (images get p zs ps ns)
  guard (next.all fun v => (List.finRange n).all fun t => v t ≤ maxCoeff)
  return next

def basis {n} : List (Row n) → Option (List (Vec n))
  | [] => if n ≤ 32 then some (units n) else none
  | r :: rs => do
    let gs ← basis rs
    project r gs

end Tamarin.ACBasis.RationalProjection
