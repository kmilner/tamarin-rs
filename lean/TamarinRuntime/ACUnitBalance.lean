import TamarinRuntime.ACBasis

namespace Tamarin.ACBasis

/-- After cancellation, every nonzero coefficient is the same positive weight. -/
def Row.equalMagnitude {n} (r : Row n) : Bool :=
  let magnitude := r.cap
  (List.finRange n).all fun i =>
    (r.pos i == 0 || r.pos i == magnitude) && (r.neg i == 0 || r.neg i == magnitude)

namespace UnitBalance

def pair {n} (i j : Fin n) : Vec n := fun k => spike i 1 k + spike j 1 k

/-- Indices after i appear in increasing order. To retain Cartesian box
order, visit the second nonzero coordinate in decreasing order. -/
def block {n} (r : Row n) (i : Fin n) (tail : List (Fin n)) : List (Vec n) :=
  if 0 < r.pos i then ((tail.filter (fun j => 0 < r.neg j)).reverse).map (pair i)
  else if 0 < r.neg i then ((tail.filter (fun j => 0 < r.pos j)).reverse).map (pair i)
  else [spike i 1]

def blocks {n} (r : Row n) : List (Fin n) → List (List (Vec n))
  | [] => []
  | i :: rest => block r i rest :: blocks r rest

def enumerate {n} (r : Row n) (indices : List (Fin n)) : List (Vec n) :=
  ((blocks r indices).reverse).flatten

end UnitBalance

def Row.unitGenerators {n} (r : Row n) : List (Vec n) :=
  UnitBalance.enumerate r (List.finRange n)

end Tamarin.ACBasis
