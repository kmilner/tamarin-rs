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
def blockWith {n α} (r : Row n) (one : Fin n → α) (two : Fin n → Fin n → α)
    (i : Fin n) (tail : List (Fin n)) : List α :=
  if 0 < r.pos i then ((tail.filter (fun j => 0 < r.neg j)).reverse).map (two i)
  else if 0 < r.neg i then ((tail.filter (fun j => 0 < r.pos j)).reverse).map (two i)
  else [one i]

def blocksWith {n α} (r : Row n) (one : Fin n → α) (two : Fin n → Fin n → α) :
    List (Fin n) → List (List α)
  | [] => []
  | i :: rest => blockWith r one two i rest :: blocksWith r one two rest

def enumerateWith {n α} (r : Row n) (one : Fin n → α) (two : Fin n → Fin n → α)
    (indices : List (Fin n)) : List α := ((blocksWith r one two indices).reverse).flatten

abbrev block {n} (r : Row n) := blockWith r (fun i => spike i 1) pair
abbrev enumerate {n} (r : Row n) := enumerateWith r (fun i => spike i 1) pair

/-- The published bounds on subsequent stages can be checked before
allocating the candidates whenever their lifts are known to be minimal. -/
def count {k} (r : Row k) : Nat :=
  let ids := List.finRange k
  let positive := ids.countP (fun i => 0 < r.pos i)
  let negative := ids.countP (fun i => 0 < r.neg i)
  k - (positive+negative) + positive*negative

/-- A private positive coordinate for every basis vector certifies that
the lift reflects componentwise inequalities. -/
def separates {k n} (gs : Vector (Vec n) k) : Bool :=
  k ≤ n && decide (∀ i : Fin k, ∃ c : Fin n, 0 < gs[i] c ∧ ∀ j : Fin k, i ≠ j → gs[j] c = 0)

end UnitBalance

def Row.unitGenerators {n} (r : Row n) : List (Vec n) :=
  UnitBalance.enumerate r (List.finRange n)

def Row.unitLift {k n} (r : Row k) (basis : Vector (Vec n) k) : List (Vec n) :=
  UnitBalance.enumerateWith r (fun i => basis[i])
    (fun i j => let a := basis[i]; let b := basis[j]; fun c => a c + b c) (List.finRange k)

end Tamarin.ACBasis
