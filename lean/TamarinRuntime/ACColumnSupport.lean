import TamarinRuntime.ACRationalProjection

namespace Tamarin.ACFeasibility.ColumnSupport
open ACBasis

structure Prepared (n : Nat) where
  row : Row n
  left : Nat
  right : Nat

def prepare {n} (r : Row n) : Prepared n := ⟨r,total r.pos,total r.neg⟩

def cells := 4096

/-- Coordinate zero is the common denominator. The other coordinates add
nonnegative corrections on the selected original variables. -/
def restrictRow {n} (S : List (Fin n)) (p : Prepared n) : Row (S.length+1) :=
  let idx := S.toArray
  let get (i : Fin S.length) := idx[i.val]'(by simp [idx])
  Row.ofWeights (prepend p.left (fun i => p.row.pos (get i)))
    (prepend p.right (fun i => p.row.neg (get i)))

def checkSupport {n} (rs : List (Prepared n)) (S : List (Fin n)) : Option Bool := do
  guard ((S.length+1) * max rs.length RationalProjection.maxRays ≤ cells)
  let gs ← RationalProjection.basis (rs.map (restrictRow S))
  return gs.any fun g => 0 < g 0

/-- Depth-first enumeration keeps one selected support on the stack. Charge
one credit per completed leaf. An unknown subproblem or exhausted search
cannot establish infeasibility. The remaining credits are shared by siblings. -/
def explore {α} (test : List α → Option Bool) : List α → Nat → List α → Nat → Option (Bool × Nat)
  | xs, room, seen, fuel => do
    guard (fuel > 0)
    match xs, room with
    | [], _ | _, 0 => return (←test seen, fuel - 1)
    | x :: xs, r + 1 =>
      let (found, left) ← explore test xs (r+1) seen fuel
      if found then return (true,left)
      explore test xs r (x::seen) left

def run {n} (rs : List (Row n)) (budget : Nat) : Option Bool := do
  guard (n ≤ 4096 ∧ rs.length ≤ 64)
  let input := rs.map prepare
  guard (input.all fun p => p.left ≤ RationalProjection.maxCoeff && p.right ≤ RationalProjection.maxCoeff)
  (explore (checkSupport input) (List.finRange n) rs.length [] budget).map Prod.fst

end Tamarin.ACFeasibility.ColumnSupport
