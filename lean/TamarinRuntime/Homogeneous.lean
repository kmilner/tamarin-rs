import TamarinRuntime.ACPlane
import TamarinRuntime.FlatMatch

namespace Tamarin.Homogeneous
open ACBasis

abbrev Matrix := Array (Array UInt64)
abbrev Arm := Array (Array UInt64)
abbrev Answers := Array Arm

/-- Alternating left/right multiplicity rows, ordered by request-local variable. -/
def readRows (n : Nat) : List (Array UInt64) → Option (List (Row n))
  | [] => some []
  | lhs :: rhs :: rest => do
    guard (lhs.size == n && rhs.size == n && lhs.any (· > 0) && rhs.any (· > 0))
    let row := Row.ofWeights (fun i : Fin n => lhs[i.val]!.toNat) (fun i : Fin n => rhs[i.val]!.toNat)
    return row :: (← readRows n rest)
  | [_] => none

def coordinates {n} (v : Vector Nat n) : Vec n := fun i => v[i]

/-- Store each coefficient table in a vector before converting it to the
coordinate function used by the basis algorithms. Minimization and later
row intersections share these stored coordinates. -/
def boundedBasis {n} : List (Row n) → Option (List (Vec n))
  | [] => some (minimize (units n))
  | r :: rs => do
    let gs ← boundedBasis rs
    guard (gs.length ≤ 12)
    let weights := r.pullback gs.get
    let positive := Vector.ofFn weights.pos
    let negative := Vector.ofFn weights.neg
    let pulled : Row gs.length := ⟨coordinates positive, coordinates negative, by
      simpa [positive, negative, coordinates] using weights.disjoint⟩
    let cap := pulled.primitive.cap
    guard (pulled.cappedFits cap 16384)
    let coeffs := pulled.cappedGenerators cap
    guard (coeffs.length ≤ 2048)
    let candidates := (lift gs.get coeffs).map Vector.ofFn
    return minimize (candidates.map coordinates)

def covers {n} (gs : List (Vec n)) (js : List (Fin gs.length)) : Bool :=
  decide (∀ i, ∃ j ∈ js, 0 < gs.get j i)

def arm {n} (gs : List (Vec n)) (js : List (Fin gs.length)) : Arm :=
  Array.ofFn fun i => (js.flatMap fun j => List.replicate (gs.get j i) j.val.toUInt64).toArray

def selections {n} (gs : List (Vec n)) :=
  (FlatMatchSearch.sublists (List.finRange gs.length)).filter (covers gs)

namespace Coverage

/-- Each node caches the coordinates covered by this generator and by the
whole remaining suffix. Both masks are built once per matrix. -/
inductive Plan (α : Type) (n : Nat) where
  | done
  | step (item : α) (support remaining : BitVec n) (tail : Plan α n)

def Plan.available {α n} : Plan α n → BitVec n
  | .done => 0
  | .step _ _ remaining _ => remaining

def prepare {α n} (mask : α → BitVec n) : List α → Plan α n
  | [] => .done
  | x :: xs =>
    let tail := prepare mask xs
    let support := mask x
    .step x support (support ||| tail.available) tail

/-- Skip every extension of a prefix that can no longer cover all coordinates.
Visiting exclusion before inclusion preserves the reference answer order. -/
def enumerate {α n} (full : BitVec n) : Plan α n → BitVec n → List (List α)
  | .done, covered => if covered = full then [[]] else []
  | .step x support remaining tail, covered =>
    if covered ||| remaining = full then
      enumerate full tail covered ++ (enumerate full tail (covered ||| support)).map (x :: ·)
    else []

def support {n} (v : Vec n) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => decide (0 < v i)))).cast (by simp)

end Coverage

def coveringSelections {n} (gs : List (Vec n)) : List (List (Fin gs.length)) :=
  let plan := Coverage.prepare (fun j => Coverage.support (gs.get j)) (List.finRange gs.length)
  Coverage.enumerate (BitVec.allOnes n) plan 0

def emit {n} (gs : List (Vec n)) : Answers := ((coveringSelections gs).map (arm gs)).toArray

def fitsOutput {n} (gs : List (Vec n)) : Bool :=
  gs.length ≤ 12 && (2 ^ gs.length) * (gs.map total).sum ≤ 65536

def solve (width : UInt64) (m : Matrix) : Option Answers := do
  guard (0 < width && width ≤ 32 && m.size ≤ 128)
  let rows ← readRows width.toNat m.toList
  let gs ← boundedBasis rows
  guard (fitsOutput gs)
  return emit gs

end Tamarin.Homogeneous
