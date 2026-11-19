import TamarinRuntime.ACBasis
import Init.Data.Fin.Fold
import Init.Data.Rat

namespace Tamarin.ACFeasibility.TwoRow
open ACBasis

inductive Column where
  | positive (slope : Rat)
  | negative (slope : Rat)
  | up | down | zero
  deriving DecidableEq

def classify {n} (p q : Row n) (i : Fin n) : Column :=
  let b := (q.pos i : Int) - q.neg i
  if 0 < p.pos i then .positive ((b : Rat) / (p.pos i : Rat))
  else if 0 < p.neg i then .negative (((-b : Int) : Rat) / (p.neg i : Rat))
  else if 0 < b then .up else if b < 0 then .down else .zero

structure Bounds where
  lo : Rat
  hi : Rat

def extend : Option Bounds → Rat → Option Bounds
  | none, x => some ⟨x,x⟩
  | some b, x => some ⟨min b.lo x,max b.hi x⟩

def above : Option Bounds → Option Bounds → Bool
  | some p, some q => q.lo < p.hi
  | _, _ => false

structure Scan where
  pos : Option Bounds := none
  neg : Option Bounds := none
  up : Bool := false
  down : Bool := false

def Scan.insert (s : Scan) : Column → Scan
  | .positive x => {s with pos := extend s.pos x}
  | .negative x => {s with neg := extend s.neg x}
  | .up => {s with up := true}
  | .down => {s with down := true}
  | .zero => s

def Scan.verdict (s : Scan) : Bool :=
  (s.pos.isSome == s.neg.isSome) &&
  ((s.up || above s.pos s.neg) == (s.down || above s.neg s.pos))

/-- Fin.foldl compiles to its tail-recursive loop; only the two extreme
slopes on each side and the signs on the vertical axis are retained. -/
def decidePair {n} (p q : Row n) : Bool :=
  (Fin.foldl n (fun s i => Scan.insert s (classify p q i)) {}).verdict

end Tamarin.ACFeasibility.TwoRow
