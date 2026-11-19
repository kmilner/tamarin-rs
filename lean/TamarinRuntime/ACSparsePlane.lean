import TamarinRuntime.ACPlane

namespace Tamarin.ACBasis

def Row.neutralAt {n} (r : Row n) (i : Fin n) : Bool :=
  r.pos i == 0 && r.neg i == 0

def Row.sparseLimits {n} (r : Row n) (cap : Nat) : Vec n :=
  let lim := r.cappedLimits cap
  fun i => if r.neutralAt i then 0 else lim i

def Row.sparseFits {n} (r : Row n) (cap budget : Nat) : Bool :=
  let lim := r.sparseLimits cap
  let size := (List.ofFn fun i => lim i + 1).prod
  size ≤ budget || (List.finRange n).any fun i =>
    (0 < r.pos i || 0 < r.neg i) && size ≤ budget * (lim i + 1)

def Row.sparseActive {n} (r : Row n) (cap : Nat) : List (Vec n) :=
  (balancedBox n (r.sparseLimits cap) r.pos r.neg 0 0).filter fun v => (List.ofFn v).any (0 < ·)

def Row.sparseUnits {n} (r : Row n) (cap : Nat) : List (Vec n) :=
  let lim := r.cappedLimits cap
  ((List.finRange n).reverse.filter (fun i => r.neutralAt i && 0 < lim i)).map (spike · 1)

/-- A mixed vector with a nonzero neutral coordinate is dominated by that
coordinate's unit. Merge units at their original lexicographic positions. -/
def Row.sparseGenerators {n} (r : Row n) (cap : Nat) : List (Vec n) :=
  (r.sparseActive cap).merge (r.sparseUnits cap) (fun a b => decide (List.ofFn a ≤ List.ofFn b))

end Tamarin.ACBasis
