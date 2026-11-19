import TamarinRuntime.ACPlane

namespace Tamarin.ACBasis.RowReduction
variable {n : Nat}

def orient (r : Row n) (j : Fin n) : Row n :=
  if r.neg j = 0 then r else ⟨r.neg,r.pos,fun i => (r.disjoint i).symm⟩

/-- Keeping the pivot row permits cancelling its selected variable in
another equation by cross multiplication. All coefficients stay integral. -/
def cancel (p t : Row n) (j : Fin n) : Row n :=
  let a := orient p j
  let b := orient t j
  let u := a.pos j
  let v := b.pos j
  if u = 0 ∨ v = 0 then t else
    Row.ofWeights (fun i => u*b.pos i + v*a.neg i) (fun i => u*b.neg i + v*a.pos i)

def stored (r : Row n) : Row n :=
  let p := Vector.ofFn r.pos
  let q := Vector.ofFn r.neg
  ⟨fun i => p[i], fun i => q[i], by simpa [p,q] using r.disjoint⟩

def reduceAt (p : Row n) (j : Fin n) (t : Row n) : Option (Row n) := do
  if t.pos j = 0 && t.neg j = 0 then return t
  let c := stored (stored (cancel p t j)).primitive
  guard (c.cap < 2^128)
  return c

def echelon : Nat → List (Row n) → Option (List (Row n))
  | 0, rows => some rows
  | _+1, [] => some []
  | k+1, p :: ts => do
    let some j := (List.finRange n).find? (fun i => 0 < p.pos i || 0 < p.neg i)
      | return p :: (← echelon k ts)
    let tail ← ts.mapM (reduceAt p j)
    return p :: (← echelon k tail)

end Tamarin.ACBasis.RowReduction
