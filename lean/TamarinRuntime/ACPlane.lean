import TamarinRuntime.ACBasis

namespace Tamarin.ACBasis

/-- Any nonzero coefficient fixes one coordinate once all the others are known.
All active coordinates have the same limit, so eliminating the last active
coordinate leaves the same grid size as eliminating any other active one. -/
def Row.fitsPlane {n} (r : Row n) (budget : Nat) : Bool :=
  let size := r.boxSize
  size ≤ budget || (List.finRange n).any fun i =>
    (0 < r.pos i || 0 < r.neg i) && size ≤ budget * (r.limits i + 1)

/-- Solve offset + weight * h = target within the coordinate limit. The
multiplication check also rejects nonintegral quotients and negative gaps. -/
def forcedHead (limit weight offset target : Nat) : List Nat :=
  let h := (target - offset) / weight
  if h ≤ limit && offset + weight * h == target then [h] else []

def neutral {n} (p q : Vec n) : Bool :=
  decide (∀ i, p i = 0 ∧ q i = 0)

/-- Enumerate balanced vectors in the reference box order. At the last active
coordinate the suffix contributes zero, so one division replaces its loop. -/
def balancedBox : (n : Nat) → Vec n → Vec n → Vec n → Nat → Nat → List (Vec n)
  | 0, _, _, _, a, b => if a = b then [Fin.elim0] else []
  | n+1, lim, p, q, a, b =>
    let l := fun i => lim i.succ
    let u := fun i => p i.succ
    let v := fun i => q i.succ
    if neutral u v && (0 < p 0 || 0 < q 0) then
      let heads := if 0 < p 0 then forcedHead (lim 0) (p 0) a b else forcedHead (lim 0) (q 0) b a
      heads.flatMap fun h => (box n l).map (Fin.cases h)
    else
      (List.range (lim 0 + 1)).flatMap fun h =>
        (balancedBox n l u v (a + p 0 * h) (b + q 0 * h)).map (Fin.cases h)

def Row.planeGenerators {n} (r : Row n) : List (Vec n) :=
  (balancedBox n r.limits r.pos r.neg 0 0).filter fun v => (List.ofFn v).any (0 < ·)

end Tamarin.ACBasis
