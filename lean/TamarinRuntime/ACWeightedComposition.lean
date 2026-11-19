import TamarinRuntime.ACBasis

namespace Tamarin.ACBasis.WeightedComposition

inductive Side where | pos | neg | neutral deriving DecidableEq, BEq

def side {n} (r : Row n) (i : Fin n) :=
  if 0 < r.pos i then Side.pos else if 0 < r.neg i then .neg else .neutral

abbrev Quota := Side → Nat

def active (a b : Nat) : Quota
  | .pos => b / Nat.gcd a b
  | .neg => a / Nat.gcd a b
  | .neutral => 0

def singleton : Quota
  | .neutral => 1
  | _ => 0

def spend (q : Quota) (s : Side) (h : Nat) : Quota := fun t => if s = t then q t - h else q t

/-- On the last occurrence of a side its coordinate is forced. In particular
a one-column side does not iterate through the size of its coefficient. -/
def heads {n} (tail : Fin n → Side) (s : Side) (goal : Nat) :=
  if ∃ i, tail i = s then List.range (goal+1) else [goal]

def draw : (n : Nat) → (Fin n → Side) → Quota → List (Vec n)
  | 0, _, q => if q .pos = 0 ∧ q .neg = 0 ∧ q .neutral = 0 then [Fin.elim0] else []
  | n+1, tag, q =>
    let s := tag 0
    let tail := fun i : Fin n => tag i.succ
    (heads tail s (q s)).flatMap fun h => (draw n tail (spend q s h)).map (prepend h)

def enumerate {n} (r : Row n) (a b : Nat) : List (Vec n) :=
  let tag := side r
  (draw n tag (active a b)).merge (draw n tag singleton) (fun l r => decide (List.ofFn l ≤ List.ofFn r))

end Tamarin.ACBasis.WeightedComposition
