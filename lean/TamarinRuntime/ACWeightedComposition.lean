import TamarinRuntime.ACBasis

namespace Tamarin.ACBasis.WeightedComposition

inductive Side where | pos | neg | neutral deriving DecidableEq

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

inductive Plan : Nat → Type where
  | done : Plan 0
  | next {k : Nat} (s : Side) (repeats : Bool) (tail : Plan k) : Plan (k+1)

def plan : (n : Nat) → (Fin n → Side) → Plan n
  | 0, _ => .done
  | n+1, tag =>
    let s := tag 0
    let tail := fun i : Fin n => tag i.succ
    .next s (decide (∃ i, tail i = s)) (plan n tail)

def Plan.draw : {n : Nat} → Plan n → Quota → List (Vec n)
  | _, .done, q => if q .pos = 0 ∧ q .neg = 0 ∧ q .neutral = 0 then [Fin.elim0] else []
  | _, .next s repeats tail, q =>
    let values := if repeats then List.range (q s+1) else [q s]
    values.flatMap fun h => (tail.draw (spend q s h)).map (prepend h)

def draw (n : Nat) (tag : Fin n → Side) (q : Quota) := (plan n tag).draw q

def enumerate {n} (r : Row n) (a b : Nat) : List (Vec n) :=
  let suffix := plan n (side r)
  let mixed := suffix.draw (active a b)
  match suffix.draw singleton with
  | [] => mixed
  | x :: xs => mixed.merge (x :: xs) (fun l r => decide (List.ofFn l ≤ List.ofFn r))

def slots {n} (tag : Fin n → Side) (s : Side) := (List.ofFn tag).count s

def magnitude {n} (v : Vec n) := (List.ofFn v).foldr max 0

def cumulative (base : Nat) : List Nat → List Nat
  | [] => []
  | h :: t => let next := base+h; next :: cumulative next t

/-- Tabulate fixed-sum counts for 1+extra slots at quotas 0 through q. -/
def counts (q : Nat) : Nat → List Nat
  | 0 => List.replicate (q+1) 1
  | d+1 => cumulative 0 (counts q d)

/-- A side with two or more slots already has at least q+1 distributions.
A singleton has exactly one, even when the required coordinate is large. -/
def waysWithin (k q budget : Nat) : Option Nat :=
  match k with
  | 0 => some (if q = 0 then 1 else 0)
  | 1 => some 1
  | d+2 => if q < budget then (counts q (d+1)).getLast? else none

def candidate {n} (r : Row n) : Option (List (Vec n)) := do
  guard (n ≤ 64)
  let a := magnitude r.pos
  let b := magnitude r.neg
  guard (0 < a ∧ 0 < b ∧ (∀ i, r.pos i = 0 ∨ r.pos i = a) ∧ ∀ i, r.neg i = 0 ∨ r.neg i = b)
  let q := active a b
  -- A giant forced coordinate takes constant enumeration space but will be
  -- multiplied during the lift. Bound its stored word length as well.
  guard (q .pos < 2^128 ∧ q .neg < 2^128)
  let tag := side r
  let p ← waysWithin (slots tag .pos) (q .pos) 2048
  let z ← waysWithin (slots tag .neg) (q .neg) 2048
  guard (p*z + slots tag .neutral ≤ 2048)
  return enumerate r a b

end Tamarin.ACBasis.WeightedComposition
