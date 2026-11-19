import TamarinRuntime.ACColumnQuotient
import TamarinRuntime.ACWeightedComposition

namespace Tamarin.ACBasis.Distributed
open ACFeasibility.ColumnQuotient

/-- The final occurrence of a class takes its remaining quota. Precompute
this once per layout since every quotient generator uses the same partition. -/
inductive Plan (k : Nat) : Nat → Type where
  | done : Plan k 0
  | next {n} (cls : Fin k) (repeats : Bool) (tail : Plan k n) : Plan k (n+1)

def plan {k} : (n : Nat) → (Fin n → Fin k) → Plan k n
  | 0, _ => .done
  | n+1, tag =>
    let tail := fun i : Fin n => tag i.succ
    .next (tag 0) (decide (∃ i, tail i = tag 0)) (plan n tail)

def spend {k} (q : Vec k) (s : Fin k) (h : Nat) : Vec k :=
  fun t => if t = s then q t-h else q t

def Plan.draw {k} : {n : Nat} → Plan k n → Vec k → List (Vec n)
  | _, .done, q => if ∀ j, q j = 0 then [Fin.elim0] else []
  | _, .next s repeats tail, q =>
    let hs := if repeats then List.range (q s+1) else [q s]
    hs.flatMap fun h => (tail.draw (spend q s h)).map (prepend h)

def slotCounts {n k} (tag : Fin n → Fin k) : Vector Nat k :=
  let tags := List.ofFn tag
  Vector.ofFn fun j => tags.count j

/-- Count allocations before constructing them. A repeated class with a
large quota is rejected before allocating its weak-composition table. -/
def charge {k} (slots : Vector Nat k) (q : Vec k) (room : Nat) : Option Nat := do
  let counts ← (List.finRange k).mapM fun j => WeightedComposition.waysWithin slots[j] (q j) room
  guard (counts.prod ≤ room)
  return room-counts.prod

def expand {n k} (tag : Fin n → Fin k) (qs : List (Vec k)) (limit : Nat) : Option (List (Vec n)) := do
  guard (n ≤ 64 ∧ k ≤ 64 ∧ limit ≤ 2048 ∧ qs.length ≤ 2048)
  let slots := slotCounts tag
  guard (slots.all (0 < ·))
  let _ ← qs.foldlM (fun room q => charge slots q room) limit
  let layout := plan n tag
  return qs.flatMap layout.draw

/-- Read the class indices back from the actual canonical representatives.
Computing a profile once per representative avoids rebuilding signatures in
the inner lookup across classes. -/
def classify {n} (rs : List (Row n)) (reps : List (Fin n)) :
    Option (Vector (Fin reps.length) n) :=
  let keys := (reps.map (profile rs)).toArray
  let groups := List.finRange reps.length
  let entries := Vector.ofFn (fun i : Fin n =>
    let key := profile rs i
    groups.find? (fun j => keys[j.val]'(by simp [keys]) == key))
  if ok : ∀ i : Fin n, entries[i].isSome then
    some (Vector.ofFn fun i => entries[i].get (ok i))
  else none

/-- Return a complete generator table in quotient-fiber order. This entry point
is suitable for consumers that accept a permutation of the Hilbert basis. -/
def run {n} (solve : {k : Nat} → List (Row k) → Option (List (Vec k)))
    (rs : List (Row n)) (limit : Nat) : Option (List (Vec n)) := do
  guard (n ≤ 64 ∧ rs.length ≤ 64)
  let reps := representatives rs
  guard (reps.length < n)
  let cls ← classify rs reps
  let gs ← solve (projected rs reps)
  expand (fun i => cls[i]) gs limit

end Tamarin.ACBasis.Distributed
