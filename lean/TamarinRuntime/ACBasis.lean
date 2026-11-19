import Std

/-! Executable numeric reference search for homogeneous AC systems. -/
namespace Tamarin.ACBasis

abbrev Vec (n : Nat) := Fin n → Nat

/-- Finite sum over all coordinates. -/
def total {n} (v : Vec n) := (List.ofFn v).sum

def dot {n} (v w : Vec n) := total (fun i => v i * w i)

def spike {n} (j : Fin n) (m : Nat) : Vec n := fun i => if i = j then m else 0

/-- A single row with cancelled coefficients, so each coordinate contributes
to at most one side. -/
structure Row (n : Nat) where
  pos : Vec n
  neg : Vec n
  disjoint : ∀ i, pos i = 0 ∨ neg i = 0

def Row.Holds {n} (r : Row n) (x : Vec n) := dot r.pos x = dot r.neg x

def Row.cap {n} (r : Row n) := (1 :: (List.ofFn r.pos ++ List.ofFn r.neg)).max (by simp)

def Row.bound {n} (r : Row n) := r.cap + n * (r.cap * r.cap)

/-- On a unit-weight side one can spend individual occurrences to balance
one item from the other side. A generator then uses at most the largest
coefficient in any coordinate. Neutral coordinates need at most one. -/
def Row.unitSide {n} (r : Row n) : Prop :=
  (∀ i, r.pos i ≤ 1) ∨ (∀ i, r.neg i ≤ 1)

instance {n} (r : Row n) : Decidable r.unitSide :=
  inferInstanceAs (Decidable ((∀ i, r.pos i ≤ 1) ∨ (∀ i, r.neg i ≤ 1)))

def Row.limits {n} (r : Row n) : Vec n :=
  let cap := r.cap
  let bound := cap + n * (cap * cap)
  let active := if r.unitSide then cap else bound
  fun i => if r.pos i == 0 && r.neg i == 0 then 1 else active

/-- Prepending a coordinate has the same pointwise semantics as finitary case analysis. -/
abbrev prepend {n} (h : Nat) (v : Vec n) : Vec (n+1) := Fin.cases h v

private def prependDirect {n} (h : Nat) (v : Vec n) : Vec (n+1)
  | ⟨0,_⟩ => h
  | ⟨j+1,lt⟩ => v ⟨j,Nat.lt_of_succ_lt_succ lt⟩

/-- `Fin.cases` uses induction on the index. Direct case analysis evaluates
just the requested coordinate of a nested coefficient vector. -/
@[csimp] theorem prepend_eq_direct : @prepend = @prependDirect := by
  funext n h v i
  cases i using Fin.cases <;> rfl

def box : (n : Nat) → Vec n → List (Vec n)
  | 0, _ => [Fin.elim0]
  | n+1, limits =>
    let tail := box n (fun i => limits i.succ)
    (List.range (limits 0 + 1)).flatMap (fun h => tail.map (prepend h))

def Row.generators {n} (r : Row n) : List (Vec n) :=
  (box n r.limits).filter fun v => dot r.pos v == dot r.neg v && (List.ofFn v).any (0 < ·)

def Row.boxSize {n} (r : Row n) := (List.ofFn (fun i => r.limits i + 1)).prod

/-- Nonnegative linear combination of a finite generator table. -/
def mix {k n} (g : Fin k → Vec n) (c : Vec k) : Vec n := fun i => dot (fun j => g j i) c

/-- Coefficients common to the two sides cancel coordinate by coordinate. -/
def Row.ofWeights {n} (p q : Vec n) : Row n where
  pos i := p i - q i
  neg i := q i - p i
  disjoint i := by omega

/-- The row induced on coefficients of a previous generator table. -/
def Row.pullback {k n} (r : Row n) (g : Fin k → Vec n) : Row k :=
  .ofWeights (fun i => dot r.pos (g i)) (fun i => dot r.neg (g i))

def lift {k n} (g : Fin k → Vec n) (coeffs : List (Vec k)) := coeffs.map (mix g)

def intersect {n} (r : Row n) (gs : List (Vec n)) :=
  lift gs.get (r.pullback gs.get).generators

def units (n : Nat) := List.ofFn (fun i : Fin n => spike i 1)

private instance vecDecEq {n} : DecidableEq (Vec n) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm

/-- Discard zero, repetitions and vectors dominated by a smaller nonzero
solution in the table. Doing this between row intersections bounds the next
coefficient dimension by the number of distinct irreducible generators. -/
def minimize {n} (gs : List (Vec n)) : List (Vec n) :=
  (gs.filter fun x => decide (∃ i, 0 < x i) &&
    !gs.any (fun y => decide ((∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ y ≠ x))).eraseDups

def generate {n} : List (Row n) → List (Vec n)
  | [] => minimize (units n)
  | r :: rs => minimize (intersect r (generate rs))

end Tamarin.ACBasis
