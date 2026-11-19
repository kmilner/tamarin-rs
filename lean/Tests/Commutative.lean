import TamarinCI

namespace Tamarin.CommutativeTests
open Commutative

-- A semantically complete candidate may still exhaust the search budget
-- by expanding two known-equivalent continuations at every nested head.
example : Correct (fun _ _ _ _ _ => 3) := by
  intro a b c d p; simp [Selected]
example : ¬ BranchBound (fun _ _ _ _ _ => 3) := by
  intro h
  exact (h 0 0 0 0 3).2.2 (by decide) rfl

-- Two candidates can return different bytes on a live input and both meet
-- the CI obligations. Four variable heads with a repeated operand admit
-- either representative of the same two continuations.
private def tieBreak (cross : Bool) (a b c d : UInt64) (p : UInt8) : UInt8 :=
  if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ p = 3 then (if cross then 2 else 1)
  else Executable.commOrientations a b c d p

example (cross : Bool) : Correct (tieBreak cross) ∧ BranchBound (tieBreak cross) := by
  constructor
  · intro a b c d p
    unfold tieBreak
    split
    · next h =>
        obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h
        cases cross <;> simp [Selected, Viable] <;> grind
    · exact exportedCommOrientations_correct a b c d p
  · intro a b c d p
    unfold tieBreak
    split
    · next h =>
        obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h
        cases cross <;> simp [Selected, Viable]
    · exact exportedCommOrientations_bound a b c d p

example : tieBreak false 0 0 0 0 3 ≠ tieBreak true 0 0 0 0 3 := by decide

-- Without child coincidences, each of the two alignments can be the only
-- solution. The tail of the conjunction can enforce either one.
example : ¬ Correct (fun _ _ _ _ _ => 1) := by
  intro h
  have hh := (h 0 0 0 0 0).2 False True (by simp)
    (by simp [Viable]) (by simp) (by simp)
  simp [Selected] at hh

-- C permits a swap at the root but no reassociation of the three leaves.
example : let f := (0 : Pairing.signature.CSym)
    let a : Pairing.PTerm := .atom (0,.pub)
    let b : Pairing.PTerm := .atom (1,.pub)
    let c : Pairing.PTerm := .atom (2,.pub)
    ¬ EquivB (.comm f (.comm f a b) c) (.comm f a (.comm f b c)) := by
  intro f a b c h
  rcases (equiv_iff ..).mp h with ⟨bad,_⟩ | ⟨_,bad⟩ <;> cases bad.head_eq

-- Test input codes represent x, y, literals a and b, and the free terms
-- h(x) and h(a). Equal closed values after substitution receive the same
-- identity even if the original children had different syntax.
private def head : Nat → UInt64
  | 0 | 1 => 0
  | 2 => 1
  | 3 => 2
  | _ => 3

private def value (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | 2 => 0
  | 3 => 1
  | 4 => x + 2
  | _ => 2

private def priority (a b c d : Nat) : UInt8 :=
  if a == b || c == d then 3
  else if a == c || b == d then 1
  else if a == d || b == c then 2 else 0

def stress : IO Unit := do
  let mut checked := 0
  let mut solutions := 0
  for a in [:6] do for b in [:6] do for c in [:6] do for d in [:6] do
    let mask := Executable.commOrientations (head a) (head b) (head c) (head d) (priority a b c d)
    for x in [:4] do for y in [:4] do
      let val := value x y
      let left := [val a, val b]
      let right := [val c, val d]
      let expected := left.mergeSort == right.mergeSort
      let found := ((mask &&& 1) != 0 && left == right) ||
        ((mask &&& 2) != 0 && left == right.reverse)
      unless found == expected do
        throw (IO.userError s!"incorrect mask {mask} for {(a,b,c,d)} under {(x,y)}")
      solutions := solutions + (if expected then 1 else 0)
      checked := checked + 1
  IO.println s!"{checked} binary C assignments, {solutions} solutions"

end Tamarin.CommutativeTests

def main := Tamarin.CommutativeTests.stress
