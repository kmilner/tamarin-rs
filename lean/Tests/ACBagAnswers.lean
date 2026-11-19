import Tamarin.ACBagAnswers

open Tamarin.Matching

private def samples : List (List UInt64 × List UInt64) :=
  let pats : List (List UInt64) := [[],[17],[17,17],[17,23],[17,17,23],[17,23,23]]
  let terms : List (List UInt64) := [[],[7],[9],[7,9],[7,7,9],[7,7,9,9],[9,9,7]]
  pats.flatMap fun p => terms.map (p,·)

/-- Independent exhaustive enumeration of nonempty images. Each target has
at most two copies of either atom, so every visible image occurs in this list. -/
private def reference (rows : ACBagSearch.Rows) : List ACBagAnswers.Arm :=
  let bags : List (List UInt64) := ((List.range 3).flatMap fun i =>
    (List.range 3).map fun j => List.replicate i 7 ++ List.replicate j 9).filter (!·.isEmpty)
  (bags.flatMap fun x => bags.filterMap fun y =>
    let image k := if k == 17 then x else y
    if rows.all (fun (ks,subj) => decide ((ks.flatMap image).Perm subj)) then
      some ((ACBagAnswers.keys rows).map image)
    else none).eraseDups

private def kinds := (List.range 48).map Nat.toUInt64

private def coupled (change : Bool) : ACBagSearch.Rows :=
  [([17,17,23], kinds.flatMap fun a => List.replicate (if a % 2 == 0 then 2 else 1) a),
   ([17,23,23], kinds.flatMap fun a => List.replicate (if a % 2 == 0 && !(change && a == 0) then 1 else 2) a)]

private theorem determined (rows : ACBagSearch.Rows) (s t : List UInt64)
    (layout : rows = [([17,17,23],s),([17,23,23],t)]) (a : UInt64) (u v : UInt64 → Nat)
    (hu : ACBags.Balanced rows a u) (hv : ACBags.Balanced rows a v) :
    ∀ k ∈ ACBagAnswers.keys rows, u k = v k := by
  subst rows
  have h₁ := hu _ List.mem_cons_self
  have h₂ := hu _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h₃ := hv _ List.mem_cons_self
  have h₄ := hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp at h₁ h₂ h₃ h₄
  intro k hk
  have : k = 17 ∨ k = 23 := by
    simp [ACBagAnswers.keys,List.mem_eraseDups] at hk
    grind
  rcases this with rfl | rfl <;> omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
example : ACBagAnswers.Within (coupled false) := by
  apply ACBagAnswers.Within.of_unique
  · refine ⟨by decide,by decide,by decide,by decide,?_⟩
    intro a ha
    refine ⟨2,?_,by decide⟩
    have bounded : ∀ b ∈ ((coupled false).flatMap Prod.snd).eraseDups,
        ∀ r ∈ coupled false, r.2.count b ≤ 2 := by decide
    exact bounded a (List.mem_eraseDups.mpr ha)
  · intro a _ u v hu hv
    exact determined _ _ _ rfl a u v hu hv
  · decide

def main : IO Unit := do
  for r in samples do
    for s in samples do
      let rows := [r,s]
      let some got := ACBagAnswers.run rows | throw (IO.userError "small family unexpectedly deferred")
      let normalized := got.map fun arm => arm.map fun bag => bag.mergeSort
      unless decide (normalized.Perm (reference rows)) do
        throw (IO.userError s!"Wrong matcher family for {rows}")
  let evens := kinds.filter fun a => a % 2 == 0
  let odds := kinds.filter fun a => a % 2 == 1
  unless ACBagAnswers.run (coupled false) == some [[evens,odds]] do
    throw (IO.userError "Coupled equations must return the unique 48-factor matcher")
  unless ACBagAnswers.run (coupled true) == some [] do
    throw (IO.userError "A factor requiring fractional counts must refute the family")
  let wide := (List.range 64).map Nat.toUInt64
  unless (ACBagAnswers.run [([17,23],wide)]).isNone do
    throw (IO.userError "The family must defer before expanding 2^64 choices")
  unless ACBagAnswers.run [([17,17,23,23],wide ++ wide ++ [77])] == some [] do
    throw (IO.userError "An impossible factor makes even a large Cartesian product empty")
