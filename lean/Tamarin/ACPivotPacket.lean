import Tamarin.ACPivot
import TamarinRuntime.ACPivot

/-! Two ordinary equations per branch. The occurrence IDs address a single
caller-owned vector. Every other equation in the conjunction stays pending. -/
namespace Tamarin.ACPivot.Packet
open Query AtomicACPair

abbrev Fields := UInt64 × List UInt64 × UInt64 × List UInt64

def offsets (n : Nat) : List UInt64 := (List.range n).map fun i => (4 + i).toUInt64

def fields {n : Nat} : Choice n → Fields
  | .matchAt i => (1, [(4 + i.val).toUInt64], 0, 2 :: (offsets n).eraseIdx i.val)
  | .whole => (2, [1], 0, offsets n)
  | .shared => (2, [1,3], 0, 3 :: offsets n)

def encode : Fields → Array UInt64
  | (x,l,y,r) => ([x, l.length.toUInt64] ++ l ++ [y] ++ r).toArray

def words {n : Nat} (c : Choice n) := encode (fields c)

abbrev Kernel := UInt64 → Option (Array (Array UInt64))

/-- The order of alternatives is free. Every occurrence and both possible
non-matching remainders must be represented on an admitted call. -/
def Correct (run : Kernel) : Prop := ∀ size,
  if 0 < size.toNat ∧ size.toNat ≤ 32 then
    ∃ rows, run size = some rows ∧ ∀ row, row ∈ rows ↔ ∃ c : Choice size.toNat, row = words c
  else run size = none

theorem correct : Correct ACPivotCandidate.run := by
  intro size
  split
  next h =>
    simp only [ACPivotCandidate.run, h.1, h.2, decide_true, Bool.and_self, guard, pure, bind,
      Option.bind, ↓reduceIte]
    refine ⟨_,rfl,?_⟩
    intro row
    simp only [List.mem_toArray, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | rfl | ⟨i, _, rfl⟩)
      · exact ⟨.whole, rfl⟩
      · exact ⟨.shared, rfl⟩
      · exact ⟨.matchAt i, rfl⟩
    · rintro ⟨c, rfl⟩
      cases c with
      | whole => exact Or.inl rfl
      | shared => exact Or.inr (Or.inl rfl)
      | matchAt i => exact Or.inr (Or.inr ⟨i, List.mem_finRange i, rfl⟩)
  next h =>
    simp [ACPivotCandidate.run, h, Bool.and_eq_true, guard]

/-- The packet actually returned by the linked candidate yields a complete
family whenever the recursive solver supplies a complete family for every
represented continuation. No assumption on the order of its results. -/
theorem complete {run : Kernel} (ok : Correct run) {sig : Signature} (q : Query sig)
    {size : UInt64} (width : size.toNat = q.operands.length) (bound : size.toNat ≤ 32)
    {rows : Array (Array UInt64)} (ran : run size = some rows)
    (atom : Atomic q.f q.a) (each : ∀ b ∈ q.operands, Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (w : Variable) (hw : w.sort = sig.acSort q.f)
    (fresh : ¬ q.problem.Occurs w) (answers : Array UInt64 → List (Substitution sig))
    (branches : ∀ c, CompleteSet (q.branch w c) (answers (words c))) :
    CompleteSet q.problem (rows.toList.flatMap answers) := by
  have nz : 0 < size.toNat := by simp [width, Query.operands]
  have h := ok size
  simp only [nz, bound, and_self, ↓reduceIte] at h
  obtain ⟨rs,hr,cover⟩ := h
  obtain rfl := Option.some.inj (ran.symm.trans hr)
  rw [width] at cover
  have cs := q.complete atom each sy w hw fresh (fun c => answers (words c)) branches
  have same (σ : Substitution sig) : σ ∈ rows.toList.flatMap answers ↔ σ ∈ q.choices.flatMap (fun c => answers (words c)) := by
    constructor
    · intro member
      obtain ⟨r,hr,hs⟩ := List.mem_flatMap.mp member
      obtain ⟨c,rfl⟩ := (cover r).mp (Array.mem_toList_iff.mp hr)
      exact List.mem_flatMap.mpr ⟨c, q.choice_mem c, hs⟩
    · intro member
      obtain ⟨c,_,hs⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨_, Array.mem_toList_iff.mpr ((cover _).mpr ⟨c,rfl⟩), hs⟩
  exact ⟨fun σ h => cs.sound _ ((same σ).mp h), fun ρ h => by
    obtain ⟨σ,hs,more⟩ := cs.covers _ h
    exact ⟨σ,(same σ).mpr hs,more⟩⟩

end Tamarin.ACPivot.Packet
