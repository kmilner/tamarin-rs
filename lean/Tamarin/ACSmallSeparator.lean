import TamarinRuntime.ACSmallSeparator
import Tamarin.ACSeparation

namespace Tamarin.ACFeasibility.SmallSeparator
open ACBasis
variable {n : Nat}

/-- A bounded integer certificate of nonexistence, in the signed coefficients
of the original equations. Its radius and work bound are fixed independently
of the search order, selected radius, or runtime certificate checker. -/
def Within (rs : List (Row n)) : Prop :=
  rs.length ≤ 12 ∧ ∃ radius : Nat, 1 ≤ radius ∧ radius ≤ 3 ∧
    (2*radius+1)^rs.length * max 1 rs.length * max 1 n ≤ 524288 ∧
    ∃ weights, Separation.Certificate rs weights ∧ ∀ w ∈ weights, w.natAbs ≤ radius

private theorem mem_digits (radius : Nat) (w : Int) : w ∈ digits radius ↔ w.natAbs ≤ radius := by
  cases w with
  | ofNat v =>
    cases v with
    | zero => simp [digits]
    | succ v =>
      simp [digits,List.mem_flatMap]
      constructor
      · rintro (zero|⟨i,hi,eq⟩) <;> omega
      · intro h; exact Or.inr ⟨v,by omega,by simp⟩
  | negSucc v =>
    simp [digits,List.mem_flatMap,Int.negSucc_eq]
    constructor
    · rintro (zero|⟨i,hi,eq⟩) <;> omega
    · intro h; exact Or.inr ⟨v,by omega,by simp⟩

private theorem search_iff (choices : List Int) (k : Nat) (test : List Int → Bool) :
    search choices k test = true ↔ ∃ ws, ws.length = k ∧ (∀ w ∈ ws, w ∈ choices) ∧ test ws = true := by
  induction k generalizing test with
  | zero => simp [search]
  | succ k ih =>
    rw [search,List.any_eq_true]
    constructor
    · rintro ⟨w,hw,rest⟩
      obtain ⟨ws,size,all,ok⟩ := (ih _).mp rest
      exact ⟨w::ws,by simp [size],by simpa using And.intro hw all,ok⟩
    · rintro ⟨ws,size,all,ok⟩
      cases ws with
      | nil => simp at size
      | cons w ws =>
        exact ⟨w,all w List.mem_cons_self,(ih _).mpr ⟨ws,by simpa using size,
          fun u hu => all u (List.mem_cons_of_mem _ hu),ok⟩⟩

theorem run_refutes {rs : List (Row n)} {b : Bool} (returned : run rs = some b) :
    b = false ∧ ¬ Feasible rs := by
  unfold run at returned
  dsimp only at returned
  split at returned <;> try contradiction
  split at returned
  · rename_i found
    obtain ⟨ws,_,_,accepted⟩ := (search_iff ..).mp found
    exact ⟨(Option.some.inj returned).symm,Separation.separates_refutes accepted⟩
  · contradiction

theorem returns_false {rs : List (Row n)} {b : Bool} (returned : run rs = some b) : b = false :=
  (run_refutes returned).1

theorem run_sound (rs : List (Row n)) (b : Bool) (returned : run rs = some b) : b = true ↔ Feasible rs := by
  obtain ⟨rfl,no⟩ := run_refutes returned
  simp [no]

private theorem radius_le {n m r : Nat} (rows : m ≤ 12) (pos : 1 ≤ r) (small : r ≤ 3)
    (cost : (2*r+1)^m * max 1 m * max 1 n ≤ 524288) : r ≤ radiusFor n m := by
  have options : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases options with rfl|rfl|rfl <;>
    simp [radiusFor,Nat.not_lt.mpr rows,cost] <;> (repeat' split) <;> decide

theorem run_complete (rs : List (Row n)) (within : Within rs) : (run rs).isSome := by
  obtain ⟨height,r,pos,small,cost,ws,certificate,bounded⟩ := within
  have le := radius_le height pos small cost
  have nonzero : radiusFor n rs.length ≠ 0 := by omega
  have found : search (digits (radiusFor n rs.length)) rs.length (Separation.separates rs) = true :=
    (search_iff ..).mpr ⟨ws,certificate.1,fun w hw => (mem_digits ..).mpr (Nat.le_trans (bounded w hw) le),
      (Separation.separates_iff ..).mpr certificate⟩
  simp [run,nonzero,found]

section
-- Pairs of opposite columns force y₁=3y₂, y₂=y₃, and y₃=y₄.
-- The final nonzero column requires y₄>0. Every integer separator therefore
-- needs a weight of magnitude at least three, independently of row rank.
private def testRow (width : Nat) (coeffs : Array Int) : Row width :=
  let z (i : Fin width) := coeffs[i.val]?.getD 0
  Row.ofWeights (fun i => (z i).toNat) (fun i => (-(z i)).toNat)

private def testRows (width : Nat) : List (Row width) :=
  [testRow width #[1,-1,0,0,0,0,0],testRow width #[-3,3,1,-1,0,0,0],
    testRow width #[0,0,-1,1,1,-1,0],testRow width #[0,0,0,0,-1,1,1]]

private theorem test_within : Within (testRows 46) := by
  refine ⟨by decide,3,by decide,by decide,by decide,[3,1,1,1],?_,by decide⟩
  exact (Separation.separates_iff ..).mp (by decide)

example : ¬ Feasible (testRows 46) := by
  obtain ⟨_,found⟩ := Option.isSome_iff_exists.mp (run_complete _ test_within)
  exact (run_refutes found).2

#guard radiusFor 46 4 == 3 && run (testRows 46) == some false
#guard radiusFor 500 4 == 1 && (run (testRows 500)).isNone
#guard radiusFor 1 4096 == 0
#guard (run (n := 0) []).isNone

end

end Tamarin.ACFeasibility.SmallSeparator
