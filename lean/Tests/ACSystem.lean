import TamarinRuntime
import Tamarin.ACSystem
import Tamarin.HomogeneousContract
import Tamarin.GroundACEquality

namespace Tamarin.ACSystem.Tests
open ACSystem
variable {sig : Signature}

private def x (s : SortId) : Variable := ⟨0,s⟩
private def y (s : SortId) : Variable := ⟨1,s⟩
private def double (x y : Variable) : Row := ⟨⟨x,[x]⟩, ⟨y,[]⟩⟩

-- Both rows separately have positive solutions. Reusing x and y in the
-- opposite row removes every positive solution.
example (f : sig.ACSym) :
    let a := x (sig.acSort f)
    let b := y (sig.acSort f)
    (problem f [double a b]).Satisfiable ∧ (problem f [double b a]).Satisfiable ∧
      ¬ (problem f [double a b, double b a]).Satisfiable := by
  dsimp only
  have one (a b : Variable) (h : a ≠ b) (ha : a.sort = sig.acSort f) (hb : b.sort = sig.acSort f) :
      (problem f [double a b]).Satisfiable := by
    apply (satisfiable_iff_positive f _ _).mpr
    · refine ⟨fun v => if v = a then 1 else 2, ?_, ?_⟩
      · intro row hr
        obtain rfl := List.mem_singleton.mp hr
        simp [double, Side.weight, Side.vars, h.symm]
      · intro v _; dsimp only; split <;> decide
    · intro v hv
      simp [variables, double, Side.vars] at hv
      rcases hv with rfl | rfl <;> simp_all [Subsort.refl]
  refine ⟨one _ _ (by simp [x,y]) rfl rfl, one _ _ (by simp [x,y]) rfl rfl, ?_⟩
  rintro ⟨σ, hσ⟩
  obtain ⟨c, hc, pos⟩ := positive_of_solution f _ σ hσ
  have h₁ := hc _ (List.mem_cons_self ..)
  have h₂ := hc _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hpos := pos (x (sig.acSort f)) (by simp [variables, double, Side.vars])
  simp [double, Side.weight, Side.vars] at h₁ h₂
  omega

-- Same image lengths do not imply equality of individual factor columns.
example (f : sig.ACSym) (a b : Variable) (hab : a ≠ b) :
    ¬ (problem f [⟨⟨a,[]⟩, ⟨b,[]⟩⟩]).Solves Substitution.identity := by
  intro sol
  have h := sol _ (List.mem_map_of_mem (List.mem_singleton_self _))
  exact hab (Term.var.inj (by cases h.head_eq; rfl : (Term.var a : Term sig) = .var b))

-- Positivity alone would admit 2x = y for a Fresh variable y. Sorting
-- excludes that solution when the outer AC symbol has result sort Msg.
example (f : sig.ACSym) (msg : sig.acSort f = .msg) (a b : Variable) (fresh : b.sort = .fresh) :
    ¬ (problem f [double a b]).Satisfiable := by
  rintro ⟨σ, hσ⟩
  have he := hσ _ (List.mem_map_of_mem (List.mem_singleton_self _))
  change EquivB (.ac f (σ.image a) (σ.image a)) (σ.image b) at he
  have hs := Term.rootSort_le (σ.sorted b)
  rw [← Term.rootSort_equiv he, fresh] at hs
  change Subsort (sig.acSort f) .fresh at hs
  rw [msg] at hs
  cases hs

end Tamarin.ACSystem.Tests

namespace Tamarin.ACBasis.Tests
open ACBasis

private def v₂ (x y : Nat) : Vec 2 := Fin.cases x (fun _ => y)
private def v₃ (x y z : Nat) : Vec 3 := Fin.cases x (Fin.cases y (fun _ => z))
private def thirds : Row 2 := Row.ofWeights (v₂ 3 0) (v₂ 0 2)
private def halves : Row 3 := Row.ofWeights (v₃ 1 1 0) (v₃ 0 0 2)
private def same : Row 3 := Row.ofWeights (v₃ 1 0 0) (v₃ 0 0 1)

private def outputs {n} (rows : List (Row n)) := (generate rows).map List.ofFn

#guard coversCoordinates (generate [thirds])
#guard !coversCoordinates (generate [thirds, .ofWeights (v₂ 1 0) (v₂ 0 1)])
#guard coversCoordinates (generate (n := 0) [])
#guard outputs [thirds] == [[2,3]]
#guard outputs [thirds,thirds] == [[2,3]]
#guard outputs [halves,same] == [[1,1,1]]
#guard outputs [same,halves] == [[1,1,1]]
#guard (outputs [halves]).mergeSort == [[0,2,1],[1,1,1],[2,0,1]]
#guard (outputs [.ofWeights (v₂ 1 2) (v₂ 1 2)]).mergeSort == [[0,1],[1,0]]
#guard outputs [thirds, .ofWeights (v₂ 1 0) (v₂ 0 1)] == []
#guard outputs (n := 0) [] == []
-- Counts in an actual solution can exceed every enumerated generator bound.
example (k : Nat) : Generates (generate [thirds]) (v₂ (2*k) (3*k)) := by
  apply (generate_correct _ _).mp
  intro row hr
  obtain rfl := List.mem_singleton.mp hr
  rw [thirds, Row.ofWeights_holds]
  simp [dot,total,v₂,List.ofFn_succ]
  omega

end Tamarin.ACBasis.Tests

namespace Tamarin.Homogeneous.Tests
open Tamarin.Executable

-- Exercise the compiled traversal with duplicate supports, empty supports,
-- uncovered coordinates, and prefixes that must keep several different arms.
private def testVector (bits : Nat) : ACBasis.Vec 3 :=
  fun i => if bits.testBit i then 1 + i.val else 0

#guard (List.range 8).all fun a => (List.range 8).all fun b => (List.range 8).all fun c =>
  let gs := [testVector a, testVector b, testVector c]
  coveringSelections gs == selections gs
#guard coveringSelections (n := 0) [] == [[]]
#guard (coveringSelections (n := 1) []).isEmpty
-- Every generator is forced, including the highest bit of a full wire-width mask.
#guard coveringSelections (ACBasis.units 32) == [List.finRange 32]

-- A conjunction with no positive solution completes with zero arms. A malformed
-- or over-budget conjunction defers, even if its suffix has valid answers.
#guard homogeneousUnify 2 #[#[2,0],#[0,1],#[0,2],#[1,0]] == some #[]
-- A five-operand YubiKey matrix reaches four successive basis intersections.
-- Each row forces the fourth operand to be empty, so no AC answer exists.
#guard homogeneousUnify 5 #[
  #[1,1,1,0,0], #[1,1,1,1,0],
  #[1,1,1,0,0], #[1,1,1,1,0],
  #[1,1,1,0,1], #[1,1,1,1,1],
  #[1,1,1,0,0], #[1,1,1,1,0]] == some #[]
#guard homogeneousUnify 2 #[#[1,0]] == none
#guard homogeneousUnify 2 #[#[1,0],#[0]] == none
#guard homogeneousUnify 2 #[#[0,0],#[1,0]] == none
-- After x = y the huge coefficient forces the only coordinate to zero.
-- Without that second row the remaining free coordinate exceeds the budget.
#guard homogeneousUnify 2 #[#[0xffffffffffffffff,0],#[0,1],#[1,0],#[0,1]] == some #[]
#guard !(ACBasis.Row.ofWeights (n := 2) (Fin.cases (2^64-1) (fun _ => 0))
  (Fin.cases 0 (fun _ => 1))).fitsPlane 16384

-- Small intersections with a unit-weight side have bases small enough
-- for an independent exhaustive oracle. Enumerate integer triples directly,
-- retain minimal nonzero solutions, and compare every coordinate.
private def triple (x y z : Nat) : ACBasis.Vec 3 :=
  Fin.cases x (Fin.cases y (fun _ => z))

private def checkUnitSide (pairs : List (ACBasis.Vec 3 × ACBasis.Vec 3)) : Bool := Id.run do
  let rows := pairs.map fun (p,q) => ACBasis.Row.ofWeights p q
  let some gs := boundedBasis rows | return false
  let mut solutions : List (List Nat) := []
  for x in [:4] do for y in [:4] do for z in [:4] do
    if x+y+z > 0 && pairs.all (fun (p,q) =>
      x*p 0 + y*p 1 + z*p 2 == x*q 0 + y*q 1 + z*q 2) then
      solutions := [x,y,z] :: solutions
  let primitive := solutions.filter fun s => !solutions.any fun t =>
    t != s && (t.zip s).all fun (a,b) => a ≤ b
  let actual := gs.map List.ofFn
  return primitive.length == actual.length && primitive.all actual.contains

-- Every signed coefficient triple in [-2,2] with a unit side, including
-- neutral coordinates and rows with unequal coefficients on the other side.
#guard (List.range 5).all fun i => (List.range 5).all fun j => (List.range 5).all fun k =>
  let p := triple (i-2) (j-2) (k-2)
  let q := triple (2-i) (2-j) (2-k)
  (!decide (ACBasis.Row.ofWeights p q).unitSide) || checkUnitSide [(p,q)]

#guard checkUnitSide [(triple 3 2 0,triple 0 0 1)]

-- Intersecting two equations forces all three coordinates to agree.
#guard checkUnitSide [(triple 2 0 0,triple 0 1 1),(triple 0 1 0,triple 0 0 1)]
-- Two non-unit sides retain the general bound.
#guard !(decide (ACBasis.Row.ofWeights (triple 2 0 0) (triple 0 3 0)).unitSide)

-- An independent oracle for p*x = q*y. Every slot must balance its own
-- multiplicities and at least one arm must realize the primitive ratio.
private def ratioCorrect (p q : Nat) : Bool := Id.run do
  let some arms := homogeneousUnify 2 #[#[p.toUInt64,0], #[0,q.toUInt64]] | return false
  let g := p.gcd q
  let mut principal := false
  for arm in arms do
    let [xs,ys] := arm.toList | return false
    let some w := xs[0]? | return false
    if ys.isEmpty then return false
    for slot in (xs.toList ++ ys.toList).eraseDups do
      if p * xs.toList.count slot != q * ys.toList.count slot then return false
    if xs.size == q/g && ys.size == p/g && xs.all (· == w) && ys.all (· == w) then
      principal := true
  return principal

#guard (List.range 7).all fun i => (List.range 7).all fun j => ratioCorrect (i+1) (j+1)
#guard ratioCorrect 11 13 && ratioCorrect 13 11

-- An optimizer that restores the old budget cannot meet the fixed contract:
-- 11x = 13y must complete even though its old box had 123,904 points.
private def lhs : Array UInt64 := #[11,0]
private def rhs : Array UInt64 := #[0,13]
private def ratioRow : ACBasis.Row 2 :=
  .ofWeights (fun i => lhs[i.val]!.toNat) (fun i => rhs[i.val]!.toNat)

example : ratioRow.boxSize = 123904 := by decide

example (run) (cert : Correct run) : (run 2 #[lhs,rhs]).isSome := by
  apply cert.completes
  refine ⟨by decide, by decide, by decide, [ratioRow], ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · simp [readRows, ratioRow, lhs, rhs, guard]
  · refine ⟨trivial, by decide, Or.inr (Or.inl (Or.inl ⟨Or.inr ⟨⟨0, by decide⟩, Or.inl (by decide), by decide⟩, ?_⟩))⟩
    rw [← ACBasis.Row.planeGenerators_eq]
    decide
  all_goals
    simp only [ACBasis.generate, ACBasis.intersect, ← ACBasis.Row.planeGenerators_eq]
    decide

-- All three coefficients exceed one, and no side has a single unit
-- occurrence. The old projected box for either row exceeded the work cap.
#guard (solve 3 #[#[7,8,0],#[0,0,15]]).map Array.size == some 5
#guard (solve 3 #[#[24,25,0],#[0,0,49]]).map Array.size == some 5
#guard (solve 3 #[#[60,61,0],#[0,0,121]]).map Array.size == some 5
-- Scaling both sides must preserve all slot identities and their order.
#guard solve 3 #[#[140,160,0],#[0,0,300]] == solve 3 #[#[7,8,0],#[0,0,15]]

-- The last row has sixteen primitive generators, one for each left/right pair.
-- The other row forces three right variables empty, in either orientation.
private def fourLeft : Array UInt64 := #[1,1,1,1,0,0,0,0]
private def fourRight : Array UInt64 := #[0,0,0,0,1,1,1,1]
private def oneRight : Array UInt64 := #[0,0,0,0,1,0,0,0]
#guard homogeneousUnify 8 #[fourLeft,oneRight,fourLeft,fourRight] == some #[]
#guard homogeneousUnify 8 #[oneRight,fourLeft,fourLeft,fourRight] == some #[]

-- A redundant row keeps every prior generator in the reference order.
#guard Id.run do
  let some rows := readRows 8 [fourLeft,fourRight] | return false
  let some prev := boundedBasis rows | return false
  let some next := boundedBasis (rows ++ rows) | return false
  return prev.length == 16 && next.map List.ofFn == (prev.map List.ofFn).reverse

-- Every unit generator is forced, even though there are 2^32 potential subsets.
#guard (solve 32 #[]).map Array.size == some 1
-- Each right variable can use the first left input, the second, or both.
-- Removing the two assignments that miss a left input leaves 3^6 - 2 arms.
#guard (solve 8 #[#[1,1,0,0,0,0,0,0],#[0,0,1,1,1,1,1,1]]).map Array.size == some 727
#guard solve 9 #[#[1,1,0,0,0,0,0,0,0],#[0,0,1,1,1,1,1,1,1]] == none

#guard (List.range 8).all fun a => (List.range 8).all fun b =>
  let gs := [testVector a, testVector b]
  let cost := ((selections gs).map (selectionWords gs)).sum
  packetFits gs cost && (cost == 0 || !packetFits gs (cost-1))

end Tamarin.Homogeneous.Tests
