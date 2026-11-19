import Tamarin.ACFeasibility
import TamarinRuntime

open Tamarin Tamarin.ACBasis Tamarin.ACFeasibility

private def row {n} (weights : Vector Int n) : Row n :=
  Row.ofWeights (fun i => weights[i].toNat) (fun i => (-weights[i]).toNat)

private def r₁ := row #v[1,-2,0]
private def r₂ := row #v[0,1,-1]
private def r₃ := row #v[1,0,-1]

-- The low-rank subsystem has a positive solution. The third row makes the
-- signed combination r₃ − r₁ − r₂ positive in the second column.
#guard checkCertificate [r₁,r₂] (.primal #[2,1,1]) == some true
#guard (checkCertificate [r₁,r₂,r₃] (.primal #[2,1,1])).isNone
#guard (checkCertificate [r₁,r₂] (.primal #[0,0,0])).isNone
#guard (checkCertificate [r₁,r₂] (.primal #[2,1])).isNone
#guard (checkCertificate [r₁,r₂] (.primal #[2,1,1,1])).isNone
#guard checkCertificate [r₁,r₂,r₃] (.dual #[-1,-1,1]) == some false
#guard (checkCertificate [r₁,r₂,r₃] (.dual #[1,1,-1])).isNone
#guard (checkCertificate [r₁,r₂,r₃] (.dual #[0,0,0])).isNone
#guard (checkCertificate [r₁,r₂,r₃] (.dual #[-1,-1])).isNone
#guard (checkCertificate [r₁,r₂,r₃] (.dual #[-1,-1,1,0])).isNone

example (rs : List (Row 3)) : Required rs := Required.fewColumns (by decide)

-- The two public rank-four regressions exercise these original matrices.
-- Their completion follows from the input even if the candidate changes.
private def gridColumn (k : Nat) : Vector Int 4 :=
  let p := ((k / 9 : Nat) : Int) - 2
  let q := (((k / 3) % 3 : Nat) : Int) - 1
  let r := ((k % 3 : Nat) : Int) - 1
  #v[p,q,r,p+2*q+3*r+1]

private def extraColumn (k : Nat) : Vector Int 4 :=
  if k = 0 then #v[8,0,0,7] else if k = 1 then #v[-8,0,0,-9] else gridColumn (k-2)

private def matrix {n} (column : Nat → Vector Int 4) : List (Row n) :=
  [0,1,2,3].map fun (j : Fin 4) => row (Vector.ofFn fun i : Fin n => (column i.val)[j])

set_option maxRecDepth 8192 in
example : Required (matrix (n := 45) gridColumn) := by
  apply Required.original
  apply BaseRequired.separator
  refine ⟨by decide,3,by decide,by decide,by decide,[-1,-2,-3,1],?_,by decide⟩
  exact (Separation.separates_iff ..).mp (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
example : Required (matrix (n := 47) extraColumn) := by
  apply Required.original
  apply BaseRequired.pairCorrection
  let x : Vec 47 := fun i => if i = 0 ∨ i = 1 then 45 else 2
  refine ⟨by decide,x,?_,?_,2,by decide,[0,1],by decide,?_⟩
  · simp only [matrix,List.map_cons,List.map_nil,SystemHolds,List.forall_mem_cons,
      List.not_mem_nil,false_implies,implies_true,and_true,Row.Holds]
    decide
  · decide
  · intro i absent
    have ne : ¬(i = 0 ∨ i = 1) := by simpa using absent
    simp [x,ne]


/-- Enumerate all signed ternary 3×3 matrices. The three-column rank test is
an independent total decision procedure. Every proposed certificate and every
final decision must agree with it, including on dependent and singular rows. -/
def main : IO Unit := do
  let rows := (List.range 27).map fun k => row (Vector.ofFn fun i : Fin 3 =>
    ((k / 3^i.val % 3 : Nat) : Int) - 1)
  let mut positive := 0
  let mut negative := 0
  for p in rows do
    for q in rows do
      for r in rows do
        let rs := [p,q,r]
        let expected := ThreeColumns.decide rs
        if let some verdict := certifiedSearch rs then
          unless verdict == expected do throw <| IO.userError "incorrect certified verdict"
        unless checkRows rs == some expected do throw <| IO.userError "incorrect or missing three-column decision"
        if expected then positive := positive + 1 else negative := negative + 1
  unless positive > 0 && negative > 0 && positive + negative == 19683 do
    throw <| IO.userError "incomplete matrix fixture"
  IO.println s!"All 19,683 ternary 3×3 systems agreed ({positive} positive and {negative} negative)."
