import Tamarin.ACFeasibility

open Tamarin Tamarin.ACBasis Tamarin.ACFeasibility

private def signedRow {n} (w : Fin n → Int) : Row n where
  pos i := (w i).toNat
  neg i := (-(w i)).toNat
  disjoint i := by
    by_cases h : w i ≤ 0
    · exact Or.inl (Int.toNat_eq_zero.mpr h)
    · exact Or.inr (Int.toNat_eq_zero.mpr (by omega))

private theorem signed_of_row {n} (w : Fin n → Int) (i : Fin n) :
    RowReduction.Reference.signed (signedRow w) i = w i := by
  simp only [RowReduction.Reference.signed,signedRow]
  omega

private def fromPlane {n} (p q : Fin n → Int) (slopes : List (Int × Int)) : List (Row n) :=
  slopes.map fun (a,b) => signedRow fun i => a*p i+b*q i

private theorem planeRequired {n} (p q : Fin n → Int) (slopes : List (Int × Int)) :
    Required (fromPlane p q slopes) := by
  apply Required.lowRank
  apply LowRank.Within.of_span _ p q
  intro r hr
  obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨1,a,b,by decide,by intro i; simp [signed_of_row]⟩

private def profiles (positive : Bool) : List (Int × Int) :=
  let common := (List.range 9).flatMap fun (p : Nat) =>
    (List.range 5).map fun (d : Nat) => ((p : Int)-4,(d : Int)+1)
  if positive then common ++ [(1,-1),(-1,-1)] else common

private def liveRows (positive : Bool) : List (Row (profiles positive).length) :=
  let cols := (profiles positive).toArray
  let get := fun i : Fin (profiles positive).length => cols[i.val]'(by simp [cols])
  fromPlane (fun i => (get i).1) (fun i => (get i).2)
    [(1,0),(1,1),(2,1),(-2,1),(-1,1),(3,-2)]

example (positive : Bool) : Required (liveRows positive) := planeRequired _ _ _

-- Both full public systems previously exhausted the existing native delegates.
-- D is strictly positive in the first system. In the second, assigning 2 to
-- each ordinary column and 135 to each extra column balances both P and D.
#guard [false,true].all fun answer =>
  let rows := liveRows answer
  LowRank.run rows == some answer && checkRows rows == some answer &&
    LowRank.run rows.reverse == some answer

private def row {n} (v : Vector Int n) : Row n := signedRow fun i => v[i]
private def z := row #v[0,0,0]
private def p := row #v[1,-1,0]
private def q := row #v[0,1,-1]

#guard LowRank.run [z,z,z,z] == some true
#guard LowRank.run [z,p,z,row #v[-7,7,0]] == some true
#guard LowRank.run [z,row #v[1,0,1],row #v[3,0,3]] == some false
#guard LowRank.run [z,p,p,z,q,row #v[1,0,-1]] == some true
-- Changing one coefficient of a dependent row introduces a third pivot.
-- Trusting the surviving pair would return true for an impossible system.
#guard (LowRank.run [z,p,p,z,q,row #v[1,0,-2]]).isNone
#guard LowRank.run [row #v[], row #v[], row #v[]] == some true

private def huge : Int := 2^175
#guard LowRank.run [row #v[huge,-huge,0],row #v[0,huge+1,-(huge+1)],
    row #v[huge,1,-(huge+1)]] == some true
