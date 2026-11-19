import Tamarin.ACSeparation

open Tamarin Tamarin.ACBasis Tamarin.ACFeasibility

private def signed {n} (v : Vector Int n) : Row n :=
  Row.ofWeights (fun i => v[i].toNat) (fun i => (-v[i]).toNat)

-- Both original equations have live terms on both sides. Their signed
-- difference isolates a single strictly positive variable.
private def p := signed #v[2,-1,1]
private def q := signed #v[2,-1,0]
#guard Separation.separates [p,q] [1,-1]
#guard !Separation.separates [p,q] [-1,1]
example : ¬ Feasible [p,q] := Separation.separates_refutes (weights := [1,-1]) (by decide)

-- A negative coefficient after a positive one still invalidates the proof.
#guard !Separation.separates [p,q] [1,0]
#guard !Separation.separates [p,p] [1,-1]
#guard !Separation.separates [p,q] [0,0]
#guard !Separation.separates [p,q] [1,-1,0]
#guard !Separation.separates [signed #v[1], signed #v[1]] [1]
#guard !Separation.separates [signed #v[]] [1]
#guard !Separation.separates (n := 4) [] []

-- Arbitrarily large positive and negative row weights may cancel exactly.
private def huge : Int := 2^180
#guard Separation.separates [p,q] [huge,-huge]
#guard !Separation.separates [signed #v[1,-1], signed #v[-1,1]] [huge,huge-1]
