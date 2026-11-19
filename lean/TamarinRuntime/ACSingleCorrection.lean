import TamarinRuntime.ACBasis

namespace Tamarin.ACFeasibility.SingleCorrection
open ACBasis
variable {n : Nat}

namespace Ratio

/-- For each signed pair (c,s), c is the coefficient sum on the chosen
coordinates and s is the sum over the entire row. Two common sizes must
satisfy c*a = (c-s)*b for every pair. -/
abbrev Constraints := List (Int × Int)

def balanced (r : Int × Int) (a b : Nat) : Bool :=
  r.1 * (a : Int) == (r.1 - r.2) * (b : Int)

def test (p : Int × Int) (rs : Constraints) : Bool :=
  let a := (p.1-p.2).natAbs
  let b := p.1.natAbs
  0 < a && 0 < b && rs.all (fun r => balanced r a b)

def run (rs : Constraints) : Bool :=
  match rs.find? (fun r => r.2 != 0) with
  | none => true
  | some p => test p rs

end Ratio

def signed (r : Row n) (j : Fin n) : Int := (r.pos j : Int) - r.neg j

def prepare (r : Row n) : Row n × Int := (r, (total r.pos : Int) - total r.neg)

def column (j : Fin n) (r : Row n × Int) : Int × Int := (signed r.1 j, r.2)

/-- Totals and the pivot row are shared by all tested coordinates. The
search and validation use linear work in the original number of cells. -/
def run (rs : List (Row n)) : Option Bool :=
  let prepared := rs.map prepare
  match prepared.find? (fun r => r.2 != 0) with
  | none => some true
  | some p =>
    if (List.finRange n).any (fun j => Ratio.test (column j p) (prepared.map (column j))) then
      some true
    else none

end Tamarin.ACFeasibility.SingleCorrection
