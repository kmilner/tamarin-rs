import TamarinRuntime.ACLowRank
import TamarinRuntime.ACSeparation

namespace Tamarin.ACBasis.SpanCertificate
open ACFeasibility
variable {n : Nat}

structure Certificate where
  scale : Int
  weights : List Int
  deriving Repr, BEq

abbrev ZRow (n : Nat) := Vector Int n

def signed (r : Row n) : ZRow n := Vector.ofFn (LowRank.coeff r)

def linear : List Int → List (ZRow n) → Fin n → Int
  | w :: ws,r :: rs,i => w*r[i] + linear ws rs i
  | _,_,_ => 0

def pivot (p : ZRow n) : Option (Fin n) :=
  (List.finRange n).find? fun i => p[i] != 0

def bounded (p : ZRow n) : Bool := p.toArray.all fun z => z.natAbs < 2^256

/-- Eliminate one column by integer cross multiplication. The pivot may
have either sign. Its row remains available when lifting the certificate. -/
def eliminate (p : ZRow n) (j : Fin n) (t : ZRow n) : ZRow n :=
  Vector.ofFn fun i => p[j]*t[i] - t[j]*p[i]

def lift (p : ZRow n) (j : Fin n) (rs : List (ZRow n)) (q : ZRow n) (c : Certificate) : Certificate :=
  let u := p[j]
  ⟨c.scale*u, (c.scale*q[j] - linear c.weights rs j) :: c.weights.map (u*·)⟩

/-- Each nonzero original row is either chosen as a pivot or reduced to
zero. Retain the row order in the certificate, including redundant rows.
A failed arithmetic bound stops before using that row in another product. -/
def search : Nat → List (ZRow n) → ZRow n → Option Certificate
  | fuel, rs, q => do
    guard (bounded q && rs.all bounded)
    if (pivot q).isNone then return ⟨1,List.replicate rs.length 0⟩
    match fuel,rs with
    | k+1,p :: tail =>
      match pivot p with
      | none =>
        let c ← search k tail q
        return ⟨c.scale,0 :: c.weights⟩
      | some j =>
        let c ← search k (tail.map (eliminate p j)) (eliminate p j q)
        return lift p j tail q c
    | _,_ => none

def dimensions (n m : Nat) : Bool :=
  decide (n ≤ 4096 ∧ m ≤ 64 ∧ (n+1)*(m+1)*(m+1) ≤ 524288)

/-- Verify every coefficient on the original rows. No pivot order,
positivity assumption, or substitution is trusted by the caller. -/
def check (rs : List (Row n)) (q : Row n) (c : Certificate) : Bool :=
  c.scale != 0 && c.weights.length == rs.length &&
    (List.finRange n).all fun i =>
      c.scale * LowRank.coeff q i == Separation.column (c.weights.zip rs) i

def run (rs : List (Row n)) (q : Row n) : Option Certificate := do
  guard (dimensions n rs.length)
  let c ← search rs.length (rs.map signed) (signed q)
  guard (check rs q c)
  return c

end Tamarin.ACBasis.SpanCertificate
