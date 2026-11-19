import Tamarin.ACTwoRowFeasibility
import TamarinRuntime.ACColumnSupport

open Tamarin Tamarin.ACBasis Tamarin.ACFeasibility TwoRow

private def signedRow {n} (weights : Vector Int n) : Row n :=
  Row.ofWeights (fun i => (weights[i]).toNat) (fun i => (-weights[i]).toNat)

private def coeffs (r : Nat) : List (Int × Int) :=
  (List.range (2*r+1)).flatMap fun (i : Nat) => (List.range (2*r+1)).map fun (j : Nat) =>
    ((i : Int) - r,(j : Int) - r)

-- Exhaust all 625 signed two-column systems of magnitude ≤ 2, and all 729
-- signed three-column systems of magnitude ≤ 1. Compare the full answer
-- with the existing exact sparse-support checker on the same input matrix.
private def agree {n} (cols : Vector (Int × Int) n) : Bool :=
  let p := signedRow (cols.map Prod.fst)
  let q := signedRow (cols.map Prod.snd)
  ColumnSupport.run [p,q] 8 == some (decidePair p q)

#guard (coeffs 2).all fun a => (coeffs 2).all fun b => agree #v[a,b]
#guard (coeffs 1).all fun a => (coeffs 1).all fun b => (coeffs 1).all fun c => agree #v[a,b,c]

-- Fractions with enormous nearly equal numerators compare by exact order.
private def N : Int := 2^170
#guard decidePair (signedRow #v[N,-(N+1), 0]) (signedRow #v[N-1,-N,1])
#guard !decidePair (signedRow #v[N,-(N+1), 0]) (signedRow #v[N-1,-N,-1])
#guard decidePair (signedRow #v[N,-(N+1)]) (signedRow #v[2*N,-(2*(N+1))])

-- The extreme slopes occur at different ends of a wide input. Both orders
-- and the case with no nonzero coordinates must agree.
private def wide (n : Nat) (separate : Bool) : Row n × Row n :=
  let common (i : Fin n) := if i.val+2 < n then 1 else 0
  (Row.ofWeights common (fun i =>
     if separate then (if i.val+2 == n then 1 else 0) else (if i.val+2 < n then 0 else 1)),
   Row.ofWeights common (fun i =>
     if separate then (if i.val+1 == n then 1 else 0) else (if i.val+2 < n then 0 else 2)))

#guard [false,true].all fun expected =>
  let (p,q) := wide 4096 expected
  decidePair p q == expected && decidePair q p == expected
#guard decidePair (signedRow #v[]) (signedRow #v[])
