namespace Tamarin.OperandRefinementCandidate

def key (l r : UInt64) : UInt64 × UInt64 :=
  if l ≤ r then (l, r) else (r, l)

/-- Keep the first occurrence of each unordered non-reflexive equation.
The input contains two interned root IDs per equation. -/
def select (index : Nat) (seen : List (UInt64 × UInt64)) : List UInt64 → List UInt64
  | l :: r :: rest =>
    if l = r ∨ key l r ∈ seen then select (index + 1) seen rest
    else index.toUInt64 :: select (index + 1) (key l r :: seen) rest
  | _ => []

def keep (sides : Array UInt64) : Array UInt64 :=
  (select 0 [] sides.toList).toArray

end Tamarin.OperandRefinementCandidate
