import TamarinRuntime.ACBasis

/-! Coalesce columns with identical coefficients in every equation before a
strict-positive feasibility query. Representatives retain their encounter order. -/
namespace Tamarin.ACFeasibility.ColumnQuotient
open ACBasis

abbrev Profile := List (Nat × Nat)

def profile {n} (rs : List (Row n)) (i : Fin n) : Profile :=
  rs.map fun r => (r.pos i,r.neg i)

def collect {n} (key : Fin n → Profile) : List (Fin n) → Std.HashSet Profile → List (Fin n) → List (Fin n)
  | [], _, stored => stored.reverse
  | i::is, seen, stored =>
    let k := key i
    if seen.contains k then collect key is seen stored
    else collect key is (seen.insert k) (i::stored)

def representatives {n} (rs : List (Row n)) : List (Fin n) :=
  collect (profile rs) (List.finRange n) ∅ []

def restrict {k n} (index : Fin k → Fin n) (r : Row n) : Row k :=
  ⟨fun i => r.pos (index i),fun i => r.neg (index i),fun i => r.disjoint (index i)⟩

def projected {n} (rs : List (Row n)) (reps : List (Fin n)) : List (Row reps.length) :=
  let idx := reps.toArray
  rs.map (restrict (fun i => idx[i.val]'(by simp [idx])))

def compressed {n} (rs : List (Row n)) := projected rs (representatives rs)

/-- The delegate receives only a strictly smaller problem. The input guard
bounds the number of coefficient pairs inspected before forming signatures. -/
def run {n} (solve : {k : Nat} → List (Row k) → Option Bool) (rs : List (Row n)) : Option Bool := do
  guard (n ≤ 4096 ∧ rs.length ≤ 64)
  let reps := representatives rs
  guard (reps.length < n)
  solve (projected rs reps)

end Tamarin.ACFeasibility.ColumnQuotient
