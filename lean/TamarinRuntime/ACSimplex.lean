import TamarinRuntime.ACBasis
import Init.Data.Rat

namespace Tamarin.ACFeasibility.Simplex
open ACBasis

/-- Candidates refer to the original row and coordinate orders. The caller
checks them against those rows before reporting a verdict. -/
inductive Certificate where
  | primal (sizes : Array Nat)
  | dual (multipliers : Array Int)
  deriving Repr, BEq

private abbrev Tableau := Array (Array Rat)

private def limit : Nat := 2^512

private def fits (r : Rat) : Bool :=
  r.num.natAbs < limit && r.den < limit

/-- With x = 1 + z the original system is A z = -A 1, z ≥ 0.
Orient each row by a sign to make its new right-hand side nonnegative.
An artificial coordinate per equation supplies the initial feasible basis.
The last tableau row stores reduced costs and minus the sum of artificials. -/
private def initial {n} (rows : List (Row n)) : Option (Tableau × Array Nat × Array Int) := do
  let m := rows.length
  let rhs := n + m
  let mut objective : Array Rat := Array.replicate (rhs+1) 0
  let mut table : Tableau := #[]
  let mut basis := #[]
  let mut signs := #[]
  for (r, i) in rows.zipIdx do
    let mut signed : Array Int := #[]
    let mut sum : Int := 0
    for j in List.finRange n do
      let pos := r.pos j
      let neg := r.neg j
      guard (pos < limit && neg < limit)
      let c := (pos : Int) - neg
      signed := signed.push c
      sum := sum + c
    let sign : Int := if 0 < sum then -1 else 1
    let b : Rat := (sum.natAbs : Rat)
    guard (fits b)
    let mut row : Array Rat := Array.replicate (rhs+1) 0
    for j in [:n] do
      let a : Rat := ((sign * signed[j]!) : Int)
      row := row.set! j a
      let cost := objective[j]! - a
      guard (fits cost)
      objective := objective.set! j cost
    let cost := objective[rhs]! - b
    guard (fits cost)
    objective := objective.set! rhs cost
    row := (row.set! (n+i) 1).set! rhs b
    table := table.push row
    basis := basis.push (n+i)
    signs := signs.push sign
  return (table.push objective, basis, signs)

/-- Bland's first negative reduced cost, then minimum ratio with ties broken
by the index of the departing basic variable. -/
private def entering (objective : Array Rat) (rhs : Nat) : Option Nat := Id.run do
  for j in [:rhs] do
    if objective[j]! < 0 then return some j
  return none

private def leaving (table : Tableau) (basis : Array Nat) (col rhs : Nat) : Option Nat := Id.run do
  let mut best : Option (Nat × Rat) := none
  for i in [:basis.size] do
    let row := table[i]!
    let a := row[col]!
    if 0 < a then
      let ratio := row[rhs]! / a
      match best with
      | none => best := some (i,ratio)
      | some (old,smallest) =>
        if ratio < smallest || (ratio == smallest && basis[i]! < basis[old]!) then
          best := some (i,ratio)
  return best.map Prod.fst

private def pivot (table : Tableau) (row col : Nat) : Option Tableau := do
  let base := table[row]!
  let a := base[col]!
  let normalized ← base.mapM fun v => do
    let w := v / a
    guard (fits w)
    return w
  let mut next := table.set! row normalized
  for i in [:table.size] do
    if i != row then
      let source := table[i]!
      let factor := source[col]!
      if factor != 0 then
        let mut changed := source
        for j in [:source.size] do
          let w := source[j]! - factor * normalized[j]!
          guard (fits w)
          changed := changed.set! j w
        next := next.set! i changed
  return next

/-- Find a common positive denominator without overflowing a fixed word or
allowing many unrelated denominators to generate an unbounded certificate. -/
private def integral (xs : Array Rat) : Option (Array Int) := do
  let mut common := 1
  for x in xs do
    common := Nat.lcm common x.den
    guard (common < limit)
  return xs.map fun x => x.num * ((common / x.den : Nat) : Int)

private def primal (n rhs : Nat) (basis : Array Nat) (table : Tableau) : Option Certificate := do
  let mut x : Array Rat := Array.replicate n 1
  for i in [:basis.size] do
    let j := basis[i]!
    if j < n then x := x.set! j (1 + table[i]![rhs]!)
  let values ← integral x
  guard (values.all (0 < ·))
  return .primal (values.map Int.toNat)

/-- Artificial column j has reduced cost 1 - πⱼ. At a nonzero phase-I
optimum, -π times the row orientations is the separating multiplier on A. -/
private def dual (n : Nat) (signs : Array Int) (objective : Array Rat) : Option Certificate := do
  let values := signs.mapIdx fun j (sign : Int) => (objective[n+j]! - 1) * (sign : Rat)
  return .dual (← integral values)

/-- Exact, stateless phase-I candidate generation. Bound tableau allocation,
rational sizes, and total pivot work separately. Every limit defers the query. -/
def search {n} (rows : List (Row n)) : Option Certificate := do
  let m := rows.length
  let rhs := n + m
  let cells := (m+1) * (rhs+1)
  guard (cells ≤ 32768)
  let (table, basis, signs) ← initial rows
  let mut table := table
  let mut basis := basis
  let turns := min 512 (4194304 / cells)
  for step in [:turns+1] do
    let objective := table[m]!
    if objective[rhs]! == 0 then return ← primal n rhs basis table
    guard (objective[rhs]! < 0)
    let some col := entering objective rhs | return ← dual n signs objective
    guard (step < turns)
    let row ← leaving table basis col rhs
    table ← pivot table row col
    basis := basis.set! row col
  none

end Tamarin.ACFeasibility.Simplex
