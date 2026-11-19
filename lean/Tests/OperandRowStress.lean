import TamarinRuntime

/-! Check the observable conjunction by evaluating its rows on assignments
of root IDs to two distinct values. The oracle never compares rows to
decide which are redundant. -/
open Tamarin

private abbrev Row := UInt64 × UInt64

private def name : Nat → UInt64
  | 0 => UInt64.ofNat (2^64 - 1)
  | 1 => 0
  | _ => 37

private def rowsFor (width code : Nat) : List Row :=
  (List.range width).map fun i =>
    let digit := code / 9^i % 9
    (name (digit / 3), name (digit % 3))

private def holds (assignment : Nat) (rows : List Row) : Bool :=
  let value := fun id => assignment.testBit (if id == name 0 then 0 else if id == name 1 then 1 else 2)
  rows.all fun (a,b) => value a == value b

private def checks (rows : List Row) (selected : Array UInt64) : Bool := Id.run do
  let some retained := selected.toList.mapM (fun i => rows[i.toNat]?) | return false
  return (List.range 8).all fun a => holds a rows == holds a retained

def main : IO Unit := do
  let distinct : List Row := [(name 0,name 1),(name 1,name 2)]
  for wrong in [#[], #[0], #[1], #[0,0], #[0,1,2]] do
    if checks distinct wrong then throw <| IO.userError "accepted missing constraint or invalid row index"
  let mut count := 0
  for width in [:5] do
    for code in [:9^width] do
      let rows := rowsFor width code
      let packet := (rows.flatMap fun (a,b) => [a,b]).toArray
      unless checks rows (Executable.operandRefine packet) do
        throw <| IO.userError s!"changed the solutions of {rows}"
      count := count + 1
  IO.println s!"{count} operand conjunctions checked on all eight two-valued assignments"
