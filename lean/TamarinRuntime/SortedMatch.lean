import TamarinWire

namespace Tamarin.SortedMatch

abbrev Answers := Array (Array (Array UInt64))
abbrev Flat := UInt64 → Array UInt64 → Array UInt64 → Array UInt64 → Answers
abbrev Kernel := UInt64 → Array UInt64 → Array UInt64 → Array UInt64 → Array UInt64 → Array UInt64 →
  Option Answers

def valid (ac : UInt64) (vars atoms occ tail rhs : Array UInt64) : Bool :=
  ac ≤ 4 && vars.size < UInt64.size &&
    vars.all (fun s => s ≤ 4 && Whole.subsort s ac) &&
    atoms.all (fun s => s ≤ 4 && Whole.subsort s ac) &&
    occ.all (fun i => i.toNat < vars.size) &&
    tail.all (fun j => j.toNat < atoms.size) && rhs.all (fun j => j.toNat < atoms.size)

/-- A singleton retains its atom's sort. A product has the sort of the AC symbol. -/
def checkRow (ac v : UInt64) (atoms row : Array UInt64) : Bool :=
  if row.size = 1 then
    (atoms[row[0]!.toNat]?).any (fun s => Whole.subsort s v)
  else
    1 < row.size && Whole.subsort ac v

def checkArm (ac : UInt64) (vars atoms : Array UInt64) (arm : Array (Array UInt64)) : Bool :=
  arm.size == vars.size && vars.size.all fun i hi =>
    (arm[i]?).any (checkRow ac vars[i] atoms)

def runWith (flat : Flat) : Kernel := fun ac vars atoms occ tail rhs =>
  if valid ac vars atoms occ tail rhs then
    some ((flat vars.size.toUInt64 occ tail rhs).filter (checkArm ac vars atoms))
  else none

end Tamarin.SortedMatch
