import Tamarin.MultisetDifferenceTR

/-!
Run with `lake env lean --run Tests/MultisetDifferenceTR.lean`.
The long cases exercise the skipped-output accumulator that made the
reference implementation recurse non-tail-first through the entire suffix.
-/
open Tamarin.Executable

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  expect (subtractSortedTR [] [] == some []) "empty input"
  expect (subtractSortedTR [2, 2] [1, 2, 2, 3] == some [1, 3]) "multiplicity"
  expect (subtractSortedTR [2, 2] [1, 2, 3] == none) "missing multiplicity"
  expect (subtractSortedTR [2] [1, 2, 3, 4] == some [1, 3, 4]) "shared suffix"
  let size := 2_000_000
  let available := (List.range size).map UInt64.ofNat
  match subtractSortedTR [UInt64.ofNat (size - 1)] available with
  | none => throw (IO.userError "long residual unexpectedly failed")
  | some rest =>
      expect (rest.length == size - 1) "long residual length"
      expect (rest.head? == some 0) "long residual order"
      expect (rest.getLast? == some (UInt64.ofNat (size - 2))) "long residual final atom"
  expect (subtractSortedTR [UInt64.ofNat size] available == none) "long failure"
  IO.println s!"Tail-recursive subtraction passed, including {size} atoms"
