import Std

/-!
Candidate-owned numerical algorithms. This module deliberately imports no
semantic contract or proof harness. Local builds may experiment here; CI
checks the selected implementation against Tamarin.BackendContract.
-/
namespace Tamarin.Executable

def subtractSortedTRGo (need available skippedRev : List UInt64) : Option (List UInt64) :=
  match available with
  | [] =>
      match need with
      | [] => some (skippedRev.reverseAux [])
      | _ :: _ => none
  | y :: ys =>
      match need with
      | [] => some (skippedRev.reverseAux (y :: ys))
      | x :: xs =>
          if x = y then subtractSortedTRGo xs ys skippedRev
          else if y < x then subtractSortedTRGo (x :: xs) ys (y :: skippedRev)
          else none
termination_by structural available

def subtractSortedTR (need available : List UInt64) : Option (List UInt64) :=
  subtractSortedTRGo need available []

def atomLE (a b : UInt64) : Bool := decide (a ≤ b)

def difference (tail rhs : List UInt64) : Option (List UInt64) :=
  subtractSortedTR (tail.mergeSort atomLE) (rhs.mergeSort atomLE)

def residual (tail rhs : List UInt64) : List UInt64 :=
  if tail.isEmpty || rhs.isEmpty then [0]
  else match difference tail rhs with
    | none => [1]
    | some [] => [1]
    | some (a :: rest) => 2 :: a :: rest

def sameMultiset (xs ys : List UInt64) : Bool :=
  xs.mergeSort atomLE == ys.mergeSort atomLE

def classify (xs ys : List UInt64) : UInt8 :=
  if xs.isEmpty || ys.isEmpty then 0
  else if sameMultiset xs ys then 2 else 1

end Tamarin.Executable
