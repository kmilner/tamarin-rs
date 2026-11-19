import Tamarin.MaskedOperandContract
import TamarinRuntime

namespace Tamarin.OperandUnificationTests
open Executable Homogeneous

#guard operandUnify 2 #[#[1,0], #[0,1]] == none
#guard operandUnify 2 #[#[0], #[2]] == none
#guard operandUnify 2 #[#[0], #[1], #[1]] == none
#guard operandUnify 1 #[#[0,0], #[0]] == some #[]
#guard (operandUnify 2 #[#[0,0], #[1,1,1]]).isSome
#guard operandUnify 2 #[#[0,0], #[1,1,1], #[0], #[1]] == some #[]


private def fourByFour : Array (Array UInt64) := #[#[0,1,2,3], #[4,5,6,7]]
#guard (maskedOperandUnify 8 255 fourByFour).map Array.size == some 24
#guard maskedOperandUnify 8 256 fourByFour == none
#guard maskedOperandUnify 2 1 #[#[0,0], #[1,1,1]] == some #[]

-- Even a replacement with a different proof cannot reuse the unmasked
-- answer here. Three occurrences of one witness violate the singleton constraint.
private def scaledSides : Array (Array UInt64) := #[#[0,0],#[1,1,1]]
private def scaledArm : Arm := #[#[0,0,0],#[0,0]]
#guard operandUnify 2 scaledSides == some #[scaledArm]
example (solver : MaskedOperands.Kernel) (ran : solver 2 1 scaledSides = some #[scaledArm]) :
    ¬ MaskedOperands.Correct solver := by
  intro ok
  have kept := (ok.valid 2 1 scaledSides _ ran).2.2 scaledArm (by simp)
  have excluded : IndivisibleOperands.keeps (IndivisibleOperands.wordMask 2 1) scaledArm = false := by decide
  rw [excluded] at kept
  contradiction

-- Interpret the tagged residual equation for each operand in the positive
-- integers under addition. All witnesses in a realizable arm have size at most
-- the sum of the two operand sizes. Their names and answer order are arbitrary.
private def realizes (x y : Nat) (arm : Arm) : Bool := Id.run do
  let entries := arm.toList.map Array.toList
  let names := (entries.flatMap List.tail).eraseDups
  if names.length > x + y then return false
  let rec choose (acc : List (UInt64 × Nat)) : List UInt64 → Bool
    | [] => entries.all fun row =>
      match row with
      | key :: rest =>
        key < 2 && !rest.isEmpty &&
          (rest.map (fun j => (acc.lookup j).getD 0)).sum == (if key == 0 then x else y)
      | [] => false
    | j :: js => (List.range (max x y)).any fun i => choose ((j,i+1)::acc) js
  return (entries.map List.head?).contains (some 0) &&
    (entries.map List.head?).contains (some 1) && choose [] names

-- Each query has one nontrivial equation and may add a second one shared
-- across both columns. A model of the original equations checks the answers
-- through the actual combined export independently of the matrix arithmetic.
private def stress : Bool := Id.run do
  let sides : List (List UInt64) :=
    [[0],[1],[0,0],[0,1],[1,0],[1,1],[0,0,1],[1,0,0],[1,1,1]]
  for l in sides do
    for r in sides do
      if !((l ++ r).contains 0 && (l ++ r).contains 1) || l.count 0 == r.count 0 && l.count 1 == r.count 1 then
        continue
      for joined in [false,true] do
        let roots := #[l.toArray, r.toArray] ++ (if joined then #[#[0],#[1]] else #[])
        let some raw := operandUnify 2 roots | return false
        let some tagged := projectAnswers 2 raw | return false
        for x in [1,2,3] do
          for y in [1,2,3] do
            let size := fun (s : List UInt64) => s.count 0 * x + s.count 1 * y
            if tagged.any (realizes x y) != (size l == size r && (!joined || x == y)) then
              return false
  return true
#guard stress

end Tamarin.OperandUnificationTests
