import TamarinRuntime
import Tamarin.OrdinalAllocation

namespace Tamarin.AnswerProjectionTests
open Executable
private def last : UInt64 := 18446744073709551615

#guard projectAnswers 2 #[#[#[last,7,last], #[7]], #[#[23], #[7,23]]] ==
  some #[#[#[0,0,1,0], #[1,1]], #[#[0,2], #[1,1,2]]]
#guard projectAnswers 2 #[] == some #[]
#guard projectAnswers 2 #[#[]] == none
#guard projectAnswers 2 #[#[#[7]]] == none
#guard projectAnswers 2 #[#[#[7], #[]]] == none
#guard projectAnswers 0 #[] == none
#guard projectAnswers 33 #[] == some #[]
#guard projectAnswers 65 #[] == some #[]
#guard projectAnswers 66 #[] == none

-- An independent first-use dictionary checks every pair of two-column arms,
-- including unequal multiplicities and sharing confined to the second arm.
private def images : List (Array UInt64) := Id.run do
  let alphabet := [0,7,last]
  return (alphabet.map fun i => #[i]) ++
    (alphabet.flatMap fun i => alphabet.map fun j => #[i,j])

private def stress : Bool := Id.run do
  let arms := images.flatMap fun a => images.map fun b => #[a,b]
  for a in arms do
    for b in arms do
      let raw := #[a,b]
      let slots := raw.toList.flatMap fun arm => arm.toList.flatMap Array.toList
      let keys := slots.foldl (fun ks k => if ks.contains k then ks else ks ++ [k]) ([] : List UInt64)
      let expected := raw.map fun arm => arm.toList.zipIdx.toArray.map fun (row,i) =>
        #[i.toUInt64] ++ row.map fun k => (keys.idxOf k).toUInt64
      if projectAnswers 2 raw != some expected then return false
  return true
#guard stress

#guard OrdinalAllocation.allocate (fun i => i == 0 || i == 2) 3 == some [1,3,4]
#guard OrdinalAllocation.takeFree (fun _ => false) UInt64.size last.toNat 1 == some [last.toNat]
#guard OrdinalAllocation.takeFree (fun _ => false) UInt64.size last.toNat 2 == none
#guard OrdinalAllocation.takeFree (· == last) UInt64.size last.toNat 1 == none
end Tamarin.AnswerProjectionTests
