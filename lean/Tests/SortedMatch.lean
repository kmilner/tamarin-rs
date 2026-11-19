import TamarinRuntime

namespace Tamarin.SortedMatchTests
open Executable

-- Singleton images have their literal's sort. Repeated occurrences of a
-- variable consume the same literal every time.
#guard sortedACMatch 2 #[0,2] #[0,1] #[0,1,0] #[] #[0,1,0] == some #[#[#[0],#[1]]]
#guard sortedACMatch 2 #[0,1] #[0,1] #[0,0,1] #[] #[0,1,1] == some #[]
#guard sortedACMatch 4 #[4] #[4,4] #[0] #[] #[0,1] == some #[#[#[0,1]]]
#guard sortedACMatch 2 #[3] #[2] #[0] #[] #[0] == none
#guard sortedACMatch 2 #[2] #[7] #[0] #[] #[0] == none
#guard sortedACMatch 2 #[2] #[0] #[1] #[] #[0] == none
#guard sortedACMatch 2 #[2] #[0] #[0] #[1] #[0] == none
#guard sortedACMatch 2 #[2] #[0] #[0] #[] #[1] == none

-- Enumerate nonempty images independently by selecting positions in the
-- subject. A sorted multiset comparison checks simultaneous consumption.
private def selections (xs : List UInt64) : List (List UInt64) :=
  xs.foldr (fun x rest => rest ++ rest.map (x :: ·)) [[]]

private def stress : Bool := Id.run do
  let ids : List UInt64 := [0,1,2]
  let sorts : Array UInt64 := #[0,1,4] -- Pub, Fresh, Nat all embed in Msg.
  let vars : List UInt64 := [0,1,2,4]
  let subjects := ids.flatMap fun a => ids.flatMap fun b => [[a,b]] ++ ids.map fun c => [a,b,c]
  for subject in subjects do
    let images := (selections subject).filter (!·.isEmpty)
    for x in vars do
      for y in vars do
        for occ in [([0,1] : List UInt64), [0,0,1]] do
          for tail in [([] : List UInt64),[0]] do
            let some got := sortedACMatch 2 #[x,y] sorts occ.toArray tail.toArray subject.toArray | return false
            let accepts (s : UInt64) (row : List UInt64) := s == 2 || match row with
              | [j] => sorts[j.toNat]? == some s
              | _ => false
            let mut expected := #[]
            for l in images do
              for r in images do
                if accepts x l && accepts y r then
                  let factors := (occ.flatMap fun i => if i == 0 then l else r) ++ tail
                  if factors.mergeSort == subject.mergeSort then expected := expected.push #[l.toArray,r.toArray]
            if !(got.all expected.contains && expected.all got.contains) then return false
  return true
#guard stress

end Tamarin.SortedMatchTests
