import Tamarin.ACBagPages
import Std.Data.HashSet

open Tamarin.Matching
open ACBagSearch (Rows)
open ACBagAnswers (Arm)
open ACBagPages (Page)

private def atoms (n : Nat) := (List.range n).map Nat.toUInt64
private def three : Rows := [([17,23,79], atoms 8)]

private def require (p : Bool) (reason : String) : IO Unit := do
  unless p do throw (IO.userError reason)

private def readPage (rows : Rows) (cursor size : Nat) : IO Page := do
  let some page := ACBagPages.run rows cursor size | throw (IO.userError s!"unexpected deferral at {cursor}")
  return page

private def pages (rows : Rows) (size expected : Nat) : IO (List Arm) := do
  let mut cursor := 0
  let mut chunks := []
  for _ in [:expected + 1] do
    let page ← readPage rows cursor size
    require (page.total == expected && page.stop ≤ expected && page.done == (page.stop == expected))
      s!"inconsistent raw range at {cursor}"
    require (page.stop - cursor ≤ size && (page.stop > cursor || page.done)) "page failed to progress"
    chunks := page.answers :: chunks
    if page.done then return chunks.reverse.flatten
    cursor := page.stop
  throw (IO.userError "no terminal page")

set_option maxRecDepth 4096 in
example : ACBagSearch.Within three := by
  refine ⟨by decide,by decide,by decide,by decide,?_⟩
  intro a ha
  refine ⟨1,?_,by decide⟩
  have ok : ∀ b ∈ three.flatMap Prod.snd, ∀ r ∈ three, r.2.count b ≤ 1 := by decide
  exact ok a ha

def main : IO Unit := do
  require (ACBagAnswers.run three).isNone "fixture fits one-shot budget"
  let empty ← readPage three 0 1
  require (!empty.done && empty.stop == 1 && empty.answers.isEmpty) "empty first pick was treated as terminal"
  let arms ← pages three 233 6561
  let alternate ← pages three 91 6561
  require (arms == alternate) "different page sizes changed answer order"
  require (arms.length == 5796 && (Std.HashSet.ofList arms).size == 5796) "incomplete or duplicate three-way partition"
  require (arms.all fun arm => arm.length == 3 && arm.all (!·.isEmpty) && decide (arm.flatten.Perm (atoms 8)))
    "invalid partition"
  let endPage ← readPage three 6561 29
  require (endPage.done && endPage.answers.isEmpty && endPage.stop == endPage.total) "invalid terminal cursor"
  require ((ACBagPages.run three 6562 1).isNone && (ACBagPages.run three 1 0).isNone) "invalid cursors accepted"

  let wide : Rows := [([17,23], atoms 120)]
  let index := 2^117
  let middle ← readPage wide index 512
  require (middle.total == 2^120 && middle.stop > index && middle.stop - index < 256 &&
    middle.answers.length == middle.stop - index) "direct large-index seek or construction bound failed"
  let last ← readPage wide (2^120 - 1) 17
  require (last.done && last.answers.isEmpty && last.stop == 2^120) "wrong last pick above UInt64"

  let impossible : Rows := [([17,17,23,23],atoms 8)]
  let no ← readPage impossible 0 3
  require (no.done && no.total == 0 && no.stop == 0 && no.answers.isEmpty) "empty factor column was ignored"
  let unit ← readPage [] 0 3
  require (unit.done && unit.total == 1 && unit.answers == [[]]) "empty product lost the identity matcher"
  IO.println "AC bag pages: 5,796 distinct three-key solutions over 6,561 raw picks; exact seek inside 2^120 picks"
