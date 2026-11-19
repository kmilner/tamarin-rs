import TamarinRuntime.ACBagAnswers

namespace Tamarin.Matching.ACBagPages
open ACBagSearch ACBagAnswers

/-- Each factor indexes a column by dividing the raw ordinal by the number of
suffixes. The first factor varies slowest, as in `ACBagAnswers.product`. -/
inductive Plan where
  | endOfFactors
  | factor (atom : UInt64) (columns : Array (List Nat)) (suffixes : Nat) (tail : Plan)

def prepare : Batch → Nat × Plan
  | [] => (1, .endOfFactors)
  | (atom, columns) :: rest =>
    let (suffixes, tail) := prepare rest
    (columns.length * suffixes, .factor atom columns.toArray suffixes tail)

/-- Called only at an ordinal strictly below the count returned by `prepare`. -/
def Plan.pick : Plan → Nat → Pick
  | .endOfFactors, _ => []
  | .factor a cs n rest, index => (a,cs[index / n]?.getD []) :: rest.pick (index % n)

structure Page where
  total : Nat
  stop : Nat
  done : Bool
  answers : List Arm
  deriving Repr, BEq

def wordsPerPick (rows : Rows) (ks as : List UInt64) :=
  1 + ks.length * (1 + as.length) + (rows.map fun r => r.2.length).sum

def render (ks : List UInt64) (picks : List Pick) :=
  (picks.map (materialize ks)).filter fun arm => arm.all (!·.isEmpty)

def readPage (ks : List UInt64) (layers : Batch) (words start requested : Nat) : Option Page :=
  let prepared := prepare layers
  let total := prepared.1
  let capacity := min 256 (65536 / words)
  if requested = 0 ∨ total < start ∨ capacity = 0 then none else
  let span := min (total - start) (min requested capacity)
  let stop := start + span
  let picks := (List.range span).map fun offset => prepared.2.pick (start + offset)
  some ⟨total, stop, decide (stop = total), render ks picks⟩

/-- `stop` is exclusive and may exceed UInt64. Empty filtered pages still
consume raw ordinals. No prior page, generator state or full product is needed. -/
def run (rows : Rows) (start requested : Nat) : Option Page := do
  let (ks,as) ← inventories rows
  readPage ks (as.map fun a => (a,choices rows ks a)) (wordsPerPick rows ks as) start requested

end Tamarin.Matching.ACBagPages
