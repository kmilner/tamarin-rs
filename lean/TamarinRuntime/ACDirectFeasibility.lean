import TamarinRuntime.ACBasis

namespace Tamarin.ACFeasibility
open ACBasis

def oneSided {n} (r : Row n) : Bool := decide ((total r.pos = 0) ↔ ¬ (total r.neg = 0))

/-- A row with a positive and a negative coefficient admits a positive
assignment. Check that same assignment against every other row before
returning a verdict for the conjunction. Scanning the input needs no basis. -/
def direct {n} (rs : List (Row n)) : Option Bool := do
  if rs.any oneSided then return false
  let some r := rs.find? (fun r => total r.pos != total r.neg) | return true
  let left := total r.pos
  let right := total r.neg
  let x := Vector.ofFn fun i => if 0 < r.pos i then right else if 0 < r.neg i then left else 1
  if rs.all (fun s => dot s.pos (fun i => x[i]) == dot s.neg (fun i => x[i])) then return true
  none

end Tamarin.ACFeasibility
