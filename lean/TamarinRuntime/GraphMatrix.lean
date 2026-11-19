import TamarinWire
import TamarinRuntime.Homogeneous

namespace Tamarin.GraphMatrix
open Whole

/- Visit occurrences even when multiple roots or children share a graph node.
Stop at 4096 leaves per side, the Rust encoder's maximum expanded request size. -/
mutual
  def gather (symbol sort : UInt64) : Tree → Array UInt64 → Option (Array UInt64)
    | .leaf k id s, acc =>
      if k = 0 ∧ s = sort ∧ acc.size < 4096 then some (acc.push id) else none
    | .app k id ts, acc =>
      if k = 4 ∧ id = symbol then gatherChildren symbol sort ts acc else none
  def gatherChildren (symbol sort : UInt64) : List Tree → Array UInt64 → Option (Array UInt64)
    | [], acc => some acc
    | t :: ts, acc => do
      let next ← gather symbol sort t acc
      gatherChildren symbol sort ts next
end

/-- Each occurrence increments one coefficient in the dense row. -/
def histogram (width : UInt64) (words : Array UInt64) : Array UInt64 :=
  words.foldl (fun acc k => acc.modify k.toNat (· + 1)) (Array.replicate width.toNat 0)

def row (width symbol sort : UInt64) (t : Tree) : Option (Array UInt64) := do
  let words ← gather symbol sort t #[]
  if words.all (· < width) then some (histogram width words) else none

def buildRows (width symbol sort : UInt64) : List (Tree × Tree) → Option (List (Array UInt64))
  | [] => some []
  | (l,r) :: tail => do
    let lhs ← row width symbol sort l
    let rhs ← row width symbol sort r
    let rest ← buildRows width symbol sort tail
    return lhs :: rhs :: rest

def readMatrix (width symbol sort : UInt64) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) : Option Homogeneous.Matrix := do
  guard (0 < width ∧ width ≤ 32 ∧ roots.size ≤ 128)
  let ds ← declarations decls.toList
  guard (ds.any (fun d => d.kind == 4 && d.id == symbol && d.output == sort))
  let ts ← decodeNodes ds nodes
  let p ← readEquations ts roots.toList
  return (← buildRows width symbol sort p).toArray

def allUsed (width : UInt64) (m : Homogeneous.Matrix) : Bool :=
  (List.finRange width.toNat).all fun i =>
    m.any fun a => a[i.val]?.any (· > 0)

def build (width symbol sort : UInt64) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) : Option Homogeneous.Matrix := do
  let matrix ← readMatrix width symbol sort decls nodes roots
  if allUsed width matrix then some matrix else none

end Tamarin.GraphMatrix
