import TamarinRuntime.ACLowRank
import TamarinRuntime.ACCertificate
import TamarinRuntime.ACSmallSeparator
import TamarinRuntime.ACSingleCorrection
import TamarinRuntime.ACPairCorrection
import TamarinRuntime.ACThreeColumns
import TamarinRuntime.ACColumnQuotient
import TamarinRuntime.ACColumnSupport
import TamarinRuntime.ACReducedFeasibility
import TamarinRuntime.GraphMatrix
import TamarinRuntime.ACRationalProjection

namespace Tamarin.ACFeasibility
open ACBasis Homogeneous

/-- The last intersection needs only the union of the supports that can
participate in a balanced combination. It never constructs the answer packet. -/
def rowFeasible {n} (r : Row n) (gs : List (Vec n)) : Bool :=
  let basis := gs.toArray
  let get := fun j : Fin gs.length => basis[j.val]'(by simp [basis])
  let p := r.pullback get
  let pos := Vector.ofFn p.pos
  let neg := Vector.ofFn p.neg
  let ids := List.finRange gs.length
  let mixed := ids.any (fun j => 0 < pos[j]) && ids.any (fun j => 0 < neg[j])
  let enabled := ids.filter fun j => mixed || (pos[j] == 0 && neg[j] == 0)
  (List.finRange n).all fun i => enabled.any fun j => 0 < get j i

def feasibleRows {n} : List (Row n) → Option Bool
  | [] => some true
  | r :: rs => do
    let gs ← RationalProjection.basis rs <|> boundedBasis rs
    return rowFeasible r gs

/-- The graph encoder already bounds the entire expanded request at 4096 nodes.
Direct positive witnesses need only one coordinate per input variable. -/
def graphWidth : UInt64 := 4096

def initialRows {n} (rs : List (Row n)) : Option Bool :=
  match rs with
  | [p,q] => some (TwoRow.decidePair p q)
  | _ => direct rs <|> LowRank.run rs

def fastRows {n} (rs : List (Row n)) : Option Bool :=
  initialRows rs <|> (if n ≤ 32 then feasibleRows rs else none) <|> reducedFeasible rs

def mainRows {n} (rs : List (Row n)) : Option Bool :=
  fastRows rs <|> ThreeColumns.run rs <|> SingleCorrection.run rs <|> certifiedSearch rs

def remainingRows {n} (rs : List (Row n)) : Option Bool :=
  SmallSeparator.run rs <|> PairCorrection.run rs <|> ColumnSupport.run rs 4096

def baseRows {n} (rs : List (Row n)) : Option Bool :=
  mainRows rs <|> remainingRows rs

def checkRows {n} (rs : List (Row n)) : Option Bool :=
  mainRows rs <|> ColumnQuotient.run (@baseRows) rs <|> remainingRows rs

/-- Tags are deferred, unsatisfiable, and satisfiable respectively. -/
def run (width symbol sort : UInt64) (decls : Array UInt64)
    (nodes : Array (Array UInt64)) (roots : Array UInt64) : UInt8 :=
  let result := do
    let m ← GraphMatrix.buildUpTo graphWidth width symbol sort decls nodes roots
    let rows ← readRows width.toNat m.toList
    checkRows rows
  match result with
  | none => 0
  | some false => 1
  | some true => 2

end Tamarin.ACFeasibility
