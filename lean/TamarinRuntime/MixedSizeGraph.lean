import TamarinWire
import Std.Data.HashMap.Lemmas
import TamarinRuntime.ACFeasibility

namespace Tamarin.MixedSizeGraph
open Whole ACBasis

/-- A variable occurrence is replaced by its whole image. All remaining
binary syntax nodes contribute a fixed number, independent of substitution. -/
structure Profile where
  fixed : Nat
  vars : List UInt64
  deriving Repr, BEq

def Profile.plus (a b : Profile) : Profile := ⟨a.fixed + b.fixed, a.vars ++ b.vars⟩

mutual
  def profile : Tree → Profile
    | .leaf k id _ => if k = 0 then ⟨0,[id]⟩ else ⟨1,[]⟩
    | .app k _ xs =>
      let p := profiles xs
      ⟨p.fixed + (if k = 4 then xs.length - 1 else 1), p.vars⟩
  def profiles : List Tree → Profile
    | [] => ⟨0,[]⟩
    | t :: ts => (profile t).plus (profiles ts)
end

def system (p : List (Tree × Tree)) : List (Profile × Profile) :=
  p.map fun (a,b) => (profile a, profile b)

def keys (s : List (Profile × Profile)) : List UInt64 :=
  (s.flatMap fun (a,b) => a.vars ++ b.vars).eraseDups

def weights (ks : List UInt64) (p : Profile) : Vec (ks.length + 1) :=
  prepend p.fixed (fun i => p.vars.count (ks.get i))

private def histogram : List UInt64 → Std.HashMap UInt64 Nat
  | [] => ∅
  | a :: as =>
    let counts := histogram as
    counts.insert a (counts.getD a 0 + 1)

private theorem histogram_count (xs : List UInt64) (k : UInt64) :
    (histogram xs).getD k 0 = xs.count k := by
  induction xs with
  | nil => simp [histogram]
  | cons a as ih =>
    by_cases same : a = k <;> simp [histogram,Std.HashMap.getD_insert,same,ih]

/-- Materialize the row once so pivot comparisons need only array lookups.
No external variable ID is used as an array allocation size. -/
private def weightVector (ks : List UInt64) (p : Profile) : Vector Nat (ks.length + 1) :=
  let counts := histogram p.vars
  let ws := p.fixed :: ks.map fun k => counts.getD k 0
  ⟨ws.toArray,by simp [ws]⟩

private theorem weight_at (ks : List UInt64) (p : Profile) (i : Fin (ks.length + 1)) :
    (weightVector ks p)[i] = weights ks p i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => simp [weights,weightVector,prepend,histogram_count]

def row (ks : List UInt64) (e : Profile × Profile) : Row (ks.length + 1) :=
  .ofWeights (weights ks e.1) (weights ks e.2)

private def cachedRow (ks : List UInt64) (e : Profile × Profile) : Row (ks.length + 1) :=
  let left := weightVector ks e.1
  let right := weightVector ks e.2
  .ofWeights (fun i => left[i]) (fun i => right[i])

@[csimp] theorem row_eq_cachedRow : @row = @cachedRow := by
  funext ks e
  unfold row cachedRow
  congr 1 <;> funext i <;> exact (weight_at ..).symm

structure Cost where
  size : Nat
  height : Nat
  deriving Repr, BEq

def appCost (cs : List Cost) : Cost :=
  ⟨1 + (cs.map Cost.size).sum, 1 + (cs.foldl (fun h c => max h c.height) 0)⟩

/-- The wire decoder independently validates kinds, signatures and sorts.
Here a parent reads only cached costs of earlier nodes, even for a shared DAG. -/
def nodeCost (prior : Array Cost) (r : Array UInt64) : Option Cost := do
  let k ← r[0]?
  if k ≤ 1 then return ⟨1,1⟩
  return appCost (← (r.toList.drop 2).mapM fun id => prior[id.toNat]?)

def pushCost (prior : Array Cost) (r : Array UInt64) : Option (Array Cost) := do
  let c ← nodeCost prior r
  guard (c.size ≤ 4096 ∧ c.height ≤ 129)
  return prior.push c

def withinGraph (ns : Array (Array UInt64)) (roots : Array UInt64) : Bool :=
  decide (ns.size ≤ 4096 ∧ roots.size ≤ 128 ∧ (ns.toList.map Array.size).sum ≤ 16384) &&
    ((ns.toList.foldlM pushCost #[]).bind fun table => do
      let cs ← roots.toList.mapM fun id => table[id.toNat]?
      return decide ((cs.map Cost.size).sum ≤ 4096)).getD false

def numericWithin (s : List (Profile × Profile)) (ks : List UInt64) : Bool :=
  decide (s.length ≤ 64 ∧ ks.length + 1 ≤ 4096 ∧ s.length * (ks.length + 1) ≤ 8192)

/-- Called with the problem decoded from these exact rows and roots. Check
the graph before visiting any expanded term, including a repeated root. -/
def refutesDecoded (ns : Array (Array UInt64)) (roots : Array UInt64) (p : List (Tree × Tree)) : Bool :=
  withinGraph ns roots &&
    (let s := system p
     let ks := keys s
     numericWithin s ks && ACFeasibility.checkRows (s.map (row ks)) == some false)

def refutes (ds : Array UInt64) (ns : Array (Array UInt64)) (roots : Array UInt64) : Bool :=
  decide (ds.size ≤ 32768 ∧ ns.size ≤ 4096 ∧ roots.size ≤ 128 ∧ (ns.toList.map Array.size).sum ≤ 16384) &&
    ((Wire.decodeProblem ds ns roots).any (refutesDecoded ns roots))

end Tamarin.MixedSizeGraph
