import TamarinRuntime.VariantOverlapGraph
import TamarinRuntime.ACSpanCertificate

namespace Tamarin.ACSpanGraph
open Whole ACBasis
abbrev Observations := VariantOverlapGraph.Observations
abbrev Key := UInt64 × Tree
abbrev Profile := List Key × List Key

/-- All rigid factors are interpreted identically in the two rows. Open
factors retain the namespace of their own substitution. -/
def tag (side : UInt64) (t : Tree) : Key := (if ground t then 2 else side, t)

def profile (f : UInt64) (e : Tree × Tree) : Profile :=
  ((parts f e.1).map (tag 0), (parts f e.2).map (tag 1))

def keys (observations : List Profile) (goal : Profile) : List Key :=
  ((goal :: observations).flatMap fun e => e.1 ++ e.2).eraseDups

def row (ks : List Key) (e : Profile) : Row ks.length :=
  .ofWeights (fun i => e.1.count (ks.get i)) (fun i => e.2.count (ks.get i))

private def cachedRow (ks : List Key) (e : Profile) : Row ks.length :=
  let left := Vector.ofFn fun i => e.1.count (ks.get i)
  let right := Vector.ofFn fun i => e.2.count (ks.get i)
  .ofWeights (fun i => left[i]) (fun i => right[i])

@[csimp] theorem row_eq_cachedRow : @row = @cachedRow := by
  funext ks e
  simp [row,cachedRow]

/-- Trees in this call are already canonical. The coefficient check works
on occurrences of entire factors, including factors that are still open. -/
def linear (f : UInt64) (obs : Observations) (a b : Tree) : Bool :=
  let rs := obs.map (profile f)
  let q := profile f (a,b)
  let ks := keys rs q
  (SpanCertificate.run (rs.map (row ks)) (row ks q)).isSome

def heads (obs : Observations) : List UInt64 :=
  let head : Tree → List UInt64
    | .app 4 f _ => [f]
    | _ => []
  (obs.flatMap fun e => head e.1 ++ head e.2).eraseDups

end Tamarin.ACSpanGraph
