import TamarinRuntime.ACSpanGraph

namespace Tamarin.ACSpanOverlap
open Whole
abbrev Observations := VariantOverlapGraph.Observations

def canonicalPairs (inputs : Observations) : Observations :=
  inputs.map fun (x,y) => (canonical x,canonical y)

/- Agreement on these pairs suffices to reconstruct the enclosing output.
An AC context may be reconstructed positionally after canonicalization. -/
mutual
  def obligations (a b : Tree) : Observations :=
    match a,b with
    | .app k f xs,.app l g ys =>
      if k = l ∧ f = g ∧ xs.length = ys.length then childObligations xs ys else [(a,b)]
    | _,_ => [(a,b)]
  def childObligations : List Tree → List Tree → Observations
    | x::xs,y::ys => obligations x y ++ childObligations xs ys
    | _,_ => []
end

def extra (raw : Observations) (x y : Tree) : Bool :=
  let obs := canonicalPairs raw
  let a := canonical x
  let b := canonical y
  let candidates := ACSpanGraph.heads obs
  decide (candidates.length ≤ 8) &&
    (candidates.any (fun f => ACSpanGraph.linear f obs a b) ||
      (let goals := (obligations a b).eraseDups
       decide (goals.length ≤ 8) &&
         goals.all fun (l,r) => candidates.any fun f => ACSpanGraph.linear f obs l r))

def run := VariantOverlapGraph.runWith extra

end Tamarin.ACSpanOverlap
