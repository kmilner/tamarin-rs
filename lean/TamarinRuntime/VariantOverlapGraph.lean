import TamarinRuntime.MixedSizeGraph
import TamarinRuntime.Whole

namespace Tamarin.VariantOverlapGraph
open Whole

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Bool
abbrev Observations := List (Tree × Tree)
abbrev Index := Std.HashSet (List UInt64 × List UInt64)

def key (a b : Tree) := (a.key,b.key)

/- A shared free head determines its aligned arguments. Keep the original
pair as well, since an output can use the entire observed term. -/
mutual
  def projections (a b : Tree) : Observations :=
    (a,b) :: (match a,b with
      | .app k f xs, .app l g ys =>
        if k = 2 ∧ l = 2 ∧ f = g then projectArgs xs ys else []
      | _, _ => [])
  def projectArgs : List Tree → List Tree → Observations
    | a :: as, b :: bs => projections a b ++ projectArgs as bs
    | _, _ => []
end

def index (inputs : Observations) : Index :=
  .ofList ((inputs.flatMap fun (a,b) => projections a b).map fun (a,b) => key a b)

/- The two variable namespaces are independent. Observed pairs and their
aligned free subterms can be used in common output contexts. -/
mutual
  def checkPair (seen : Index) (a b : Tree) : Bool :=
    seen.contains (key a b) ||
      match a,b with
      | .leaf k i s, .leaf l j t => k == 1 && l == 1 && i == j && s == t
      | .app k f xs, .app l g ys => k == l && f == g && matchesArgs seen xs ys
      | _, _ => false
  def matchesArgs (seen : Index) : List Tree → List Tree → Bool
    | [], [] => true
    | a :: as, b :: bs => checkPair seen a b && matchesArgs seen as bs
    | _, _ => false
end

/-- All pairs preceding the final pair are observed inputs. Bound the shared
graph before decoding its term trees or constructing structural keys. -/
def run : Kernel := fun ds ns es =>
  decide (ds.size ≤ 32768) && MixedSizeGraph.withinGraph ns es &&
  ((Wire.decodeProblem ds ns es).any fun raw =>
    match raw.reverse with
    | [] => false
    | (a,b) :: inputs => checkPair (index inputs.reverse) a b)

end Tamarin.VariantOverlapGraph
