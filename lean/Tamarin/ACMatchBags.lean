/-! A directional AC matching problem after flattening and factoring out
fixed operands. One nonempty multiset of rigid subject factors is chosen
for each pattern variable, shared at every occurrence in every equation. -/
namespace Tamarin.Matching.ACBags

def Feasible {κ α : Type} (rows : List (List κ × List α)) : Prop :=
  ∃ image : κ → List α, (∀ r ∈ rows, ∀ k ∈ r.1, image k ≠ []) ∧
    ∀ r ∈ rows, (r.1.flatMap image).Perm r.2

end Tamarin.Matching.ACBags
