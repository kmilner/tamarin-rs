/-! A directional AC matching problem after flattening and factoring out
fixed operands. One nonempty multiset of rigid subject factors is chosen
for each pattern variable, shared at every occurrence in every equation. -/
namespace Tamarin.Matching.ACBags

def Solution {κ α : Type} (rows : List (List κ × List α)) (image : κ → List α) : Prop :=
  (∀ r ∈ rows, ∀ k ∈ r.1, image k ≠ []) ∧
    ∀ r ∈ rows, (r.1.flatMap image).Perm r.2

def Feasible {κ α : Type} (rows : List (List κ × List α)) : Prop := ∃ image, Solution rows image

/-- Only variables occurring in the pattern are observable. The ordering
of equivalent factors inside one image does not distinguish two matchers. -/
structure Complete {κ α : Type} (rows : List (List κ × List α)) (images : List (κ → List α)) : Prop where
  sound : ∀ arm ∈ images, Solution rows arm
  covers : ∀ image, Solution rows image → ∃ arm ∈ images, ∀ r ∈ rows, ∀ k ∈ r.1, (image k).Perm (arm k)

theorem complete_perm {κ α : Type} {rs ss : List (List κ × List α)} {arms : List (κ → List α)}
    (order : rs.Perm ss) (ok : Complete rs arms) : Complete ss arms where
  sound im hm := by simpa only [Solution,← order.mem_iff] using ok.sound im hm
  covers im hs := by
    simpa only [← order.mem_iff] using ok.covers im (by simpa only [Solution,order.mem_iff] using hs)

theorem feasible_perm {κ α : Type} {rs ss : List (List κ × List α)} (order : rs.Perm ss) :
    Feasible rs ↔ Feasible ss := by
  simp only [Feasible,Solution,order.mem_iff]

end Tamarin.Matching.ACBags
