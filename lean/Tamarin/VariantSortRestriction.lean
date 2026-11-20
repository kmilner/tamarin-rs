import Tamarin.UnavailableSort
import Tamarin.MaudeOperations

/-! Rust modules without the optional Nat sort filter returned variant
bindings on the observed keys. A single concrete covering witness survives
that filter together with all its tuple coordinates. -/
namespace Tamarin.VariantSortRestriction
open Rewriting UnavailableSort MaudeOperations
variable {s : Signature} {R : Root s}

def allowed (q : List (Term s)) (a : Variant s) :=
  (q.flatMap Term.variables).all fun v => (a.subst.image v).variables.all (fun w => w.sort != .nat)

theorem covers_iff (q : List (Term s)) (rows : List (Variant s)) (ρ : Substitution s)
    (clean : ∀ v, Observed q v → marked .nat (ρ.image v) = false) (values : List (Term s)) :
    (∃ a ∈ rows, a.Covers R q ρ values) ↔ ∃ a ∈ rows.filter (allowed q), a.Covers R q ρ values := by
  constructor
  · rintro ⟨a,ha,δ,normal,agree,fit⟩
    have observed (v) (hv : v ∈ q.flatMap Term.variables) : Observed q v := by
      obtain ⟨t,ht,live⟩ := List.mem_flatMap.mp hv
      exact ⟨t,ht,(t.mem_variables _).mp live⟩
    exact ⟨a,List.mem_filter.mpr ⟨ha,clean_images _ ρ a.subst δ
      (fun v h => clean v (observed v h)) (fun v h => agree v (observed v h))⟩,
      δ,normal,agree,fit⟩
  · rintro ⟨a,ha,hit⟩
    exact ⟨a,(List.mem_filter.mp ha).1,hit⟩

theorem complete_on_module {q avoid rows} (reply : VariantReply R q avoid rows)
    (ρ : Substitution s) (clean : ∀ v, Observed q v → marked .nat (ρ.image v) = false)
    (normal : Normalized R ρ) (values : List (Term s))
    (forms : Aligned (fun t u => NormalForm R (ρ.apply t) u) q values) :
    ∃ a ∈ rows.filter (allowed q), a.Covers R q ρ values :=
  (covers_iff q rows ρ clean values).mp (reply.complete.2 ρ normal values forms)

end Tamarin.VariantSortRestriction
