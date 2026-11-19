import Tamarin.VariantJoin

/-! The join driver reserves variables in values that are absent from the
input equations. This gives precisely the additional factorization domain
that sending reflexive equations for the value terms would provide. -/
namespace Tamarin.Rewriting.VariantJoin
variable {sig : Signature} {I A B : Type}

def AmbientOnly (p : Problem sig) (anchors : List (Term sig)) (v : Variable) :=
  Observed anchors v ∧ ¬p.Occurs v

/-- An output-only identity cannot be bound or reused as an auxiliary in
the image of an input variable. Variables shared by inputs and values
remain ordinary unification variables. -/
structure Reserves (p : Problem sig) (anchors : List (Term sig)) (μ : Substitution sig) : Prop where
  fixed : ∀ w, AmbientOnly p anchors w → μ.image w = .var w
  avoids : ∀ v, p.Occurs v → ∀ w, (μ.image v).Occurs w → ¬AmbientOnly p anchors w

/-- The solver's ordinary scope guarantees suffice if its avoid set includes
every output-only identity. It may reserve a larger set. -/
theorem Reserves.of_scoped {p : Problem sig} {anchors : List (Term sig)} {μ : Substitution sig}
    {avoid : List Variable} (domain : DomainRestricted p μ) (fresh : FreshFor p avoid μ)
    (included : ∀ w, AmbientOnly p anchors w → w ∈ avoid) : Reserves p anchors μ where
  fixed w h := domain w h.2
  avoids v hv w hw h := fresh v hv w hw h.2 (included w h)

/-- Free factoring and residual search compose their substitutions before
applying the join. A domain-restricted residual answer preserves the
reservation if the remaining equations omit output-only names and the
residual allocator continues to avoid them. -/
theorem Reserves.after_residual {p pending : Problem sig} {anchors : List (Term sig)}
    {σ τ : Substitution sig} {avoid : List Variable} (early : Reserves p anchors σ)
    (domain : DomainRestricted pending τ) (fresh : FreshFor pending avoid τ)
    (absent : ∀ w, AmbientOnly p anchors w → ¬pending.Occurs w)
    (included : ∀ w, AmbientOnly p anchors w → w ∈ avoid) : Reserves p anchors (τ.compose σ) where
  fixed w hw := by
    change τ.apply (σ.image w) = .var w
    rw [early.fixed w hw]; exact domain w (absent w hw)
  avoids v hv w occurrence hw := by
    obtain ⟨u,hu,occ⟩ := τ.occurs_in_image (σ.image v) w occurrence
    by_cases live : pending.Occurs u
    · exact fresh u live w occ (absent w hw) (included w hw)
    · rw [domain u live] at occ
      obtain rfl : w = u := occ
      exact early.avoids v hv w hu hw

/-- The ordinary solution factorization extends to the entire observable
domain using a single sorted finite substitution. Its action on variables
in input images is inherited from the original factorization. -/
theorem Reserves.factor {p : Problem sig} {anchors : List (Term sig)}
    {ρ μ : Substitution sig} (reserved : Reserves p anchors μ)
    (covered : Substitution.InstanceOn p.Occurs ρ μ) :
    Substitution.InstanceOn (fun v => p.Occurs v ∨ Observed anchors v) ρ μ := by
  classical
  obtain ⟨η,agree⟩ := covered
  let δ := choose (AmbientOnly p anchors) ρ η
  refine ⟨δ,?_⟩
  intro v live
  change EquivB (ρ.image v) (δ.apply (μ.image v))
  by_cases hv : p.Occurs v
  · rw [(choose_apply _ ρ η (μ.image v)).2 (reserved.avoids v hv)]
    exact agree v hv
  · have ambient : AmbientOnly p anchors v := ⟨live.resolve_left hv,hv⟩
    rw [reserved.fixed v ambient]
    change EquivB (ρ.image v) (if AmbientOnly p anchors v then ρ.image v else η.image v)
    rw [ite_eq_left ambient]; exact .refl _

/-- Omitting the reflexive anchors from a unification call preserves its CSU
for the anchored problem under the two reservation conditions above. -/
theorem complete_with_anchors {p : Problem sig} {answers : List (Substitution sig)}
    (csu : CompleteSet p answers) (anchors : List (Term sig))
    (reserved : ∀ μ ∈ answers, Reserves p anchors μ) :
    CompleteSet (p ++ anchors.map fun t => ⟨t,t⟩) answers := by
  constructor
  · intro μ hm eq he
    rcases List.mem_append.mp he with h|h
    · exact csu.sound μ hm eq h
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp h; exact .refl _
  · intro ρ sol
    obtain ⟨μ,hm,covered⟩ := csu.covers ρ (fun e h => sol e (List.mem_append_left _ h))
    obtain ⟨δ,agree⟩ := (reserved μ hm).factor covered
    refine ⟨μ,hm,δ,?_⟩
    rintro v ⟨e,he,occurs⟩
    rcases List.mem_append.mp he with h|h
    · exact agree v (.inl ⟨e,h,occurs⟩)
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      exact agree v (.inr ⟨t,ht,occurs.elim id id⟩)

/-- The anchored CSU premise of the row and family join theorems can be
discharged by a completed call on the input equations alone. -/
theorem join_csu {q : Row sig I A} {r : Row sig I B} {keys : List I}
    {answers : List (Substitution sig)} (inputs : CompleteSet (problem q r keys []) answers)
    (anchors : List (Term sig)) (reserved : ∀ μ ∈ answers, Reserves (problem q r keys []) anchors μ) :
    CompleteSet (problem q r keys anchors) answers := by
  simpa only [problem,List.map_nil,List.append_nil] using complete_with_anchors inputs anchors reserved

end Tamarin.Rewriting.VariantJoin
