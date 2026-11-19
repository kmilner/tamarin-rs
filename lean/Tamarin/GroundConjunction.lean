import Tamarin.VariableElimination

/-!
# Assembling ground answers for conjunctions

Each component must have a complete singleton answer whose images on all
observed variables are ground. A merged substitution must agree with every
component on its observed variables. This permits shared variables only when
their bindings agree modulo B; it does not assume independent equations.
Rust currently constructs this merge and checks identical canonical ground
terms. The representation and merge checks remain integration obligations.
-/
namespace Tamarin

def Term.Ground {sig : Signature} (t : Term sig) : Prop :=
  ∀ v, ¬ t.Occurs v

theorem Term.Ground.apply_eq {sig : Signature} {t : Term sig}
    (h : t.Ground) (σ : Substitution sig) : σ.apply t = t := by
  calc
    σ.apply t = t.subst Term.var :=
      t.subst_eq_of_agree σ.image Term.var (fun v hv => False.elim (h v hv))
    _ = t := t.subst_id

def Substitution.GroundOn {sig : Signature} (observed : Variable → Prop)
    (σ : Substitution sig) : Prop :=
  ∀ v, observed v → (σ.image v).Ground

/-- Ground complete singleton answers determine every observed image modulo
B, including images of arbitrary nonground candidate solutions. -/
theorem CompleteSet.ground_agrees {sig : Signature} {p : Problem sig}
    {σ : Substitution sig} (h : CompleteSet p [σ])
    (hg : σ.GroundOn p.Occurs) {ρ : Substitution sig} (hρ : p.Solves ρ) :
    Substitution.AgreesOn p.Occurs ρ σ := by
  obtain ⟨τ, hτ, δ, hd⟩ := h.covers ρ hρ
  have ht : τ = σ := by simpa using hτ
  subst τ
  intro v hv
  have hi := hd v hv
  change EquivB (ρ.image v) (δ.apply (σ.image v)) at hi
  rw [(hg v hv).apply_eq δ] at hi
  exact hi

/-- Ground observed images contain no auxiliary variables to capture. -/
theorem Substitution.GroundOn.fresh {sig : Signature} {p : Problem sig}
    {σ : Substitution sig} (hg : σ.GroundOn p.Occurs) (avoid : List Variable) :
    FreshFor p avoid σ := by
  intro v hv w hw
  exact False.elim (hg v hv w hw)

namespace GroundConjunction
variable {sig : Signature}

/-- The merge may be optimized freely, provided this agreement is retained.
The conclusion uses the same CompleteSet contract as each component. -/
theorem complete (parts : List (Problem sig × Substitution sig))
    (merged : Substitution sig)
    (hc : ∀ part ∈ parts, CompleteSet part.1 [part.2])
    (hg : ∀ part ∈ parts, part.2.GroundOn part.1.Occurs)
    (hm : ∀ part ∈ parts, Substitution.AgreesOn part.1.Occurs merged part.2) :
    CompleteSet (parts.flatMap Prod.fst) [merged] := by
  constructor
  · intro σ hσ
    have he : σ = merged := by simpa using hσ
    subst σ
    intro e he
    obtain ⟨part, hp, he⟩ := List.mem_flatMap.mp he
    apply (Problem.solves_instance part.1 ((hc part hp).sound part.2 (by simp))) _ e he
    refine ⟨Substitution.identity, ?_⟩
    intro v hv
    simpa only [Substitution.compose, Substitution.apply_identity] using hm part hp v hv
  · intro ρ hρ
    refine ⟨merged, by simp, Substitution.identity, ?_⟩
    intro v hv
    obtain ⟨e, he, hv⟩ := hv
    obtain ⟨part, hp, he⟩ := List.mem_flatMap.mp he
    have ho : Problem.Occurs part.1 v := ⟨e, he, hv⟩
    have hs : Problem.Solves part.1 ρ := fun e he =>
      hρ e (List.mem_flatMap.mpr ⟨part, hp, he⟩)
    have ha := (hc part hp).ground_agrees (hg part hp) hs v ho
    simpa only [Substitution.compose, Substitution.apply_identity] using
      ha.trans (hm part hp v ho).symm

/-- A complete failure of any component closes the conjunction. -/
theorem empty (parts : List (Problem sig)) (p : Problem sig) (hp : p ∈ parts)
    (h : CompleteSet p []) : CompleteSet parts.flatten [] := by
  apply (complete_empty_iff _).mpr
  intro ⟨ρ, hρ⟩
  apply (complete_empty_iff p).mp h
  exact ⟨ρ, fun e he => hρ e (List.mem_flatten.mpr ⟨p, hp, he⟩)⟩

/-- Contextual safety of a successful merge additionally requires its domain
to stay inside the input and its observed images to remain ground. These
conditions hold for the current Rust merge of ground bindings but still need
a representation theorem for that implementation. -/
theorem correctIn (parts : List (Problem sig × Substitution sig))
    (merged : Substitution sig) (avoid : List Variable)
    (hc : ∀ part ∈ parts, CompleteSet part.1 [part.2])
    (hg : ∀ part ∈ parts, part.2.GroundOn part.1.Occurs)
    (hm : ∀ part ∈ parts, Substitution.AgreesOn part.1.Occurs merged part.2)
    (hd : DomainRestricted (parts.flatMap Prod.fst) merged)
    (hground : merged.GroundOn (Problem.Occurs (parts.flatMap Prod.fst))) :
    (Outcome.complete [merged]).CorrectIn (parts.flatMap Prod.fst) avoid := by
  refine ⟨complete parts merged hc hg hm, ?_, ?_⟩
  · intro σ hσ
    have he : σ = merged := by simpa [Outcome.answers] using hσ
    subst σ
    exact hd
  · intro σ hσ
    have he : σ = merged := by simpa [Outcome.answers] using hσ
    subst σ
    exact hground.fresh avoid

end GroundConjunction
end Tamarin
