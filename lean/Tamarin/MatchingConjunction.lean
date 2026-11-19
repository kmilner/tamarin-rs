import Tamarin.Matching

namespace Tamarin.Matching
variable {sig : Signature}

noncomputable def merge (p : Problem sig) (σ τ : Substitution sig) : Substitution sig := by
  classical
  exact {
  image := fun v => if Observed p v then σ.image v else τ.image v
  support := σ.support ++ τ.support
  outside := by
    intro v hv
    have hs : v ∉ σ.support := fun h => hv (List.mem_append_left _ h)
    have ht : v ∉ τ.support := fun h => hv (List.mem_append_right _ h)
    split <;> simp_all [σ.outside v hs, τ.outside v ht]
  sorted := by
    intro v
    split
    · exact σ.sorted v
    · exact τ.sorted v
  }

def Compatible (p q : Problem sig) (σ τ : Substitution sig) : Prop :=
  ∀ v, Observed p v → Observed q v → EquivB (σ.image v) (τ.image v)

noncomputable def join (p q : Problem sig) (left right : List (Substitution sig)) : List (Substitution sig) := by
  classical
  exact left.flatMap fun σ => right.filterMap fun τ =>
    if Compatible p q σ τ then some (merge p σ τ) else none

theorem observed_append (p q : Problem sig) (v : Variable) :
    Observed (p ++ q) v ↔ Observed p v ∨ Observed q v := by
  simp [Observed, List.mem_append, or_and_right, exists_or]

theorem merge_matches {p q : Problem sig} {σ τ : Substitution sig}
    (hs : Matches p σ) (ht : Matches q τ) (hc : Compatible p q σ τ) :
    Matches (p ++ q) (merge p σ τ) := by
  classical
  have hp : Matches p (merge p σ τ) := matches_of_agrees hs (by
    intro v hv; simp only [merge, hv, ↓reduceIte]; exact .refl _)
  have hq : Matches q (merge p σ τ) := matches_of_agrees ht (by
    intro v hv
    by_cases h : Observed p v
    · simpa only [merge, h, ↓reduceIte] using hc v h hv
    · simp only [merge, h, ↓reduceIte]; exact .refl _)
  intro e he
  exact (List.mem_append.mp he).elim (hp e) (hq e)

theorem merge_scoped {p q : Problem sig} {σ τ : Substitution sig}
    (_hs : Scoped p (fun _ => True) σ) (ht : Scoped q (fun _ => True) τ) :
    Scoped (p ++ q) (fun _ => True) (merge p σ τ) := by
  classical
  intro v hv
  have hp : ¬ Observed p v := fun h => hv ⟨(observed_append p q v).mpr (Or.inl h), trivial⟩
  have hq : ¬ Observed q v := fun h => hv ⟨(observed_append p q v).mpr (Or.inr h), trivial⟩
  simp only [merge, hp, ↓reduceIte]
  exact ht v (fun h => hq h.1)

/-- Join all compatible branches; dropping conflicts is complete because
matching coverage is exact on the shared variables, unlike unifier coverage. -/
theorem join_complete (p q : Problem sig) (left right : List (Substitution sig))
    (hl : Complete p (fun _ => True) left) (hr : Complete q (fun _ => True) right) :
    Complete (p ++ q) (fun _ => True) (join p q left right) := by
  classical
  constructor
  · intro result hm
    obtain ⟨σ, hs, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨τ, ht, hm⟩ := List.mem_filterMap.mp hm
    split at hm
    · rename_i hc
      cases hm
      exact ⟨merge_matches (hl.sound σ hs).1 (hr.sound τ ht).1 hc,
        merge_scoped (hl.sound σ hs).2 (hr.sound τ ht).2⟩
    · cases hm
  · intro ρ hm hscope
    -- Restrict the candidate solution for each subproblem before coverage:
    -- its global domain may contain variables from the other component.
    let restrict := fun (r : Problem sig) => merge r ρ Substitution.identity
    have hscoped (r : Problem sig) : Scoped r (fun _ => True) (restrict r) := by
      intro v hv
      have hh : ¬ Observed r v := fun h => hv ⟨h, trivial⟩
      simp [restrict, merge, hh, Substitution.identity]
    have agrees (r : Problem sig) : Substitution.AgreesOn (Observed r) ρ (restrict r) := by
      intro v hv; simp [restrict, merge, hv]; exact .refl _
    have hpm : Matches p ρ := fun e he => hm e (List.mem_append_left _ he)
    have hqm : Matches q ρ := fun e he => hm e (List.mem_append_right _ he)
    have hpr : Matches p (restrict p) := matches_of_agrees hpm (fun v hv => (agrees p v hv).symm)
    have hqr : Matches q (restrict q) := matches_of_agrees hqm (fun v hv => (agrees q v hv).symm)
    obtain ⟨σ, hs, hσ⟩ := hl.covers _ hpr (hscoped p)
    obtain ⟨τ, ht, hτ⟩ := hr.covers _ hqr (hscoped q)
    have asg : Substitution.AgreesOn (Observed p) ρ σ := fun v hv => (agrees p v hv).trans (hσ v hv)
    have atg : Substitution.AgreesOn (Observed q) ρ τ := fun v hv => (agrees q v hv).trans (hτ v hv)
    have hc : Compatible p q σ τ := fun v hp hq => (asg v hp).symm.trans (atg v hq)
    refine ⟨merge p σ τ, List.mem_flatMap.mpr ⟨σ, hs, List.mem_filterMap.mpr ⟨τ, ht, ?_⟩⟩, ?_⟩
    · simp [hc]
    · intro v hv
      by_cases hp : Observed p v
      · simpa [merge, hp] using asg v hp
      · have hq := (observed_append p q v).mp hv |>.resolve_left hp
        simpa [merge, hp] using atg v hq

end Tamarin.Matching
