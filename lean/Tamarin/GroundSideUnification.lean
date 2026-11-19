import Tamarin.MatchingConjunction

namespace Tamarin.Matching
variable {sig : Signature}

private theorem occurs_image {v w : Variable} (σ : Substitution sig) (t : Term sig)
    (hv : t.Occurs v) (hw : (σ.image v).Occurs w) : (σ.apply t).Occurs w := by
  induction t with
  | var x => change v = x at hv; subst x; exact hw
  | atom => exact False.elim hv
  | free f args ih =>
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, ih i hi⟩
  | comm _ _ _ ih ik | ac _ _ _ ih ik =>
    exact hv.elim (fun h => Or.inl (ih h)) (fun h => Or.inr (ik h))

/-- Every image of an observed variable is ground when its subject is ground.
This includes arbitrary mathematical matchers, independently of their codec. -/
theorem Matches.groundOn {p : Problem sig} {σ : Substitution sig} (hm : Matches p σ)
    (hg : ∀ e ∈ p, e.rhs.Ground) : σ.GroundOn p.Occurs := by
  intro v ⟨e, he, hv⟩ w hw
  rcases hv with hl | hr
  · exact hg e he w (((hm e he).occurs_iff w).mp (occurs_image σ e.lhs hl hw))
  · exact hg e he v hr

/-- An exact directional matcher is a complete unifier for a conjunction
with ground subjects. Restrict the arbitrary unifier to the pattern domain
before invoking matching coverage. Its other bindings may be arbitrary. -/
theorem Complete.groundSide {p : Problem sig} {answers : List (Substitution sig)}
    (h : Complete p (fun _ => True) answers) (hg : ∀ e ∈ p, e.rhs.Ground) :
    CompleteSet p answers := by
  classical
  constructor
  · intro σ hs; exact (ground_subjects_iff p hg σ).mp (h.sound σ hs).1
  · intro ρ hρ
    let restricted := merge p ρ Substitution.identity
    have ha (v : Variable) (hv : Observed p v) : restricted.image v = ρ.image v := by
      simp [restricted, merge, hv]
    have hr : Matches p restricted := matches_of_agrees ((ground_subjects_iff p hg ρ).mpr hρ)
      (fun v hv => by rw [ha v hv]; exact .refl _)
    have hd : Scoped p (fun _ => True) restricted := by
      intro v hv
      have hv' : ¬ Observed p v := fun hv' => hv ⟨hv', trivial⟩
      simp [restricted, merge, hv', Substitution.identity]
    obtain ⟨σ, hs, hagree⟩ := h.covers _ hr hd
    refine ⟨σ, hs, Substitution.identity, ?_⟩
    intro v hv
    have ho : Observed p v := by
      obtain ⟨e, he, hl | hr⟩ := hv
      · exact ⟨e, he, hl⟩
      · exact False.elim (hg e he v hr)
    simpa only [Substitution.compose, Substitution.apply_identity, ha v ho] using hagree v ho

/-- Equation orientation may be chosen independently for every conjunct. -/
def orient (flip : Equation sig → Bool) (e : Equation sig) : Equation sig :=
  if flip e then ⟨e.rhs, e.lhs⟩ else e

theorem orient_complete_iff (flip : Equation sig → Bool) (p : Problem sig)
    (answers : List (Substitution sig)) :
    CompleteSet (p.map (orient flip)) answers ↔ CompleteSet p answers := by
  have ho : Problem.Occurs (p.map (orient flip)) = p.Occurs := by
    funext v; apply propext
    have same (e : Equation sig) :
        ((orient flip e).lhs.Occurs v ∨ (orient flip e).rhs.Occurs v) ↔
        (e.lhs.Occurs v ∨ e.rhs.Occurs v) := by
      cases hf : flip e <;> simp [orient, hf, or_comm]
    constructor
    · rintro ⟨_, he, hv⟩
      obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp he
      exact ⟨e, hmem, (same e).mp hv⟩
    · rintro ⟨e, he, hv⟩
      exact ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩, (same e).mpr hv⟩
  have hs (σ : Substitution sig) : Problem.Solves (p.map (orient flip)) σ ↔ p.Solves σ := by
    simp only [Problem.Solves, List.forall_mem_map]
    apply forall_congr'; intro e
    cases hf : flip e
    · simp [orient, hf]
    · simp only [orient, hf, ↓reduceIte]
      exact imp_congr_right fun _ => ⟨EquivB.symm, EquivB.symm⟩
  constructor <;> intro h
  · exact ⟨fun σ hm => (hs σ).mp (h.sound σ hm),
      fun ρ hr => ho ▸ h.covers ρ ((hs ρ).mpr hr)⟩
  · exact ⟨fun σ hm => (hs σ).mpr (h.sound σ hm),
      fun ρ hr => ho.symm ▸ h.covers ρ ((hs ρ).mp hr)⟩

end Tamarin.Matching
