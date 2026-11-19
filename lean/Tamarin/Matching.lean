import Tamarin.GroundConjunction

/-! Directional matching modulo B. Equations here are (pattern, subject),
unlike Rust's ordinary `match_eqs` argument order. Subject terms are rigid:
substitution is applied only to the pattern, even when a variable identity
occurs on both sides. Coverage is exact agreement modulo B, not instantiation.
-/
namespace Tamarin.Matching
variable {sig : Signature}

def Observed (p : Problem sig) (v : Variable) : Prop :=
  ∃ e ∈ p, e.lhs.Occurs v

def Matches (p : Problem sig) (σ : Substitution sig) : Prop :=
  ∀ e ∈ p, EquivB (σ.apply e.lhs) e.rhs

/-- The caller chooses bindable variables. All other identities, including
context variables occurring in patterns, must remain untouched. -/
def Scoped (p : Problem sig) (bindable : Variable → Prop) (σ : Substitution sig) : Prop :=
  ∀ v, ¬ (Observed p v ∧ bindable v) → σ.image v = .var v

structure Complete (p : Problem sig) (bindable : Variable → Prop)
    (answers : List (Substitution sig)) : Prop where
  sound : ∀ σ ∈ answers, Matches p σ ∧ Scoped p bindable σ
  covers : ∀ ρ, Matches p ρ → Scoped p bindable ρ →
    ∃ σ ∈ answers, Substitution.AgreesOn (Observed p) ρ σ

/-- A bounded matcher must expose partial enumeration separately. -/
inductive Result (sig : Signature) where
  | complete (answers : List (Substitution sig))
  | stopped (reason : StopReason) (answers : List (Substitution sig))

def Result.Correct (p : Problem sig) (bindable : Variable → Prop) : Result sig → Prop
  | .complete answers => Complete p bindable answers
  | .stopped _ answers => ∀ σ ∈ answers, Matches p σ ∧ Scoped p bindable σ

structure VerifiedMatcher (sig : Signature) where
  run : (p : Problem sig) → p.WellFormed → (bindable : List Variable) →
    List (Substitution sig)
  correct : ∀ p hp bindable, Complete p (fun v => v ∈ bindable) (run p hp bindable)

theorem matches_of_agrees {p : Problem sig} {σ ρ : Substitution sig}
    (hs : Matches p σ) (ha : Substitution.AgreesOn (Observed p) ρ σ) : Matches p ρ := by
  intro e he
  exact (e.lhs.subst_equiv ρ.image σ.image (fun v hv => ha v ⟨e, he, hv⟩)).trans (hs e he)

theorem empty_iff (p : Problem sig) (bindable : Variable → Prop) :
    Complete p bindable [] ↔ ¬ ∃ σ, Matches p σ ∧ Scoped p bindable σ := by
  constructor
  · intro h ⟨σ, hs, hc⟩
    obtain ⟨_, hm, _⟩ := h.covers σ hs hc
    exact List.not_mem_nil hm
  · intro h
    exact ⟨by simp, fun σ hs hc => False.elim (h ⟨σ, hs, hc⟩)⟩

/-- Soundness transfers under exact agreement; this would be false for an
arbitrary instance of a matcher, since the subject is never instantiated. -/
theorem Complete.matches_iff {p : Problem sig} {bindable : Variable → Prop}
    {answers : List (Substitution sig)} (h : Complete p bindable answers)
    (ρ : Substitution sig) (hr : Scoped p bindable ρ) :
    Matches p ρ ↔ ∃ σ ∈ answers, Substitution.AgreesOn (Observed p) ρ σ := by
  constructor
  · exact fun hm => h.covers ρ hm hr
  · rintro ⟨σ, hs, ha⟩
    exact matches_of_agrees (h.sound σ hs).1 ha

/-- Ground subjects make directional matching and ordinary B-unification
coincide semantically. This alone does not transfer the completeness contract. -/
theorem ground_subjects_iff (p : Problem sig)
    (hg : ∀ e ∈ p, e.rhs.Ground) (σ : Substitution sig) :
    Matches p σ ↔ p.Solves σ := by
  constructor <;> intro h e he
  · rw [(hg e he).apply_eq σ]; exact h e he
  · have hs := h e he
    rw [(hg e he).apply_eq σ] at hs
    exact hs

/-- Ground images turn the instantiation preorder of unification into the
exact agreement required of directional matching. -/
theorem of_ground_unification (p : Problem sig) (answers : List (Substitution sig))
    (hg : ∀ e ∈ p, e.rhs.Ground) (hc : CompleteSet p answers)
    (ha : ∀ σ ∈ answers, σ.GroundOn p.Occurs)
    (hd : ∀ σ ∈ answers, DomainRestricted p σ) : Complete p (fun _ => True) answers := by
  constructor
  · intro σ hs
    refine ⟨(ground_subjects_iff p hg σ).mpr (hc.sound σ hs), ?_⟩
    intro v hv
    apply hd σ hs v
    rintro ⟨e, he, hl | hr⟩
    · exact hv ⟨⟨e, he, hl⟩, trivial⟩
    · exact hg e he v hr
  · intro ρ hr _
    obtain ⟨σ, hs, δ, hi⟩ := hc.covers ρ ((ground_subjects_iff p hg ρ).mp hr)
    refine ⟨σ, hs, ?_⟩
    intro v ⟨e, he, hv⟩
    have ho : p.Occurs v := ⟨e, he, Or.inl hv⟩
    have h := hi v ho
    change EquivB (ρ.image v) (δ.apply (σ.image v)) at h
    rw [(ha σ hs v ho).apply_eq δ] at h
    exact h

/-- Every occurrence in an input variable’s image survives substitution
into the enclosing pattern. The basis axioms preserve occurrences. -/
private theorem occurrence_survives (σ : Substitution sig) (t : Term sig) (v w : Variable)
    (input : t.Occurs v) (image : (σ.image v).Occurs w) : (σ.apply t).Occurs w := by
  induction t with
  | var x => cases input; exact image
  | atom => contradiction
  | free f xs ih => obtain ⟨i,hi⟩ := input; exact ⟨i, ih i hi⟩
  | ac f l r il ir | comm f l r il ir => exact input.elim (fun h => .inl (il h)) (fun h => .inr (ir h))

/-- Ground subjects force all observed variable images to be ground in any
ordinary solution, including when the pattern has nested AC, C or free heads. -/
theorem ground_images_of_solves {p : Problem sig} (hg : ∀ e ∈ p, e.rhs.Ground)
    {σ : Substitution sig} (sol : p.Solves σ) : σ.GroundOn p.Occurs := by
  intro v hv w hw
  obtain ⟨e, he, l | r⟩ := hv
  · have matched := (ground_subjects_iff p hg σ).mpr sol e he
    exact hg e he w ((matched.occurs_iff w).mp (occurrence_survives σ e.lhs v w l hw))
  · exact hg e he v r

/-- A complete ordinary solver restricted to the input domain therefore
provides an exact directional matcher on every ground-subject conjunction. -/
theorem of_ground_subjects (p : Problem sig) (answers : List (Substitution sig))
    (hg : ∀ e ∈ p, e.rhs.Ground) (hc : CompleteSet p answers)
    (hd : ∀ σ ∈ answers, DomainRestricted p σ) : Complete p (fun _ => True) answers :=
  of_ground_unification p answers hg hc (fun σ hs => ground_images_of_solves hg (hc.sound σ hs)) hd

end Tamarin.Matching
