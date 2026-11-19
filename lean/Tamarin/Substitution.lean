import Tamarin.Algebra

namespace Tamarin

/-- A finite-support, sort-respecting simultaneous substitution.
`support` is a finite upper bound, not a required canonical domain.
Identity bindings and unused support entries have no semantic significance.
No acyclicity/idempotence restriction is imposed on *candidate* substitutions:
completeness must cover all finite, sorted substitutions that solve the query.
Terms themselves are finite trees, not rational trees. -/
structure Substitution (sig : Signature) where
  image : Variable → Term sig
  support : List Variable
  outside : ∀ v, v ∉ support → image v = .var v
  sorted : ∀ v, HasSort (image v) v.sort

namespace Substitution
variable {sig : Signature}

def apply (σ : Substitution sig) (t : Term sig) : Term sig := t.subst σ.image

/-- A variable in an instantiated term comes from the image of an input variable. -/
theorem occurs_in_image (σ : Substitution sig) (t : Term sig) (w : Variable)
    (h : (σ.apply t).Occurs w) : ∃ x, t.Occurs x ∧ (σ.image x).Occurs w := by
  induction t with
  | var n => exact ⟨n, rfl, h⟩
  | atom => exact False.elim h
  | free f args ih =>
    obtain ⟨i, hi⟩ := h
    obtain ⟨x, hx, hw⟩ := ih i hi
    exact ⟨x, ⟨i, hx⟩, hw⟩
  | ac _ _ _ ia ib | comm _ _ _ ia ib =>
    rcases h with h | h
    · obtain ⟨x, hx, hw⟩ := ia h
      exact ⟨x, Or.inl hx, hw⟩
    · obtain ⟨x, hx, hw⟩ := ib h
      exact ⟨x, Or.inr hx, hw⟩

def identity : Substitution sig where
  image := Term.var
  support := []
  outside := by intros; rfl
  sorted := HasSort.var

/-- `compose δ σ` means first σ, then δ. -/
def compose (δ σ : Substitution sig) : Substitution sig where
  image := fun v => δ.apply (σ.image v)
  support := σ.support ++ δ.support
  outside := by
    intro v h
    have hσ : v ∉ σ.support := fun hv => h (List.mem_append_left _ hv)
    have hδ : v ∉ δ.support := fun hv => h (List.mem_append_right _ hv)
    simp only [apply, σ.outside v hσ, Term.subst, δ.outside v hδ]
  sorted := fun v => (σ.sorted v).subst δ.image δ.sorted

@[simp] theorem apply_identity (t : Term sig) : identity.apply t = t :=
  Term.subst_id t

theorem apply_compose (δ σ : Substitution sig) (t : Term sig) :
    (compose δ σ).apply t = δ.apply (σ.apply t) :=
  (Term.subst_comp δ.image σ.image t).symm

/-- Equality of answers is semantic and only on observable input variables. -/
def AgreesOn (observed : Variable → Prop) (σ τ : Substitution sig) : Prop :=
  ∀ v, observed v → EquivB (σ.image v) (τ.image v)

/-- `InstanceOn observed specific general`: one *shared*, sorted finite
substitution instantiates the general answer on every observed variable.
Allowing a different instantiation per variable would be unsound. -/
def InstanceOn (observed : Variable → Prop)
    (specific general : Substitution sig) : Prop :=
  ∃ δ : Substitution sig, AgreesOn observed specific (compose δ general)

theorem instanceOn_refl (observed : Variable → Prop) (σ : Substitution sig) :
    InstanceOn observed σ σ := by
  refine ⟨identity, ?_⟩
  intro v _
  change EquivB (σ.image v) (identity.apply (σ.image v))
  rw [apply_identity]
  exact .refl _

theorem instanceOn_trans (observed : Variable → Prop)
    {ρ σ τ : Substitution sig}
    (h : InstanceOn observed ρ σ) (k : InstanceOn observed σ τ) :
    InstanceOn observed ρ τ := by
  obtain ⟨δ, hδ⟩ := h
  obtain ⟨ε, hε⟩ := k
  refine ⟨compose δ ε, ?_⟩
  intro v hv
  have first := hδ v hv
  have second := (hε v hv).subst δ.image
  change EquivB (σ.image v |>.subst δ.image)
    ((ε.apply (τ.image v)).subst δ.image) at second
  change EquivB (ρ.image v) ((compose δ ε).apply (τ.image v))
  rw [apply_compose]
  exact .trans first second

end Substitution
end Tamarin
