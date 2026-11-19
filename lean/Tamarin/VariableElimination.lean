import Tamarin.Unification

/-!
# Verified variable elimination

Singleton binding is a genuine nonground unifier: its right-hand side may
contain arbitrary free, C, and AC terms and other variables. The operation
requires sort compatibility and an occurs check. Completeness is modulo B,
using the same `CompleteSet` contract as the eventual general solver.
-/
namespace Tamarin

namespace Term
variable {sig : Signature}

/-- Exact substitution extensionality restricted to occurring variables. -/
theorem subst_eq_of_agree (σ τ : Variable → Term sig) (t : Term sig) :
    (∀ v, t.Occurs v → σ v = τ v) → t.subst σ = t.subst τ := by
  induction t with
  | var v => intro h; exact h v rfl
  | atom a => intro _; rfl
  | free f args ih =>
    intro h
    simp only [subst]
    congr
    funext i
    exact ih i (fun v hv => h v ⟨i, hv⟩)
  | comm f a b ha hb =>
    intro h
    simp only [subst]
    rw [ha (fun v hv => h v (Or.inl hv)), hb (fun v hv => h v (Or.inr hv))]
  | ac f a b ha hb =>
    intro h
    simp only [subst]
    rw [ha (fun v hv => h v (Or.inl hv)), hb (fun v hv => h v (Or.inr hv))]

/-- Executable occurrence decision. It needs equality only on variables,
not on arbitrary symbol identities. -/
def occursDecidable (v : Variable) : (t : Term sig) → Decidable (t.Occurs v)
  | .var w => inferInstanceAs (Decidable (v = w))
  | .atom _ => inferInstanceAs (Decidable False)
  | .free _ args =>
    letI : ∀ i, Decidable ((args i).Occurs v) := fun i => occursDecidable v (args i)
    inferInstanceAs (Decidable (∃ i, (args i).Occurs v))
  | .comm _ a b | .ac _ a b =>
    letI := occursDecidable v a
    letI := occursDecidable v b
    inferInstanceAs (Decidable (a.Occurs v ∨ b.Occurs v))

end Term

namespace Substitution
variable {sig : Signature}

/-- Finite, simultaneous binding. `h` is erased from executable code. -/
def binding (v : Variable) (t : Term sig) (h : HasSort t v.sort) : Substitution sig where
  image := fun w => if w = v then t else .var w
  support := [v]
  outside := by
    intro w hw
    have hn : w ≠ v := by simpa using hw
    simp [hn]
  sorted := by
    intro w
    split
    · next he => subst w; exact h
    · exact .var w

@[simp] theorem binding_image_self (v : Variable) (t : Term sig) (h : HasSort t v.sort) :
    (binding v t h).image v = t := by simp [binding]

theorem binding_image_other (v w : Variable) (t : Term sig) (h : HasSort t v.sort)
    (hw : w ≠ v) : (binding v t h).image w = .var w := by simp [binding, hw]

theorem binding_apply_of_not_occurs (v : Variable) (t u : Term sig)
    (h : HasSort t v.sort) (hu : ¬ u.Occurs v) : (binding v t h).apply u = u := by
  calc
    (binding v t h).apply u = u.subst Term.var := by
      apply Term.subst_eq_of_agree
      intro w hw
      have hne : w ≠ v := by
        intro he
        subst w
        exact hu hw
      exact binding_image_other v w t h hne
    _ = u := Term.subst_id u

/-- Any solution of `v = t` factors through the singleton binding. This
agreement holds on every variable, which is useful when eliminating an
equation from a larger conjunction. -/
theorem binding_factor (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (ρ : Substitution sig) (hρ : EquivB (ρ.image v) (ρ.apply t)) :
    ∀ w, EquivB (ρ.image w) ((ρ.compose (binding v t ht)).image w) := by
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [compose, binding_image_self] using hρ
  · change EquivB (ρ.image w) (ρ.apply ((binding v t ht).image w))
    rw [binding_image_other v w t ht hw]
    exact .refl _

end Substitution

namespace VariableElimination
variable {sig : Signature}

/-- The original equation, with the variable on the left. -/
def problem (v : Variable) (t : Term sig) : Problem sig := [⟨.var v, t⟩]

theorem binding_solves (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (ho : ¬ t.Occurs v) : (problem v t).Solves (Substitution.binding v t ht) := by
  intro e he
  have heq : e = ⟨.var v, t⟩ := by simpa [problem] using he
  subst e
  change EquivB ((Substitution.binding v t ht).image v)
    ((Substitution.binding v t ht).apply t)
  rw [Substitution.binding_image_self, Substitution.binding_apply_of_not_occurs v t t ht ho]
  exact .refl _

theorem binding_complete (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (ho : ¬ t.Occurs v) :
    CompleteSet (problem v t) [Substitution.binding v t ht] := by
  constructor
  · intro σ hσ
    have heq : σ = Substitution.binding v t ht := by simpa using hσ
    subst σ
    exact binding_solves v t ht ho
  · intro ρ hρ
    refine ⟨Substitution.binding v t ht, by simp, ρ, ?_⟩
    have he := hρ ⟨.var v, t⟩ (by simp [problem])
    intro w _
    exact Substitution.binding_factor v t ht ρ he w

theorem binding_domain (v : Variable) (t : Term sig) (ht : HasSort t v.sort) :
    DomainRestricted (problem v t) (Substitution.binding v t ht) := by
  intro w hw
  apply Substitution.binding_image_other
  intro he
  subst w
  exact hw ⟨⟨.var v, t⟩, by simp [problem], Or.inl rfl⟩

theorem binding_fresh (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (avoid : List Variable) : FreshFor (problem v t) avoid (Substitution.binding v t ht) := by
  intro w hw u hu hnot _
  apply hnot
  by_cases he : w = v
  · subst w
    rw [Substitution.binding_image_self] at hu
    exact ⟨⟨.var v, t⟩, by simp [problem], Or.inr hu⟩
  · rw [Substitution.binding_image_other v w t ht he] at hu
    have heu : u = w := hu
    subst u
    exact hw

/-- Executable solver for a well-sorted single-variable equation. An occurs
check failure is explicitly unsupported here; it is not asserted to be an
unsatisfiability result (e.g. `v = v` needs the identity case separately). -/
def solve (v : Variable) (t : Term sig) (ht : HasSort t v.sort) : Outcome sig :=
  letI : Decidable (t.Occurs v) := t.occursDecidable v
  if t.Occurs v then .stopped .unsupported []
  else .complete [Substitution.binding v t ht]

theorem solve_correct (v : Variable) (t : Term sig) (ht : HasSort t v.sort) :
    (solve v t ht).Correct (problem v t) := by
  unfold solve
  split
  · intro σ hσ; exact False.elim (List.not_mem_nil hσ)
  · next ho => exact binding_complete v t ht ho

theorem solve_completes (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (ho : ¬ t.Occurs v) :
    solve v t ht = .complete [Substitution.binding v t ht] := by
  simp [solve, ho]

end VariableElimination

namespace Problem
variable {sig : Signature}

/-- Substitute every equation, preserving conjunction order. -/
def substitute (p : Problem sig) (σ : Substitution sig) : Problem sig :=
  p.map fun e => ⟨σ.apply e.lhs, σ.apply e.rhs⟩

theorem solves_substitute_iff (p : Problem sig) (σ ρ : Substitution sig) :
    (p.substitute σ).Solves ρ ↔ p.Solves (ρ.compose σ) := by
  constructor
  · intro h e he
    have hh := h ⟨σ.apply e.lhs, σ.apply e.rhs⟩ (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa only [Substitution.apply_compose] using hh
  · intro h e he
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
    simpa only [Substitution.apply_compose] using h old hold

end Problem

namespace VariableElimination
variable {sig : Signature}

/-- Eliminating `v = t` is sound for the whole remaining conjunction. -/
theorem eliminate_sound (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (ho : ¬ t.Occurs v) (p : Problem sig) (ρ : Substitution sig)
    (hρ : (p.substitute (Substitution.binding v t ht)).Solves ρ) :
    Problem.Solves (⟨.var v, t⟩ :: p) (ρ.compose (Substitution.binding v t ht)) := by
  intro e he
  rcases List.mem_cons.mp he with he | he
  · subst e
    exact (problem v t).solves_compose (binding_solves v t ht ho) ρ
      ⟨.var v, t⟩ (by simp [problem])
  · exact (p.solves_substitute_iff (Substitution.binding v t ht) ρ).mp hρ e he

/-- Every original solution also solves the substituted remainder. Together
with `eliminate_sound`, this is the semantic variable-elimination rule. -/
theorem eliminate_complete (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (p : Problem sig) (ρ : Substitution sig)
    (hρ : Problem.Solves (⟨.var v, t⟩ :: p) ρ) :
    (p.substitute (Substitution.binding v t ht)).Solves ρ := by
  apply (p.solves_substitute_iff (Substitution.binding v t ht) ρ).mpr
  have hfirst := hρ ⟨.var v, t⟩ (by simp)
  have factor := Substitution.binding_factor v t ht ρ hfirst
  intro e he
  have hl := e.lhs.subst_equiv ρ.image (ρ.compose (Substitution.binding v t ht)).image
    (fun w _ => factor w)
  have hr := e.rhs.subst_equiv ρ.image (ρ.compose (Substitution.binding v t ht)).image
    (fun w _ => factor w)
  exact .trans hl.symm (.trans (hρ e (List.mem_cons_of_mem _ he)) hr)

theorem eliminate_satisfiable_iff (v : Variable) (t : Term sig) (ht : HasSort t v.sort)
    (ho : ¬ t.Occurs v) (p : Problem sig) :
    Problem.Satisfiable (⟨.var v, t⟩ :: p) ↔
      (p.substitute (Substitution.binding v t ht)).Satisfiable := by
  constructor
  · intro ⟨ρ, hρ⟩
    exact ⟨ρ, eliminate_complete v t ht p ρ hρ⟩
  · intro ⟨ρ, hρ⟩
    exact ⟨ρ.compose (Substitution.binding v t ht), eliminate_sound v t ht ho p ρ hρ⟩

end VariableElimination
end Tamarin
