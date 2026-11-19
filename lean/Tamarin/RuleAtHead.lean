import Tamarin.ConstructorVariants
import Tamarin.VariablePermutation

/-! Selecting an application-headed rule from a finite table and freshening
its locally bound variables. Both sides of the rule use one substitution. -/
namespace Tamarin.Rewriting
variable {sig : Signature}

/-- All and only instances of rules in the same head bucket can rewrite a free
application. This characterization permits overlapping rules, any right-hand
side, and any traversal order of the rule table. -/
theorem ruleRoot_free_iff (rules : List (Equation sig)) (d : sig.FreeSym)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (ys : Fin (sig.arity d) → Term sig) (b : Term sig) :
    ruleRoot rules (.free d ys) b ↔
      ∃ p rhs, (⟨.free d p, rhs⟩ : Equation sig) ∈ rules ∧
        ∃ σ : Substitution sig, (∀ i, ys i = σ.apply (p i)) ∧ b = σ.apply rhs := by
  constructor
  · rintro ⟨⟨lhs, rhs⟩, hm, σ, hl, hb⟩
    have ha := apps _ hm
    cases lhs with
    | free g p =>
      have he : d = g := Head.free.inj (congrArg ConstructorVariants.head hl)
      subst g
      change Term.free d ys = Term.free d (fun i => σ.apply (p i)) at hl
      cases hl
      exact ⟨p, rhs, hm, σ, fun _ => rfl, hb⟩
    | var | atom => exact False.elim ha
    | comm | ac => cases hl
  · rintro ⟨_, _, hm, σ, hy, hb⟩
    exact ⟨_, hm, σ, congrArg (Term.free d) (funext hy), hb⟩

/-- Specialize the full table to a free head with a unique rule. Other table
entries may use any declared symbols and have arbitrary right-hand sides. -/
theorem ruleRoot_unique_free_iff (rules : List (Equation sig)) (d : sig.FreeSym)
    (p : Fin (sig.arity d) → Term sig) (rhs : Term sig)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free d →
      r = ⟨.free d p, rhs⟩)
    (ys : Fin (sig.arity d) → Term sig) (b : Term sig) :
    ruleRoot rules (.free d ys) b ↔
      ∃ σ : Substitution sig, (∀ i, ys i = σ.apply (p i)) ∧ b = σ.apply rhs := by
  rw [ruleRoot_free_iff rules d apps]
  constructor
  · rintro ⟨p', rhs', hm, witnesses⟩
    cases only _ hm rfl
    exact witnesses
  · exact fun witnesses => ⟨p, rhs, present, witnesses⟩

/-- A finite sort-preserving permutation preserves the instantiated rule
relation. Its executable inverse transfers any match back to the original
table, including matches in which different rule variables share images. -/
theorem ruleRoot_fresh_free (rules : List (Equation sig)) (d : sig.FreeSym)
    (p : Fin (sig.arity d) → Term sig) (rhs : Term sig) (π : VariablePermutation)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free d →
      r = ⟨.free d p, rhs⟩)
    (ys : Fin (sig.arity d) → Term sig) (b : Term sig) :
    ruleRoot rules (.free d ys) b ↔ ∃ σ : Substitution sig,
      (∀ i, ys i = σ.apply ((π.subst sig).apply (p i))) ∧
      b = σ.apply ((π.subst sig).apply rhs) := by
  rw [ruleRoot_unique_free_iff rules d p rhs apps present only]
  constructor
  · rintro ⟨σ, hy, hb⟩
    refine ⟨σ.compose (π.inverse.subst sig), ?_, ?_⟩
    · intro i; simpa only [Substitution.apply_compose, π.inverse_apply] using hy i
    · simpa only [Substitution.apply_compose, π.inverse_apply] using hb
  · rintro ⟨σ, hy, hb⟩
    refine ⟨σ.compose (π.subst sig), ?_, ?_⟩
    · intro i; simpa only [Substitution.apply_compose] using hy i
    · simpa only [Substitution.apply_compose] using hb

theorem ruleRoot_fresh_selected (rules : List (Equation sig)) (d : sig.FreeSym)
    (p : Fin (sig.arity d) → Term sig) (z : Variable) (π : VariablePermutation)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free d p, .var z⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free d →
      r = ⟨.free d p, .var z⟩)
    (ys : Fin (sig.arity d) → Term sig) (b : Term sig) :
    ruleRoot rules (.free d ys) b ↔ ∃ σ : Substitution sig,
      (∀ i, ys i = σ.apply ((π.subst sig).apply (p i))) ∧ b = σ.image (π.forward z) :=
  ruleRoot_fresh_free rules d p (.var z) π apps present only ys b

end Tamarin.Rewriting
