import Tamarin.NormalAlgebra
import Tamarin.SubtermVariants

/-! Local obligations for an active associative-commutative operator in a mixed
presentation. Each operator's evidence refers to the same complete rule table. -/
namespace Tamarin.ActiveAC
open Rewriting ConstructorVariants ShortVariantPaths MaudeOperations
variable {s : Signature} {rs : Problem s}

structure Operator (rs : Problem s) (f : s.ACSym) where
  product : NormalAlgebra.Product f (ruleRoot rs)
  unique : ∀ r ∈ rs, head r.lhs = .ac f → NormalAlgebra.UniqueRow rs r
  bounded : ∃ k, ∀ a b, Normal (ruleRoot rs) a → Normal (ruleRoot rs) b →
    ∃ u, Path (ruleRoot rs) k (.ac f a b) u ∧ Normal (ruleRoot rs) u

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Compose arbitrary certified free/C normalization bounds with the
algebras of all active AC heads on the same table. -/
theorem complete_of_bounds (pres : NormalAlgebra.Presentation rs) (scope : ReferenceReduction.Bound rs)
    (active : ∀ f, Head.ac f ∈ ruleHeads rs → Operator rs f)
    (unique : ∀ r ∈ rs, (∀ f, head r.lhs ≠ .ac f) → NormalAlgebra.UniqueRow rs r)
    (free : CanonicalPresentation (ruleRoot rs) → ∀ f : s.FreeSym, ∃ k, ∀ xs,
      (∀ i, Normal (ruleRoot rs) (xs i)) → ∃ u, Path (ruleRoot rs) k (.free f xs) u ∧ Normal (ruleRoot rs) u)
    (comm : CanonicalPresentation (ruleRoot rs) → ∀ f : s.CSym, ∃ k, ∀ a b,
      Normal (ruleRoot rs) a → Normal (ruleRoot rs) b →
      ∃ u, Path (ruleRoot rs) k (.comm f a b) u ∧ Normal (ruleRoot rs) u) :
    CanonicalPresentation (ruleRoot rs) ∧ FiniteVariantProperty (ruleRoot rs) := by
  classical
  have can := pres.canonical (fun f => if h : Head.ac f ∈ ruleHeads rs then (active f h).product
    else NormalAlgebra.inertProduct pres f h) (by
    intro r hr
    by_cases h : ∃ f, head r.lhs = .ac f
    · obtain ⟨f,h⟩ := h
      exact (active f (List.mem_map.mpr ⟨r,hr,h⟩)).unique r hr h
    · exact unique r hr (fun f eq => h ⟨f,eq⟩))
  refine ⟨can,finiteVariantProperty_of_operators scope can ?_⟩
  constructor
  · exact free can
  · exact comm can
  · intro f
    by_cases h : Head.ac f ∈ ruleHeads rs
    · exact (active f h).bounded
    · exact ⟨0,fun a b na nb => ⟨_,.basis (.refl _),
        constructor_node_normal _ pres.apps (.ac f a b) h ⟨na,nb⟩⟩⟩

/-- Every active AC head supplies an algebra and a bound for products of two
normal operands. Free and commutative rules can use the constructor-result criterion. Unused AC symbols remain ordinary constructors. -/
theorem complete (pres : NormalAlgebra.Presentation rs) (scope : ReferenceReduction.Bound rs)
    (active : ∀ f, Head.ac f ∈ ruleHeads rs → Operator rs f)
    (constructor : ∀ r ∈ rs, (∀ f, head r.lhs ≠ .ac f) →
      SubtermVariants.ResultRow rs r ∧ NormalAlgebra.UniqueRow rs r) :
    CanonicalPresentation (ruleRoot rs) ∧ FiniteVariantProperty (ruleRoot rs) := by
  apply complete_of_bounds pres scope active (fun r hr h => (constructor r hr h).2)
  · intro can f
    exact SubtermVariants.free_result_bound scope can pres.apps f fun r hr h =>
      (constructor r hr (by intro g eq; rw [h] at eq; cases eq)).1
  · intro can f
    exact SubtermVariants.comm_result_bound scope can pres.apps f fun r hr h =>
      (constructor r hr (by intro g eq; rw [h] at eq; cases eq)).1

end Tamarin.ActiveAC
