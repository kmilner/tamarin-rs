import Tamarin.OpenNarrowing
import Tamarin.GroundNarrowing
import Tamarin.PairingRewriting

/-! The live interface decodes a substitution and recomputes the packed values.
A proof of reconstruction must therefore cover every possible normal result
of each instantiated observation. These theorems use local uniqueness at the
query, independently of any unrelated nonconfluence in the active rule table. -/
namespace Tamarin.Rewriting.VariantReconstruction
variable {sig : Signature} {R : Root sig}

private theorem unique_at_normal {t u v : Term sig} (normal : Normal R t)
    (hu : NormalForm R t u) (hv : NormalForm R t v) : EquivB u v :=
  (normal_reduces_equiv hu.1 normal).symm.trans (normal_reduces_equiv hv.1 normal)

/-- The constructor decision applies to unsorted kind-level terms as well.
None of their constructor heads can rewrite after a normalized substitution. -/
theorem constructors (rules : List (Equation sig)) (q : List (Term sig))
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (absent : ∀ t ∈ q, ∀ f ∈ ConstructorVariants.operators t, f ∉ ConstructorVariants.ruleHeads rules)
    {a : Variant sig} (sound : a.Sound (ruleRoot rules) q) :
    a.Reconstructible (ruleRoot rules) q := by
  apply Variant.reconstructible_of_unique sound
  intro t ht _ _
  exact unique_at_normal ((ConstructorVariants.constructor_normal rules apps).2
    t (absent t ht) a.subst sound.1)

/-- Every substitution packet in the pairing backend uses this reference
decoder. Projection rewriting has unique normal forms modulo B on all inputs. -/
theorem pairing (q : List Pairing.PTerm) (σ : Pairing.PSubst) :
    (Pairing.referenceVariant q σ).Reconstructible Pairing.root q := by
  intro values hv
  apply Aligned.map_right hv
  intro t _ u hu
  exact Pairing.normal_unique_modulo (Pairing.rewriting_reducesModulo hu.1)
    (.rewrite (Pairing.normalize_reduces (σ.apply t))) ((Pairing.normal_iff_rewriting _).mpr hu.2.1)
    (Pairing.normalize_normal _)

/-- Every sound choice of arms at a sole projection-pattern rule is
reconstructible, independent of the order, representation, or branch names. -/
theorem openRule (s : OpenNarrowing.Schema sig) (q : List (Option s.Index))
    (atHead : s.AtHead R) {a : Variant sig} (sound : a.Sound R (q.map s.input)) :
    a.Reconstructible R (q.map s.input) := by
  apply Variant.reconstructible_of_unique sound
  intro t ht u v hu hv
  obtain ⟨part, _, rfl⟩ := List.mem_map.mp ht
  cases part with
  | some i => exact unique_at_normal (sound.1 (s.x i)) hu hv
  | none =>
    exact s.unique atHead a.subst sound.1 hu hv

/-- The finite table and fresh pattern renaming used by the open decoder
supply the local root condition. This applies to every sound returned arm. -/
theorem openTable (s : OpenNarrowing.Schema sig) (rules : List (Equation sig))
    (original : s.Index → Term sig) (rhs : Variable) (π : VariablePermutation)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free s.d original, .var rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free s.d →
      r = ⟨.free s.d original, .var rhs⟩)
    (patterns : ∀ i, s.p i = (π.subst sig).apply (original i)) (result : s.z = π.forward rhs)
    (q : List (Option s.Index)) {a : Variant sig} (sound : a.Sound (ruleRoot rules) (q.map s.input)) :
    a.Reconstructible (ruleRoot rules) (q.map s.input) := by
  apply openRule s q _ sound
  intro ys b
  simpa only [patterns, result] using ruleRoot_fresh_selected rules s.d original rhs π apps present only ys b

/-- Ground-rule results are unique at a matching root. A failed match leaves
an irreducible constructor context. Fixed and flexible arguments can share
the fresh variables of the decoded substitution. -/
theorem groundUnique (s : GroundNarrowing.Plan sig) (rules : List (Equation sig))
    (original : Fin (sig.arity s.d) → Term sig) (rename : VariablePermutation)
    (q : List (Option (Term sig))) (dom : s.Domain rules q)
    (present : (⟨.free s.d original, s.rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free s.d → r = ⟨.free s.d original, s.rhs⟩)
    (renamed : ∀ i, s.pat i = (rename.subst sig).apply (original i))
    (ρ : Substitution sig) (hn : Normalized (ruleRoot rules) ρ) {u v}
    (hu : NormalForm (ruleRoot rules) (ρ.apply (s.input none)) u)
    (hv : NormalForm (ruleRoot rules) (ρ.apply (s.input none)) v) : EquivB u v := by
  obtain ⟨vars,ctor⟩ := ConstructorVariants.constructor_normal rules dom.apps

  have atHead : SpecializedRule.AtHead (ruleRoot rules) s.d s.pat s.rhs := by
    simpa only [funext renamed] using SpecializedRule.ground_at_head_fresh rules s.d original s.rhs rename
      dom.apps present only s.ground
  have args := fun i => ctor _ (dom.argConstructors i) ρ hn
  by_cases hit : ∃ μ, SpecializedRule.Matches s.arg s.pat ρ μ
  · obtain ⟨μ, hit⟩ := hit
    have normal : Normal (ruleRoot rules) s.rhs := by
      simpa using ctor _ dom.resultConstructors Substitution.identity vars
    exact (SpecializedRule.uniqueEq atHead hit args normal hu).trans
      (SpecializedRule.uniqueEq atHead hit args normal hv).symm
  · exact unique_at_normal (SpecializedRule.noMatch atHead args hit) hu hv

theorem groundTable (s : GroundNarrowing.Plan sig) (rules : List (Equation sig))
    (original : Fin (sig.arity s.d) → Term sig) (rename : VariablePermutation)
    (q : List (Option (Term sig))) (dom : s.Domain rules q)
    (present : (⟨.free s.d original, s.rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free s.d → r = ⟨.free s.d original, s.rhs⟩)
    (renamed : ∀ i, s.pat i = (rename.subst sig).apply (original i))
    {a : Variant sig} (sound : a.Sound (ruleRoot rules) (q.map s.input)) :
    a.Reconstructible (ruleRoot rules) (q.map s.input) := by
  apply Variant.reconstructible_of_unique sound
  intro t ht u v hu hv
  obtain ⟨part, hp, rfl⟩ := List.mem_map.mp ht
  have ctor := (ConstructorVariants.constructor_normal rules dom.apps).2
  cases part with
  | some t => exact unique_at_normal (ctor _ (dom.observers t hp) _ sound.1) hu hv
  | none => exact groundUnique s rules original rename q dom present only renamed a.subst sound.1 hu hv

end Tamarin.Rewriting.VariantReconstruction
