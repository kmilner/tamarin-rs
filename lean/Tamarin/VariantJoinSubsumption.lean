import Tamarin.VariantJoinFamily

namespace Tamarin.Rewriting.VariantJoin

variable {sig : Signature} {I A : Type} {rules : List (Equation sig)}

/-- A single sorted substitution must explain all caller images and all
returned values modulo the declared B axioms. This comparison leaves
rewrite redexes intact, including ones created by the substitution. -/
def Row.Subsumes (general specific : Row sig I A) : Prop :=
  ∃ σ : Substitution sig, Fits general specific.input specific.value σ

theorem Fits.compose {general specific : Row sig I A} {x : I → Term sig} {y : A → Term sig}
    {σ δ : Substitution sig} (h : Fits general specific.input specific.value σ)
    (hit : Fits specific x y δ) : Fits general x y (δ.compose σ) := by
  constructor
  · intro i
    rw [Substitution.apply_compose]
    exact (hit.inputs i).trans ((h.inputs i).subst δ.image)
  · intro a
    rw [Substitution.apply_compose]
    exact (hit.values a).trans ((h.values a).subst δ.image)

theorem Row.Subsumes.refl (q : Row sig I A) : q.Subsumes q := by
  refine ⟨.identity,?_,?_⟩ <;> intro i <;> rw [Substitution.apply_identity] <;> exact .refl _

theorem Row.Subsumes.trans {p q r : Row sig I A}
    (hp : p.Subsumes q) (hq : q.Subsumes r) : p.Subsumes r := by
  obtain ⟨σ,h⟩ := hp
  obtain ⟨δ,k⟩ := hq
  exact ⟨δ.compose σ,h.compose k⟩

/-- A normalized instance of a discarded row is an instance of its
covering row. The composed substitution can have reducible images on
unused witnesses; restrict it to the witnesses actually in the row. -/
theorem Row.Subsumes.denotes {general specific : Row sig I A}
    (subsumes : general.Subsumes specific) (vars : Normalized (ruleRoot rules) Substitution.identity)
    {x : I → Term sig} {y : A → Term sig}
    (nx : ∀ i, Normal (ruleRoot rules) (x i)) (ny : ∀ a, Normal (ruleRoot rules) (y a))
    (hit : Denotes (ruleRoot rules) specific x y) : Denotes (ruleRoot rules) general x y := by
  obtain ⟨σ,h⟩ := subsumes
  obtain ⟨δ,_,fit⟩ := hit
  exact (normal_witness vars nx ny (h.compose fit)).2

/-- Pruning a family preserves its exact semantics when every removed row
has a surviving representative which subsumes it. Rows may be reordered,
and the check can conservatively retain rows it cannot compare. -/
theorem Exact.pruned {ids : I → Variable} {query : A → Term sig} {rows kept : List (Row sig I A)}
    (family : Exact (ruleRoot rules) ids query rows)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (subset : ∀ q ∈ kept, q ∈ rows)
    (removed : ∀ q ∈ rows, q ∉ kept → ∃ p ∈ kept, p.Subsumes q) :
    Exact (ruleRoot rules) ids query kept := by
  intro ρ nρ y ny
  rw [family ρ nρ y ny]
  constructor
  · rintro ⟨q,mem,hit⟩
    by_cases survives : q ∈ kept
    · exact ⟨q,survives,hit⟩
    · obtain ⟨p,pm,covers⟩ := removed q mem survives
      exact ⟨p,pm,covers.denotes vars (fun i => nρ (ids i)) ny hit⟩
  · rintro ⟨q,mem,hit⟩
    exact ⟨q,subset q mem,hit⟩

/-- A batch of deletions can use other discarded rows as witnesses if every
edge strictly decreases a natural measure. For variable images a suitable
measure is the number of input slots minus the number of distinct images. -/
theorem Exact.prunedByRank {ids : I → Variable} {query : A → Term sig} {rows kept : List (Row sig I A)}
    (family : Exact (ruleRoot rules) ids query rows)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (subset : ∀ q ∈ kept, q ∈ rows)
    (measure : Row sig I A → Nat)
    (removed : ∀ q ∈ rows, q ∉ kept → ∃ p ∈ rows, measure p < measure q ∧ p.Subsumes q) :
    Exact (ruleRoot rules) ids query kept := by
  have reaches (n : Nat) : ∀ q ∈ rows, measure q = n → ∃ p ∈ kept, p.Subsumes q := by
    induction n using Nat.strongRecOn with
    | ind n smaller =>
      intro q mem size
      by_cases survives : q ∈ kept
      · exact ⟨q,survives,Row.Subsumes.refl q⟩
      · obtain ⟨p,pm,dec,sub⟩ := removed q mem survives
        obtain ⟨r,rm,covers⟩ := smaller (measure p) (by simpa [size] using dec) p pm rfl
        exact ⟨r,rm,covers.trans sub⟩
  exact family.pruned vars subset fun q mem _ => reaches (measure q) q mem rfl

end Tamarin.Rewriting.VariantJoin
