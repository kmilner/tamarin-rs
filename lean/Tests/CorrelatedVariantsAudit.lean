import TamarinCI

/-! Regression for the two value tuples printed by Maude for the YubiKey
query. The sole equation in this test is project(l + r) = l with pure AC +.
Both occurrences may select the same factor. Keeping the printed tuples
intact still misses that legal joint result under CompleteVariants. -/
namespace Tamarin.Rewriting.CorrelatedVariantsAudit
open Tamarin.Pairing (signature PTerm)

private def x : Variable := ⟨0, .msg⟩
private def l : Variable := ⟨1, .msg⟩
private def r : Variable := ⟨2, .msg⟩
private def project (t : PTerm) : PTerm := .free (.other 0 1) (fun _ => t)
private def joined : PTerm := .ac 0 (.var l) (.var r)
private def rule : Equation signature := ⟨project joined, .var l⟩
private abbrev R := ruleRoot [rule]
private def query := [Term.var x, project (.var x), project (.var x)]
private def split : Substitution signature :=
  .binding x joined (HasSort.ac (sig := signature) 0 _ _ (HasSort.var l) (HasSort.var r))

private theorem vars_normal : Normalized R Substitution.identity :=
  (ConstructorVariants.constructor_normal [rule] (by simp [rule, project, ConstructorVariants.Application])).1

private theorem joined_normal : Normal R joined := by
  refine ConstructorVariants.constructor_node_normal [rule] ?_ joined ?_ ?_
  · simp [rule, project, ConstructorVariants.Application]
  · intro h
    have e := List.mem_singleton.mp h
    cases e
  · exact ⟨vars_normal l, vars_normal r⟩

private theorem split_normal : Normalized R split := by
  intro v
  by_cases h : v = x
  · subst v
    have image : split.image x = joined := Substitution.binding_image_self ..
    rw [image]
    exact joined_normal
  · have other : split.image v = .var v := Substitution.binding_image_other _ _ _ _ h
    rw [other]
    exact vars_normal v

private theorem left_normal_form : NormalForm R (project joined) (.var l) := by
  have fires : R (project joined) (.var l) :=
    ⟨rule, by simp, Substitution.identity, (Substitution.apply_identity _).symm,
      (Substitution.apply_identity _).symm⟩
  exact ⟨.step ⟨_, _, .refl _, .root fires, .refl _⟩, vars_normal l,
    fun _ hs => .widen (HasSort.var l) (Term.rootSort_le hs)⟩

theorem printed_variants_incomplete :
    ¬ CompleteVariants R query
      [⟨Substitution.identity, query⟩, ⟨split, [joined, .var l, .var r]⟩] := by
  intro complete
  have image : split.image x = joined := Substitution.binding_image_self ..
  have anchor : NormalForm R (split.apply (.var x)) joined := by
    change NormalForm R (split.image x) joined
    rw [image]
    exact ⟨.basis (.refl _), joined_normal, fun _ hs => hs⟩
  have same : NormalForm R (split.apply (project (.var x))) (.var l) := by
    change NormalForm R (project (split.image x)) _
    rw [image]
    exact left_normal_form
  obtain ⟨answer, mem, δ, _, _, values⟩ :=
    complete.2 split split_normal [joined, .var l, .var l] ⟨anchor, same, same, trivial⟩
  rcases List.mem_cons.mp mem with h | h
  · subst answer
    exact nomatch values.2.1.head_eq
  · obtain rfl := List.mem_singleton.mp h
    have dup := values.1.trans (EquivB.ac_congr (sig := signature) 0 values.2.1.symm values.2.2.1.symm)
    have weights := dup.eval_eq (weightModel signature) (fun v => if v = r then 1 else 0)
    change (0 + 1 : Nat) = 0 + 0 at weights
    omega

-- The same concrete equation does admit complete value-carrying answers
-- when the query observes the conclusion once, together with the argument.
private abbrev observed : OpenNarrowing.Schema signature (fun _ => True) where
  d := .other 0 1
  p := fun _ => joined
  z := l
  x := fun _ => x
  distinct := fun _ _ _ => Subsingleton.elim _ _
  inputSort := fun _ => .refl _
  typed := fun _ => HasSort.ac _ _ _ (.var _) (.var _)
  resultSort := .refl _
  pattern_mem := fun _ => trivial
  rigid := ⟨0, trivial⟩
  outputOccurs := ⟨0, Or.inl rfl⟩

example : let q := observed.observations [0]
    CompleteVariants R (q.map observed.input) [observed.identityArm q, observed.ruleArm q] := by
  apply observed.observed_complete _ vars_normal (fun _ => joined_normal)
  intro ys b
  exact ruleRoot_unique_free_iff [rule] observed.d observed.p (.var l)
    (by simp [rule, project, ConstructorVariants.Application]) (by simp [rule, project])
    (fun r hr _ => List.mem_singleton.mp hr) ys b

end Tamarin.Rewriting.CorrelatedVariantsAudit
