import Tamarin.FreshSubstitution
import Tamarin.Rewriting

/-! Fresh-range encodings preserve simultaneous specialization and rewriting
semantics. Each alias uses the same finite permutation and inverse. -/
namespace Tamarin.Rewriting.SpecializedFresh
variable {sig : Signature} {R : Root sig}

theorem decode_apply (vs : List Variable) (sol : Substitution sig) (π : VariablePermutation)
    (t : Term sig) (included : ∀ v, t.Occurs v → v ∈ vs) :
    ((FreshAnswer.encode vs sol).decode π).apply t = (π.subst sig).apply (sol.apply t) := by
  change t.subst _ = (t.subst sol.image).subst _
  rw [Term.subst_comp]
  apply Term.subst_eq_of_agree
  intro v hv
  exact (FreshAnswer.decode_encode_image vs sol π v).trans (ite_eq_left (included v hv))

theorem inverse_comp_normal (π : VariablePermutation) {δ : Substitution sig} (hn : Normalized R δ) :
    Normalized R (δ.compose (π.inverse.subst sig)) := fun v => hn (π.backward v)

theorem inverse_comp_apply (δ : Substitution sig) (π : VariablePermutation) (t : Term sig) :
    (δ.compose (π.inverse.subst sig)).apply ((π.subst sig).apply t) = δ.apply t := by
  rw [Substitution.apply_compose, π.inverse_apply]

theorem safe_idempotent (vs : List Variable) (sol : Substitution sig) (π : VariablePermutation)
    (q : List (Term sig)) (avoid : List Variable) (inventory : ∀ v, v ∈ vs ↔ Observed q v)
    (fresh : ∀ v ∈ vs, ∀ w, (sol.image v).Occurs w → π.forward w ∉ vs ++ avoid)
    (values : List (Term sig))
    (freshValues : ∀ t ∈ values, ∀ w, t.Occurs w → Observed q w ∨ w ∉ avoid) :
    let σ := (FreshAnswer.encode vs sol).decode π
    (Variant.mk σ values).Safe q avoid ∧ ∀ v, σ.apply (σ.image v) = σ.image v := by
  let σ := (FreshAnswer.encode vs sol).decode π
  have inside (v) (hv : v ∈ vs) : σ.image v = (π.subst sig).apply (sol.image v) :=
    (FreshAnswer.decode_encode_image vs sol π v).trans (ite_eq_left hv)
  have outside (v) (hv : v ∉ vs) : σ.image v = .var v :=
    (FreshAnswer.decode_encode_image vs sol π v).trans (ite_eq_right hv)
  have disjoint (v) (hv : v ∈ vs) (w) (hw : (σ.image v).Occurs w) : w ∉ vs ++ avoid := by
    rw [inside v hv] at hw
    obtain ⟨a, ha, rfl⟩ := (Term.occurs_rename (sol.image v) π.forward w).mp hw
    exact fresh v hv a ha
  constructor
  · exact ⟨fun v hv => outside v (fun hm => hv ((inventory v).mp hm)),
      fun v hv w hw => Or.inr (fun hm =>
        disjoint v ((inventory v).mpr hv) w hw (List.mem_append_right _ hm)), freshValues⟩
  · intro v
    by_cases hv : v ∈ vs
    · exact (Term.subst_eq_of_agree σ.image Term.var (σ.image v)
        (fun w hw => outside w (fun hm => disjoint v hv w hw (List.mem_append_left _ hm)))).trans
        (σ.image v).subst_id
    · change σ.apply (σ.image v) = σ.image v
      rw [outside v hv]; exact outside v hv

theorem step_subst (rules : List (Equation sig)) (σ : Substitution sig) {a b : Term sig}
    (h : Step (ruleRoot rules) a b) : Step (ruleRoot rules) (σ.apply a) (σ.apply b) := by
  induction h with
  | root hr =>
    obtain ⟨r, hm, ρ, rfl, rfl⟩ := hr
    exact .root ⟨r, hm, σ.compose ρ, (Substitution.apply_compose ..).symm,
      (Substitution.apply_compose ..).symm⟩
  | free f args i h ih =>
    have step := Step.free f (fun j => σ.apply (args j)) i ih
    simpa only [Substitution.apply, Term.subst, apply_ite] using step
  | comm_left f c _ ih => exact .comm_left f _ ih
  | comm_right f c _ ih => exact .comm_right f _ ih
  | ac_left f c _ ih => exact .ac_left f _ ih
  | ac_right f c _ ih => exact .ac_right f _ ih

theorem stepModulo_subst (rules : List (Equation sig)) (σ : Substitution sig) {a b : Term sig}
    (h : StepModulo (ruleRoot rules) a b) : StepModulo (ruleRoot rules) (σ.apply a) (σ.apply b) := by
  obtain ⟨_, _, he, hs, ht⟩ := h
  exact ⟨_, _, he.subst σ.image, step_subst rules σ hs, ht.subst σ.image⟩

theorem normal_rename (rules : List (Equation sig)) (π : VariablePermutation) (t : Term sig) :
    Normal (ruleRoot rules) ((π.subst sig).apply t) ↔ Normal (ruleRoot rules) t := by
  constructor
  · intro h u hu; exact h _ (stepModulo_subst _ _ hu)
  · intro h u hu
    have hh := stepModulo_subst rules (π.inverse.subst sig) hu
    rw [π.inverse_apply] at hh
    exact h _ hh

theorem reduces_subst (rules : List (Equation sig)) (σ : Substitution sig) {a b : Term sig}
    (h : Reduces (ruleRoot rules) a b) : Reduces (ruleRoot rules) (σ.apply a) (σ.apply b) := by
  induction h with
  | basis he => exact .basis (he.subst σ.image)
  | step hs => exact .step (stepModulo_subst rules σ hs)
  | trans _ _ ih ik => exact .trans ih ik
  | free f a b _ ih => exact .free f _ _ ih
  | comm f _ _ ih ik => exact .comm f ih ik
  | ac f _ _ ih ik => exact .ac f ih ik

theorem normalForm_rename (rules : List (Equation sig)) (π : VariablePermutation) {a b : Term sig}
    (h : NormalForm (ruleRoot rules) a b) :
    NormalForm (ruleRoot rules) ((π.subst sig).apply a) ((π.subst sig).apply b) := by
  refine ⟨reduces_subst _ _ h.1, (normal_rename _ _ _).mpr h.2.1, ?_⟩
  intro s hs
  have ha := hs.subst (π.inverse.subst sig).image (π.inverse.subst sig).sorted
  change HasSort ((π.inverse.subst sig).apply ((π.subst sig).apply a)) s at ha
  rw [π.inverse_apply] at ha
  exact (h.2.2 s ha).subst (π.subst sig).image (π.subst sig).sorted

def renameArm (vs : List Variable) (π : VariablePermutation) (a : Variant sig) : Variant sig :=
  ⟨(FreshAnswer.encode vs a.subst).decode π, a.values.map (π.subst sig).apply⟩

/-- Opening all range occurrences with one sort-preserving permutation per
arm preserves reconstruction from the substitution alone. The opened values
may be computed using any complete ordinary normalization of the query. -/
theorem reconstructible_rename (rules : List (Equation sig)) (vs : List Variable) (π : VariablePermutation)
    (q : List (Term sig)) (a : Variant sig) (included : ∀ v, Observed q v → v ∈ vs)
    (rebuild : a.Reconstructible (ruleRoot rules) q) :
    (renameArm vs π a).Reconstructible (ruleRoot rules) q := by
  intro values nfs
  let undo := (π.inverse.subst sig).apply
  have unmap (ts us : List (Term sig)) (inc : ∀ t ∈ ts, ∀ v, t.Occurs v → v ∈ vs)
      (given : Aligned (fun t u => NormalForm (ruleRoot rules) ((renameArm vs π a).subst.apply t) u) ts us) :
      Aligned (fun t u => NormalForm (ruleRoot rules) (a.subst.apply t) u) ts (us.map undo) := by
    induction ts generalizing us with
    | nil => cases us <;> exact given
    | cons t ts ih =>
      cases us with
      | nil => exact given
      | cons u us =>
        refine ⟨?_,ih us (fun z hz => inc z (List.mem_cons_of_mem _ hz)) given.2⟩
        have form := normalForm_rename _ π.inverse given.1
        change NormalForm _ (undo (((FreshAnswer.encode vs a.subst).decode π).apply t)) (undo u) at form
        simpa only [decode_apply vs a.subst π t (inc t (by simp)),undo,π.inverse_apply] using form
  have raw := rebuild _ (unmap q values (fun t ht v hv => included v ⟨t,ht,hv⟩) nfs)
  have ret (us ws : List (Term sig)) (h : Aligned EquivB (us.map undo) ws) :
      Aligned EquivB us (ws.map (π.subst sig).apply) := by
    induction us generalizing ws with
    | nil => cases ws <;> exact h
    | cons u us ih =>
      cases ws with
      | nil => exact h
      | cons w ws =>
        have eq := h.1.subst (π.subst sig).image
        change EquivB ((π.inverse.inverse.subst sig).apply ((π.inverse.subst sig).apply u)) _ at eq
        exact ⟨π.inverse.inverse_apply u ▸ eq,ih ws h.2⟩
  exact ret values a.values raw

private theorem sound_rename (rules : List (Equation sig)) (vs : List Variable) (π : VariablePermutation)
    (vars : Normalized (ruleRoot rules) Substitution.identity) {q : List (Term sig)} {a : Variant sig}
    (included : ∀ t ∈ q, ∀ v, t.Occurs v → v ∈ vs) (h : a.Sound (ruleRoot rules) q) :
    (renameArm vs π a).Sound (ruleRoot rules) q := by
  constructor
  · intro v
    change Normal _ (((FreshAnswer.encode vs a.subst).decode π).image v)
    rw [FreshAnswer.decode_encode_image]
    split
    · exact (normal_rename _ _ _).mpr (h.1 v)
    · exact vars v
  · obtain ⟨σ, values⟩ := a
    have hv := h.2
    change Aligned (fun t u => NormalForm _ (((FreshAnswer.encode vs σ).decode π).apply t) u)
      q (values.map (π.subst sig).apply)
    clear h
    induction q generalizing values with
    | nil => cases values <;> exact hv
    | cons t ts ih =>
      cases values with
      | nil => exact hv
      | cons u us =>
        constructor
        · change NormalForm _ (((FreshAnswer.encode vs σ).decode π).apply t) ((π.subst sig).apply u)
          rw [decode_apply vs σ π t (included t (by simp))]
          exact normalForm_rename _ _ hv.1
        · exact ih (fun y hy => included y (List.mem_cons_of_mem _ hy)) us hv.2

private theorem covers_rename (vs : List Variable) (π : VariablePermutation)
    {q : List (Term sig)} {ρ : Substitution sig} {values : List (Term sig)} {a : Variant sig}
    (inventory : ∀ v, Observed q v → v ∈ vs) (h : a.Covers R q ρ values) :
    (renameArm vs π a).Covers R q ρ values := by
  obtain ⟨δ, hn, hv, hval⟩ := h
  refine ⟨δ.compose (π.inverse.subst sig), inverse_comp_normal π hn, ?_, ?_⟩
  · intro v ho
    change EquivB _ ((δ.compose (π.inverse.subst sig)).apply (((FreshAnswer.encode vs a.subst).decode π).image v))
    rw [FreshAnswer.decode_encode_image, ite_eq_left (inventory v ho), inverse_comp_apply]
    exact hv v ho
  · obtain ⟨σ, us⟩ := a
    change Aligned _ values (us.map (π.subst sig).apply)
    clear hv
    induction values generalizing us with
    | nil => cases us <;> exact hval
    | cons t ts ih =>
      cases us with
      | nil => exact hval
      | cons u us =>
        constructor
        · change EquivB t ((δ.compose (π.inverse.subst sig)).apply ((π.subst sig).apply u))
          rw [inverse_comp_apply]; exact hval.1
        · exact ih us hval.2

/-- Rename each whole answer independently, preserving its semantic soundness,
completeness on the packed query and the shared instantiation of its values.
Permutations can be chosen per answer after the candidate has finished. -/
theorem complete_rename (rules : List (Equation sig)) (vs : List Variable) (q : List (Term sig))
    (arms : List (Variant sig)) (π : Variant sig → VariablePermutation)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (inventory : ∀ v, Observed q v → v ∈ vs) (complete : CompleteVariants (ruleRoot rules) q arms) :
    CompleteVariants (ruleRoot rules) q (arms.map fun a => renameArm vs (π a) a) := by
  constructor
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact sound_rename rules vs (π a) vars (fun t ht v hv => inventory v ⟨t, ht, hv⟩) (complete.1 a ha)
  · intro ρ hn values hv
    obtain ⟨a, ha, hc⟩ := complete.2 ρ hn values hv
    exact ⟨_, List.mem_map_of_mem ha, covers_rename vs (π a) inventory hc⟩

/-- Keep the earlier variants exactly as emitted and freshen one branch.
An identity arm can remain an empty substitution under this transfer. -/
theorem complete_rename_last (rules : List (Equation sig)) (vs : List Variable) (q : List (Term sig))
    (earlier : List (Variant sig)) (a : Variant sig) (π : VariablePermutation)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (inventory : ∀ v, Observed q v → v ∈ vs) (complete : CompleteVariants (ruleRoot rules) q (earlier ++ [a])) :
    CompleteVariants (ruleRoot rules) q (earlier ++ [renameArm vs π a]) := by
  constructor
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact complete.1 b (List.mem_append_left _ hb)
    · obtain rfl := List.mem_singleton.mp hb
      exact sound_rename rules vs π vars (fun t ht v hv => inventory v ⟨t, ht, hv⟩)
        (complete.1 a (by simp))
  · intro ρ hn values hv
    obtain ⟨b, hb, hc⟩ := complete.2 ρ hn values hv
    rcases List.mem_append.mp hb with hb | hb
    · exact ⟨b, List.mem_append_left _ hb, hc⟩
    · obtain rfl := List.mem_singleton.mp hb
      exact ⟨_, by simp, covers_rename vs π inventory hc⟩

/-- Completeness is extensional in the answer set, so a candidate remains free
to change enumeration order or coalesce duplicate answers. -/
theorem complete_iff_mem {a b : List (Variant sig)} (q : List (Term sig))
    (same : ∀ x, x ∈ a ↔ x ∈ b) : CompleteVariants R q a ↔ CompleteVariants R q b := by
  simp only [CompleteVariants, same]

end Tamarin.Rewriting.SpecializedFresh
