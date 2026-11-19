import Tamarin.ResidualSearch

/-! Lift residual unifiers through free factoring. The trace records local
equation transformations; it makes no assumption about how a unifier chooses
its bindings or stores its worklist. -/
namespace Tamarin.FactoredUnification
variable {sig : Signature}

/-- Successful free factoring steps. C/AC equations may be delayed and
reordered; free heads decompose positionally. -/
inductive Trace : Problem sig → Substitution sig → Problem sig → Substitution sig → Prop where
  | done (p θ) : Trace p θ p θ
  | bind (v : Variable) (t : Term sig) (ht : HasSort t v.sort) (ho : ¬ t.Occurs v)
      (p : Problem sig) (θ : Substitution sig) :
      Trace (⟨.var v,t⟩ :: p) θ (p.substitute (.binding v t ht)) ((Substitution.binding v t ht).compose θ)
  | positional (f : sig.FreeSym) (xs ys : Fin (sig.arity f) → Term sig) (p : Problem sig) (θ) :
      Trace (⟨.free f xs,.free f ys⟩ :: p) θ (Matching.children f xs ys ++ p) θ
  | swap (a b : Term sig) (p : Problem sig) (θ) : Trace (⟨a,b⟩ :: p) θ (⟨b,a⟩ :: p) θ
  | discard {a b : Term sig} (same : EquivB a b) (p : Problem sig) (θ) : Trace (⟨a,b⟩ :: p) θ p θ
  | perm {p q : Problem sig} (h : p.Perm q) (θ) : Trace p θ q θ
  | trans {p q r : Problem sig} {θ ψ χ : Substitution sig} :
      Trace p θ q ψ → Trace q ψ r χ → Trace p θ r χ

theorem Trace.denotes {p q : Problem sig} {θ ψ : Substitution sig} (tr : Trace p θ q ψ)
    (observed : Variable → Prop) (ρ : Substitution sig) :
    Residual.Denotes observed p θ ρ ↔ Residual.Denotes observed q ψ ρ := by
  induction tr with
  | done => rfl
  | bind v t ht ho p θ => exact Residual.bind observed v t ht ho p θ ρ
  | positional f xs ys p θ => exact Residual.positional observed f xs ys p θ ρ
  | swap a b p θ => exact Residual.swap observed a b p θ ρ
  | discard h p θ => exact Residual.discard observed h p θ ρ
  | perm h θ => exact Residual.perm observed h θ ρ
  | trans _ _ ih ik => exact ih.trans ik

/-- Semantic meaning of a successful factorization. Different factoring
algorithms and validators can establish this interface. -/
structure Factoring (p q : Problem sig) (θ : Substitution sig) : Prop where
  forward : ∀ σ, q.Solves σ → p.Solves (σ.compose θ)
  residual : ∀ ρ, p.Solves ρ → q.Solves ρ
  stable : ∀ ρ, p.Solves ρ → Substitution.AgreesOn p.Occurs ρ (ρ.compose θ)

private theorem Trace.preserves {p q : Problem sig} {θ ψ : Substitution sig}
    (tr : Trace p θ q ψ) (ρ : Substitution sig) (sol : p.Solves ρ) :
    q.Solves ρ ∧ ∀ v, EquivB (ρ.apply (θ.image v)) (ρ.apply (ψ.image v)) := by
  induction tr with
  | done => exact ⟨sol, fun _ => .refl _⟩
  | bind v t ht ho p θ =>
    refine ⟨VariableElimination.eliminate_complete v t ht p ρ sol, fun w => ?_⟩
    have agree := Substitution.binding_factor v t ht ρ (sol _ List.mem_cons_self)
    change EquivB _ (ρ.apply ((Substitution.binding v t ht).apply (θ.image w)))
    rw [← Substitution.apply_compose]
    exact (θ.image w).subst_equiv _ _ (fun u _ => agree u)
  | positional f xs ys p θ =>
    refine ⟨?_, fun _ => .refl _⟩
    simpa [Problem.Solves, Matching.children, Substitution.apply, Term.subst,
      Matching.free_equiv_iff, or_imp, forall_and] using sol
  | swap a b p θ =>
    simp only [Problem.Solves, List.forall_mem_cons] at sol ⊢
    exact ⟨⟨sol.1.symm, sol.2⟩, fun _ => .refl _⟩
  | discard h p θ => exact ⟨fun e he => sol e (List.mem_cons_of_mem _ he), fun _ => .refl _⟩
  | perm h θ => exact ⟨fun e he => sol e (h.mem_iff.mpr he), fun _ => .refl _⟩
  | trans _ _ ih ik =>
    obtain ⟨sq, first⟩ := ih sol
    obtain ⟨sr, second⟩ := ik sq
    exact ⟨sr, fun v => (first v).trans (second v)⟩

theorem Trace.factoring {p q : Problem sig} {θ : Substitution sig}
    (tr : Trace p .identity q θ) : Factoring p q θ where
  forward σ hσ := (Residual.start p.Occurs p (fun _ h => h) _).mp
    ((tr.denotes p.Occurs _).mpr ⟨σ, hσ, fun _ _ => .refl _⟩)
  residual ρ hρ := (tr.preserves ρ hρ).1
  stable ρ hρ v _ := (tr.preserves ρ hρ).2 v

/-- Restore the solution on the variables absent from the residual that the
accumulated bindings still observe. These names must be disjoint from the
residual answer's witnesses. -/
private noncomputable def restore (q : Problem sig) (kept : List Variable)
    (ρ δ : Substitution sig) : Substitution sig := by
  classical
  exact {
    image := fun v => if v ∈ kept ∧ ¬ q.Occurs v then ρ.image v else δ.image v
    support := ρ.support ++ δ.support
    outside := by intro v h; simp only [List.mem_append, not_or] at h
                  simp [ρ.outside v h.1, δ.outside v h.2]
    sorted := by intro v; split <;> first | exact ρ.sorted v | exact δ.sorted v }

/-- The factored images can still mention a variable that disappeared from
all residual equations. Only those names need protection for coverage. -/
def Protected (p q : Problem sig) (θ : Substitution sig) (reserved : List Variable) : Prop :=
  ∀ v, p.Occurs v → ∀ w, (θ.image v).Occurs w → ¬ q.Occurs w → w ∈ reserved

theorem lift_complete {p q : Problem sig} {θ : Substitution sig} {arms : List (Substitution sig)}
    {reserved : List Variable} (fact : Factoring p q θ)
    (residual : (Outcome.complete arms).CorrectIn q reserved)
    (kept : Protected p q θ reserved) :
    CompleteSet p (arms.map fun σ => σ.compose θ) := by
  classical
  have cs : CompleteSet q arms := residual.mathematical
  constructor
  · rintro _ hm
    obtain ⟨σ, hs, rfl⟩ := List.mem_map.mp hm
    exact fact.forward σ (cs.sound σ hs)
  · intro ρ hρ
    obtain ⟨σ, hs, δ, inst⟩ := cs.covers ρ (fact.residual ρ hρ)
    let ε := restore q reserved ρ δ
    refine ⟨σ.compose θ, List.mem_map_of_mem hs, ε, ?_⟩
    intro v hv
    change EquivB (ρ.image v) (ε.apply ((σ.compose θ).image v))
    change EquivB (ρ.image v) (ε.apply (σ.apply (θ.image v)))
    rw [← Substitution.apply_compose]
    apply (fact.stable ρ hρ v hv).trans
    apply Term.subst_equiv
    intro w hw
    by_cases hq : q.Occurs w
    · have keep : ε.apply (σ.image w) = δ.apply (σ.image w) := by
        apply Term.subst_eq_of_agree
        intro z hz
        have miss : ¬ (z ∈ reserved ∧ ¬ q.Occurs z) :=
          fun h => residual.fresh σ hs w hq z hz h.2 h.1
        simp [ε, restore, miss]
      change EquivB _ (ε.apply (σ.image w))
      rw [keep]
      exact inst w hq
    · change EquivB _ (ε.apply (σ.image w))
      rw [residual.domain σ hs w hq]
      change EquivB _ (ε.image w)
      simp [ε, restore, kept v hv w hw hq, hq, EquivB.refl]

/-- Free factoring introduces no new variables. This condition accounts for
the residual, for eliminated bindings, and for the outside-query domain. -/
structure Scope (live : Variable → Prop) (q : Problem sig) (θ : Substitution sig) : Prop where
  pending : ∀ v, q.Occurs v → live v
  outside : ∀ v, ¬ live v → θ.image v = .var v
  images : ∀ v, live v → ∀ w, (θ.image v).Occurs w → live w

theorem Trace.scope {p q : Problem sig} {θ ψ : Substitution sig}
    (tr : Trace p θ q ψ) {live : Variable → Prop} (scope : Scope live p θ) : Scope live q ψ := by
  induction tr with
  | done => exact scope
  | bind v t ht ho p θ =>
    let β := Substitution.binding v t ht
    have first : live v := scope.pending v ⟨_, List.mem_cons_self, Or.inl rfl⟩
    have imgs (u) (hu : live u) (w) (hw : (β.image u).Occurs w) : live w := by
      by_cases h : u = v
      · subst u
        rw [show β.image v = t from Substitution.binding_image_self ..] at hw
        exact scope.pending w ⟨_, List.mem_cons_self, Or.inr hw⟩
      · rw [show β.image u = .var u from Substitution.binding_image_other _ _ _ _ h] at hw
        exact (show w = u from hw) ▸ hu
    constructor
    · rintro w ⟨_, hm, hocc⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases hocc with l | r
      · obtain ⟨u, hu, hw⟩ := β.occurs_in_image _ _ l
        exact imgs u (scope.pending u ⟨_, List.mem_cons_of_mem _ he, Or.inl hu⟩) w hw
      · obtain ⟨u, hu, hw⟩ := β.occurs_in_image _ _ r
        exact imgs u (scope.pending u ⟨_, List.mem_cons_of_mem _ he, Or.inr hu⟩) w hw
    · intro w hw
      change β.apply (θ.image w) = _
      rw [scope.outside w hw]
      exact Substitution.binding_image_other _ _ _ _ (fun h => hw (h ▸ first))
    · intro w hw z hz
      obtain ⟨u, hu, uz⟩ := β.occurs_in_image (θ.image w) z hz
      exact imgs u (scope.images w hw u hu) z uz
  | positional f xs ys p θ =>
    refine ⟨?_, scope.outside, scope.images⟩
    rintro w ⟨e, he, hw⟩
    rcases List.mem_append.mp he with hc | hp
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      apply scope.pending w
      refine ⟨_, List.mem_cons_self, ?_⟩
      exact hw.imp (fun h => ⟨i,h⟩) (fun h => ⟨i,h⟩)
    · exact scope.pending w ⟨e, List.mem_cons_of_mem _ hp, hw⟩
  | swap a b p θ =>
    refine ⟨?_, scope.outside, scope.images⟩
    rintro w ⟨e, he, hw⟩
    rcases List.mem_cons.mp he with rfl | h
    · exact scope.pending w ⟨_, List.mem_cons_self, hw.symm⟩
    · exact scope.pending w ⟨e, List.mem_cons_of_mem _ h, hw⟩
  | discard h p θ =>
    exact ⟨fun w ⟨e,he,hw⟩ => scope.pending w ⟨e,List.mem_cons_of_mem _ he,hw⟩,
      scope.outside, scope.images⟩
  | perm perm θ =>
    exact ⟨fun w ⟨e,he,hw⟩ => scope.pending w ⟨e,perm.mem_iff.mpr he,hw⟩,
      scope.outside, scope.images⟩
  | trans _ _ ih ik => exact ik (ih scope)

theorem Trace.original_scope {p q : Problem sig} {θ : Substitution sig}
    (tr : Trace p .identity q θ) : Scope p.Occurs q θ :=
  tr.scope ⟨fun _ h => h, fun _ _ => rfl, fun _ hv _ hw => (show _ = _ from hw) ▸ hv⟩

/-- Scope-preserving factorization followed by a hygienic residual solution
has a complete, domain-restricted, fresh answer in the original problem.
Only residual witnesses must avoid the caller and the surviving free variables. -/
theorem lift_correctIn {p q : Problem sig} {θ : Substitution sig} {arms : List (Substitution sig)}
    {reserved avoid : List Variable} (fact : Factoring p q θ) (scope : Scope p.Occurs q θ)
    (residual : (Outcome.complete arms).CorrectIn q reserved)
    (kept : Protected p q θ reserved) (caller : ∀ v ∈ avoid, v ∈ reserved) :
    (Outcome.complete (arms.map fun σ => σ.compose θ)).CorrectIn p avoid := by
  refine ⟨lift_complete fact residual kept, ?_, ?_⟩
  · intro ans ha v hv
    obtain ⟨σ, hs, rfl⟩ := List.mem_map.mp ha
    change σ.apply (θ.image v) = _
    rw [scope.outside v hv]
    exact residual.domain σ hs v (fun h => hv (scope.pending v h))
  · intro ans ha v hv w hw new avoidW
    obtain ⟨σ, hs, rfl⟩ := List.mem_map.mp ha
    obtain ⟨u, hu, uw⟩ := σ.occurs_in_image (θ.image v) w hw
    by_cases live : q.Occurs u
    · exact residual.fresh σ hs u live w uw (fun h => new (scope.pending w h)) (caller w avoidW)
    · rw [residual.domain σ hs u live] at uw
      exact new ((show w = u from uw) ▸ scope.images v hv u hu)

/-- Source-level end-to-end result for a checked trace. Reserving the
original variables covers every free variable retained by factoring, including
variables with no occurrence in the matrix. -/
theorem Trace.correctIn {p q : Problem sig} {θ : Substitution sig} {arms : List (Substitution sig)}
    {inputVars avoid : List Variable} (tr : Trace p .identity q θ)
    (inputs : ∀ v, p.Occurs v → v ∈ inputVars)
    (residual : (Outcome.complete arms).CorrectIn q (inputVars ++ avoid)) :
    (Outcome.complete (arms.map fun σ => σ.compose θ)).CorrectIn p avoid :=
  lift_correctIn tr.factoring tr.original_scope residual
    (fun v hv w hw _ => List.mem_append_left _ (inputs w (tr.original_scope.images v hv w hw)))
    (fun _ => List.mem_append_right _)

end Tamarin.FactoredUnification
