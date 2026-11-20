import Tamarin.MatchingSignatureExtension
import Tamarin.NarrowingFrontier
import Tamarin.ReferenceReduction

/-! Extending the signature cannot add a new outcome of concrete reduction:
range restriction prevents a rewrite from introducing any foreign symbol. -/
namespace Tamarin.SignatureExtension
open Rewriting
variable {s x : Signature} {rs : Problem s}

private theorem local_instance (p : Term s) (σ : Substitution (joined s x))
    (env : ∀ v, p.Occurs v → Local (σ.image v)) : Local (σ.apply (embed x p)) := by
  induction p with
  | var v => exact env v rfl
  | atom => trivial
  | free f args ih => exact fun i => ih i (fun v hv => env v ⟨i,hv⟩)
  | ac _ _ _ il ir | comm _ _ _ il ir =>
    exact ⟨il (fun v hv => env v (.inl hv)),ir (fun v hv => env v (.inr hv))⟩

private theorem lift_step {a b : Term s} (h : Step (ruleRoot rs) a b) :
    Step (ruleRoot (query x rs)) (embed x a) (embed x b) := by
  classical
  induction h with
  | root h =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := h
    exact .root ⟨_,List.mem_map_of_mem hr,liftSubst x σ,(embed_apply ..).symm,(embed_apply ..).symm⟩
  | @free f as i u st ih =>
    have eq : embed x (.free f (fun j => if j = i then u else as j)) =
        Term.free (sig := joined s x) (.inl f) (fun j => @ite _ (j = i) (instDecidableEqFin _ j i) (embed x u) (embed x (as j))) := by
      apply congrArg (Term.free _)
      funext j
      dsimp only
      split <;> split <;> first | rfl | contradiction
    rw [eq]
    exact Step.free (root := ruleRoot (query x rs)) (.inl f) (fun j => embed x (as j)) i ih
  | comm_left _ c _ ih => exact .comm_left _ (embed x c) ih
  | comm_right _ c _ ih => exact .comm_right _ (embed x c) ih
  | ac_left _ c _ ih => exact .ac_left _ (embed x c) ih
  | ac_right _ c _ ih => exact .ac_right _ (embed x c) ih

private theorem lift_modulo {a b : Term s} (h : StepModulo (ruleRoot rs) a b) :
    StepModulo (ruleRoot (query x rs)) (embed x a) (embed x b) := by
  obtain ⟨_,_,e,st,f⟩ := h
  exact ⟨_,_,embed_eq e,lift_step st,embed_eq f⟩

private theorem project_step (bound : ReferenceReduction.Bound rs) {a b : Term (joined s x)}
    (h : Step (ruleRoot (query x rs)) a b) (loc : Local a) :
    Local b ∧ Step (ruleRoot rs) (restrictTerm a) (restrictTerm b) := by
  classical
  induction h with
  | root h =>
    obtain ⟨_,hr,σ,rfl,rfl⟩ := h
    obtain ⟨r,mem,rfl⟩ := List.mem_map.mp hr
    exact ⟨local_instance _ _ (fun v hv => local_image σ _ (bound r mem v hv) loc),
      .root ⟨r,mem,restrictSubst σ,(restrict_apply ..).symm,(restrict_apply ..).symm⟩⟩
  | @free f as i u st ih =>
    cases f with
    | inr => contradiction
    | inl f =>
      have ⟨hb,step⟩ := ih (loc i)
      refine ⟨fun j => ?_,?_⟩
      · dsimp only
        split
        · exact hb
        · exact loc j
      · have eq : restrictTerm (Term.free (sig := joined s x) (.inl f) (fun j => if j = i then u else as j)) =
            Term.free f (fun j => @ite _ (j = i) (instDecidableEqFin _ j i) (restrictTerm u) (restrictTerm (as j))) := by
          apply congrArg (Term.free _)
          funext j
          dsimp only
          split <;> split <;> first | rfl | contradiction
        rw [eq]
        exact Step.free (root := ruleRoot rs) f (fun j => restrictTerm (as j)) i step
  | comm_left f c st ih | ac_left f c st ih =>
    cases f with
    | inr => contradiction
    | inl f =>
      have ⟨hb,step⟩ := ih loc.1
      first | exact ⟨⟨hb,loc.2⟩,.comm_left _ _ step⟩ | exact ⟨⟨hb,loc.2⟩,.ac_left _ _ step⟩
  | comm_right f c st ih | ac_right f c st ih =>
    cases f with
    | inr => contradiction
    | inl f =>
      have ⟨hb,step⟩ := ih loc.2
      first | exact ⟨⟨loc.1,hb⟩,.comm_right _ _ step⟩ | exact ⟨⟨loc.1,hb⟩,.ac_right _ _ step⟩

private theorem project_modulo (bound : ReferenceReduction.Bound rs) {a b : Term (joined s x)}
    (h : StepModulo (ruleRoot (query x rs)) a b) (loc : Local a) :
    Local b ∧ StepModulo (ruleRoot rs) (restrictTerm a) (restrictTerm b) := by
  obtain ⟨_,_,eq,fire,out⟩ := h
  obtain ⟨inside,st⟩ := project_step bound fire ((local_equiv eq).mp loc)
  exact ⟨(local_equiv out).mp inside,_,_,restrict_eq eq,st,restrict_eq out⟩

private theorem lift_path {a b : Term s} (p : Reduces (ruleRoot rs) a b) :
    Reduces (ruleRoot (query x rs)) (embed x a) (embed x b) :=
  RootNarrowing.reduction_invariant (fun t => Reduces (ruleRoot (query x rs)) (embed x a) (embed x t))
    (fun h e => h.trans (.basis (embed_eq e))) (fun h st => h.trans (.step (lift_modulo st)))
    p (.basis (.refl _))

private theorem project_path (bound : ReferenceReduction.Bound rs) {a : Term s} {b : Term (joined s x)}
    (p : Reduces (ruleRoot (query x rs)) (embed x a) b) :
    Local b ∧ Reduces (ruleRoot rs) a (restrictTerm b) :=
  RootNarrowing.reduction_invariant (fun z => Local z ∧ Reduces (ruleRoot rs) a (restrictTerm z))
    (fun ⟨l,h⟩ e => ⟨(local_equiv e).mp l,h.trans (.basis (restrict_eq e))⟩)
    (fun ⟨l,h⟩ st => let ⟨l',step⟩ := project_modulo bound st l; ⟨l',h.trans (.step step)⟩)
    p ⟨embedding_local _,restrict_embed _ ▸ Reduces.basis (.refl _)⟩

/-- A canonical range-restricted table stays canonical on the original terms
when the extended signature is used to establish its certificate. In particular
both sides of an ambient join from local inputs project to the same term. -/
theorem reflect_canonical (x : Signature) (rs : Problem s) (scope : ReferenceReduction.Bound (query x rs))
    (can : MaudeOperations.CanonicalPresentation (ruleRoot (query x rs))) :
    ReferenceReduction.Bound rs ∧ MaudeOperations.CanonicalPresentation (ruleRoot rs) := by
  have bound : ReferenceReduction.Bound rs := fun r hr v hv =>
    (embed_occurs (x := x) r.lhs v).mp
      (scope ⟨embed x r.lhs,embed x r.rhs⟩ (List.mem_map_of_mem (f := fun e =>
        (⟨embed x e.lhs,embed x e.rhs⟩ : Equation (joined s x))) hr) v ((embed_occurs ..).mpr hv))
  refine ⟨bound,⟨Subrelation.wf (fun st => lift_modulo st) (InvImage.wf (embed x) can.terminating),?_,?_⟩⟩
  · intro _ _ _ left right
    obtain ⟨w,a,b⟩ := can.confluent (lift_path left) (lift_path right)
    exact ⟨restrictTerm w,(project_path bound a).2,(project_path bound b).2⟩
  · intro _ _ st k ht
    simpa only [restrict_embed] using restrict_sort (can.sortPreserving (lift_modulo st) k (embed_sort ht))

theorem reduction (x : Signature) (rs : Problem s) (bound : ReferenceReduction.Bound rs) (a b : Term s)
    (reply : MaudeOperations.ReductionReply (ruleRoot rs) a b) :
    MaudeOperations.ReductionReply (ruleRoot (query x rs)) (embed x a) (embed x b) := by
  refine ⟨⟨lift_path reply.normalForm.1,?_,?_⟩,?_⟩
  · intro u hu
    have st := (project_modulo bound hu (embedding_local _)).2
    rw [restrict_embed] at st
    exact reply.normalForm.2.1 _ st
  · intro k ha
    have sort := restrict_sort ha
    rw [restrict_embed] at sort
    exact embed_sort (reply.normalForm.2.2 k sort)
  · intro u other
    have ⟨inside,path⟩ := project_path bound other.1
    have nf : Normal (ruleRoot rs) (restrictTerm u) := by
      intro t st
      have big := lift_modulo (x := x) st
      rw [embed_restrict u inside] at big
      exact other.2.1 _ big
    have eq := embed_eq (x := x) (reply.unique _ ⟨path,nf,fun k ha => restrict_sort (other.2.2 k (embed_sort ha))⟩)
    simpa [embed_restrict u inside] using eq

end Tamarin.SignatureExtension
