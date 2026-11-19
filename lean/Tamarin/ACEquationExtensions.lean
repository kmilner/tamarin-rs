import Tamarin.ReferenceReduction

/-! Core Maude narrows with the equations present in its table. Make the
one-remainder rule explicit for each AC-headed equation. These derived rules
preserve every contextual rewrite, including on kind-level terms. -/
namespace Tamarin.ACEquationExtensions
open Rewriting ACSubproductReduction ConstructorVariants ContextualReduction
variable {s : Signature}

def remainder (f : s.ACSym) (r : Equation s) : Variable :=
  ⟨VariablePermutation.freshBound (r.lhs.variables ++ r.rhs.variables),s.acSort f⟩

def extended (rules : List (Equation s)) : List (Equation s) :=
  rules ++ rules.filterMap fun r => match head r.lhs with
    | .ac f => some (pattern f (remainder f r) r true)
    | _ => none

private theorem cases_mem {rules : List (Equation s)} {r : Equation s} (h : r ∈ extended rules) :
    r ∈ rules ∨ ∃ p ∈ rules, ∃ f, head p.lhs = .ac f ∧ r = pattern f (remainder f p) p true := by
  rcases List.mem_append.mp h with base|extra
  · exact .inl base
  · obtain ⟨p,hp,eq⟩ := List.mem_filterMap.mp extra
    split at eq
    · next f hd => exact .inr ⟨p,hp,f,hd,(Option.some.inj eq).symm⟩
    · contradiction

theorem bound {rules : List (Equation s)} (base : ReferenceReduction.Bound rules) :
    ReferenceReduction.Bound (extended rules) := by
  intro r hr v hv
  rcases cases_mem hr with old|⟨p,hp,_,_,rfl⟩
  · exact base r old v hv
  · exact hv.imp (base p hp v) id

private theorem step_lift {R S : Root s} (root : ∀ a b, R a b → Step S a b) {a b} (st : Step R a b) :
    Step S a b := by
  induction st with
  | root h => exact root _ _ h
  | free f xs i _ ih => exact .free f xs i ih
  | comm_left f t _ ih => exact .comm_left f t ih
  | comm_right f t _ ih => exact .comm_right f t ih
  | ac_left f t _ ih => exact .ac_left f t ih
  | ac_right f t _ ih => exact .ac_right f t ih

theorem steps (rules : List (Equation s)) (a b : Term s) :
    Step (ruleRoot (extended rules)) a b ↔ Step (ruleRoot rules) a b := by
  constructor
  · apply step_lift
    rintro _ _ ⟨r,hr,σ,rfl,rfl⟩
    rcases cases_mem hr with old|⟨p,hp,f,_,rfl⟩
    · exact .root ⟨r,old,σ,rfl,rfl⟩
    · exact .ac_left f _ (.root ⟨p,hp,σ,rfl,rfl⟩)
  · apply step_lift
    rintro _ _ ⟨r,hr,σ,rfl,rfl⟩
    exact .root ⟨r,List.mem_append_left _ hr,σ,rfl,rfl⟩

theorem modulo (rules : List (Equation s)) (a b : Term s) :
    StepModulo (ruleRoot (extended rules)) a b ↔ StepModulo (ruleRoot rules) a b := by
  simp only [StepModulo,steps]

private theorem transport {R S : Root s} (one : ∀ a b, StepModulo R a b → StepModulo S a b)
    {a b} (h : Reduces R a b) : Reduces S a b := by
  induction h with
  | basis e => exact .basis e
  | step h => exact .step (one _ _ h)
  | trans _ _ ih jh => exact .trans ih jh
  | free f xs ys _ ih => exact .free f xs ys ih
  | comm f _ _ ih jh => exact .comm f ih jh
  | ac f _ _ ih jh => exact .ac f ih jh

theorem reductions (rules : List (Equation s)) (a b : Term s) :
    Reduces (ruleRoot (extended rules)) a b ↔ Reduces (ruleRoot rules) a b :=
  ⟨transport (fun x y => (modulo rules x y).mp),transport (fun x y => (modulo rules x y).mpr)⟩

theorem forms (rules : List (Equation s)) (a b : Term s) :
    NormalForm (ruleRoot (extended rules)) a b ↔ NormalForm (ruleRoot rules) a b := by
  simp only [NormalForm,Normal,modulo,reductions]

theorem variants (rules : List (Equation s)) (q : List (Term s)) (avoid : List Variable) (rows : List (Variant s)) :
    MaudeOperations.VariantReply (ruleRoot (extended rules)) q avoid rows ↔
      MaudeOperations.VariantReply (ruleRoot rules) q avoid rows := by
  have normals : Normal (ruleRoot (extended rules)) = Normal (ruleRoot rules) :=
    funext fun t => propext (by simp only [Normal,modulo])
  have nfs : NormalForm (ruleRoot (extended rules)) = NormalForm (ruleRoot rules) :=
    funext fun t => funext fun u => propext (forms rules t u)
  have sound (a : Variant s) : a.Sound (ruleRoot (extended rules)) q ↔ a.Sound (ruleRoot rules) q := by
    simp only [Variant.Sound,Normalized,normals,nfs]
  have same : CompleteVariants (ruleRoot (extended rules)) q rows ↔ CompleteVariants (ruleRoot rules) q rows := by
    simp only [CompleteVariants,Variant.Covers,Normalized,normals,nfs,sound]
  have recover (a : Variant s) : a.Reconstructible (ruleRoot (extended rules)) q ↔ a.Reconstructible (ruleRoot rules) q := by
    simp only [Variant.Reconstructible,nfs]
  exact ⟨fun h => ⟨same.mp h.complete,h.nonempty,h.safe,fun a ha => (recover a).mp (h.reconstructible a ha)⟩,
    fun h => ⟨same.mpr h.complete,h.nonempty,h.safe,fun a ha => (recover a).mpr (h.reconstructible a ha)⟩⟩

/-- On sorted products every proper-subproduct rule instance is exposed to
ordinary whole-position narrowing by the explicitly extended table. -/
theorem atRoot_of_occurrence (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (a b : Term s) (typed : HasSort a (s.acSort f))
    (step : Occurrence (ruleRoot rules) f a b) : AtRoot (ruleRoot (extended rules)) a b := by
  have fresh (r : Equation s) (_ : r ∈ rules) : ¬r.lhs.Occurs (remainder f r) := by
    intro occ
    have lt := VariablePermutation.lt_freshBound _ _ (List.mem_append_left r.rhs.variables ((r.lhs.mem_variables _).mpr occ))
    exact (Nat.lt_irrefl _) lt
  obtain ⟨r,hr,hd,ext,σ,l,out⟩ := (occurrence_iff_instances f rules apps (fun r hr _ => bound r hr) a b typed
    (remainder f) (fun _ _ => rfl) fresh).mp step
  refine ⟨_,_,l,⟨_,?_,σ,rfl,rfl⟩,out⟩
  cases ext with
  | false => exact List.mem_append_left _ hr
  | true => exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨r,hr,by simp [hd]⟩)

end Tamarin.ACEquationExtensions
