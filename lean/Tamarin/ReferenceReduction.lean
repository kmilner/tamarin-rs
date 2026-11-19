import Tamarin.ReferenceMatching
import Tamarin.ReduceViaSteps
import Tamarin.NarrowingPositions

/-! Complete ordinary one-step rewriting for the active equation table. At an
AC head Maude can replace a matched subproduct and retain its complement.
Here the binary partitions of the operands enumerate all such extensions. -/
namespace Tamarin.ReferenceReduction
open Rewriting MaudeOperations
open ACSubproductReduction ContextualReduction
variable {s : Signature}

def Bound (rules : List (Equation s)) : Prop :=
  ∀ r ∈ rules, ∀ v, r.rhs.Occurs v → r.lhs.Occurs v

private def Represents (rows : List (Term s)) (t : Term s) : Prop :=
  ∃ u ∈ rows, EquivB u t

private theorem append_iff (xs ys : List (Term s)) (b : Term s) :
    Represents (xs ++ ys) b ↔ Represents xs b ∨ Represents ys b := by
  simp [Represents,List.mem_append,or_and_right,exists_or]

private theorem lift_iff {R : Root s} {a : Term s} {rows : List (Term s)}
    (ih : ∀ u, Represents rows u ↔ StepModulo R a u)
    (build : Term s → Term s) (congruent : ∀ {u v}, EquivB u v → EquivB (build u) (build v))
    (b : Term s) :
    Represents (rows.map build) b ↔ ∃ v, StepModulo R a v ∧ EquivB (build v) b := by
  constructor
  · rintro ⟨_,member,eq⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp member
    exact ⟨u,(ih _).mp ⟨_,hu,.refl _⟩,eq⟩
  · rintro ⟨v,step,out⟩
    obtain ⟨u,hu,eq⟩ := (ih _).mpr step
    exact ⟨_,List.mem_map_of_mem hu,(congruent eq).trans out⟩

private theorem atRoot_step {R : Root s} {a b : Term s} :
    AtRoot R a b → StepModulo R a b := fun ⟨p,q,l,hit,r⟩ => ⟨p,q,l,.root hit,r⟩

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def roots (rules : List (Equation s)) (t : Term s) : List (Term s) :=
  rules.flatMap fun r =>
    let p : Problem s := [⟨r.lhs,t⟩]
    ((ReferenceMatching.matcher s).run p trivial (patternVariables p)).map (fun σ => σ.apply r.rhs)

private theorem roots_iff (rules : List (Equation s)) (bound : Bound rules) (a b : Term s) :
    Represents (roots rules a) b ↔ AtRoot (ruleRoot rules) a b := by
  constructor
  · rintro ⟨_,member,out⟩
    obtain ⟨r,hr,arm⟩ := List.mem_flatMap.mp member
    obtain ⟨θ,ht,rfl⟩ := List.mem_map.mp arm
    have hit := (RuleMatches.of_complete (r := r) (plain_match (ReferenceMatching.matcher s) _ trivial)).sound θ ht
    exact ⟨_,_,hit.symm,⟨r,hr,θ,rfl,rfl⟩,out⟩
  · rintro ⟨_,_,before,⟨r,hr,σ,rfl,rfl⟩,after⟩
    obtain ⟨θ,ht,agree⟩ := (RuleMatches.of_complete (r := r)
      (plain_match (ReferenceMatching.matcher s) _ trivial)).complete σ before.symm
    have image := r.rhs.subst_equiv σ.image θ.image (fun v hv => agree v (bound r hr v hv))
    exact ⟨_,List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨θ,ht,rfl⟩⟩,image.symm.trans after⟩

private def extensions (rules : List (Equation s)) (f : s.ACSym) (t : Term s) :=
  (ACSplits.splits f t).flatMap fun (part,rest) =>
    (roots rules part).map (fun result => Term.ac f result rest)

def successors (rules : List (Equation s)) (t : Term s) : List (Term s) :=
  roots rules t ++ match t with
  | .var _ | .atom _ => []
  | .free f xs => (List.finRange (s.arity f)).flatMap fun i =>
      (successors rules (xs i)).map fun u => .free f (fun j => if j = i then u else xs j)
  | .comm f a b =>
      (successors rules a).map (fun u => .comm f u b) ++ (successors rules b).map (.comm f a)
  | .ac f a b => extensions rules f (.ac f a b) ++
      ((successors rules a).map (fun u => .ac f u b) ++ (successors rules b).map (.ac f a))

private theorem extension_sound (rules : List (Equation s)) (bound : Bound rules)
    (f : s.ACSym) {a b} (hit : Represents (extensions rules f a) b) :
    StepModulo (ruleRoot rules) a b := by
  obtain ⟨_,member,out⟩ := hit
  obtain ⟨⟨l,r⟩,split,member⟩ := List.mem_flatMap.mp member
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp member
  obtain ⟨p,q,before,fire,after⟩ := (roots_iff rules bound l u).mp ⟨_,hu,.refl _⟩
  exact ⟨_,_,(ACSplits.sound f a split).trans (.ac_congr f before (.refl _)),
    .ac_left f r (.root fire),(EquivB.ac_congr f after (.refl _)).trans out⟩

private theorem extensions_cover (rules : List (Equation s)) (bound : Bound rules)
    (f : s.ACSym) {a b} (hit : Occurrence (ruleRoot rules) f a b) :
    Represents (roots rules a) b ∨ Represents (extensions rules f a) b := by
  obtain ⟨p,q,rest,_,rule,before,after⟩ := hit
  cases rest with
  | none => exact .inl ((roots_iff rules bound _ _).mpr ⟨p,q,before,rule,after⟩)
  | some rem =>
    obtain ⟨l,r,split,left,right⟩ := ACSplits.complete f before
    obtain ⟨u,hu,out⟩ := (roots_iff rules bound l q).mpr ⟨_,_,left.symm,rule,.refl _⟩
    exact .inr ⟨_,List.mem_flatMap.mpr ⟨(l,r),split,List.mem_map.mpr ⟨u,hu,rfl⟩⟩,
      (EquivB.ac_congr f out right.symm).trans after⟩

theorem exactSteps (rules : List (Equation s)) (bound : Bound rules) (a b : Term s) :
    (∃ u ∈ successors rules a, EquivB u b) ↔ StepModulo (ruleRoot rules) a b := by
  change Represents (successors rules a) b ↔ _
  induction a generalizing b with
  | var v =>
    simp only [successors,List.append_nil,roots_iff rules bound]
    refine ⟨atRoot_step, ?_⟩
    rintro ⟨p,q,l,fire,r⟩
    cases p <;> cases l.head_eq
    cases fire with | root h => exact ⟨_,_,l,h,r⟩
  | atom a =>
    simp only [successors,List.append_nil,roots_iff rules bound]
    refine ⟨atRoot_step, ?_⟩
    rintro ⟨p,q,l,fire,r⟩
    cases p <;> cases l.head_eq
    cases fire with | root h => exact ⟨_,_,l,h,r⟩
  | free f xs ih =>
    rw [successors,append_iff,roots_iff rules bound,free_iff]
    apply or_congr_right
    constructor
    · rintro ⟨_,member,out⟩
      obtain ⟨i,_,member⟩ := List.mem_flatMap.mp member
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp member
      exact ⟨i,u,(ih i u).mp ⟨_,hu,.refl _⟩,out⟩
    · rintro ⟨i,v,step,out⟩
      obtain ⟨u,hu,eq⟩ := (ih i v).mpr step
      refine ⟨_,List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨u,hu,rfl⟩⟩,
        (EquivB.free f _ _ ?_).trans out⟩
      intro j
      by_cases e : j = i
      · simpa [e] using eq
      · simp [e,EquivB.refl]
  | comm f x y il ir =>
    rw [successors,append_iff,roots_iff rules bound,append_iff,comm_iff]
    rw [lift_iff il _ (fun eq => EquivB.comm_congr f eq (.refl _)),
      lift_iff ir _ (fun eq => EquivB.comm_congr f (.refl _) eq)]
  | ac f x y il ir =>
    rw [successors,append_iff,append_iff,append_iff,
      lift_iff il _ (fun eq => EquivB.ac_congr f eq (.refl _)),
      lift_iff ir _ (fun eq => EquivB.ac_congr f (.refl _) eq)]
    constructor
    · rintro (top|ext|child)
      · exact atRoot_step ((roots_iff rules bound _ _).mp top)
      · exact extension_sound rules bound f ext
      · exact (NarrowingPositions.ac_children_iff ..).mpr (.inr child)
    · intro step
      rcases (NarrowingPositions.ac_children_iff ..).mp step with group|child
      · exact (extensions_cover rules bound f group).elim Or.inl (Or.inr ∘ Or.inl)
      · exact .inr (.inr child)

/-- The reference step finder needs no bound on the number or size of redexes.
Termination of the complete reducer is a separate property of the presentation. -/
def finder (rules : List (Equation s)) (bound : Bound rules) : StepFinder (ruleRoot rules) where
  next t := (successors rules t).head?
  stoppedAtNormal t stop u step := by
    obtain ⟨v,hv,_⟩ := (exactSteps rules bound t u).mpr step
    rw [List.head?_eq_none_iff.mp stop] at hv
    exact List.not_mem_nil hv
  step t u hit := (exactSteps rules bound t u).mp ⟨u,List.mem_of_mem_head? hit,.refl _⟩

def reducer (rules : List (Equation s)) (bound : Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) : VerifiedReducer (ruleRoot rules) :=
  reducerOfSteps canonical (finder rules bound)

end
end Tamarin.ReferenceReduction
