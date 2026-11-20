import Tamarin.CompleteNarrowing

/-! Table matching modulo the declared axioms. Numeric packets and source
schemas may arrange the factors, rules, or repeated rules differently. The
direction of each equation and the sharing of its variables are preserved. -/
namespace Tamarin.TablePresentation
open Rewriting MaudeOperations

variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def includes (a b : Problem s) : Bool :=
  a.all fun r => b.any fun t => ReferenceMatching.equal r.lhs t.lhs && ReferenceMatching.equal r.rhs t.rhs

def Agrees (a b : Problem s) : Bool := includes a b && includes b a

/-- Reordering or reassociating a row preserves the variables on each side. -/
theorem bound_of_agrees {a b : Problem s} (h : Agrees a b) (scope : ReferenceReduction.Bound b) :
    ReferenceReduction.Bound a := by
  intro r hr v occ
  obtain ⟨t,ht,ok⟩ := List.any_eq_true.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 r hr)
  obtain ⟨lhs,rhs⟩ := Bool.and_eq_true_iff.mp ok
  exact (((ReferenceMatching.equal_iff ..).mp lhs).occurs_iff v).mpr
    (scope t ht v ((((ReferenceMatching.equal_iff ..).mp rhs).occurs_iff v).mp occ))

private theorem liftRoot {a b : Problem s} (h : includes a b) {l r} (root : ruleRoot a l r) :
    StepModulo (ruleRoot b) l r := by
  obtain ⟨e,he,σ,rfl,rfl⟩ := root
  obtain ⟨t,ht,good⟩ := List.any_eq_true.mp (List.all_eq_true.mp h e he)
  have pair := Bool.and_eq_true_iff.mp good
  exact ⟨σ.apply t.lhs,σ.apply t.rhs,((ReferenceMatching.equal_iff ..).mp pair.1).subst σ.image,
    .root ⟨t,ht,σ,rfl,rfl⟩,((ReferenceMatching.equal_iff ..).mp pair.2).symm.subst σ.image⟩

private theorem liftRaw {a b : Problem s} (h : includes a b) {l r} (st : Step (ruleRoot a) l r) :
    StepModulo (ruleRoot b) l r := by
  induction st with
  | root fire => exact liftRoot h fire
  | free f xs i st ih =>
    apply (ContextualReduction.free_iff ..).mpr
    exact .inr ⟨i,_,ih,.refl _⟩
  | comm_left f t st ih => exact (ContextualReduction.comm_iff ..).mpr (.inr (.inl ⟨_,ih,.refl _⟩))
  | comm_right f t st ih => exact (ContextualReduction.comm_iff ..).mpr (.inr (.inr ⟨_,ih,.refl _⟩))
  | ac_left f t st ih => exact (NarrowingPositions.ac_children_iff ..).mpr (.inr (.inl ⟨_,ih,.refl _⟩))
  | ac_right f t st ih => exact (NarrowingPositions.ac_children_iff ..).mpr (.inr (.inr ⟨_,ih,.refl _⟩))

private theorem liftModulo {a b : Problem s} (h : includes a b) {l r} (st : StepModulo (ruleRoot a) l r) :
    StepModulo (ruleRoot b) l r := by
  obtain ⟨_,_,pre,one,post⟩ := st
  obtain ⟨x,y,left,edge,right⟩ := liftRaw h one
  exact ⟨x,y,pre.trans left,edge,right.trans post⟩

private theorem liftReduces {a b : Problem s} (h : includes a b) {l r} (red : Reduces (ruleRoot a) l r) :
    Reduces (ruleRoot b) l r :=
  RootNarrowing.reduction_invariant (fun t => Reduces (ruleRoot b) l t)
    (fun prior eq => prior.trans (.basis eq)) (fun prior st => prior.trans (.step (liftModulo h st)))
    red (.basis (.refl _))

theorem steps_iff {a b : Problem s} (h : Agrees a b) {l r} :
    StepModulo (ruleRoot a) l r ↔ StepModulo (ruleRoot b) l r :=
  ⟨liftModulo (Bool.and_eq_true_iff.mp h).1,liftModulo (Bool.and_eq_true_iff.mp h).2⟩

theorem reductions_iff {a b : Problem s} (h : Agrees a b) {l r} :
    Reduces (ruleRoot a) l r ↔ Reduces (ruleRoot b) l r :=
  ⟨liftReduces (Bool.and_eq_true_iff.mp h).1,liftReduces (Bool.and_eq_true_iff.mp h).2⟩

theorem canonical_iff {a b : Problem s} (h : Agrees a b) :
    CanonicalPresentation (ruleRoot a) ↔ CanonicalPresentation (ruleRoot b) := by
  have steps := funext fun x => funext fun y => propext (steps_iff (l := x) (r := y) h)
  have reductions := funext fun x => funext fun y => propext (reductions_iff (l := x) (r := y) h)
  constructor
  · rintro ⟨wf,joins,sorts⟩
    rw [steps] at wf sorts; rw [reductions] at joins
    exact ⟨wf,joins,sorts⟩
  · rintro ⟨wf,joins,sorts⟩
    rw [← steps] at wf sorts; rw [← reductions] at joins
    exact ⟨wf,joins,sorts⟩

theorem finite_iff {a b : Problem s} (h : Agrees a b) :
    FiniteVariantProperty (ruleRoot a) ↔ FiniteVariantProperty (ruleRoot b) := by
  have steps := funext fun x => funext fun y => propext (steps_iff (l := x) (r := y) h)
  have reductions := funext fun x => funext fun y => propext (reductions_iff (l := x) (r := y) h)
  simp only [FiniteVariantProperty,CompleteVariants,Variant.Sound,Variant.Covers,Normalized,Normal,NormalForm,steps,reductions]

end Tamarin.TablePresentation
