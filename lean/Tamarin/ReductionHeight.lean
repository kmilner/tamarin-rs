import Tamarin.ReferenceReduction
import Tamarin.NarrowingFrontier

/-! A finite complete step finder on a terminating presentation gives a
natural-number height invariant under the axioms. Heights measure concrete
specializations in the proof of folding variant search. -/
namespace Tamarin.ReductionHeight
open Rewriting MaudeOperations
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def maximum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: as => max (f a) (maximum f as)

private theorem below_max {α : Type} {f : α → Nat} {as : List α} {a} (h : a ∈ as) :
    f a ≤ maximum f as := by
  induction as with
  | nil => contradiction
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl|later
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih later) (Nat.le_max_right ..)

private theorem max_below {α : Type} {f : α → Nat} {as : List α} {k}
    (h : ∀ a ∈ as, f a ≤ k) : maximum f as ≤ k := by
  induction as with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    exact Nat.max_le.mpr ⟨h a List.mem_cons_self,ih (fun b hb => h b (List.mem_cons_of_mem _ hb))⟩

variable {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (wf : WellFounded (fun next current => StepModulo (ruleRoot rules) current next))

def height (bound : ReferenceReduction.Bound rules)
    (wf : WellFounded (fun next current => StepModulo (ruleRoot rules) current next)) (t : Term s) : Nat :=
  maximum (fun u : {v // v ∈ ReferenceReduction.successors rules t} => height bound wf u.val + 1)
    (ReferenceReduction.successors rules t).attach
termination_by wf.wrap t
decreasing_by exact (ReferenceReduction.exactSteps rules bound ..).mp ⟨u.val,u.property,.refl _⟩

private theorem child {a b : Term s} (h : b ∈ ReferenceReduction.successors rules a) :
    height bound wf b < height bound wf a := by
  rw [height.eq_1 bound wf a]
  exact below_max (f := fun u => height bound wf u.val + 1) (List.mem_attach _ ⟨b,h⟩)

/-- Any natural-valued descent for individual rewrites bounds the maximum
length of every branch, including in the presence of alternative rewrites. -/
theorem le_rank (rank : Term s → Nat)
    (decreases : ∀ {a b}, StepModulo (ruleRoot rules) a b → rank b < rank a) (t : Term s) :
    height bound wf t ≤ rank t := by
  induction t using wf.induction with
  | h t smaller =>
    rw [height.eq_1 bound wf t]
    apply max_below
    intro u _
    have st := (ReferenceReduction.exactSteps rules bound t u.val).mp ⟨u.val,u.property,.refl _⟩
    exact Nat.lt_of_le_of_lt (smaller u.val st) (decreases st)

private theorem equiv_le (a : Term s) : ∀ b, EquivB a b → height bound wf a ≤ height bound wf b := by
  induction a using wf.induction with
  | h a ih =>
    intro b equivalent
    rw [height.eq_1 bound wf a]
    apply max_below
    intro c _
    have step := (ReferenceReduction.exactSteps rules bound ..).mp ⟨c.val,c.property,.refl _⟩
    obtain ⟨l,r,start,one,finish⟩ := step
    obtain ⟨d,member,same⟩ := (ReferenceReduction.exactSteps rules bound b c.val).mpr
      ⟨l,r,equivalent.symm.trans start,one,finish⟩
    exact Nat.lt_of_le_of_lt (ih c.val ⟨l,r,start,one,finish⟩ d same.symm) (child bound wf member)

theorem equiv {a b : Term s} (e : EquivB a b) : height bound wf a = height bound wf b :=
  Nat.le_antisymm (equiv_le bound wf a b e) (equiv_le bound wf b a e.symm)

theorem step {a b : Term s} (h : StepModulo (ruleRoot rules) a b) : height bound wf b < height bound wf a := by
  obtain ⟨u,member,same⟩ := (ReferenceReduction.exactSteps rules bound a b).mpr h
  rw [← equiv bound wf same]
  exact child bound wf member

theorem reduces {a b : Term s} (h : Reduces (ruleRoot rules) a b) : height bound wf b ≤ height bound wf a :=
  RootNarrowing.reduction_invariant (fun u => height bound wf u ≤ height bound wf a)
    (fun prior e => equiv bound wf e ▸ prior) (fun prior st => Nat.le_trans (Nat.le_of_lt (step bound wf st)) prior)
    h (Nat.le_refl _)

end Tamarin.ReductionHeight
