import Tamarin.UnifierSize
import Tamarin.ReferenceReduction

/-! Sufficient checks on a finite presentation. Strict node decrease and
multiplicities are invariant under B and hold for every rule instance, even
in a kind-level context. Sort preservation is checked separately. -/
namespace Tamarin.TableDecrease
open Rewriting FiniteOccurs
variable {s : Signature} {rules : List (Equation s)}

def decreases (r : Equation s) : Bool :=
  nodes r.rhs < nodes r.lhs && r.rhs.variables.all fun v =>
    r.rhs.variables.count v ≤ r.lhs.variables.count v

def decreasing (rules : List (Equation s)) : Bool := rules.all decreases

private theorem counts {r : Equation s} (ok : decreases r = true) (v : Variable) :
    r.rhs.variables.count v ≤ r.lhs.variables.count v := by
  by_cases occurs : v ∈ r.rhs.variables
  · exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 v occurs)
  · simp [List.count_eq_zero_of_not_mem occurs]

theorem bound (ok : decreasing rules = true) : ReferenceReduction.Bound rules := by
  intro r hr v hv
  have pos := List.count_pos_iff.mpr ((Term.mem_variables ..).mpr hv)
  exact (Term.mem_variables ..).mp (List.count_pos_iff.mp
    (Nat.lt_of_lt_of_le pos (counts (List.all_eq_true.mp ok r hr) v)))

private theorem sum_lt {n : Nat} (i : Fin n) (xs ys : Fin n → Nat)
    (lt : ys i < xs i) (rest : ∀ j, j ≠ i → ys j = xs j) :
    (List.ofFn ys).sum < (List.ofFn xs).sum := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    cases i using Fin.cases with
    | zero =>
      have same : (fun j : Fin n => ys j.succ) = (fun j => xs j.succ) :=
        funext fun j => rest j.succ (Fin.succ_ne_zero j)
      exact same ▸ Nat.add_lt_add_right lt _
    | succ i =>
      rw [rest 0 (Fin.ne_of_lt (Nat.zero_lt_succ _))]
      exact Nat.add_lt_add_left (ih i _ _ lt fun j ne =>
        rest j.succ (fun h => ne (Fin.succ_inj.mp h))) _

private theorem inside_lt (ok : decreasing rules = true) {a b : Term s}
    (h : Step (ruleRoot rules) a b) : nodes b < nodes a := by
  induction h with
  | root h =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := h
    have rule := List.all_eq_true.mp ok r hr
    exact UnifierSize.substituted_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp rule).1) (counts rule) σ
  | @free f args i u h ih =>
    change (List.ofFn (fun j => nodes (if j = i then u else args j))).sum + 1 < (List.ofFn (fun j => nodes (args j))).sum + 1
    apply Nat.add_lt_add_right _ 1
    apply sum_lt i
    · simpa using ih
    · intro j hj
      simp [hj]
  | ac_left _ _ _ ih | comm_left _ _ _ ih => exact Nat.add_lt_add_right (Nat.add_lt_add_right ih _) _
  | ac_right _ _ _ ih | comm_right _ _ _ ih => exact Nat.add_lt_add_right (Nat.add_lt_add_left ih _) _

theorem step_lt (accepted : decreasing rules = true) {a b : Term s}
    (step : StepModulo (ruleRoot rules) a b) : nodes b < nodes a := by
  obtain ⟨_,_,before,one,after⟩ := step
  simpa only [← nodes_equiv before,nodes_equiv after] using inside_lt accepted one

theorem terminating (accepted : decreasing rules = true) :
    WellFounded (fun b a => StepModulo (ruleRoot rules) a b) :=
  Subrelation.wf (fun h => step_lt accepted h) (measure nodes).wf

/-- A strict upper bound on the number of rewrites, with fuel left to
check that the reached term is irreducible. -/
def budget (rules : List (Equation s)) (t : Term s) : Option Nat :=
  if decreasing rules then some (nodes t + 1) else none

/-- Variables at the root can acquire a narrower sort under substitution.
A rule with a fixed source head has its declared root sort at every instance. -/
def sortRule (r : Equation s) : Bool := match r.lhs with
  | .var _ => false
  | _ => r.rhs.checkSort r.lhs.rootSort

def sorted (rules : List (Equation s)) : Bool := rules.all sortRule

private theorem sort_root (ok : sorted rules = true) {a b : Term s}
    (h : ruleRoot rules a b) {k} (typed : HasSort a k) : HasSort b k := by
  obtain ⟨⟨l,r⟩,hr,σ,rfl,rfl⟩ := h
  have okr := List.all_eq_true.mp ok ⟨l,r⟩ hr
  have source := Term.rootSort_le typed
  cases l <;> simp [sortRule] at okr <;>
    exact .widen ((Term.checkSort_sound _ _ okr).subst σ.image σ.sorted) source

private theorem inside_sort (ok : sorted rules = true) {a b : Term s}
    (st : Step (ruleRoot rules) a b) (k) (ht : HasSort a k) : HasSort b k := by
  induction st generalizing k with
  | root h => exact sort_root ok h ht
  | free f xs i st ih =>
    simp only [← Term.checkSort_iff,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at ht ⊢
    refine ⟨ht.1,fun j hj => ?_⟩
    by_cases e : j = i
    · subst j
      simpa using Term.checkSort_complete (ih _ (Term.checkSort_sound _ _ (ht.2 i hj)))
    · simpa [e] using ht.2 j hj
  | comm_left f t st ih | ac_left f t st ih =>
    simp only [← Term.checkSort_iff,Term.checkSort,Bool.and_eq_true] at ht ⊢
    exact ⟨⟨ht.1.1,Term.checkSort_complete (ih _ (Term.checkSort_sound _ _ ht.1.2))⟩,ht.2⟩
  | comm_right f t st ih | ac_right f t st ih =>
    simp only [← Term.checkSort_iff,Term.checkSort,Bool.and_eq_true] at ht ⊢
    exact ⟨ht.1,Term.checkSort_complete (ih _ (Term.checkSort_sound _ _ ht.2))⟩

theorem sortPreserving (accepted : sorted rules = true) {a b : Term s}
    (st : StepModulo (ruleRoot rules) a b) (k) (typed : HasSort a k) : HasSort b k := by
  obtain ⟨_,_,before,one,after⟩ := st
  have src := Term.checkSort_complete typed
  rw [SortClash.check_equiv before] at src
  have dst := Term.checkSort_complete (inside_sort accepted one k (Term.checkSort_sound _ _ src))
  exact Term.checkSort_sound _ _ (SortClash.check_equiv after k ▸ dst)

end Tamarin.TableDecrease
