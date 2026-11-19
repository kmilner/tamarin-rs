import Tamarin.VariableElimination

/-!
Finite, sort-preserving renamings with executable inverses. Freshening uses
a finite permutation rather than an infinite-support substitution, so both
directions are legal witnesses for the existing InstanceOn contract.
-/
namespace Tamarin

namespace Term
variable {sig : Signature}

/-- Finite variable inventory. Repetitions are harmless for scope closure. -/
def variables : Term sig → List Variable
  | .var v => [v]
  | .atom _ => []
  | .free _ args => (List.ofFn fun i => (args i).variables).flatten
  | .comm _ a b | .ac _ a b => a.variables ++ b.variables

@[simp] theorem mem_variables (t : Term sig) (v : Variable) :
    v ∈ t.variables ↔ t.Occurs v := by
  induction t with
  | var w => simp [variables, Occurs]
  | atom a => simp [variables, Occurs]
  | free f args ih =>
    simp only [variables, List.mem_flatten, List.mem_ofFn, Occurs]
    constructor
    · rintro ⟨vs, ⟨i, rfl⟩, hv⟩
      exact ⟨i, (ih i).mp hv⟩
    · rintro ⟨i, hv⟩
      exact ⟨(args i).variables, ⟨i, rfl⟩, (ih i).mpr hv⟩
  | comm f a b ha hb => simp [variables, Occurs, ha, hb]
  | ac f a b ha hb => simp [variables, Occurs, ha, hb]

theorem occurs_rename (t : Term sig) (rename : Variable → Variable) (v : Variable) :
    (t.subst (fun w => .var (rename w))).Occurs v ↔
      ∃ w, t.Occurs w ∧ v = rename w := by
  induction t with
  | var w => simp [subst, Occurs]
  | atom a => simp [subst, Occurs]
  | free f args ih =>
    simp only [subst, Occurs, ih]
    constructor
    · rintro ⟨i, w, hw, he⟩
      exact ⟨w, ⟨i, hw⟩, he⟩
    · rintro ⟨w, ⟨i, hw⟩, he⟩
      exact ⟨i, w, hw, he⟩
  | comm f a b ha hb | ac f a b ha hb =>
    simp only [subst, Occurs, ha, hb]
    constructor
    · rintro (⟨w, hw, he⟩ | ⟨w, hw, he⟩)
      · exact ⟨w, Or.inl hw, he⟩
      · exact ⟨w, Or.inr hw, he⟩
    · rintro ⟨w, hw | hw, he⟩
      · exact Or.inl ⟨w, hw, he⟩
      · exact Or.inr ⟨w, hw, he⟩

end Term

namespace Problem
variable {sig : Signature}

def variables (p : Problem sig) : List Variable :=
  p.flatMap fun e => e.lhs.variables ++ e.rhs.variables

@[simp] theorem mem_variables (p : Problem sig) (v : Variable) :
    v ∈ p.variables ↔ p.Occurs v := by
  simp [variables, List.mem_flatMap, Occurs]

end Problem

structure VariablePermutation where
  forward : Variable → Variable
  backward : Variable → Variable
  support : List Variable
  outside : ∀ v, v ∉ support → forward v = v
  left_inverse : ∀ v, backward (forward v) = v
  right_inverse : ∀ v, forward (backward v) = v
  sorted : ∀ v, (forward v).sort = v.sort

namespace VariablePermutation

def subst (π : VariablePermutation) (sig : Signature) : Substitution sig where
  image := fun v => .var (π.forward v)
  support := π.support
  outside := by intro v hv; rw [π.outside v hv]
  sorted := by intro v; simpa only [π.sorted] using HasSort.var (sig := sig) (π.forward v)

def inverse (π : VariablePermutation) : VariablePermutation where
  forward := π.backward
  backward := π.forward
  support := π.support
  outside := by
    intro v hv
    have h := π.left_inverse v
    rwa [π.outside v hv] at h
  left_inverse := π.right_inverse
  right_inverse := π.left_inverse
  sorted := by
    intro v
    have h := π.sorted (π.backward v)
    rw [π.right_inverse v] at h
    exact h.symm

theorem inverse_apply (π : VariablePermutation) {sig : Signature} (t : Term sig) :
    (π.inverse.subst sig).apply ((π.subst sig).apply t) = t := by
  change (t.subst (fun v => .var (π.forward v))).subst
    (fun v => .var (π.backward v)) = t
  rw [Term.subst_comp]
  simpa only [Term.subst, π.left_inverse] using t.subst_id

/-- A fresh starting ID above every listed variable. This uses mathematical
Nat IDs; a fixed-width ABI must separately check allocation overflow. -/
def freshBound : List Variable → Nat
  | [] => 0
  | v :: vs => max (v.id + 1) (freshBound vs)

theorem lt_freshBound (vs : List Variable) (v : Variable) (hv : v ∈ vs) :
    v.id < freshBound vs := by
  induction vs with
  | nil => simp at hv
  | cons w ws ih =>
    rcases List.mem_cons.mp hv with he | hm
    · subst v
      have h := Nat.le_max_left (w.id + 1) (freshBound ws)
      change w.id < max (w.id + 1) (freshBound ws)
      omega
    · have h := ih hm
      have hm := Nat.le_max_right (w.id + 1) (freshBound ws)
      change v.id < max (w.id + 1) (freshBound ws)
      omega

def shift (base : Nat) (v : Variable) : Variable := ⟨v.id + base, v.sort⟩
def unshift (base : Nat) (v : Variable) : Variable := ⟨v.id - base, v.sort⟩

@[simp] theorem unshift_shift (base : Nat) (v : Variable) :
    unshift base (shift base v) = v := by cases v; simp [shift, unshift]

theorem shift_unshift (base : Nat) (v : Variable) (h : base ≤ v.id) :
    shift base (unshift base v) = v := by
  cases v
  dsimp at h
  simp only [shift, unshift, Variable.mk.injEq, and_true]
  omega

/-- Swap a finite source set with its disjoint shifted copy. Using the entire
variable identity, including sort, avoids collapsing equal IDs of different
sorts. Duplicate source entries do not change the permutation. -/
def swapBlock (vars : List Variable) (base : Nat) (v : Variable) : Variable :=
  if v ∈ vars then shift base v
  else if base ≤ v.id ∧ unshift base v ∈ vars then unshift base v
  else v

theorem shift_not_mem (vars : List Variable) (base : Nat)
    (hb : ∀ v ∈ vars, v.id < base) (v : Variable) : shift base v ∉ vars := by
  intro hv
  have h := hb (shift base v) hv
  simp only [shift] at h
  omega

theorem swapBlock_source (vars : List Variable) (base : Nat)
    (v : Variable) (hv : v ∈ vars) : swapBlock vars base v = shift base v := by
  simp [swapBlock, hv]

theorem swapBlock_target (vars : List Variable) (base : Nat)
    (hb : ∀ v ∈ vars, v.id < base) (v : Variable) (hv : v ∈ vars) :
    swapBlock vars base (shift base v) = v := by
  have hbase : base ≤ (shift base v).id := by dsimp [shift]; omega
  simp only [swapBlock, ite_eq_right (shift_not_mem vars base hb v),
    hbase, unshift_shift, hv, and_self, ↓reduceIte]

theorem swapBlock_involutive (vars : List Variable) (base : Nat)
    (hb : ∀ v ∈ vars, v.id < base) (v : Variable) :
    swapBlock vars base (swapBlock vars base v) = v := by
  by_cases hv : v ∈ vars
  · rw [swapBlock_source vars base v hv, swapBlock_target vars base hb v hv]
  · by_cases ht : base ≤ v.id ∧ unshift base v ∈ vars
    · have hstep : swapBlock vars base v = unshift base v := by simp [swapBlock, hv, ht]
      rw [hstep, swapBlock_source vars base _ ht.2, shift_unshift base v ht.1]
    · simp only [swapBlock, ite_eq_right hv, ite_eq_right ht]

def ofBlock (vars : List Variable) (base : Nat)
    (hb : ∀ v ∈ vars, v.id < base) : VariablePermutation where
  forward := swapBlock vars base
  backward := swapBlock vars base
  support := vars ++ vars.map (shift base)
  outside := by
    intro v hv
    have hs : v ∉ vars := fun hm => hv (List.mem_append_left _ hm)
    rw [swapBlock, ite_eq_right hs]
    split
    · next ht =>
      exact False.elim (hv (List.mem_append_right _
        (List.mem_map.mpr ⟨unshift base v, ht.2, shift_unshift base v ht.1⟩)))
    · rfl
  left_inverse := swapBlock_involutive vars base hb
  right_inverse := swapBlock_involutive vars base hb
  sorted := by
    intro v
    unfold swapBlock
    split
    · rfl
    · split <;> rfl

end VariablePermutation
end Tamarin
