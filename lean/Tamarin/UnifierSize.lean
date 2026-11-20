import Tamarin.ACRepresentation
import Tamarin.FiniteOccurs
import Tamarin.VariablePermutation

/-! Finite terms grow by the size of each substituted image minus the one
variable node it replaces. This gives a refutation before AC allocation,
including when several variables occur on both sides under different heads. -/
namespace Tamarin.UnifierSize
open FiniteOccurs
variable {sig : Signature}

/-- The Rust array has one fewer binary AC node than operands, including
when one of those operands is itself an unflattened application. -/
theorem nodes_fold (f : sig.ACSym) (a : Term sig) (xs : List (Term sig)) :
    nodes (ACRepresentation.fold f a xs) = nodes a + (xs.map nodes).sum + xs.length := by
  induction xs generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih =>
    change nodes a + nodes (ACRepresentation.fold f b bs) + 1 = _
    rw [ih]; simp only [List.map_cons,List.sum_cons,List.length_cons]; omega

theorem variables_fold (f : sig.ACSym) (a : Term sig) (xs : List (Term sig)) :
    (ACRepresentation.fold f a xs).variables = a.variables ++ (xs.map Term.variables).flatten := by
  induction xs generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih => simp [ACRepresentation.fold,Term.variables,ih]

private theorem sum_parts {n : Nat} (a b : Fin n → Nat) :
    (List.ofFn fun i => a i + b i).sum = (List.ofFn a).sum + (List.ofFn b).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    rw [ih (fun i => a i.succ) (fun i => b i.succ)]
    omega

private theorem sum_flat (ls : List (List Nat)) : ls.flatten.sum = (ls.map List.sum).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [List.sum_append,ih]

/-- A single affine size profile applies to all finite sorted substitutions. -/
theorem substituted (σ : Substitution sig) (t : Term sig) :
    nodes (σ.apply t) = nodes t + (t.variables.map (fun v => nodes (σ.image v) - 1)).sum := by
  let extra := fun v => nodes (σ.image v) - 1
  induction t with
  | var v =>
    change nodes (σ.image v) = 1 + (([v].map extra).sum)
    have pos (a : Term sig) : 0 < nodes a := by
      cases a with
      | var | atom => exact Nat.zero_lt_one
      | free _ _ => exact Nat.zero_lt_succ _
      | ac | comm => exact Nat.zero_lt_succ _
    simp only [extra,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    have := pos (σ.image v)
    omega
  | atom => rfl
  | comm f a b ia ib | ac f a b ia ib =>
    change nodes (σ.apply a) + nodes (σ.apply b) + 1 = nodes a + nodes b + 1 +
      (((a.variables ++ b.variables).map extra).sum)
    rw [ia,ib,List.map_append,List.sum_append]; dsimp [extra]; omega
  | free f args ih =>
    change (List.ofFn (fun i => nodes (σ.apply (args i)))).sum + 1 =
      (List.ofFn (fun i => nodes (args i))).sum + 1 +
        (((List.ofFn (fun i => (args i).variables)).flatten.map extra).sum)
    simp only [List.map_flatten,List.map_ofFn,sum_flat,Function.comp_def]
    rw [show (fun i => nodes (σ.apply (args i))) =
      (fun i => nodes (args i) + ((args i).variables.map extra).sum) from funext ih, sum_parts]
    omega

private theorem sum_perm {xs ys : List Nat} (p : xs.Perm ys) : xs.sum = ys.sum := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ ih ik => exact ih.trans ik

private theorem weighted_le (weight : Variable → Nat) (xs ys : List Variable)
    (le : ∀ v, xs.count v ≤ ys.count v) : (xs.map weight).sum ≤ (ys.map weight).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have pos := le x
    simp only [List.count_cons_self] at pos
    have perm := List.perm_cons_erase (a := x) (l := ys) (List.count_pos_iff.mp (by omega))
    have smaller : ∀ v, xs.count v ≤ (ys.erase x).count v := by
      intro v
      have eq := perm.count_eq v
      have h := le v
      simp only [List.count_cons] at h eq
      omega
    have sum := sum_perm (perm.map weight)
    have tail := ih _ smaller
    simp only [List.map_cons,List.sum_cons] at *
    omega

/-- A strict size decrease stays strict after any sorted substitution when
each variable occurs at most as often on the smaller side. -/
theorem substituted_lt {a b : Term sig} (strict : nodes a < nodes b)
    (counts : ∀ v, a.variables.count v ≤ b.variables.count v) (σ : Substitution sig) :
    nodes (σ.apply a) < nodes (σ.apply b) := by
  rw [substituted,substituted]
  exact Nat.add_lt_add_of_lt_of_le strict (weighted_le _ _ _ counts)

/-- Unequal initial sizes and componentwise variable multiplicities in the
same direction give a contradiction for every substitution. In particular
the inputs may share every variable and have no common top-level factors. -/
theorem refutes {a b : Term sig} (strict : nodes a < nodes b)
    (counts : ∀ v, a.variables.count v ≤ b.variables.count v) (σ : Substitution sig) :
    ¬ EquivB (σ.apply a) (σ.apply b) := by
  exact fun eq => (Nat.ne_of_lt (substituted_lt strict counts σ)) (nodes_equiv eq)

end Tamarin.UnifierSize
