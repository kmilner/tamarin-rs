import Tamarin.XorRules
import Tamarin.DHProduct
import Tamarin.ACRepresentation

/-! Cancellation in finite XOR trees of Fresh leaves. The additional table
inventory specifies the right hand sides of all active XOR-headed rules. -/
namespace Tamarin.Rewriting.FreshXor.Flat
open ACRepresentation Cancellation
variable {sig : Signature}

structure Table (sig : Signature) extends FreshXor.Table sig where
  unitRule : ∃ v : Variable, v.sort = .msg ∧ (⟨.ac f (.var v) zero, .var v⟩ : Equation sig) ∈ rules
  inventory : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .ac f →
    r = ⟨.ac f (.var param) (.var param), zero⟩ ∨
    (∃ v, r = ⟨.ac f (.var v) zero, .var v⟩) ∨
    (∃ u v, r = ⟨.ac f (.var u) (.ac f (.var u) (.var v)), .var v⟩) ∨
    (∃ u v, r = ⟨.ac f (.ac f (.var u) (.var u)) (.var v), .var v⟩)

namespace Table
variable (T : Table sig)
abbrev R := T.toTable.R

def value : List (Term sig) → Term sig
  | [] => T.zero
  | a :: as => ACRepresentation.fold T.f a as

theorem value_perm {xs ys : List (Term sig)} (p : xs.Perm ys) : EquivB (T.value xs) (T.value ys) := by
  cases xs with
  | nil => have := p.nil_eq; subst ys; exact .refl _
  | cons x xs =>
    cases ys with
    | nil => cases p.eq_nil
    | cons y ys => exact decode_perm T.f p _ _ rfl rfl

theorem fresh_msg {t : Term sig} (h : HasSort t .fresh) : HasSort t .msg := h.widen .fresh_msg

theorem value_msg (xs : List (Term sig)) (h : ∀ t ∈ xs, HasSort t .fresh) : HasSort (T.value xs) .msg := by
  cases xs with
  | nil => exact T.zeroSort
  | cons a as =>
    rw [← T.fSort]
    exact fold_hasSort T.f a as (T.fSort ▸ fresh_msg (h _ List.mem_cons_self))
      (fun t ht => T.fSort ▸ fresh_msg (h _ (List.mem_cons_of_mem _ ht)))

theorem unit {a : Term sig} (h : HasSort a .msg) : T.R (.ac T.f a T.zero) a := by
  obtain ⟨v,sv,unitMem⟩ := T.unitRule
  let σ := Substitution.binding v a (sv ▸ h)
  refine ⟨_,unitMem,σ,?_,?_⟩
  change Term.ac T.f a T.zero = Term.ac T.f (σ.image v) (σ.apply T.zero)
  rw [T.toTable.fixes_zero]
  all_goals simp [σ,Substitution.binding,Substitution.apply,Term.subst]

theorem dropPair {a : Term sig} (xs : List (Term sig)) (ha : HasSort a .fresh)
    (hs : ∀ t ∈ xs, HasSort t .fresh) :
    Reduces T.R (T.value (a :: a :: xs)) (T.value xs) := by
  cases xs with
  | nil => exact (T.toTable.duplicate_nf ha).1
  | cons x xs =>
    refine .trans (.basis (.symm (.ac_assoc T.f a a _))) ?_
    refine .trans (.ac _ (T.toTable.duplicate_nf ha).1 (.basis (.refl _))) ?_
    exact .step ⟨_,_,.ac_swap _ _ _,.root (T.unit (T.value_msg (x::xs) hs)),.refl _⟩

private theorem split_pair {α : Type} [DecidableEq α] {a : α} {xs : List α} (h : 2 ≤ xs.count a) :
    ∃ ys, xs.Perm (a :: a :: ys) := by
  have m := List.count_pos_iff.mp (show 0 < xs.count a by omega)
  have p := List.perm_cons_erase m
  have cnt := p.count_eq a
  rw [List.count_cons_self] at cnt
  have m' := List.count_pos_iff.mp (show 0 < (xs.erase a).count a by omega)
  exact ⟨_,p.trans ((List.perm_cons_erase m').cons a)⟩

/-- Reachability from the table uses only cancellation and the unit. Branch
selection and the order of the chosen representative list are unrestricted. -/
theorem reduces_parity [DecidableEq (Term sig)] {xs ys : List (Term sig)}
    (hx : ∀ t ∈ xs, HasSort t .fresh) (hy : ys.Nodup)
    (same : ∀ t, xs.count t % 2 = ys.count t % 2) :
    Reduces T.R (T.value xs) (T.value ys) := by
  by_cases nd : xs.Nodup
  · apply Reduces.basis (T.value_perm (List.perm_iff_count.mpr _))
    intro t
    have h := same t
    have a := List.nodup_iff_count.mp nd t
    have b := List.nodup_iff_count.mp hy t
    omega
  · obtain ⟨t,h⟩ : ∃ t, 2 ≤ xs.count t := by
      apply Classical.byContradiction; intro hn
      exact nd (List.nodup_iff_count.mpr (fun t => by have bad : ¬ 2 ≤ xs.count t := fun h => hn ⟨t,h⟩; omega))
    obtain ⟨zs,p⟩ := split_pair h
    have hz u (hu : u ∈ zs) := hx u (p.mem_iff.mpr (by simp [hu]))
    refine .trans (.basis (T.value_perm p)) (.trans (T.dropPair zs (hx t (p.mem_iff.mpr List.mem_cons_self)) hz) ?_)
    apply reduces_parity hz hy
    intro u
    have n := p.count_eq u
    have h := same u
    by_cases e : t = u <;> simp [e] at n <;> omega
termination_by xs.length
decreasing_by have := p.length_eq; simp at this; omega

end Table
end Tamarin.Rewriting.FreshXor.Flat
