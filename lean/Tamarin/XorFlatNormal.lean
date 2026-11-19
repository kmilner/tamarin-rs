import Tamarin.XorFlatInvariant
import Tamarin.SortClash

/-! A parity representative is exactly the observable normal form, modulo B. -/
namespace Tamarin.Rewriting.FreshXor.Flat.Table
open Cancellation ConstructorVariants ACRepresentation
variable {sig : Signature} (T : Flat.Table sig)

noncomputable section
open Classical

private theorem fold_bag (a : Term sig) (as : List (Term sig)) (hs : ∀ x ∈ a::as, HasSort x .fresh) :
    T.bag (ACRepresentation.fold T.f a as) = ((a :: as).map classOf) := by
  induction as generalizing a with
  | nil => exact T.bag_leaf (hs _ List.mem_cons_self)
  | cons b bs ih =>
    rw [ACRepresentation.fold,bag,flatten_ac,← bag, T.bag_leaf (hs _ List.mem_cons_self)]
    change [classOf a] ++ T.bag (ACRepresentation.fold T.f b bs) = _
    rw [ih b (fun x hx => hs x (List.mem_cons_of_mem _ hx))]; rfl

private theorem value_pure (xs : List (Term sig)) (hs : ∀ x ∈ xs, HasSort x .fresh)
    (hn : ∀ x ∈ xs, Normal T.R x) : T.Pure (T.value xs) := by
  cases xs with
  | nil => exact T.pure_zero
  | cons a as =>
    intro k hk
    rw [value,T.fold_bag _ _ hs] at hk
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hk
    exact .inr ⟨x,hs _ hx,hn _ hx,rfl⟩

private theorem value_normal (xs : List (Term sig)) (hs : ∀ x ∈ xs, HasSort x .fresh)
    (hn : ∀ x ∈ xs, Normal T.R x) (nd : xs.Nodup) : Normal T.R (T.value xs) := by
  cases xs with
  | nil => exact T.toTable.zero_normal
  | cons x xs =>
    let whole := T.value (x::xs)
    have eq : T.bag whole = (x::xs).map classOf := T.fold_bag _ _ hs
    have noZero : T.zeroClass ∉ T.bag whole := by
      rw [eq]
      rintro h
      obtain ⟨a,ha,ez⟩ := List.mem_map.mp h
      exact T.not_zero (hs a ha) ez
    have nodup : (T.bag whole).Nodup := by
      rw [eq,List.Nodup,List.pairwise_map]
      exact nd.imp_of_mem fun ha _ ne h => ne (T.leaf_eq (hs _ ha) (Quotient.exact h))
    apply DHProduct.subgroup_normal T.f whole
    · intro t ht
      have hm : classOf t ∈ T.bag whole := by
        rw [bag,DHProduct.classes]; exact List.mem_map_of_mem ht
      obtain ⟨a,ha,eq⟩ := List.mem_map.mp (eq ▸ hm)
      exact (normal_equiv _ (Quotient.exact eq)).mp (hn _ ha)
    · intro p q hp sub step
      obtain ⟨rs,perm⟩ := sub
      have counts (k) : (T.bag p).count k ≤ 1 := by
        have h := perm.count_eq k
        rw [List.count_append] at h
        have l := List.nodup_iff_count.mp nodup k
        change (T.bag whole).count k = (T.bag p).count k + _ at h
        omega
      have duplicate (a : Term sig) : ∃ k, 0 < (T.bag a).count k := by
        obtain ⟨k,h⟩ := List.exists_mem_of_ne_nil _ (T.bag_nonempty a)
        exact ⟨k,List.count_pos_iff.mpr h⟩
      rcases T.root_cases hp step with ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
      · obtain ⟨k,h⟩ := duplicate a
        have := counts k; simp only [bag,flatten_ac,List.count_append] at *; omega
      · apply noZero (perm.mem_iff.mpr (List.mem_append_left _ ?_))
        rw [flatten_ac]
        change _ ∈ _ ++ T.bag T.zero
        rw [T.bag_zero]
        simp
      · obtain ⟨k,h⟩ := duplicate a
        have := counts k; simp only [bag,flatten_ac,List.count_append] at *; omega
      · obtain ⟨k,h⟩ := duplicate a
        have := counts k; simp only [bag,flatten_ac,List.count_append] at *; omega

private theorem combine_values (xs ys : List (Term sig)) (hs : ∀ x ∈ xs, HasSort x .fresh)
    (ht : ∀ x ∈ ys, HasSort x .fresh) :
    Reduces T.R (.ac T.f (T.value xs) (T.value ys)) (T.value (xs ++ ys)) := by
  cases ys with
  | nil => exact .step ⟨_,_,.refl _,.root (T.unit (T.value_msg xs hs)),by simp [value]; exact .refl _⟩
  | cons y ys =>
    cases xs with
    | nil => exact .step ⟨_,_,.ac_swap _ _ _,.root (T.unit (T.value_msg (y::ys) ht)),.refl _⟩
    | cons x xs => exact .basis (fold_append T.f x xs y ys).symm

/-- Strip any number of unit factors introduced by intermediate reductions.
No pure term can reach factors outside the input Fresh/unit fragment. -/
private theorem strip (t : Term sig) (pure : T.Pure t) : ∃ xs : List (Term sig),
    (∀ x ∈ xs, HasSort x .fresh ∧ Normal T.R x) ∧ Reduces T.R t (T.value xs) ∧
    ∀ k, k ≠ T.zeroClass → (T.bag t).count k = (xs.map classOf).count k := by
  have alien (t : Term sig) (p : T.Pure t) (eq : T.bag t = [classOf t]) :
      ∃ xs : List (Term sig), (∀ x ∈ xs, HasSort x .fresh ∧ Normal T.R x) ∧
      Reduces T.R t (T.value xs) ∧ ∀ k, k ≠ T.zeroClass → (T.bag t).count k = (xs.map classOf).count k := by
    rcases p _ (eq ▸ List.mem_cons_self) with he|⟨a,ha,hn,he⟩
    · exact ⟨[],by simp,.basis (Quotient.exact he),fun k ne => by simp [eq,he,Ne.symm ne]⟩
    · exact ⟨[a],by simpa using And.intro ha hn,.basis (Quotient.exact he.symm),fun k _ => by simp [eq,he]⟩
  induction t with
  | var | atom | free | comm => exact alien _ pure rfl
  | ac f a b ia ib =>
    by_cases he : f = T.f
    · subst f
      obtain ⟨pl,pr⟩ := (T.pure_ac ..).mp pure
      obtain ⟨xs,hx,rx,kx⟩ := ia pl
      obtain ⟨ys,hy,ry,ky⟩ := ib pr
      refine ⟨xs ++ ys,fun x h => (List.mem_append.mp h).elim (hx x) (hy x),
        (Reduces.ac _ rx ry).trans (T.combine_values xs ys (fun x h => (hx x h).1) (fun x h => (hy x h).1)),?_⟩
      intro k ne
      simp only [bag,flatten_ac,List.count_append,List.map_append]
      change (T.bag a).count k + (T.bag b).count k = _
      rw [kx k ne,ky k ne]
    · exact alien _ pure (by simp [bag,Cancellation.flatten,Ne.symm he])

include T in
private theorem count_class [DecidableEq (Term sig)] (xs : List (Term sig)) (t : Term sig)
    (hs : ∀ x ∈ xs, HasSort x .fresh) :
    (xs.map classOf).count (classOf t) = xs.count t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have eq : classOf x = classOf t ↔ x = t := ⟨fun h => T.leaf_eq (hs _ List.mem_cons_self) (Quotient.exact h),
      fun e => congrArg _ e⟩
    simp only [List.map_cons,List.count_cons,beq_iff_eq,eq,ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))]

/-- Any output order with the right parities denotes exactly the normal forms
of the input under the entire active rule table and rewriting modulo B. -/
theorem normalForm_iff [DecidableEq (Term sig)] {a b : Term sig} {xs ys : List (Term sig)}
    (fresh : ∀ t ∈ a::b::xs, HasSort t .fresh) (normal : ∀ t ∈ a::b::xs, Normal T.R t)
    (distinct : ys.Nodup) (same : ∀ t, (a::b::xs).count t % 2 = ys.count t % 2) (u : Term sig) :
    NormalForm T.R (T.value (a::b::xs)) u ↔ EquivB u (T.value ys) := by
  have subset (t : Term sig) (ht : t ∈ ys) : t ∈ a::b::xs := by
    have e := same t
    rw [distinct.count_of_mem ht] at e
    apply List.count_pos_iff.mp; omega
  have fy := fun t ht => fresh t (subset t ht)
  have ny := fun t ht => normal t (subset t ht)
  constructor
  · intro nf
    have kept := T.reduces_kept nf.1 (T.value_pure _ fresh normal)
    obtain ⟨zs,hz,red,counts⟩ := T.strip u kept.1
    refine normal_reduces_equiv (red.trans (T.reduces_parity (fun x h => (hz x h).1) distinct ?_)) nf.2.1
    intro t
    by_cases ht : t ∈ zs ∨ t ∈ ys
    · have hsort : HasSort t .fresh := ht.elim (fun h => (hz t h).1) (fy t)
      have ne := T.not_zero hsort
      have eq := kept.2 (classOf t) ne
      rw [counts _ ne, value, T.fold_bag _ _ fresh, T.count_class _ _ fresh,
        T.count_class _ _ (fun x h => (hz x h).1)] at eq
      exact eq.symm.trans (same t)
    · have h := not_or.mp ht
      simp [List.count_eq_zero.mpr h.1,List.count_eq_zero.mpr h.2]
  · intro eq
    refine ⟨(T.reduces_parity fresh distinct same).trans (.basis eq.symm),
      (normal_equiv _ eq).mpr (T.value_normal _ fy ny distinct),?_⟩
    intro s h
    have typed := T.value_msg ys fy
    have transport := SortClash.check_equiv eq.symm .msg ▸ Term.checkSort_complete typed
    exact HasSort.widen (Term.checkSort_sound _ _ transport) (T.fSort ▸ Term.rootSort_le h)

end
end Tamarin.Rewriting.FreshXor.Flat.Table
