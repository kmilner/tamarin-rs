import Tamarin.BinaryXorFactors

namespace Tamarin.Rewriting.BinaryXor
open Cancellation ACRepresentation
variable {sig : Signature} (T : Table sig)
noncomputable section
open Classical

def assemble (xs : List (Class sig)) := T.value (xs.map rep)

theorem value_typed (xs : List (Term sig)) (h : ∀ x ∈ xs, HasSort x .msg) : HasSort (T.value xs) .msg := by
  cases xs with
  | nil => exact T.zeroSort
  | cons a as =>
    rw [← T.fSort]
    exact fold_hasSort T.f a as (T.fSort ▸ h _ List.mem_cons_self)
      (fun t ht => T.fSort ▸ h _ (List.mem_cons_of_mem _ ht))

theorem assemble_typed {xs : List (Class sig)} (f : ∀ k ∈ xs, Fact T k) : HasSort (assemble T xs) .msg := by
  apply value_typed
  rintro _ h
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h; exact (f k hk).1.1

theorem fold_classes {a : Term sig} {xs : List (Term sig)} (h : ∀ t ∈ a::xs, T.bag t = [classOf t]) :
    T.bag (ACRepresentation.fold T.f a xs) = (a::xs).map classOf := by
  induction xs generalizing a with
  | nil => exact h a List.mem_cons_self
  | cons b bs ih =>
    change T.bag (.ac T.f a _) = _
    rw [FreshXor.Flat.Table.bag,flatten_ac]
    change T.bag a ++ T.bag (ACRepresentation.fold T.f b bs) = _
    rw [h _ List.mem_cons_self,ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    rfl

theorem assemble_bag {xs : List (Class sig)} (f : ∀ k ∈ xs, Fact T k) :
    T.bag (assemble T xs) = if xs.isEmpty then [T.zeroClass] else xs := by
  cases xs with
  | nil => exact T.bag_zero
  | cons a as =>
    change T.bag (ACRepresentation.fold T.f (rep a) (as.map rep)) = a :: as
    rw [fold_classes T]
    · simp [List.map_map,Function.comp_def,rep_key]
    · intro x hx
      change x ∈ (a::as).map rep at hx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
      rw [rep_key]; exact (f k hk).2

theorem normal_clean {t : Term sig} (nd : (T.bag t).Nodup) (nz : T.zeroClass ∉ T.bag t)
    (atoms : ∀ k ∈ T.bag t, Fact T k) : Normal T.R t := by
  apply DHProduct.subgroup_normal T.f t
  · intro x hx
    have hk : classOf x ∈ T.bag t := by rw [FreshXor.Flat.Table.bag,DHProduct.classes]; exact List.mem_map_of_mem hx
    exact (normal_equiv _ (Quotient.exact (rep_key (classOf x)))).mp (atoms _ hk).1.2
  · intro p q hp sub step
    obtain ⟨rs,perm⟩ := sub
    have counts (k) : (T.bag p).count k ≤ 1 := by
      have h := perm.count_eq k
      rw [List.count_append] at h
      have l := List.nodup_iff_count.mp nd k
      change (T.bag t).count k = (T.bag p).count k + _ at h; omega
    have duplicate (a : Term sig) : ∃ k, 0 < (T.bag a).count k := by
      obtain ⟨k,h⟩ := List.exists_mem_of_ne_nil _ (T.bag_nonempty a)
      exact ⟨k,List.count_pos_iff.mpr h⟩
    rcases T.root_cases hp step with ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
    · obtain ⟨k,h⟩ := duplicate a
      have := counts k; simp only [FreshXor.Flat.Table.bag,flatten_ac,List.count_append] at *; omega
    · apply nz (perm.mem_iff.mpr (List.mem_append_left _ ?_))
      rw [flatten_ac]; change _ ∈ _ ++ T.bag T.zero; rw [T.bag_zero]; simp
    · obtain ⟨k,h⟩ := duplicate a
      have := counts k; simp only [FreshXor.Flat.Table.bag,flatten_ac,List.count_append] at *; omega
    · obtain ⟨k,h⟩ := duplicate a
      have := counts k; simp only [FreshXor.Flat.Table.bag,flatten_ac,List.count_append] at *; omega

theorem assemble_good {xs : List (Class sig)} (f : ∀ k ∈ xs, Fact T k) (nd : xs.Nodup) (nz : T.zeroClass ∉ xs) :
    Good T (assemble T xs) := by
  refine ⟨assemble_typed T f,?_⟩
  cases xs with
  | nil => exact T.toTable.zero_normal
  | cons a as =>
    have eq : T.bag (assemble T (a::as)) = a::as := assemble_bag T f
    apply normal_clean T <;> rwa [eq]

theorem assemble_perm {xs ys : List (Class sig)} (p : xs.Perm ys) :
    EquivB (assemble T xs) (assemble T ys) := T.value_perm (p.map rep)

private theorem drop_zero (xs : List (Class sig)) (f : ∀ k ∈ xs, Fact T k) :
    Reduces T.R (assemble T (T.zeroClass::xs)) (assemble T xs) := by
  have e : EquivB (rep T.zeroClass) T.zero := Quotient.exact (rep_key _)
  cases xs with
  | nil => exact .basis e
  | cons a as => exact .step ⟨_,_,(EquivB.ac_congr _ e (.refl _)).trans (.ac_swap ..),
      .root (T.unit (assemble_typed T f)),.refl _⟩

private theorem drop_pair {k : Class sig} (xs : List (Class sig)) (g : Fact T k) (f : ∀ j ∈ xs, Fact T j) :
    Reduces T.R (assemble T (k::k::xs)) (assemble T xs) := by
  have red : Reduces T.R (.ac T.f (rep k) (rep k)) T.zero :=
    .step ⟨_,_,.refl _,.root (dup_msg T g.1.1),.refl _⟩
  cases xs with
  | nil => exact red
  | cons a as =>
    exact (Reduces.basis (.symm (.ac_assoc _ _ _ _))).trans ((Reduces.ac _ red (Reduces.basis (.refl _))).trans
      (.step ⟨_,_,.ac_swap _ _ _,.root (T.unit (assemble_typed T f)),.refl _⟩))

/-- Delete unit factors and cancel duplicate classes in any order. -/
theorem reduce_classes {xs ys : List (Class sig)} (f : ∀ k ∈ xs, Fact T k) (nd : ys.Nodup)
    (nz : T.zeroClass ∉ ys) (same : ∀ k, k ≠ T.zeroClass → xs.count k % 2 = ys.count k % 2) :
    Reduces T.R (assemble T xs) (assemble T ys) := by
  by_cases unit : T.zeroClass ∈ xs
  · have perm := List.perm_cons_erase unit
    have facts k (h : k ∈ xs.erase T.zeroClass) := f k (perm.mem_iff.mpr (List.mem_cons_of_mem _ h))
    refine (Reduces.basis (assemble_perm T perm)).trans ((drop_zero T _ facts).trans (reduce_classes facts nd nz ?_))
    intro k ne; have c := perm.count_eq k
    simp [Ne.symm ne] at c
    rw [← c]; exact same k ne
  · by_cases good : xs.Nodup
    · apply Reduces.basis (assemble_perm T (List.perm_iff_count.mpr _))
      intro k
      by_cases e : k = T.zeroClass
      · subst k; rw [List.count_eq_zero.mpr unit,List.count_eq_zero.mpr nz]
      · have h := same k e
        have a := List.nodup_iff_count.mp good k
        have b := List.nodup_iff_count.mp nd k
        omega
    · obtain ⟨k,m⟩ : ∃ k, 2 ≤ xs.count k := by
        apply Classical.byContradiction; intro no
        exact good (List.nodup_iff_count.mpr (fun k => by have bad : ¬ 2 ≤ xs.count k := fun h => no ⟨k,h⟩; omega))
      have present := List.count_pos_iff.mp (show 0 < xs.count k by omega)
      have first := List.perm_cons_erase present
      have count := first.count_eq k
      rw [List.count_cons_self] at count
      have second := List.perm_cons_erase (List.count_pos_iff.mp (show 0 < (xs.erase k).count k by omega))
      have perm := first.trans (second.cons k)
      have facts j (hj : j ∈ (xs.erase k).erase k) := f j (perm.mem_iff.mpr (by simp [hj]))
      refine (Reduces.basis (assemble_perm T perm)).trans
        ((drop_pair T _ (f k present) facts).trans (reduce_classes facts nd nz ?_))
      intro j ne
      have c := perm.count_eq j; have h := same j ne
      by_cases e : k = j
      · subst j; rw [List.count_cons_self,List.count_cons_self] at c; omega
      · rw [List.count_cons_of_ne e,List.count_cons_of_ne e] at c; omega
termination_by xs.length
decreasing_by all_goals have h := perm.length_eq; simp at h; omega

/-- Any width, arbitrary normalized opaque factors, with explicit units
allowed in the input. The output can use any order of the odd B classes. -/
theorem parity_normalForm {t : Term sig} (typed : HasSort t .msg) (root : t.rootSort = .msg)
    (facts : ∀ k ∈ T.bag t, Fact T k) {ys : List (Class sig)} (nd : ys.Nodup)
    (nz : T.zeroClass ∉ ys) (same : ∀ k, k ≠ T.zeroClass → (T.bag t).count k % 2 = ys.count k % 2)
    (u : Term sig) : NormalForm T.R t u ↔ EquivB u (assemble T ys) := by
  have fy (k) (hk : k ∈ ys) : Fact T k := by
    apply facts
    have ne : k ≠ T.zeroClass := fun eq => nz (eq ▸ hk)
    have e := same k ne
    rw [nd.count_of_mem hk] at e
    apply List.count_pos_iff.mp; omega
  have gy := assemble_good T fy nd nz
  have orig : EquivB t (assemble T (T.bag t)) := by
    apply equiv_of_flatten_perm T.f
    change (T.bag t).Perm (T.bag (assemble T (T.bag t)))
    rw [assemble_bag T facts]
    simp [T.bag_nonempty]
  have red := (Reduces.basis orig).trans (reduce_classes T facts nd nz same)
  have pure : T.PureFrom (fun _ => True) t := fun k hk => .inr ⟨rep k,trivial,(facts k hk).1.2,rep_key k⟩
  constructor
  · intro nf
    have p := T.reduces_kept nf.1 pure
    have q := T.reduces_kept red pure
    exact normal_eq T ⟨nf.2.2 _ typed,nf.2.1⟩ gy (fun k ne => (p.2 k ne).symm.trans (q.2 k ne))
  · intro eq
    exact ⟨red.trans (.basis eq.symm),(normal_equiv _ eq).mpr gy.2,
      fun _ h => .widen (sort_equiv eq.symm gy.1) (root ▸ Term.rootSort_le h)⟩

theorem assemble_input {t : Term sig} (gt : Good T t) : EquivB t (assemble T (pieces T t)) := by
  apply equiv_of_flatten_perm T.f
  change (T.bag t).Perm (T.bag (assemble T (pieces T t)))
  rw [assemble_bag T (xs := pieces T t) (fun k hk => fact_of_mem T gt (List.mem_filter.mp hk).1)]
  exact List.Perm.of_eq (bag_of_pieces T gt)

theorem pieces_good {t : Term sig} (gt : Good T t) :
    (pieces T t).Nodup ∧ T.zeroClass ∉ pieces T t ∧ ∀ k ∈ pieces T t, Fact T k := by
  exact ⟨(nodup T gt).filter _,by simp [pieces],fun k hk => fact_of_mem T gt (List.mem_filter.mp hk).1⟩

end
end Tamarin.Rewriting.BinaryXor
