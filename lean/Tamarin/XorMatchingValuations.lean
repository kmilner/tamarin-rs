import Tamarin.XorMatchings

/-! Cancellation choices commute with specializing Fresh inputs. Equal
values can be paired until at most one of each remains, and deleting any
disjoint equal pairs preserves the parity of every value's multiplicity. -/
namespace Tamarin.XorMatchings

private theorem fit_list {α ι : Type} [DecidableEq ι] (val : ι → α) (xs : List ι) (nd : xs.Nodup) :
    ∃ p : ι → ι, (∀ i, p (p i) = i) ∧ (∀ i, i ∉ xs → p i = i) ∧
      (∀ i, val (p i) = val i) ∧
      ∀ i ∈ xs, ∀ j ∈ xs, p i = i → p j = j → val i = val j → i = j := by
  classical
  induction xs with
  | nil => exact ⟨id,fun _ => rfl,fun _ _ => rfl,fun _ => rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨nx,tail⟩ := List.nodup_cons.mp nd
    obtain ⟨p,inv,out,keep,distinct⟩ := ih tail
    have px := out x nx
    by_cases hit : ∃ k ∈ xs, p k = k ∧ val k = val x
    · obtain ⟨k,mem,pk,kx⟩ := hit
      have ne : x ≠ k := by intro e; exact nx (e ▸ mem)
      let q := fun i => if i = x then k else if i = k then x else p i
      refine ⟨q,?_,?_,?_,?_⟩
      · intro i
        by_cases ix : i = x
        · simp [q,ix,ne.symm]
        by_cases ik : i = k
        · simp [q,ik,ne.symm]
        have fx : p i ≠ x := fun eq => ix ((inv i).symm.trans ((congrArg p eq).trans px))
        have fk : p i ≠ k := fun eq => ik ((inv i).symm.trans ((congrArg p eq).trans pk))
        simp [q,ix,ik,fx,fk,inv]
      · intro i absence
        have ix : i ≠ x := fun eq => absence (List.mem_cons.mpr (.inl eq))
        have no : i ∉ xs := fun mem => absence (List.mem_cons_of_mem _ mem)
        have ik : i ≠ k := fun eq => no (eq ▸ mem)
        simp [q,ix,ik,out i no]
      · intro i; by_cases ix : i = x
        · simp [q,ix,kx]
        by_cases ik : i = k <;> simp [q,ix,ik,ne.symm,kx,keep]
      · have old (i) (hi : i ∈ x :: xs) (fixed : q i = i) : i ∈ xs ∧ p i = i := by
          by_cases ix : i = x
          · simp [q,ix,ne.symm] at fixed
          by_cases ik : i = k
          · simp [q,ik,ne,ne.symm] at fixed
          exact ⟨(List.mem_cons.mp hi).resolve_left ix,by simpa [q,ix,ik] using fixed⟩
        intro i hi j hj fi fj eq
        exact distinct i (old i hi fi).1 j (old j hj fj).1 (old i hi fi).2 (old j hj fj).2 eq
    · refine ⟨p,inv,fun i h => out i (fun mem => h (List.mem_cons_of_mem _ mem)),keep,?_⟩
      intro i hi j hj fi fj eq
      rcases List.mem_cons.mp hi with ix|innerI
      · subst i
        rcases List.mem_cons.mp hj with jx|innerJ
        · exact jx.symm
        · exact False.elim (hit ⟨j,innerJ,fj,eq.symm⟩)
      · rcases List.mem_cons.mp hj with jx|innerJ
        · subst j; exact False.elim (hit ⟨i,innerI,fi,eq⟩)
        · exact distinct i innerI j innerJ fi fj eq

theorem exists_fitting {α : Type} {n : Nat} (val : Fin n → α) :
    ∃ p : Fin n → Fin n, (∀ i, p (p i) = i) ∧ (∀ i, val (p i) = val i) ∧
      (((List.finRange n).filter fun i => p i == i).map val).Nodup := by
  obtain ⟨p,inv,_,keep,distinct⟩ := fit_list val (List.finRange n) (List.nodup_finRange n)
  refine ⟨p,inv,keep,List.pairwise_map.mpr ?_⟩
  apply ((List.nodup_finRange n).filter (fun i => p i == i)).imp_of_mem
  intro i j hi hj ne eq
  obtain ⟨hi,fi⟩ := List.mem_filter.mp hi
  obtain ⟨hj,fj⟩ := List.mem_filter.mp hj
  exact ne (distinct i hi j hj (beq_iff_eq.mp fi) (beq_iff_eq.mp fj) eq)

theorem fixed_parity {α : Type} [DecidableEq α] {n : Nat} (val : Fin n → α) (p : Fin n → Fin n)
    (inv : ∀ i, p (p i) = i) (keep : ∀ i, val (p i) = val i) (a : α) :
    ((((List.finRange n).filter fun i => p i == i).map val).count a) % 2 =
      (((List.finRange n).map val).count a) % 2 := by
  let xs := List.finRange n
  let rest := xs.filter fun i => !(p i == i)
  let low := rest.filter fun i => decide (i < p i)
  let high := rest.filter fun i => !decide (i < p i)
  have split := (List.filter_append_perm (fun i => p i == i) xs).map val
  have sides := (List.filter_append_perm (fun i => decide (i < p i)) rest).map val
  have inj {i j : Fin n} (eq : p i = p j) : i = j := (inv i).symm.trans ((congrArg p eq).trans (inv j))
  have nd := (List.nodup_finRange n).filter (fun i => !(p i == i))
  have ndl : (low.map p).Nodup := List.pairwise_map.mpr
    ((nd.filter (fun i => decide (i < p i))).imp (fun h eq => h (inj eq)))
  have swap : (low.map p).Perm high := by
    apply (List.perm_ext_iff_of_nodup ndl (nd.filter (fun i => !decide (i < p i)))).mpr
    intro i
    simp only [low,rest,xs,List.mem_map,List.mem_filter,List.mem_finRange,true_and,
      Bool.not_eq_true',beq_eq_false_iff_ne,decide_eq_true_eq,decide_eq_false_iff_not]
    constructor
    · rintro ⟨j,⟨_,lt⟩,rfl⟩; rw [inv]
      exact ⟨fun e => Nat.ne_of_lt lt (congrArg Fin.val e),fun e => Nat.lt_asymm lt e⟩
    · rintro ⟨ne,le⟩
      have gt : p i < i := by
        by_cases h : (p i).val = i.val
        · exact False.elim (ne (Fin.ext h))
        · change ¬i.val < (p i).val at le
          change (p i).val < i.val; omega
      exact ⟨p i,by rw [inv]; exact ⟨Ne.symm ne,gt⟩,inv i⟩
  have paired : (low.map val).Perm (high.map val) := by
    simpa [List.map_map, Function.comp_def,keep] using swap.map val
  have h := split.count_eq a
  have k := sides.count_eq a
  change ((low ++ high).map val).count a = _ at k
  rw [List.map_append,List.count_append,paired.count_eq a] at k
  change (((xs.filter fun i => p i == i) ++ rest).map val).count a = _ at h
  rw [List.map_append,List.count_append,← k] at h
  change (((xs.filter fun i => p i == i).map val).count a) % 2 = ((xs.map val).count a) % 2
  omega

private theorem map_even {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (xs : List α) (even : ∀ a, xs.count a % 2 = 0) (b : β) : (xs.map f).count b % 2 = 0 := by
  match xs with
  | [] => simp
  | x :: xs =>
    have mem : x ∈ xs := by
      by_cases h : x ∈ xs
      · exact h
      · have := even x; simp [List.count_eq_zero.mpr h] at this
    have perm := (List.perm_cons_erase mem).cons x
    have rest (a : α) : (xs.erase x).count a % 2 = 0 := by
      have e := even a
      rw [perm.count_eq a] at e
      simp only [List.count_cons] at e
      split at e <;> omega
    have ih := map_even f (xs.erase x) rest b
    rw [(perm.map f).count_eq b]
    by_cases h : f x = b <;> simp [h] <;> omega
termination_by xs.length
decreasing_by have := List.length_erase_le (l := xs) (a := x); simp; omega

/-- Renaming can coalesce previously different labels. Equal parities on
the original labels still imply equal parities after an arbitrary map. -/
theorem map_parity {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) {xs ys : List α}
    (same : ∀ a, xs.count a % 2 = ys.count a % 2) (b : β) :
    (xs.map f).count b % 2 = (ys.map f).count b % 2 := by
  have even (a) : (xs ++ ys).count a % 2 = 0 := by rw [List.count_append]; have := same a; omega
  have total := map_even f _ even b
  simp only [List.map_append,List.count_append] at total
  omega

/-- For every valuation, an actual returned row cancels just equal terms,
leaves each remaining value once, and preserves the parity of all inputs. -/
theorem Correct.fitting {run} (candidate : Correct run) {width rows} (ran : run width = some rows)
    {α : Type} [DecidableEq α] (val : Fin width.toNat → α) :
    ∃ row ∈ rows, ∃ p : Fin width.toNat → Fin width.toNat,
      Encodes p row ∧ (∀ i, p (p i) = i) ∧ (∀ i, val (p i) = val i) ∧
      let survivors := ((List.finRange width.toNat).filter fun i => p i == i).map val
      survivors.Nodup ∧ ∀ a, survivors.count a % 2 = ((List.finRange width.toNat).map val).count a % 2 := by
  obtain ⟨p,inv,keep,distinct⟩ := exists_fitting val
  exact ⟨_,((candidate width).2 _ ran _).mpr ⟨p,inv,rfl⟩,p,rfl,inv,keep,distinct,
    fixed_parity val p inv keep⟩

end Tamarin.XorMatchings
