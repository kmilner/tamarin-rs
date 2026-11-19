import Tamarin.MatchPrefilter

/-! A variable has one image across the whole match. Even a compound image
has a leaf. Counting the same leaf in every subject coordinate gives a
necessary condition before enumerating C permutations and AC partitions. -/
namespace Tamarin.Matching.Prefilter
variable {s : Signature}

inductive Leaf (s : Signature) where
  | var (v : Variable)
  | atom (a : s.Atom)
  | constant (f : s.FreeSym)

noncomputable section
open Classical

def Leaf.count (k : Leaf s) : Term s → Nat
  | .var v => if k = .var v then 1 else 0
  | .atom a => if k = .atom a then 1 else 0
  | .free f xs =>
    (if s.arity f = 0 ∧ k = .constant f then 1 else 0) + (List.ofFn fun i => k.count (xs i)).sum
  | .comm _ a b | .ac _ a b => k.count a + k.count b

theorem Leaf.count_equiv (k : Leaf s) {a b : Term s} (eq : EquivB a b) : k.count a = k.count b := by
  induction eq with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free _ _ _ _ ih => simp only [count,ih]
  | comm_congr _ _ _ ih ik | ac_congr _ _ _ ih ik => simp only [count,ih,ik]
  | comm_swap | ac_swap | ac_assoc => simp only [count]; omega

private theorem child_positive {n : Nat} (f : Fin n → Nat) (i : Fin n) (h : 0 < f i) :
    0 < (List.ofFn f).sum := by
  have nz : (List.ofFn f).sum ≠ 0 := fun eq => (Nat.ne_of_gt h)
    ((List.sum_eq_zero_iff_forall_eq_nat.mp eq) _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  omega

theorem Leaf.exists_positive (t : Term s) : ∃ k : Leaf s, 0 < k.count t := by
  induction t with
  | var v => exact ⟨.var v,by simp [count]⟩
  | atom a => exact ⟨.atom a,by simp [count]⟩
  | free f args ih =>
    by_cases zero : s.arity f = 0
    · exact ⟨.constant f,by simp [count,zero]; omega⟩
    · let i : Fin (s.arity f) := ⟨0,Nat.pos_of_ne_zero zero⟩
      obtain ⟨k,pos⟩ := ih i
      exact ⟨k,by
        have positive := child_positive (fun j => k.count (args j)) i pos
        simp only [count]; omega⟩
  | ac _ a _ ih _ | comm _ a _ ih _ =>
    obtain ⟨k,pos⟩ := ih
    exact ⟨k,by simp only [count]; omega⟩

private theorem sum_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih fun i => h i.succ)

theorem Leaf.count_instance (σ : Substitution s) (v : Variable) (k : Leaf s)
    (used : 0 < k.count (σ.image v)) (t : Term s) :
    (Leaf.var v).count t ≤ k.count (σ.apply t) := by
  induction t with
  | var w =>
    by_cases same : v = w
    · subst w; simp only [count,ite_true,Substitution.apply,Term.subst]; omega
    · simp [count,same]
  | atom a => simp [count]
  | free f args ih =>
    change _ ≤ (if _ then 1 else 0) + (List.ofFn fun i => k.count (σ.apply (args i))).sum
    have le := sum_le ih
    simp only [count,reduceCtorEq,and_false,ite_false,Nat.zero_add]; omega
  | ac f a b ih ik | comm f a b ih ik => exact Nat.add_le_add ih ik

/-- One target leaf must dominate all occurrence counts of this source
variable at once. Subject variables and nullary function symbols count as
leaves in their own right. The bound also holds for saturated counters. -/
theorem shared_leaf_of_match {qs : Problem s} {σ : Substitution s} (matched : Matches qs σ)
    (v : Variable) (occurs : ∃ e ∈ qs, 0 < (Leaf.var v).count e.lhs) (limit : Nat) :
    ∃ k : Leaf s, (∃ e ∈ qs, 0 < k.count e.rhs) ∧
      ∀ e ∈ qs, min ((Leaf.var v).count e.lhs) limit ≤ min (k.count e.rhs) limit := by
  obtain ⟨k,pos⟩ := Leaf.exists_positive (σ.image v)
  have le (e) (he : e ∈ qs) := (k.count_equiv (matched e he)) ▸ k.count_instance σ v pos e.lhs
  obtain ⟨e,he,used⟩ := occurs
  exact ⟨k,⟨e,he,Nat.lt_of_lt_of_le used (le e he)⟩,fun q hq => by have := le q hq; omega⟩

theorem target_variable_origin (σ : Substitution s) (w : Variable) (t : Term s)
    (present : 0 < (Leaf.var w).count (σ.apply t)) :
    ∃ v, 0 < (Leaf.var v).count t ∧ 0 < (Leaf.var w).count (σ.image v) := by
  induction t with
  | var v => exact ⟨v,by simp [Leaf.count],present⟩
  | atom a => simp [Substitution.apply,Term.subst,Leaf.count] at present
  | free f xs ih =>
    simp only [Substitution.apply,Term.subst,Leaf.count,reduceCtorEq,and_false,ite_false,Nat.zero_add] at present
    have has : ∃ i, 0 < (Leaf.var w).count (σ.apply (xs i)) := by
      apply Classical.byContradiction
      intro absent
      have zero : (List.ofFn fun i => (Leaf.var w).count (σ.apply (xs i))).sum = 0 :=
        List.sum_eq_zero_iff_forall_eq_nat.mpr fun _ h => by
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
          exact Nat.eq_zero_of_not_pos (fun h => absent ⟨i,h⟩)
      exact (Nat.ne_of_gt present) zero
    obtain ⟨i,hi⟩ := has
    obtain ⟨v,hv,hw⟩ := ih i hi
    exact ⟨v,by simpa [Leaf.count] using child_positive (fun j => (Leaf.var v).count (xs j)) i hv,hw⟩
  | ac _ a b ia ib | comm _ a b ia ib =>
    change 0 < (Leaf.var w).count (σ.apply a) + (Leaf.var w).count (σ.apply b) at present
    by_cases left : 0 < (Leaf.var w).count (σ.apply a)
    · obtain ⟨v,hv,hw⟩ := ia left
      exact ⟨v,by simp only [Leaf.count]; omega,hw⟩
    · obtain ⟨v,hv,hw⟩ := ib (by omega)
      exact ⟨v,by simp only [Leaf.count]; omega,hw⟩

/-- Every rigid subject variable in a particular coordinate must come from
some capture in that coordinate, and its count must dominate that source
variable across the entire simultaneous match. -/
theorem source_for_target_variable {qs : Problem s} {σ : Substitution s} (matched : Matches qs σ)
    {e : Equation s} (he : e ∈ qs) (w : Variable) (present : 0 < (Leaf.var w).count e.rhs) (limit : Nat) :
    ∃ v, 0 < (Leaf.var v).count e.lhs ∧
      ∀ q ∈ qs, min ((Leaf.var v).count q.lhs) limit ≤ min ((Leaf.var w).count q.rhs) limit := by
  rw [← (Leaf.var w).count_equiv (matched e he)] at present
  obtain ⟨v,hv,hw⟩ := target_variable_origin σ w e.lhs present
  refine ⟨v,hv,fun q hq => ?_⟩
  have le := (Leaf.var w).count_instance σ v hw q.lhs
  rw [(Leaf.var w).count_equiv (matched q hq)] at le
  omega

end
end Tamarin.Matching.Prefilter
