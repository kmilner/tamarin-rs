import TamarinRuntime.ACSparsePlane
import Tamarin.ACPlane
import Tamarin.ACGridBudget
import Tamarin.ACCompactBasis

namespace Tamarin.ACBasis
namespace SparsePlane

variable {n : Nat}

private abbrev Before (v w : Vec n) := List.ofFn v < List.ofFn w
private abbrev Ordered (v w : Vec n) := decide (List.ofFn v ≤ List.ofFn w) = true

theorem box_sorted (n : Nat) (lim : Vec n) : (box n lim).Pairwise Before := by
  induction n with
  | zero => simp [box]
  | succ n ih =>
    rw [box,List.pairwise_flatMap]
    constructor
    · intro h _
      apply List.pairwise_map.mpr
      exact (ih _).imp (fun {a b} hab => by simpa [Before,List.ofFn_succ] using hab)
    · apply List.pairwise_lt_range.imp
      intro h k hk _ ha _ hb
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
      simp only [Before,List.ofFn_succ,Fin.cases_zero,Fin.cases_succ]
      exact List.Lex.rel hk

private theorem spikes_sorted {n} (i j : Fin n) (h : j < i) : Before (spike i 1) (spike j 1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp only [Before,List.ofFn_succ,spike,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i),ite_false,ite_true]
        exact List.Lex.rel (by decide : 0 < 1)
      | succ j =>
        have smaller := ih i j (Fin.succ_lt_succ_iff.mp h)
        change List.ofFn (spike i 1) < List.ofFn (spike j 1) at smaller
        simp [Before,List.ofFn_succ,spike,Ne.symm (Fin.succ_ne_zero i),
          Ne.symm (Fin.succ_ne_zero j)]
        exact smaller

private def plane (r : Row n) (lim : Vec n) : List (Vec n) :=
  (balancedBox n lim r.pos r.neg 0 0).filter (fun v => (List.ofFn v).any (0 < ·))

private theorem plane_sorted (r : Row n) (lim : Vec n) : (plane r lim).Pairwise Before := by
  rw [plane,balancedBox_eq _ _ _ _ r.disjoint]
  exact ((box_sorted _ _).sublist (List.filter_sublist)).sublist List.filter_sublist

private theorem mem_plane (r : Row n) (lim v : Vec n) :
    v ∈ plane r lim ↔ (∀ i, v i ≤ lim i) ∧ r.Holds v ∧ ∃ i, 0 < v i := by
  rw [plane,balancedBox_eq _ _ _ _ r.disjoint]
  simp [mem_box,Row.Holds]; grind

private theorem units_sorted (r : Row n) (cap : Nat) : (r.sparseUnits cap).Pairwise Before := by
  apply List.pairwise_map.mpr
  exact ((List.pairwise_reverse.mpr (List.pairwise_lt_finRange n)).sublist
    List.filter_sublist).imp (fun h => spikes_sorted _ _ h)

private def Clear (r : Row n) (c : Vec n) := ∀ i, r.neutralAt i = true → c i = 0
private def UnitAt (r : Row n) (c : Vec n) := ∃ i, r.neutralAt i = true ∧ c = spike i 1
noncomputable def keep (r : Row n) (c : Vec n) : Bool := by
  classical exact decide (Clear r c ∨ UnitAt r c)

private theorem mem_active (r : Row n) (cap : Nat) (c : Vec n) :
    c ∈ r.sparseActive cap ↔ c ∈ r.cappedGenerators cap ∧ Clear r c := by
  change c ∈ plane _ _ ↔ c ∈ plane _ _ ∧ _
  rw [mem_plane,mem_plane]
  constructor
  · rintro ⟨bd,holds,nz⟩
    refine ⟨⟨fun i => ?_,holds,nz⟩,fun i hi => ?_⟩
    · have h := bd i
      by_cases hi : r.neutralAt i <;> simp_all [Row.sparseLimits]
    · simpa [Row.sparseLimits,hi] using bd i
  · rintro ⟨⟨bd,holds,nz⟩,clear⟩
    refine ⟨fun i => ?_,holds,nz⟩
    by_cases hi : r.neutralAt i <;> simp [Row.sparseLimits,hi,clear i,bd i]

private theorem mem_units (r : Row n) (cap : Nat) (c : Vec n) :
    c ∈ r.sparseUnits cap ↔ c ∈ r.cappedGenerators cap ∧ UnitAt r c := by
  change _ ↔ c ∈ plane _ _ ∧ _
  simp only [Row.sparseUnits,List.mem_map,List.mem_filter,List.mem_reverse,List.mem_finRange,
    true_and,Bool.and_eq_true,decide_eq_true_eq,mem_plane]
  constructor
  · rintro ⟨i,⟨hi,bd⟩,rfl⟩
    have ⟨p,q⟩ : r.pos i = 0 ∧ r.neg i = 0 := by simpa [Row.neutralAt] using hi
    refine ⟨⟨fun j => ?_,by simp [Row.Holds,dot_spike,p,q],i,by simp [spike]⟩,i,hi,rfl⟩
    by_cases eq : j = i <;> simp_all [spike] <;> omega
  · rintro ⟨⟨bd,_⟩,i,hi,rfl⟩
    exact ⟨i,⟨hi,by have h := bd i; simp [spike] at h; omega⟩,rfl⟩

private theorem strict_nodup {vs : List (Vec n)} (h : vs.Pairwise Before) : vs.Nodup := by
  exact h.imp fun {a b} ab eq => by subst b; exact (List.lt_irrefl _) ab

private theorem weak_sorted {vs : List (Vec n)} (h : vs.Pairwise Before) : vs.Pairwise Ordered :=
  h.imp fun ab => decide_eq_true (List.le_of_lt ab)

private theorem ofFn_inj {a b : Vec n} (h : List.ofFn a = List.ofFn b) : a = b := by
  funext i
  have he := congrArg (fun l : List Nat => l[i.val]?) h
  simpa [List.getElem?_ofFn,i.isLt] using he

theorem filtered (r : Row n) (cap : Nat) :
    r.sparseGenerators cap = (r.cappedGenerators cap).filter (keep r) := by
  classical
  have merge : r.sparseGenerators cap =
      (r.sparseActive cap).merge (r.sparseUnits cap) (fun a b => decide (List.ofFn a ≤ List.ofFn b)) := by
    unfold Row.sparseGenerators; cases r.sparseUnits cap <;> simp
  rw [merge]
  have act : (r.sparseActive cap).Pairwise Before := plane_sorted r _
  have units := units_sorted r cap
  have ref : ((r.cappedGenerators cap).filter (keep r)).Pairwise Before :=
    (plane_sorted r _).sublist List.filter_sublist
  have perm : (r.sparseActive cap ++ r.sparseUnits cap).Perm ((r.cappedGenerators cap).filter (keep r)) := by
    apply (List.perm_ext_iff_of_nodup _ (strict_nodup ref)).mpr
    · intro v
      simp [mem_active,mem_units,keep]; grind
    · refine List.nodup_append.mpr ⟨strict_nodup act,strict_nodup units,?_⟩
      intro a ha _ hb eq
      obtain ⟨i,hi,he⟩ := ((mem_units ..).mp hb).2
      have hz := ((mem_active ..).mp ha).2 i hi
      simp [eq,he,spike] at hz
  apply List.Perm.eq_of_pairwise (le := Ordered)
  · intro a b _ _ ab ba
    exact ofFn_inj (List.le_antisymm (of_decide_eq_true ab) (of_decide_eq_true ba))
  · apply List.pairwise_merge _ _ _ _ (weak_sorted act) (weak_sorted units)
    · intro a b c ab bc
      exact decide_eq_true (List.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))
    · intro a b
      simpa using List.le_total (List.ofFn a) (List.ofFn b)
  · exact weak_sorted ref
  · exact (List.merge_perm_append ..).trans perm

theorem minimize_lift {k n} (r : Row k) (cap : Nat) (g : Fin k → Vec n)
    (live : ∀ j, ∃ i, 0 < g j i) :
    minimize (lift g (r.sparseGenerators cap)) = minimize (lift g (r.cappedGenerators cap)) := by
  classical
  rw [filtered]
  apply minimize_lift_filter _ _ _ live
  intro c hc hk
  have outside : ¬ Clear r c := by
    intro clear
    simp [keep,clear] at hk
  obtain ⟨i,hi,nz⟩ : ∃ i, r.neutralAt i = true ∧ c i ≠ 0 := by
    simpa [Clear] using outside
  have bd := ((mem_plane r (r.cappedLimits cap) c).mp hc).1 i
  have hu : spike i 1 ∈ r.sparseUnits cap := by
    simp only [Row.sparseUnits,List.mem_map,List.mem_filter,List.mem_reverse,List.mem_finRange,
      true_and,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨i,⟨hi,by omega⟩,rfl⟩
  have unit := (mem_units ..).mp hu
  have kept : keep r (spike i 1) = true := by simp [keep,unit.2]
  refine ⟨spike i 1,unit.1,kept,⟨i,by simp [spike]⟩,?_,?_⟩
  · intro j
    by_cases eq : j = i <;> simp [spike,eq]
    omega
  · intro eq
    simp [eq,hk] at kept

theorem length_le (r : Row n) (cap : Nat) :
    (r.sparseGenerators cap).length ≤ (r.cappedGenerators cap).length := by
  rw [filtered]
  exact List.length_filter_le ..

theorem fits_iff (r : Row n) (cap b : Nat) :
    r.sparseFits cap b = true ↔ GridBudget r (r.sparseLimits cap) b := by
  simp [Row.sparseFits,GridBudget,gridSize]

theorem fits_of_capped (r : Row n) {cap b : Nat} (h : r.cappedFits cap b = true) :
    r.sparseFits cap b = true := by
  apply (fits_iff ..).mpr
  apply GridBudget.shrink (hi := r.cappedLimits cap)
  · simpa [Row.cappedFits,GridBudget,gridSize] using h
  · intro i
    by_cases hi : r.neutralAt i <;> simp [Row.sparseLimits,hi]

end SparsePlane
end Tamarin.ACBasis
