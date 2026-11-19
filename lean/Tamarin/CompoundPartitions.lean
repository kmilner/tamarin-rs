import Tamarin.SortedMatchRefinement
import Tamarin.CompoundMatching

/-! The flat partition export can consume IDs for arbitrary ground factors.
Each live ID represents one AC factor, and distinct IDs reflect distinct
B-classes. Every occurrence of a pattern variable uses the same returned row. -/
namespace Tamarin.CompoundPartitions
open Cancellation
variable {sig : Signature}

private theorem classes (f : sig.ACSym) (σ : Substitution sig) (d : UInt64 → Term sig) (ids : List UInt64)
    (ground : ∀ i ∈ ids, (d i).Ground) (factor : ∀ i ∈ ids, flatten f (d i) = [classOf (d i)]) :
    (ids.map d).flatMap (fun t => flatten f (σ.apply t)) = ids.map (fun i => classOf (d i)) := by
  induction ids with
  | nil => rfl
  | cons i is ih =>
    simpa only [List.map_cons, List.flatMap_cons, (ground i (by simp)).apply_eq,
      factor i (by simp), List.cons_append, List.nil_append] using
      congrArg (classOf (d i) :: ·) (ih (fun j hj => ground j (List.mem_cons_of_mem _ hj))
        (fun j hj => factor j (List.mem_cons_of_mem _ hj)))

private theorem semantics (f : sig.ACSym) (σ : Substitution sig) (d : UInt64 → Term sig)
    {n : Nat} (vars : Fin n → Variable) (occ : List (Fin n)) (ids : List UInt64)
    (ground : ∀ i ∈ ids, (d i).Ground) (factor : ∀ i ∈ ids, flatten f (d i) = [classOf (d i)]) :
    ACResidual.Holds f σ (occ.map (fun i => .var (vars i))) (ids.map d) ↔
      (occ.flatMap (fun i => flatten f (σ.image (vars i)))).Perm (ids.map (fun i => classOf (d i))) := by
  rw [ACResidual.holds_iff, classes f σ d ids ground factor, List.flatMap_map]
  rfl

private theorem binding (f : sig.ACSym) (σ : Substitution sig) (v : Variable)
    (d : UInt64 → Term sig) (ids : List UInt64)
    (ground : ∀ i ∈ ids, (d i).Ground) (factor : ∀ i ∈ ids, flatten f (d i) = [classOf (d i)]) :
    (flatten f (σ.image v)).Perm (ids.map (fun i => classOf (d i))) ↔
      ∃ t, ACRepresentation.decode f (ids.map d) = some t ∧ EquivB (σ.image v) t := by
  have h := semantics f σ d (fun _ : Fin 1 => v) [0] ids ground factor
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil] at h
  rw [← h]
  cases ids with
  | nil => simp [ACResidual.Holds, ACRepresentation.decode]
  | cons i is =>
    let t := ACRepresentation.fold f (d i) (is.map d)
    have hg : t.Ground := CompoundMatching.fold_ground f _ _ (by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (show x ∈ (i::is).map d from hx)
      exact ground j hj)
    change EquivB (σ.image v) (σ.apply t) ↔ ∃ u, some t = some u ∧ EquivB (σ.image v) u
    simp [hg.apply_eq]

private theorem perm_flatMap {α β : Type} {l r : α → List β} (h : ∀ i, (l i).Perm (r i))
    (occ : List α) : (occ.flatMap l).Perm (occ.flatMap r) := by
  induction occ with
  | nil => exact .nil
  | cons i is ih => exact (h i).append ih

private theorem word_inverse {α : Type} (decode : UInt64 → α) (ids : List UInt64)
    (reflects : ∀ i ∈ ids, ∀ j ∈ ids, decode i = decode j → i = j) :
    ∃ back : α → UInt64, ∀ i ∈ ids, back (decode i) = i := by
  classical
  let back a := if h : ∃ i ∈ ids, decode i = a then h.choose else 0
  refine ⟨back, ?_⟩
  intro i hi
  have h : ∃ j ∈ ids, decode j = decode i := ⟨i,hi,rfl⟩
  exact (dite_eq_left h).trans (reflects _ h.choose_spec.1 _ hi h.choose_spec.2)

def row (rows : List (List UInt64)) (i : Nat) := rows[i]?.getD []

def Packet (out : SortedMatch.Answers) := out.toList.map (fun a => a.toList.map Array.toList)

/-- Exactness after decoding the actual kernel rows. Ground factors can contain
any internal structure meeting the stated singleton and identity laws. -/
def Correct (flat : SortedMatch.Flat) : Prop :=
  ∀ {s : Signature} (f : s.ACSym) (d : UInt64 → Term s) (n : UInt64)
    (vars : Fin n.toNat → Variable) (occ : List (Fin n.toNat)) (rhs : Array UInt64),
    (∀ i, i ∈ occ) →
    (∀ i ∈ rhs.toList, (d i).Ground) →
    (∀ i ∈ rhs.toList, flatten f (d i) = [classOf (d i)]) →
    (∀ i ∈ rhs.toList, ∀ j ∈ rhs.toList, EquivB (d i) (d j) → i = j) →
    ∀ σ : Substitution s,
      ACResidual.Holds f σ (occ.map (fun i => .var (vars i))) (rhs.toList.map d) ↔
        ∃ rows ∈ Packet (flat n (occ.map (fun i => i.val.toUInt64)).toArray #[] rhs),
          ∀ i, ∃ t, ACRepresentation.decode f ((row rows i.val).map d) = some t ∧ EquivB (σ.image (vars i)) t

theorem correct {flat} (base : SortedMatchRefinement.FlatCorrect flat) : Correct flat := by
  intro s f d n vars occ rhs used ground factor faithful σ
  let cls j := classOf (d j)
  let parts i := flatten f (σ.image (vars i))
  obtain ⟨back,recover⟩ := word_inverse cls rhs.toList (fun i hi j hj eq => faithful i hi j hj (Quotient.exact eq))
  rw [semantics f σ d vars occ rhs.toList ground factor]
  let indices := (occ.map (fun i => i.val.toUInt64)).toArray
  have exactRows (rows : List (List UInt64)) :
      rows ∈ Packet (flat n indices #[] rhs) ↔
      rows.length = n.toNat ∧ (∀ r ∈ rows, r ≠ [] ∧ List.Sublist r rhs.toList) ∧
        (FlatMatchSearch.expand rows (occ.map Fin.val)).Perm rhs.toList := by
    have decodeIndex (i : Fin n.toNat) : i.val.toUInt64.toNat = i.val :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt n.toNat_lt)
    simpa [Packet,indices,List.map_map,Function.comp_def,decodeIndex] using base n indices #[] rhs rows
  constructor
  · intro h
    have each (i : Fin n.toNat) : ∃ r, List.Sublist r rhs.toList ∧ r ≠ [] ∧ (parts i).Perm (r.map cls) := by
      have sub : List.Sublist (parts i) (occ.flatMap parts) := FlatMatching.part_sublist parts (used i)
      obtain ⟨ys,perm,sub⟩ := List.exists_perm_sublist sub h
      obtain ⟨r,hr,rfl⟩ := List.sublist_map_iff.mp sub
      refine ⟨r,hr,fun nil => ?_,perm.symm⟩
      subst r
      have empty : parts i = [] := perm.symm.eq_nil
      have folded := fold_flatten f (σ.image (vars i))
      change fold f (parts i) = _ at folded
      rw [empty] at folded
      cases folded
    let rs i := (each i).choose
    have hr i := (each i).choose_spec
    have full : ((occ.flatMap rs).map cls).Perm (rhs.toList.map cls) := by
      simpa [List.map_flatMap] using (perm_flatMap (fun i => (hr i).2.2) occ).symm.trans h
    have unmap (xs : List UInt64) (sub : xs ⊆ rhs.toList) : (xs.map cls).map back = xs := by
      rw [List.map_map]
      exact (List.map_congr_left (g := id) (fun i hi => recover i (sub hi))).trans (List.map_id _)
    have numeric : (occ.flatMap rs).Perm rhs.toList := by
      have inside : occ.flatMap rs ⊆ rhs.toList := by
        intro j hj
        obtain ⟨i,_,hr'⟩ := List.mem_flatMap.mp hj
        exact (hr i).1.subset hr'
      simpa only [unmap _ inside, unmap _ (fun _ hi => hi)] using full.map back
    refine ⟨List.ofFn rs,(exactRows _).mpr ⟨List.length_ofFn,?_,?_⟩,?_⟩
    · intro r hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      exact ⟨(hr i).2.1,(hr i).1⟩
    · simpa [FlatMatchSearch.expand,List.flatMap_map,List.getElem?_ofFn] using numeric
    · intro i
      have b := (binding f σ (vars i) d (rs i) (fun j hj => ground j ((hr i).1.subset hj))
        (fun j hj => factor j ((hr i).1.subset hj))).mp (hr i).2.2
      simpa [row,List.getElem?_ofFn] using b
  · rintro ⟨rows,hm,images⟩
    obtain ⟨len,sub,perm⟩ := (exactRows _).mp hm
    have each (i : Fin n.toNat) : (parts i).Perm ((row rows i.val).map cls) := by
      have live := (sub _ (List.getElem_mem (l := rows) (n := i.val) (by omega))).2
      have sub' : row rows i.val ⊆ rhs.toList := by
        simpa [row,List.getElem?_eq_getElem (show i.val < rows.length by omega)] using live.subset
      exact (binding _ _ _ _ _ (fun j hj => ground j (sub' hj)) (fun j hj => factor j (sub' hj))).mpr (images i)
    apply (perm_flatMap each occ).trans
    simpa [FlatMatchSearch.expand,List.flatMap_map,List.map_flatMap,row] using perm.map cls

/-- The caller interns closed free terms by structural identity and checks the
sort of each decoded image. Every genuine match passes that check, including
when several occurrences share the same narrower-sort variable. -/
theorem Correct.freeGround {flat} (ok : Correct flat)
    (f : sig.ACSym) (d : UInt64 → Term sig) (n : UInt64) (vars : Fin n.toNat → Variable)
    (occ : List (Fin n.toNat)) (rhs : Array UInt64) (used : ∀ i, i ∈ occ)
    (closed : ∀ i ∈ rhs.toList, CompoundMatching.FreeGround (d i))
    (ids : ∀ i ∈ rhs.toList, ∀ j ∈ rhs.toList, d i = d j → i = j) (σ : Substitution sig) :
    ACResidual.Holds f σ (occ.map (fun i => .var (vars i))) (rhs.toList.map d) ↔
      ∃ rows ∈ Packet (flat n (occ.map (fun i => i.val.toUInt64)).toArray #[] rhs),
        ∀ i, ∃ t, ACRepresentation.decode f ((row rows i.val).map d) = some t ∧
          Subsort t.rootSort (vars i).sort ∧ EquivB (σ.image (vars i)) t := by
  rw [ok f d n vars occ rhs used (fun i hi => (closed i hi).ground)
    (fun i hi => (closed i hi).factor f) (fun i hi j hj eq => ids i hi j hj ((closed i hi).rigid _ eq)) σ]
  constructor
  · rintro ⟨rows,mem,read⟩
    refine ⟨rows,mem,fun i => ?_⟩
    obtain ⟨t, decoded, same⟩ := read i
    exact ⟨t,decoded,Term.rootSort_equiv same ▸ Term.rootSort_le (σ.sorted _),same⟩
  · rintro ⟨rows,mem,read⟩
    refine ⟨rows,mem,fun i => ?_⟩
    obtain ⟨t, decoded, _, same⟩ := read i
    exact ⟨t,decoded,same⟩

end Tamarin.CompoundPartitions
