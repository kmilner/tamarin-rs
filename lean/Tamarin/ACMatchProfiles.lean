import Tamarin.OpenMatch

/-! A coordinate with distinct rigid factors determines one owner for every
factor. The owner's multiplicity in every other coordinate must then exactly
equal the multiplicity of that rigid factor there. -/
namespace Tamarin.OpenMatch.Profiles
variable {α β : Type} [DecidableEq α] [DecidableEq β]

private theorem one_owner (images : α → List β) (keys : List α)
    (nd : (keys.flatMap images).Nodup) {a b} (ha : a ∈ keys) (hb : b ∈ images a) :
    ∀ v ∈ keys, (images v).count b = if v = a then 1 else 0 := by
  have dis := (List.perm_cons_erase ha).flatMap_right images
  have parts := List.nodup_append.mp (dis.nodup_iff.mp nd)
  intro v hv
  by_cases eq : v = a
  · subst v; simp [parts.1.count,hb]
  · have off : b ∉ images v := fun mem => parts.2.2 b hb b
        (List.mem_flatMap.mpr ⟨v,(List.mem_erase_of_ne eq).mpr hv,mem⟩) rfl
    simp [eq,List.count_eq_zero.mpr off]

private theorem count_at {images : α → List β} {a b} (ks : List α)
    (owner : ∀ k ∈ ks, (images k).count b = if k = a then 1 else 0) :
    (ks.flatMap images).count b = ks.count a := by
  induction ks with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.count_append,owner x List.mem_cons_self,
      ih (fun v h => owner v (List.mem_cons_of_mem _ h))]
    by_cases e : x = a <;> simp [e,Nat.add_comm]

omit [DecidableEq α] [DecidableEq β] in
private theorem flat_sub {xs ys : List α} (im : α → List β) (h : xs.Sublist ys) :
    (xs.flatMap im).Sublist (ys.flatMap im) := by
  induction h with
  | slnil => exact .slnil
  | cons x _ ih => exact ih.trans (List.sublist_append_right ..)
  | cons_cons x _ ih => exact ih.append_left (im x)

omit [DecidableEq α] [DecidableEq β] in
private theorem total_nonempty (im : α → List β) (ks : List α) (live : ∀ a ∈ ks, im a ≠ []) :
    ks.length ≤ (ks.flatMap im).length := by
  induction ks with
  | nil => simp
  | cons a rest ih =>
    have h := ih fun k hk => live k (List.mem_cons_of_mem _ hk)
    have nz := List.length_pos_iff.mpr (live a List.mem_cons_self)
    simp only [List.length_cons,List.flatMap_cons,List.length_append]; omega

def profile {γ} [DecidableEq γ] (coords : List (List γ)) (item : γ) :=
  coords.map (fun c => c.count item)

/-- Every rejection by the rigid-pivot test contradicts these three facts:
subjects use only pivot factors, every factor has an owner with the same
profile, and each profile has enough factors for its nonempty captures. -/
theorem necessary (keys : List α) (atoms : List β) (rows : List (List α × List β))
    (im : α → List β) (live : ∀ k ∈ keys, im k ≠ []) (nd : atoms.Nodup)
    (pivot : (keys.flatMap im).Perm atoms) (cover : ∀ r ∈ rows, r.1 ⊆ keys)
    (solution : ∀ r ∈ rows, (r.1.flatMap im).Perm r.2) :
    (∀ r ∈ rows, r.2 ⊆ atoms) ∧
    (∀ b ∈ atoms, ∃ a ∈ keys, profile (rows.map Prod.fst) a = profile (rows.map Prod.snd) b) ∧
    ∀ group, (keys.filter (fun a => profile (rows.map Prod.fst) a == group)).length ≤
      (atoms.filter (fun b => profile (rows.map Prod.snd) b == group)).length := by
  have distinct := pivot.nodup_iff.mpr nd
  have agree {a b} (ha : a ∈ keys) (hb : b ∈ im a) :
      profile (rows.map Prod.fst) a = profile (rows.map Prod.snd) b := by
    simp only [profile,List.map_map,Function.comp_def]
    apply List.map_inj_left.mpr; intro row hr
    rw [← (solution row hr).count_eq b, count_at row.1
      (fun k hk => one_owner im keys distinct ha hb k (cover row hr hk))]
  constructor
  · intro row hr b hb
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp ((solution row hr).symm.subset hb)
    exact pivot.subset (List.mem_flatMap.mpr ⟨a,cover row hr ha,mem⟩)
  constructor
  · intro b hb; obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp (pivot.symm.subset hb)
    exact ⟨a,ha,agree ha mem⟩
  · intro group
    let chosen := keys.filter (fun a => profile (rows.map Prod.fst) a == group)
    have sub := flat_sub im (List.filter_sublist (p := fun a => profile (rows.map Prod.fst) a == group) (l := keys))
    apply Nat.le_trans (total_nonempty im chosen (fun a ha => live a (List.mem_filter.mp ha).1))
    apply (distinct.sublist sub).length_le_of_subset
    intro b hb
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp hb
    obtain ⟨used,eq⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr ⟨pivot.subset (List.mem_flatMap.mpr ⟨a,used,mem⟩),by rw [←agree used mem]; exact eq⟩

/-- Flattened rigid-subject matching of one all-variable coordinate supplies
the exact bag equation used by the numeric test, even for compound factors. -/
theorem coordinate {sig : Signature} (f : sig.ACSym) (ks : List Variable) (s : List (Term sig))
    (atoms : ∀ t ∈ s, Cancellation.flatten f t = [Cancellation.classOf t])
    (σ : Substitution sig) (run : Holds f (ks.map Term.var) s σ) :
    (ks.flatMap fun k => Cancellation.flatten f (σ.image k)).Perm (s.map Cancellation.classOf) := by
  have h := (holds_iff ..).mp run
  have flat : s.flatMap (Cancellation.flatten f) = s.map Cancellation.classOf := by
    clear run h
    induction s with
    | nil => rfl
    | cons a as ih => simp [atoms a List.mem_cons_self,ih (fun t ht => atoms t (List.mem_cons_of_mem _ ht))]
  simpa [List.flatMap_map,Substitution.apply,Term.subst,flat] using h

end Tamarin.OpenMatch.Profiles
