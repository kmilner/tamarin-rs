import TamarinRuntime.FlatMatch
import Tamarin.WordCodec

namespace Tamarin.FlatMatchSearch
variable {α : Type}

theorem mem_sublists (xs ys : List α) : xs ∈ sublists ys ↔ List.Sublist xs ys := by
  induction ys generalizing xs with
  | nil => simp [sublists]
  | cons y ys ih =>
    constructor
    · intro h
      simp only [sublists, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨zs, hz, rfl⟩
      · exact (ih _).mp h |>.cons y
      · exact (ih _).mp hz |>.cons_cons y
    · intro h
      cases h with
      | cons _ h => exact List.mem_append_left _ ((ih _).mpr h)
      | cons_cons _ h => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, (ih _).mpr h, rfl⟩)

theorem mem_choices (rhs : List α) (n : Nat) (rows : List (List α)) :
    rows ∈ choices rhs n ↔ rows.length = n ∧ ∀ row ∈ rows, row ≠ [] ∧ List.Sublist row rhs := by
  induction n generalizing rows with
  | zero => cases rows <;> simp [choices]
  | succ n ih =>
    cases rows with
    | nil => simp [choices]
    | cons row rows =>
      simp only [choices, List.mem_flatMap, List.mem_filter, Bool.not_eq_true',
        List.isEmpty_eq_false_iff, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨r, ⟨hr, hn⟩, rs, hrs, he, hes⟩
        subst r; subst rs
        obtain ⟨hl, hrows⟩ := (ih _).mp hrs
        exact ⟨by simp [hl], by simpa using And.intro ⟨hn, (mem_sublists _ _).mp hr⟩ hrows⟩
      · rintro ⟨hl, hh⟩
        have hrow := hh row (by simp)
        refine ⟨row, ⟨(mem_sublists _ _).mpr hrow.2, hrow.1⟩, rows, ?_, rfl, rfl⟩
        exact (ih _).mpr ⟨by simpa using hl, fun r hr => hh r (by simp [hr])⟩

theorem mem_solve [DecidableEq α] (n : Nat) (occurrences : List Nat)
    (tail rhs : List α) (rows : List (List α)) : rows ∈ solve n occurrences tail rhs ↔
    rows.length = n ∧ (∀ row ∈ rows, row ≠ [] ∧ List.Sublist row rhs) ∧
      (expand rows occurrences ++ tail).Perm rhs := by
  simp only [solve, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq, mem_choices, and_assoc]

theorem sublists_map {β : Type} (f : α → β) (xs : List α) :
    sublists (xs.map f) = (sublists xs).map (List.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sublists, ih, List.map_append, List.map_map, Function.comp_def]

theorem choices_map {β : Type} (f : α → β) (rhs : List α) (n : Nat) :
    choices (rhs.map f) n = (choices rhs n).map (List.map (List.map f)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [choices, sublists_map, ih, List.filter_map, List.map_flatMap,
      List.flatMap_map, List.map_map, Function.comp_def]

theorem expand_map {β : Type} (f : α → β) (rows : List (List α)) (occ : List Nat) :
    expand (rows.map (List.map f)) occ = (expand rows occ).map f := by
  simp only [expand, List.map_flatMap]
  have he : (fun i : Nat => (rows.map (List.map f))[i]?.getD []) =
      (fun i => (rows[i]?.getD []).map f) := by
    funext i
    simp only [List.getElem?_map]
    cases rows[i]? <;> rfl
  rw [he]

/-- Every atom in an expanded assignment came from one of its rows.
Out-of-range occurrence IDs expand to the empty list. -/
private theorem mem_expanded {rows : List (List α)} {occ : List Nat} {a : α}
    (h : a ∈ expand rows occ) : ∃ row ∈ rows, a ∈ row := by
  obtain ⟨i, _, ha⟩ := List.mem_flatMap.mp h
  cases he : rows[i]? with
  | none => simp [he] at ha
  | some row => exact ⟨row, List.mem_of_getElem? he, by simpa [he] using ha⟩

/-- A request-local decoder can alias unused words. Only IDs present in the
subject or the literal tail need to round-trip for this request. -/
theorem mem_solve_map {β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (encode : β → Option α) (n : Nat) (occ : List Nat)
    (tail rhs : List α) (live : ∀ a ∈ tail ++ rhs, encode (f a) = some a)
    (mapped : List (List β)) :
    mapped ∈ solve n occ (tail.map f) (rhs.map f) ↔
      ∃ rows ∈ solve n occ tail rhs, mapped = rows.map (List.map f) := by
  simp only [solve, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq, choices_map, List.mem_map]
  constructor
  · rintro ⟨⟨rows, hr, rfl⟩, hp⟩
    refine ⟨rows, ⟨hr, ?_⟩, rfl⟩
    rw [expand_map, ← List.map_append] at hp
    have source (a) (ha : a ∈ expand rows occ ++ tail) : a ∈ tail ++ rhs := by
      rcases List.mem_append.mp ha with he | ht
      · obtain ⟨row, hrow, ha⟩ := mem_expanded he
        exact List.mem_append_right _ ((((mem_choices _ _ _).mp hr).2 row hrow).2.subset ha)
      · exact List.mem_append_left _ ht
    simpa only [recover_words f encode _ (fun a h => live a (source a h)),
      recover_words f encode rhs (fun a h => live a (List.mem_append_right _ h))]
      using hp.filterMap encode
  · rintro ⟨rows, ⟨hr, hp⟩, rfl⟩
    refine ⟨⟨rows, hr, rfl⟩, ?_⟩
    simpa [expand_map, List.map_append] using hp.map f

end Tamarin.FlatMatchSearch
