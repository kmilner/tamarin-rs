import TamarinRuntime
import Tamarin.BackendContract
import Tamarin.FlatAC
import Tamarin.MultisetDifference
import Tamarin.FlatACVariable
import Tamarin.DifferenceFailure
import Tamarin.MultisetDifferenceTR

namespace Tamarin.Executable

private theorem atomLE_trans (a b c : UInt64) : atomLE a b → atomLE b c → atomLE a c := by
  simp only [atomLE, decide_eq_true_eq]
  exact UInt64.le_trans

private theorem atomLE_total (a b : UInt64) : atomLE a b || atomLE b a := by
  simp only [Bool.or_eq_true, atomLE, decide_eq_true_eq]
  exact UInt64.le_total a b

theorem difference_sound (tail rhs rest : List UInt64)
    (h : difference tail rhs = some rest) : rhs.Perm (rest ++ tail) := by
  have hs := subtractSorted_sound _ _ _
    (show subtractSorted (tail.mergeSort atomLE) (rhs.mergeSort atomLE) = some rest from
      by simpa only [difference, subtractSortedTR_eq] using h)
  exact ((List.mergeSort_perm rhs atomLE).symm.trans
    (hs.symm.trans ((List.mergeSort_perm tail atomLE).append_right rest))).trans
      List.perm_append_comm

theorem difference_failure (tail rhs : List UInt64)
    (h : difference tail rhs = none) : ∃ a, rhs.count a < tail.count a := by
  have ht : (tail.mergeSort atomLE).Pairwise (fun a b => a ≤ b) := by
    simpa only [atomLE, decide_eq_true_eq] using
      List.pairwise_mergeSort atomLE_trans atomLE_total tail
  have hr : (rhs.mergeSort atomLE).Pairwise (fun a b => a ≤ b) := by
    simpa only [atomLE, decide_eq_true_eq] using
      List.pairwise_mergeSort atomLE_trans atomLE_total rhs
  obtain ⟨a, ha⟩ := subtractSorted_failure _ _ ht hr
    (show subtractSorted (tail.mergeSort atomLE) (rhs.mergeSort atomLE) = none from
      by simpa only [difference, subtractSortedTR_eq] using h)
  exact ⟨a, by simpa only [(List.mergeSort_perm rhs atomLE).count_eq,
    (List.mergeSort_perm tail atomLE).count_eq] using ha⟩

/-- Every supported one-variable query completes; `unsupported` is reserved
for the explicitly excluded empty-product inputs. -/
theorem residual_completes (tail rhs : List UInt64) (ht : tail ≠ []) (hr : rhs ≠ []) :
    residual tail rhs = [1] ∨ ∃ rest, rest ≠ [] ∧ residual tail rhs = 2 :: rest := by
  unfold residual
  simp only [List.isEmpty_eq_false_iff.mpr ht, List.isEmpty_eq_false_iff.mpr hr,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases difference tail rhs with
  | none => exact Or.inl rfl
  | some rest =>
    cases rest with
    | nil => exact Or.inl rfl
    | cons a rest => exact Or.inr ⟨a :: rest, by simp, rfl⟩

theorem residual_success (tail rhs rest : List UInt64)
    (h : residual tail rhs = 2 :: rest) :
    tail ≠ [] ∧ rhs ≠ [] ∧ rest ≠ [] ∧ rhs.Perm (rest ++ tail) := by
  unfold residual at h
  split at h
  · simp at h
  · next hnonempty =>
    have ht : tail ≠ [] := by intro ht; subst tail; simp at hnonempty
    have hr : rhs ≠ [] := by intro hr; subst rhs; simp at hnonempty
    cases hd : difference tail rhs with
    | none => simp [hd] at h
    | some r =>
      cases r with
      | nil => simp [hd] at h
      | cons a r =>
        simp only [hd, List.cons.injEq, true_and] at h
        subst rest
        exact ⟨ht, hr, by simp, difference_sound tail rhs _ hd⟩

/-- Completeness for the exact binding returned by the native residual
function, after a faithful atom decoding and the adapter's sort check. -/
theorem residual_complete {sig : Signature}
    (decode : UInt64 → sig.Atom) (v : Variable) (f : sig.ACSym)
    (tail rhs rest : List UInt64) (h : residual tail rhs = 2 :: rest)
    (hs : HasSort (FlatAC.term f (rest.map decode)) v.sort) :
    CompleteSet (FlatAC.variableProblem v f (tail.map decode) (rhs.map decode))
      [Substitution.binding v (FlatAC.term f (rest.map decode)) hs] := by
  obtain ⟨ht, hr, he, hp⟩ := residual_success tail rhs rest h
  apply FlatAC.variable_complete_difference v f _ _ _
    (by simpa using ht) (by simpa using hr) (by simpa using he) _ hs
  simpa only [List.map_append] using hp.map decode

theorem count_decode {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (a : UInt64) (xs : List UInt64) (ha : encode (decode a) = some a)
    (live : ∀ b ∈ xs, encode (decode b) = some b) :
    (xs.map decode).count (decode a) = xs.count a := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have he : decode b = decode a ↔ b = a := by
      constructor
      · intro h; exact Option.some.inj ((live b (by simp)).symm.trans ((congrArg encode h).trans ha))
      · intro h; exact congrArg decode h
    simp [List.count_cons, ih (fun c hc => live c (by simp [hc])), BEq.beq, he]

theorem residual_empty_complete {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (v : Variable) (f : sig.ACSym) (tail rhs : List UInt64)
    (live : ∀ a ∈ tail ++ rhs, encode (decode a) = some a) (h : residual tail rhs = [1]) :
    CompleteSet (FlatAC.variableProblem v f (tail.map decode) (rhs.map decode)) [] := by
  unfold residual at h
  split at h
  · simp at h
  · next hnonempty =>
    have ht : tail ≠ [] := by intro ht; subst tail; simp at hnonempty
    have hr : rhs ≠ [] := by intro hr; subst rhs; simp at hnonempty
    cases hd : difference tail rhs with
    | none =>
      obtain ⟨a, ha⟩ := difference_failure tail rhs hd
      apply FlatAC.variable_missing_atom v f _ _ (by simpa using ht) (by simpa using hr)
        (decode a)
      have hmem : a ∈ tail := List.count_pos_iff.mp (by omega)
      have hl := live a (List.mem_append_left _ hmem)
      rwa [count_decode decode encode a _ hl (fun b hb => live b (List.mem_append_right _ hb)),
        count_decode decode encode a _ hl (fun b hb => live b (List.mem_append_left _ hb))]
    | some r =>
      cases r with
      | nil =>
        have hp : rhs.Perm tail := by simpa using difference_sound tail rhs [] hd
        exact FlatAC.variable_empty_difference v f _ _
          (by simpa using ht) (by simpa using hr) (hp.map decode)
      | cons a r => simp [hd] at h

theorem sameMultiset_iff (xs ys : List UInt64) : sameMultiset xs ys ↔ xs.Perm ys := by
  simp only [sameMultiset, beq_iff_eq]
  constructor
  · intro h
    exact (List.mergeSort_perm xs atomLE).symm.trans
      ((List.Perm.of_eq h).trans (List.mergeSort_perm ys atomLE))
  · intro h
    apply List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => UInt64.le_antisymm
        (of_decide_eq_true hab) (of_decide_eq_true hba))
      (List.pairwise_mergeSort atomLE_trans atomLE_total xs)
      (List.pairwise_mergeSort atomLE_trans atomLE_total ys)
    exact (List.mergeSort_perm xs atomLE).trans (h.trans (List.mergeSort_perm ys atomLE).symm)

theorem classify_completes (xs ys : List UInt64) (hx : xs ≠ []) (hy : ys ≠ []) :
    classify xs ys = 1 ∨ classify xs ys = 2 := by
  unfold classify
  simp only [List.isEmpty_eq_false_iff.mpr hx, List.isEmpty_eq_false_iff.mpr hy,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The executable ground kernel satisfies the complete-set contract on its
supported inputs. Unsupported inputs have explicit, sound empty partials. -/
theorem classify_correct {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (f : sig.ACSym) (xs ys : List UInt64)
    (live : ∀ a ∈ xs ++ ys, encode (decode a) = some a) :
    (decodeStatus (sig := sig) (classify xs ys)).Correct
      (FlatAC.problem f (xs.map decode) (ys.map decode)) := by
  by_cases hx : xs = []
  · subst xs; simp [classify, decodeStatus, Outcome.Correct, Sound]
  by_cases hy : ys = []
  · subst ys; simp [classify, decodeStatus, Outcome.Correct, Sound]
  have hx' : xs.map decode ≠ [] := by simpa using hx
  have hy' : ys.map decode ≠ [] := by simpa using hy
  by_cases hp : xs.Perm ys
  · have hs := (sameMultiset_iff xs ys).mpr hp
    have hc : classify xs ys = 2 := by simp [classify, hx, hy, hs]
    rw [hc]
    exact FlatAC.complete_identity f _ _ hx' hy' (hp.map decode)
  · have hs : sameMultiset xs ys = false := by
      cases h : sameMultiset xs ys
      · rfl
      · exact False.elim (hp ((sameMultiset_iff xs ys).mp h))
    have hc : classify xs ys = 1 := by simp [classify, hx, hy, hs]
    rw [hc]
    apply FlatAC.complete_empty f _ _ hx' hy'
    intro hm
    apply hp
    simpa only [recover_words decode encode xs (fun a h => live a (List.mem_append_left _ h)),
      recover_words decode encode ys (fun a h => live a (List.mem_append_right _ h))]
      using hm.filterMap encode

/-! These obligations name the actual exported definitions. Keeping proofs
only about `classify`/`residual` would let an edit to an ABI wrapper disconnect
the compiled entry point from its proof without breaking the build. -/

theorem flatAC_empty_inputs (lhs rhs : Array UInt64) (h : lhs = #[] ∨ rhs = #[]) :
    flatACEqual lhs rhs = 0 ∧ flatACResidual lhs rhs = #[0] := by
  rcases h with rfl | rfl <;>
    simp [flatACEqual, flatACResidual, RuntimeCandidate.backend, classify, residual]

theorem flatACEqual_correct {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (f : sig.ACSym) (xs ys : Array UInt64)
    (live : ∀ a ∈ xs.toList ++ ys.toList, encode (decode a) = some a) :
    (decodeStatus (sig := sig) (flatACEqual xs ys)).Correct
      (FlatAC.problem f (xs.toList.map decode) (ys.toList.map decode)) := by
  exact classify_correct decode encode f xs.toList ys.toList live

theorem flatACEqual_completes (xs ys : Array UInt64)
    (hx : xs.toList ≠ []) (hy : ys.toList ≠ []) :
    flatACEqual xs ys = 1 ∨ flatACEqual xs ys = 2 := by
  exact classify_completes xs.toList ys.toList hx hy

theorem flatACResidual_complete {sig : Signature}
    (decode : UInt64 → sig.Atom) (v : Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64)
    (h : flatACResidual tail rhs = (2 :: rest).toArray)
    (hs : HasSort (FlatAC.term f (rest.map decode)) v.sort) :
    CompleteSet
      (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode))
      [Substitution.binding v (FlatAC.term f (rest.map decode)) hs] := by
  apply residual_complete decode v f tail.toList rhs.toList rest _ hs
  simpa only [flatACResidual, RuntimeCandidate.backend, List.toList_toArray] using congrArg Array.toList h

theorem flatACResidual_empty_complete {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (v : Variable) (f : sig.ACSym) (tail rhs : Array UInt64)
    (live : ∀ a ∈ tail.toList ++ rhs.toList, encode (decode a) = some a) (h : flatACResidual tail rhs = #[1]) :
    CompleteSet
      (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode)) [] := by
  apply residual_empty_complete decode encode v f tail.toList rhs.toList live
  simpa only [flatACResidual, RuntimeCandidate.backend, List.toList_toArray] using
    congrArg Array.toList h

theorem flatACResidual_completes (tail rhs : Array UInt64)
    (ht : tail.toList ≠ []) (hr : rhs.toList ≠ []) :
    flatACResidual tail rhs = #[1] ∨
      ∃ rest : List UInt64, rest ≠ [] ∧ flatACResidual tail rhs = (2 :: rest).toArray := by
  rcases residual_completes tail.toList rhs.toList ht hr with h | ⟨rest, hn, h⟩
  · exact Or.inl (congrArg List.toArray h)
  · exact Or.inr ⟨rest, hn, congrArg List.toArray h⟩

end Tamarin.Executable
