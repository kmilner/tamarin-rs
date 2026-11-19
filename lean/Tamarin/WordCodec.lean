import Std

namespace Tamarin

/-- Filtering through a partial inverse recovers a word list when each of its
own IDs round-trips. No condition on the rest of the word space is needed. -/
theorem recover_words {α β : Type} (decode : α → β) (encode : β → Option α)
    (xs : List α) (live : ∀ x ∈ xs, encode (decode x) = some x) :
    (xs.map decode).filterMap encode = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [live a (by simp), ih (fun b hb => live b (by simp [hb]))]

end Tamarin
