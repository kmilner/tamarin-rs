import Tamarin.FlatAC

namespace Tamarin.Executable

/-- Linear merge subtraction on sorted lists. Failure is explicit, and a
successful result preserves multiplicities. The soundness theorem below
does not assume sortedness; sorting is needed for success completeness. -/
def subtractSorted (need : List UInt64) (available : List UInt64) : Option (List UInt64) :=
  match need, available with
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xs, y :: ys =>
      if x = y then subtractSorted xs ys
      else if y < x then (subtractSorted (x :: xs) ys).map (y :: ·)
      else none
termination_by available.length

theorem subtractSorted_sound (need available rest : List UInt64)
    (h : subtractSorted need available = some rest) : (need ++ rest).Perm available := by
  induction available generalizing need rest with
  | nil =>
    cases need with
    | nil => simp only [subtractSorted, Option.some.injEq] at h; subst rest; exact .refl _
    | cons x xs => simp only [subtractSorted, reduceCtorEq] at h
  | cons y ys ih =>
    cases need with
    | nil => simp only [subtractSorted, Option.some.injEq] at h; subst rest; exact .refl _
    | cons x xs =>
      simp only [subtractSorted] at h
      split at h
      · next heq => subst x; exact .cons y (ih xs rest h)
      · next hne =>
        split at h
        · next hlt =>
          cases hs : subtractSorted (x :: xs) ys with
          | none => simp [hs] at h
          | some r =>
            simp only [hs, Option.map_some, Option.some.injEq] at h
            subst rest
            have hp := ih (x :: xs) r hs
            exact (List.perm_middle).trans (.cons y hp)
        · simp only [reduceCtorEq] at h

end Tamarin.Executable
