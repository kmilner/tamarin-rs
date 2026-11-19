import Tamarin.CanonicalTree

namespace Tamarin.CanonicalTreeTests

private abbrev sig : Signature where
  FreeSym := Unit
  CSym := Unit
  ACSym := Bool
  Atom := Nat
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .pub

private def a (n : Nat) : Term sig := .atom n
private def c (x y : Term sig) : Term sig := .comm () x y
private def ac (f : Bool) (x y : Term sig) := Term.ac f x y
private def h (x : Term sig) : Term sig := .free () (fun _ => x)
private def rank : Term sig → Nat
  | .atom n => n
  | .var _ => 4
  | .comm .. => 5
  | .free .. => 6
  | .ac .. => 7
private abbrev le (x y : Term sig) := rank x ≤ rank y
private def order : CanonicalTree.Ordering le where
  sort xs := xs.mergeSort (fun a b => decide (le a b))
  perm _ := List.mergeSort_perm ..
  ordered xs := by
    have sorted := List.pairwise_mergeSort (le := fun a b => decide (le a b))
      (fun _ _ _ ha hb => by simpa only [decide_eq_true_eq] using Nat.le_trans (of_decide_eq_true ha) (of_decide_eq_true hb))
      (fun a b => by simpa only [Bool.or_eq_true,decide_eq_true_eq] using Nat.le_total (rank a) (rank b)) xs
    simpa only [decide_eq_true_eq] using sorted

-- AC(false) stays a single operand of AC(true). Both copies must survive
-- all reordering under C and under the free head.
private def inner := ac false (ac false (a 2) (a 0)) (a 1)
private def raw := h (ac true (ac true inner (c (a 2) (a 1))) inner)
private def sortedInner := ac false (a 0) (ac false (a 1) (a 2))
private def normalized := h (ac true (c (a 1) (a 2)) (ac true sortedInner sortedInner))

private def shape : Term sig → String
  | .atom n => toString n
  | .var _ => "v"
  | .free _ xs => "h(" ++ shape (xs ⟨0,Nat.zero_lt_one⟩) ++ ")"
  | .ac f a b => (if f then "+" else "*") ++ "(" ++ shape a ++ "," ++ shape b ++ ")"
  | .comm _ a b => "C(" ++ shape a ++ "," ++ shape b ++ ")"

#guard shape (CanonicalTree.normalize le order raw) == shape normalized

example : EquivB (CanonicalTree.normalize le order raw) raw := CanonicalTree.normalize_equiv order raw

example : CanonicalTree.Canonical le (CanonicalTree.normalize le order raw) :=
  CanonicalTree.normalize_canonical order (fun x y => Nat.le_total (rank x) (rank y))
    (t := raw) (by simp [raw,h,inner,ac,c,a,Term.Ground,Term.Occurs])

example : ACRepresentation.flatten true (ac true (c (a 1) (a 2)) (ac true sortedInner sortedInner)) =
    [c (a 1) (a 2), sortedInner, sortedInner] := rfl

end Tamarin.CanonicalTreeTests
