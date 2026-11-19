import Tamarin.SortCheck

/-!
Interpretation of Rust-style nonempty AC argument arrays. Entries may be
open compound terms. There is no empty product. A singleton is its sole child.
-/
namespace Tamarin.ACRepresentation
variable {sig : Signature}

def fold (f : sig.ACSym) (a : Term sig) : List (Term sig) → Term sig
  | [] => a
  | b :: bs => .ac f a (fold f b bs)

def decode (f : sig.ACSym) : List (Term sig) → Option (Term sig)
  | [] => none
  | a :: as => some (fold f a as)

theorem fold_append (f : sig.ACSym) (a : Term sig) (as : List (Term sig))
    (b : Term sig) (bs : List (Term sig)) :
    EquivB (fold f a (as ++ b :: bs)) (.ac f (fold f a as) (fold f b bs)) := by
  induction as generalizing a with
  | nil => exact .refl _
  | cons x xs ih =>
    exact .trans (.ac_congr f (.refl a) (ih x)) (.symm (.ac_assoc f a _ _))

theorem decode_append (f : sig.ACSym) (as bs : List (Term sig))
    (a b : Term sig) (ha : decode f as = some a) (hb : decode f bs = some b) :
    ∃ t, decode f (as ++ bs) = some t ∧ EquivB t (.ac f a b) := by
  cases as with
  | nil => simp [decode] at ha
  | cons x xs =>
    cases bs with
    | nil => simp [decode] at hb
    | cons y ys =>
      simp only [decode, Option.some.injEq] at ha hb
      subst a; subst b
      exact ⟨_, rfl, fold_append f x xs y ys⟩

/-- Swapping adjacent array entries preserves ordinary AC semantics even when
entries themselves contain variables or compound applications. -/
theorem fold_swap (f : sig.ACSym) (a b : Term sig) (as : List (Term sig)) :
    EquivB (fold f a (b :: as)) (fold f b (a :: as)) := by
  cases as with
  | nil => exact .ac_swap f a b
  | cons c cs =>
    exact .trans (.symm (.ac_assoc f a b _))
      (.trans (.ac_congr f (.ac_swap f a b) (.refl _)) (.ac_assoc f b a _))

theorem fold_perm (f : sig.ACSym) (a : Term sig) {as bs : List (Term sig)}
    (h : as.Perm bs) : EquivB (fold f a as) (fold f a bs) := by
  induction h generalizing a with
  | nil => exact .refl _
  | cons x h ih => exact .ac_congr f (.refl a) (ih x)
  | swap x y xs => exact .ac_congr f (.refl a) (fold_swap f y x xs)
  | trans h k ih ik => exact .trans (ih a) (ik a)

theorem decode_perm (f : sig.ACSym) {as bs : List (Term sig)}
    (h : as.Perm bs) (a b : Term sig)
    (ha : decode f as = some a) (hb : decode f bs = some b) : EquivB a b := by
  induction h generalizing a b with
  | nil => simp [decode] at ha
  | cons x h =>
    simp only [decode, Option.some.injEq] at ha hb
    subst a; subst b
    exact fold_perm f x h
  | swap x y xs =>
    simp only [decode, Option.some.injEq] at ha hb
    subst a; subst b
    exact fold_swap f y x xs
  | @trans xs ys zs h k ih ik =>
    cases ys with
    | nil =>
      have hx := List.Perm.length_eq h
      have : xs = [] := by simpa using hx
      simp [this, decode] at ha
    | cons y ys => exact .trans (ih _ _ ha rfl) (ik _ _ rfl hb)

/-- Flatten only the selected AC symbol; all other heads remain opaque.
Sorting/permuting entries is a separate representation operation. -/
def flatten [DecidableEq sig.ACSym] (f : sig.ACSym) : Term sig → List (Term sig)
  | .ac g a b => if f = g then flatten f a ++ flatten f b else [.ac g a b]
  | t => [t]

theorem flatten_correct [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Term sig) :
    ∃ u, decode f (flatten f t) = some u ∧ EquivB u t := by
  induction t with
  | var v => exact ⟨_, rfl, .refl _⟩
  | atom a => exact ⟨_, rfl, .refl _⟩
  | free g args _ => exact ⟨_, rfl, .refl _⟩
  | comm g a b _ _ => exact ⟨_, rfl, .refl _⟩
  | ac g a b ia ib =>
    simp only [flatten]
    split
    · rename_i h
      subst g
      obtain ⟨a', ha, ea⟩ := ia
      obtain ⟨b', hb, eb⟩ := ib
      obtain ⟨u, hu, eu⟩ := decode_append f _ _ a' b' ha hb
      exact ⟨u, hu, .trans eu (.ac_congr f ea eb)⟩
    · exact ⟨_, rfl, .refl _⟩

theorem flatten_nonempty [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Term sig) :
    flatten f t ≠ [] := by
  obtain ⟨u, hu, _⟩ := flatten_correct f t
  intro h
  simp [h, decode] at hu

theorem fold_hasSort (f : sig.ACSym) (a : Term sig) (as : List (Term sig))
    (ha : HasSort a (sig.acSort f))
    (hs : ∀ t ∈ as, HasSort t (sig.acSort f)) :
    HasSort (fold f a as) (sig.acSort f) := by
  induction as generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    exact .ac f a _ ha (ih b (hs b (by simp)) (fun t ht => hs t (by simp [ht])))

theorem flatten_hasSort [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Term sig)
    (h : HasSort t (sig.acSort f)) :
    ∀ u ∈ flatten f t, HasSort u (sig.acSort f) := by
  induction t with
  | ac g a b ia ib =>
    by_cases he : f = g
    · subst g
      have hc := Term.checkSort_complete h
      simp only [Term.checkSort, Bool.and_eq_true] at hc
      have ha := ia (Term.checkSort_sound _ _ hc.1.2)
      have hb := ib (Term.checkSort_sound _ _ hc.2)
      intro u hu
      simp only [flatten, ite_true, List.mem_append] at hu
      exact hu.elim (ha u) (hb u)
    · simpa only [flatten, ite_eq_right he, List.mem_singleton, forall_eq] using h
  | var v => simpa only [flatten, List.mem_singleton, forall_eq] using h
  | atom a => simpa only [flatten, List.mem_singleton, forall_eq] using h
  | free g args _ => simpa only [flatten, List.mem_singleton, forall_eq] using h
  | comm g a b _ _ => simpa only [flatten, List.mem_singleton, forall_eq] using h

theorem flatten_typed_correct [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Term sig)
    (h : HasSort t (sig.acSort f)) :
    ∃ u, decode f (flatten f t) = some u ∧ EquivB u t ∧ HasSort u (sig.acSort f) := by
  obtain ⟨u, hu, he⟩ := flatten_correct f t
  have hs := flatten_hasSort f t h
  refine ⟨u, hu, he, ?_⟩
  cases hx : flatten f t with
  | nil => simp [hx, decode] at hu
  | cons a as =>
    simp only [hx, decode, Option.some.injEq] at hu
    subst u
    exact fold_hasSort f a as (hs a (by simp [hx])) (fun v hv => hs v (by simp [hx, hv]))

end Tamarin.ACRepresentation
