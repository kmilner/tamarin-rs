import Tamarin.Unification
import Tamarin.Models

namespace Tamarin.FlatAC

variable {sig : Signature}

/-- A nonempty list denotes a right-associated AC product of rigid atoms.
The empty case is a sentinel; executable callers must reject it. -/
def term (f : sig.ACSym) : List sig.Atom → Term sig
  | [] => .var ⟨0, .msg⟩
  | [a] => .atom a
  | a :: b :: xs => .ac f (.atom a) (term f (b :: xs))

theorem perm_equiv (f : sig.ACSym) {xs ys : List sig.Atom} (h : xs.Perm ys) :
    EquivB (term f xs) (term f ys) := by
  induction h with
  | nil => exact .refl _
  | @cons a xs ys h ih =>
    cases xs with
    | nil => have hy : ys = [] := (List.Perm.nil_eq h).symm; subst ys; exact .refl _
    | cons x xs =>
      cases ys with
      | nil => cases List.Perm.nil_eq h.symm
      | cons y ys => exact .ac_congr f (.refl _) ih
  | swap a b xs =>
    cases xs with
    | nil => exact .ac_swap f _ _
    | cons x xs =>
      exact .trans (.symm (.ac_assoc f _ _ _))
        (.trans (.ac_congr f (.ac_swap f _ _) (.refl _)) (.ac_assoc f _ _ _))
  | trans _ _ ha hb => exact .trans ha hb

abbrev atomCountModel [DecidableEq sig.Atom] (a : sig.Atom) : Model sig where
  Carrier := Nat
  atom := fun b => if b = a then 1 else 0
  free := fun _ _ => 0
  comm := fun _ x y => x + y
  ac := fun _ x y => x + y
  comm_swap := fun _ => Nat.add_comm
  ac_swap := fun _ => Nat.add_comm
  ac_assoc := fun _ => Nat.add_assoc

theorem count_eval [DecidableEq sig.Atom] (f : sig.ACSym) (a : sig.Atom)
    (xs : List sig.Atom) :
    (atomCountModel a).eval (fun _ => 0) (term f xs) = xs.count a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [term, Model.eval, atomCountModel, List.count_cons, BEq.beq]
    | cons y ys =>
      simp only [term, Model.eval] at ih ⊢
      rw [ih]
      simp [List.count_cons, BEq.beq, Nat.add_comm]

theorem equiv_perm [DecidableEq sig.Atom] (f : sig.ACSym)
    {xs ys : List sig.Atom} (h : EquivB (term f xs) (term f ys)) : xs.Perm ys := by
  apply List.perm_iff_count.mpr
  intro a
  have he := h.eval_eq (atomCountModel a) (fun _ => 0)
  simpa only [count_eval] using he

theorem equiv_iff_perm [DecidableEq sig.Atom] (f : sig.ACSym) (xs ys : List sig.Atom) :
    EquivB (term f xs) (term f ys) ↔ xs.Perm ys :=
  ⟨equiv_perm f, perm_equiv f⟩

theorem subst_term (f : sig.ACSym) (xs : List sig.Atom) (hx : xs ≠ [])
    (σ : Variable → Term sig) : (term f xs).subst σ = term f xs := by
  induction xs with
  | nil => exact False.elim (hx rfl)
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [term, Term.subst]
      congr 1
      exact ih (by simp)

def problem (f : sig.ACSym) (xs ys : List sig.Atom) : Problem sig :=
  [⟨term f xs, term f ys⟩]

theorem solves_iff [DecidableEq sig.Atom] (f : sig.ACSym)
    (xs ys : List sig.Atom) (hx : xs ≠ []) (hy : ys ≠ []) (σ : Substitution sig) :
    (problem f xs ys).Solves σ ↔ xs.Perm ys := by
  constructor
  · intro h
    have he := h ⟨term f xs, term f ys⟩ (by simp [problem])
    simp only [Substitution.apply, subst_term f xs hx, subst_term f ys hy] at he
    exact equiv_perm f he
  · intro h e he
    have heq : e = ⟨term f xs, term f ys⟩ := by simpa [problem] using he
    subst e
    simp only [Substitution.apply, subst_term f xs hx, subst_term f ys hy]
    exact perm_equiv f h

theorem complete_identity [DecidableEq sig.Atom] (f : sig.ACSym)
    (xs ys : List sig.Atom) (hx : xs ≠ []) (hy : ys ≠ []) (hp : xs.Perm ys) :
    CompleteSet (problem f xs ys) [Substitution.identity] := by
  constructor
  · intro σ _; exact (solves_iff f xs ys hx hy σ).mpr hp
  · intro ρ _
    refine ⟨Substitution.identity, by simp, ρ, ?_⟩
    intro v _
    exact .refl _

theorem complete_empty [DecidableEq sig.Atom] (f : sig.ACSym)
    (xs ys : List sig.Atom) (hx : xs ≠ []) (hy : ys ≠ []) (hp : ¬ xs.Perm ys) :
    CompleteSet (problem f xs ys) [] := by
  apply (complete_empty_iff _).mpr
  intro ⟨σ, hσ⟩
  exact hp ((solves_iff f xs ys hx hy σ).mp hσ)

end Tamarin.FlatAC
