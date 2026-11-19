import Tamarin.Algebra

/-!
# Cancellation for an AC symbol

Flatten at one AC symbol into a multiset of B-equivalence classes. Alien
subterms retain their complete B-class. This proof needs no ordering or
executable equality on symbols and does not impose cancellation as an axiom.
-/
namespace Tamarin
namespace Cancellation
variable {sig : Signature}

def termSetoid (sig : Signature) : Setoid (Term sig) where
  r := EquivB
  iseqv := ⟨EquivB.refl, EquivB.symm, EquivB.trans⟩

abbrev Class (sig : Signature) := Quotient (termSetoid sig)

def classOf (t : Term sig) : Class sig := Quotient.mk _ t

def mul (f : sig.ACSym) (a b : Class sig) : Class sig :=
  Quotient.liftOn₂ a b (fun s t => classOf (.ac f s t))
    (fun _ _ _ _ hs ht => Quotient.sound (EquivB.ac_congr f hs ht))

theorem mul_comm (f : sig.ACSym) (a b : Class sig) : mul f a b = mul f b a := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact Quotient.sound (EquivB.ac_swap f a b)

theorem mul_assoc (f : sig.ACSym) (a b c : Class sig) :
    mul f (mul f a b) c = mul f a (mul f b c) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      induction c using Quotient.inductionOn with
      | h c => exact Quotient.sound (EquivB.ac_assoc f a b c)

def combine (f : sig.ACSym) : Option (Class sig) → Option (Class sig) → Option (Class sig)
  | none, b => b
  | a, none => a
  | some a, some b => some (mul f a b)

theorem combine_comm (f : sig.ACSym) (a b : Option (Class sig)) :
    combine f a b = combine f b a := by
  cases a <;> cases b <;> simp only [combine, mul_comm]

theorem combine_assoc (f : sig.ACSym) (a b c : Option (Class sig)) :
    combine f (combine f a b) c = combine f a (combine f b c) := by
  cases a <;> cases b <;> cases c <;> simp only [combine, mul_assoc]

def fold (f : sig.ACSym) : List (Class sig) → Option (Class sig)
  | [] => none
  | x :: xs => combine f (some x) (fold f xs)

theorem fold_append (f : sig.ACSym) (xs ys : List (Class sig)) :
    fold f (xs ++ ys) = combine f (fold f xs) (fold f ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, fold, ih, combine_assoc]

theorem fold_perm (f : sig.ACSym) {xs ys : List (Class sig)} (h : xs.Perm ys) :
    fold f xs = fold f ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [fold, ih]
  | swap x y xs =>
    simp only [fold, ← combine_assoc]
    rw [combine_comm f (some y) (some x)]
  | trans _ _ ha hb => exact ha.trans hb

noncomputable def flatten (f : sig.ACSym) : Term sig → List (Class sig)
  | .ac g a b => @ite _ (f = g) (Classical.propDecidable _)
      (flatten f a ++ flatten f b) [classOf (.ac g a b)]
  | t => [classOf t]

theorem flatten_ac (f : sig.ACSym) (a b : Term sig) :
    flatten f (.ac f a b) = flatten f a ++ flatten f b := by
  simp only [flatten, ite_true]

theorem flatten_equiv (f : sig.ACSym) {a b : Term sig} (h : EquivB a b) :
    (flatten f a).Perm (flatten f b) := by
  classical
  induction h with
  | refl t => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ha hb => exact ha.trans hb
  | free g a b h _ =>
    have he : classOf (.free g a) = classOf (.free g b) := Quotient.sound (.free g a b h)
    simp only [flatten, he]
    exact .refl _
  | comm_congr g ha hb _ _ =>
    have he : classOf (.comm g _ _) = classOf (.comm g _ _) :=
      Quotient.sound (.comm_congr g ha hb)
    simp only [flatten, he]
    exact .refl _
  | ac_congr g ha hb ia ib =>
    by_cases hf : f = g
    · subst g; simpa only [flatten_ac] using ia.append ib
    · have he : classOf (.ac g _ _) = classOf (.ac g _ _) :=
        Quotient.sound (.ac_congr g ha hb)
      simp only [flatten, ite_eq_right hf, he]
      exact .refl _
  | comm_swap g a b =>
    have he : classOf (.comm g a b) = classOf (.comm g b a) :=
      Quotient.sound (.comm_swap g a b)
    simp only [flatten, he]
    exact .refl _
  | ac_swap g a b =>
    by_cases hf : f = g
    · subst g; simpa only [flatten_ac] using List.perm_append_comm (l₁ := flatten f a)
        (l₂ := flatten f b)
    · have he : classOf (.ac g a b) = classOf (.ac g b a) :=
        Quotient.sound (.ac_swap g a b)
      simp only [flatten, ite_eq_right hf, he]
      exact .refl _
  | ac_assoc g a b c =>
    by_cases hf : f = g
    · subst g; simp only [flatten_ac, List.append_assoc]; exact .refl _
    · have he : classOf (.ac g (.ac g a b) c) = classOf (.ac g a (.ac g b c)) :=
        Quotient.sound (.ac_assoc g a b c)
      simp only [flatten, ite_eq_right hf, he]
      exact .refl _

theorem fold_flatten (f : sig.ACSym) (t : Term sig) :
    fold f (flatten f t) = some (classOf t) := by
  classical
  induction t with
  | var v => rfl
  | atom a => rfl
  | free g args _ => rfl
  | comm g a b _ _ => rfl
  | ac g a b ha hb =>
    by_cases hf : f = g
    · subst g
      rw [flatten_ac, fold_append, ha, hb]
      rfl
    · simp only [flatten, ite_eq_right hf, fold, combine]

theorem equiv_of_flatten_perm (f : sig.ACSym) {a b : Term sig}
    (h : (flatten f a).Perm (flatten f b)) : EquivB a b := by
  have hh := fold_perm f h
  rw [fold_flatten, fold_flatten] at hh
  exact Quotient.exact (Option.some.inj hh)

end Cancellation

theorem EquivB.ac_cancel_right {sig : Signature} (f : sig.ACSym)
    {a b c : Term sig} (h : EquivB (.ac f a c) (.ac f b c)) : EquivB a b := by
  have hh := Cancellation.flatten_equiv f h
  rw [Cancellation.flatten_ac, Cancellation.flatten_ac] at hh
  exact Cancellation.equiv_of_flatten_perm f ((List.perm_append_right_iff _).mp hh)

theorem EquivB.ac_cancel_left {sig : Signature} (f : sig.ACSym)
    {a b c : Term sig} (h : EquivB (.ac f c a) (.ac f c b)) : EquivB a b :=
  EquivB.ac_cancel_right f (.trans (.ac_swap f a c) (.trans h (.ac_swap f c b)))

end Tamarin
