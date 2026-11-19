import Tamarin.FlatAC
import Tamarin.VariableElimination
import Tamarin.Cancellation

/-!
# One-variable flat AC unification

The supported pattern contains one occurrence of one variable and otherwise
rigid atoms. The right side is a nonempty flat product of rigid atoms.
The result is a nonempty multiset difference. Completeness uses generic AC
cancellation, not just a successful substitution check.
-/
namespace Tamarin.FlatAC

variable {sig : Signature}

theorem term_not_occurs (f : sig.ACSym) (xs : List sig.Atom) (hx : xs ≠ [])
    (v : Variable) : ¬ (term f xs).Occurs v := by
  induction xs with
  | nil => exact False.elim (hx rfl)
  | cons a xs ih =>
    cases xs with
    | nil => exact id
    | cons b xs =>
      intro h
      rcases h with h | h
      · exact h
      · exact ih (by simp) h

theorem term_hasSort (f : sig.ACSym) (xs : List sig.Atom) (hx : xs ≠ [])
    (hs : ∀ a ∈ xs, Subsort (sig.atomSort a) (sig.acSort f)) :
    HasSort (term f xs) (sig.acSort f) := by
  induction xs with
  | nil => exact False.elim (hx rfl)
  | cons a xs ih =>
    have ha : HasSort (.atom a : Term sig) (sig.acSort f) :=
      .widen (.atom a) (hs a (by simp))
    cases xs with
    | nil => exact ha
    | cons b xs =>
      exact .ac f _ _ ha (ih (by simp) (fun c hc => hs c (List.mem_cons_of_mem _ hc)))

theorem term_hasSort_widen (f : sig.ACSym) (xs : List sig.Atom) (hx : xs ≠ [])
    (hs : ∀ a ∈ xs, Subsort (sig.atomSort a) (sig.acSort f))
    (s : SortId) (hf : Subsort (sig.acSort f) s) : HasSort (term f xs) s :=
  .widen (term_hasSort f xs hx hs) hf

/-- Bare `v = product(xs)` is covered by the same singleton binding contract. -/
theorem variable_complete (v : Variable) (f : sig.ACSym) (xs : List sig.Atom)
    (hx : xs ≠ []) (ht : HasSort (term f xs) v.sort) :
    CompleteSet (VariableElimination.problem v (term f xs))
      [Substitution.binding v (term f xs) ht] :=
  VariableElimination.binding_complete v (term f xs) ht (term_not_occurs f xs hx v)

/-- Joining two nonempty atom lists denotes the AC product of their terms. -/
theorem append_equiv (f : sig.ACSym) (xs ys : List sig.Atom)
    (hx : xs ≠ []) (hy : ys ≠ []) :
    EquivB (term f (xs ++ ys)) (.ac f (term f xs) (term f ys)) := by
  induction xs with
  | nil => exact False.elim (hx rfl)
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => exact False.elim (hy rfl)
      | cons b ys => exact .refl _
    | cons b xs =>
      simp only [List.cons_append, term]
      exact .trans (.ac_congr f (.refl _) (ih (by simp))) (.symm (.ac_assoc f _ _ _))

/-- One occurrence of `v`, followed by a nonempty rigid tail. -/
def variableProblem (v : Variable) (f : sig.ACSym)
    (tail rhs : List sig.Atom) : Problem sig :=
  [⟨.ac f (.var v) (term f tail), term f rhs⟩]

/-- A computed nonempty multiset difference supplies an equivalent binding
equation for ALL sorted substitutions, including nonground substitutions. -/
theorem variable_solves_iff (v : Variable) (f : sig.ACSym)
    (tail rhs rest : List sig.Atom)
    (htail : tail ≠ []) (hrhs : rhs ≠ []) (hrest : rest ≠ [])
    (hp : rhs.Perm (rest ++ tail)) (σ : Substitution sig) :
    (variableProblem v f tail rhs).Solves σ ↔
      EquivB (σ.image v) (term f rest) := by
  have hr : EquivB (term f rhs) (.ac f (term f rest) (term f tail)) :=
    .trans (perm_equiv f hp) (append_equiv f rest tail hrest htail)
  constructor
  · intro h
    have he := h ⟨.ac f (.var v) (term f tail), term f rhs⟩ (by simp [variableProblem])
    simp only [Substitution.apply, Term.subst, subst_term f tail htail,
      subst_term f rhs hrhs] at he
    exact EquivB.ac_cancel_right f (.trans he hr)
  · intro h e he
    have heq : e = ⟨.ac f (.var v) (term f tail), term f rhs⟩ := by
      simpa [variableProblem] using he
    subst e
    simp only [Substitution.apply, Term.subst, subst_term f tail htail,
      subst_term f rhs hrhs]
    exact .trans (.ac_congr f h (.refl _)) hr.symm

/-- Full soundness and completeness for the nonempty-difference branch. -/
theorem variable_complete_difference (v : Variable) (f : sig.ACSym)
    (tail rhs rest : List sig.Atom)
    (htail : tail ≠ []) (hrhs : rhs ≠ []) (hrest : rest ≠ [])
    (hp : rhs.Perm (rest ++ tail)) (hs : HasSort (term f rest) v.sort) :
    CompleteSet (variableProblem v f tail rhs)
      [Substitution.binding v (term f rest) hs] := by
  constructor
  · intro σ hσ
    have heq : σ = Substitution.binding v (term f rest) hs := by simpa using hσ
    subst σ
    apply (variable_solves_iff v f tail rhs rest htail hrhs hrest hp _).mpr
    rw [Substitution.binding_image_self]
    exact .refl _
  · intro ρ hρ
    have hb := (variable_solves_iff v f tail rhs rest htail hrhs hrest hp ρ).mp hρ
    refine ⟨Substitution.binding v (term f rest) hs, by simp, ρ, ?_⟩
    intro w _
    apply Substitution.binding_factor v (term f rest) hs ρ
    simpa only [Substitution.apply, subst_term f rest hrest] using hb

theorem variable_difference_domain (v : Variable) (f : sig.ACSym)
    (tail rhs rest : List sig.Atom) (hs : HasSort (term f rest) v.sort) :
    DomainRestricted (variableProblem v f tail rhs) (Substitution.binding v (term f rest) hs) := by
  intro w hw
  apply Substitution.binding_image_other
  intro he
  subst w
  exact hw ⟨⟨.ac f (.var v) (term f tail), term f rhs⟩,
    by simp [variableProblem], Or.inl (Or.inl rfl)⟩

theorem variable_difference_fresh (v : Variable) (f : sig.ACSym)
    (tail rhs rest : List sig.Atom) (hrest : rest ≠ [])
    (hs : HasSort (term f rest) v.sort) (avoid : List Variable) :
    FreshFor (variableProblem v f tail rhs) avoid (Substitution.binding v (term f rest) hs) := by
  intro w hw u hu hnot _
  by_cases he : w = v
  · subst w
    rw [Substitution.binding_image_self] at hu
    exact term_not_occurs f rest hrest u hu
  · rw [Substitution.binding_image_other v w (term f rest) hs he] at hu
    have heu : u = w := hu
    subst u
    exact hnot hw

/-- Every finite term has positive weight in this model, including variable
images and alien free/C subterms. There is no hidden empty product. -/
theorem positive_weight (t : Term sig) :
    0 < (weightModel sig).eval (fun _ => 1) t := by
  induction t with
  | var v => exact Nat.zero_lt_one
  | atom a => exact Nat.zero_lt_one
  | free f args _ =>
    change 0 < 1 + (List.ofFn fun i => (weightModel sig).eval (fun _ => 1) (args i)).sum
    exact Nat.add_pos_left Nat.zero_lt_one _
  | comm f a b _ _ =>
    change 0 <
      ((weightModel sig).eval (fun _ => 1) a + (weightModel sig).eval (fun _ => 1) b + 1) *
      ((weightModel sig).eval (fun _ => 1) a + (weightModel sig).eval (fun _ => 1) b + 1)
    exact Nat.mul_pos (Nat.add_pos_right _ Nat.zero_lt_one) (Nat.add_pos_right _ Nat.zero_lt_one)
  | ac f a b ha _ =>
    change 0 < (weightModel sig).eval (fun _ => 1) a +
      (weightModel sig).eval (fun _ => 1) b
    exact Nat.add_pos_left ha _

/-- An empty multiset difference is unsatisfiable because AC has no unit. -/
theorem variable_empty_difference (v : Variable) (f : sig.ACSym)
    (tail rhs : List sig.Atom) (htail : tail ≠ []) (hrhs : rhs ≠ [])
    (hp : rhs.Perm tail) : CompleteSet (variableProblem v f tail rhs) [] := by
  apply (complete_empty_iff _).mpr
  intro ⟨σ, hσ⟩
  have he := hσ ⟨.ac f (.var v) (term f tail), term f rhs⟩ (by simp [variableProblem])
  simp only [Substitution.apply, Term.subst, subst_term f tail htail,
    subst_term f rhs hrhs] at he
  have hcancel := EquivB.trans he (perm_equiv f hp)
  have hw := hcancel.eval_eq (weightModel sig) (fun _ => 1)
  have hpos := positive_weight (σ.image v)
  change (weightModel sig).eval (fun _ => 1) (σ.image v) +
    (weightModel sig).eval (fun _ => 1) (term f tail) =
    (weightModel sig).eval (fun _ => 1) (term f tail) at hw
  have hz := Nat.add_right_cancel (hw.trans (Nat.zero_add _).symm)
  exact (Nat.ne_of_lt hpos) hz.symm

/-- If any rigid atom occurs more often in the pattern tail than on the
right, no possible variable image can remove those occurrences. -/
theorem variable_missing_atom [DecidableEq sig.Atom]
    (v : Variable) (f : sig.ACSym) (tail rhs : List sig.Atom)
    (htail : tail ≠ []) (hrhs : rhs ≠ [])
    (a : sig.Atom) (ha : rhs.count a < tail.count a) :
    CompleteSet (variableProblem v f tail rhs) [] := by
  apply (complete_empty_iff _).mpr
  intro ⟨σ, hσ⟩
  have he := hσ ⟨.ac f (.var v) (term f tail), term f rhs⟩ (by simp [variableProblem])
  simp only [Substitution.apply, Term.subst, subst_term f tail htail,
    subst_term f rhs hrhs] at he
  have hw := he.eval_eq (atomCountModel a) (fun _ => 0)
  change (atomCountModel a).eval (fun _ => 0) (σ.image v) +
    (atomCountModel a).eval (fun _ => 0) (term f tail) =
    (atomCountModel a).eval (fun _ => 0) (term f rhs) at hw
  rw [count_eval, count_eval] at hw
  have hle := Nat.le_add_left (tail.count a) ((atomCountModel a).eval (fun _ => 0) (σ.image v))
  rw [hw] at hle
  exact (Nat.not_lt_of_ge hle) ha

end Tamarin.FlatAC
