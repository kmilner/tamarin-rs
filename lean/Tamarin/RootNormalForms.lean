import Tamarin.ConstructorVariants
import Tamarin.MatchingFree

/-! Local normal forms for defined free heads. Children may contain arbitrary
free, C and AC symbols, and the ambient rule table need not be confluent. -/
namespace Tamarin.Rewriting
variable {sig : Signature} {R : Root sig}
variable {f : sig.FreeSym} {xs : Fin (sig.arity f) → Term sig}

theorem free_equiv_view {u : Term sig} (h : EquivB (.free f xs) u) :
    ∃ ys, u = .free f ys ∧ ∀ i, EquivB (xs i) (ys i) := by
  cases u with
  | free g ys =>
    have he : f = g := Head.free.inj h.head_eq
    subst g
    exact ⟨ys, rfl, (Matching.free_equiv_iff _ _ _).mp h⟩
  | _ => cases h.head_eq

theorem normal_free_arg (h : Normal R (.free f xs)) (i : Fin (sig.arity f)) :
    Normal R (xs i) := normal_free_child f xs h i

/-- With irreducible arguments, a step modulo B must use a root rule on a
pointwise B-equivalent tuple. This statement also supplies the converse witness. -/
theorem stepModulo_free_iff {u : Term sig} (hn : ∀ i, Normal R (xs i)) :
    StepModulo R (.free f xs) u ↔
      ∃ ys b, (∀ i, EquivB (xs i) (ys i)) ∧ R (.free f ys) b ∧ EquivB b u := by
  constructor
  · rintro ⟨s, b, he, hs, hb⟩
    obtain ⟨ys, rfl, hy⟩ := free_equiv_view he
    cases hs with
    | root hr => exact ⟨ys, b, hy, hr, hb⟩
    | free _ _ i h =>
      exact False.elim (((normal_equiv _ (hy i)).mp (hn i)) _ ⟨_, _, .refl _, h, .refl _⟩)
  · rintro ⟨ys, b, hy, hr, hb⟩
    exact ⟨_, _, .free _ _ _ hy, .root hr, hb⟩

theorem normal_free_no_root (hn : ∀ i, Normal R (xs i))
    (none : ∀ ys, (∀ i, EquivB (xs i) (ys i)) → ∀ b, ¬ R (.free f ys) b) :
    Normal R (.free f xs) := by
  intro u hs
  obtain ⟨ys, b, hy, hr, _⟩ := (stepModulo_free_iff hn).mp hs
  exact none ys hy b hr

/-- When every root rewrite returns a normal value, any reduction that leaves
the original B-class reaches the B-class of an actual root result. This also
covers tables with several applicable rules and different normal results. -/
theorem reduces_free_root_results {u : Term sig} (hn : ∀ i, Normal R (xs i))
    (results : Term sig → Prop) (normal : ∀ v, results v → Normal R v)
    (all : ∀ ys, (∀ i, EquivB (xs i) (ys i)) → ∀ b, R (.free f ys) b →
      ∃ v, results v ∧ EquivB b v)
    (red : Reduces R (.free f xs) u) :
    EquivB (.free f xs) u ∨ ∃ v, results v ∧ EquivB u v := by
  have go {a b : Term sig} (r : Reduces R a b) :
      EquivB (.free f xs) a → EquivB (.free f xs) b ∨ ∃ v, results v ∧ EquivB b v := by
    induction r with
    | basis e => exact fun h => Or.inl (h.trans e)
    | step hs =>
      intro h
      obtain ⟨s, t, e, hs, et⟩ := hs
      obtain ⟨ys, t', he, hr, hu⟩ := (stepModulo_free_iff hn).mp ⟨s, t, h.trans e, hs, et⟩
      obtain ⟨v, hv, ht⟩ := all _ he _ hr
      exact Or.inr ⟨v, hv, hu.symm.trans ht⟩
    | trans r s ih ik =>
      intro h
      rcases ih h with h | h
      · exact ik h
      · obtain ⟨v, hv, h⟩ := h
        exact Or.inr ⟨v, hv, (normal_reduces_equiv s ((normal_equiv _ h).mpr
          (normal v hv))).symm.trans h⟩
    | free g a b rs _ =>
      intro h
      have he : f = g := Head.free.inj h.head_eq
      subst g
      have ha := (Matching.free_equiv_iff _ _ _).mp h
      exact Or.inl (.free _ _ _ fun i => (ha i).trans (normal_reduces_equiv (rs i)
        ((normal_equiv _ (ha i)).mp (hn i))))
    | comm | ac => intro h; cases h.head_eq
  exact go red (.refl _)

theorem reduces_free_root_cases {v u : Term sig} (hn : ∀ i, Normal R (xs i))
    (hv : Normal R v)
    (all : ∀ ys, (∀ i, EquivB (xs i) (ys i)) → ∀ b, R (.free f ys) b → EquivB b v)
    (red : Reduces R (.free f xs) u) : EquivB (.free f xs) u ∨ EquivB u v := by
  simpa using reduces_free_root_results hn (· = v) (fun _ h => h ▸ hv)
    (fun ys hy b hr => ⟨v, rfl, all ys hy b hr⟩) red

theorem normalForm_free_root_unique {v u : Term sig} (hn : ∀ i, Normal R (xs i))
    (hv : Normal R v) (fires : StepModulo R (.free f xs) v)
    (all : ∀ ys, (∀ i, EquivB (xs i) (ys i)) → ∀ b, R (.free f ys) b → EquivB b v)
    (nf : NormalForm R (.free f xs) u) : EquivB u v := by
  rcases reduces_free_root_cases hn hv all nf.1 with h | h
  · exact False.elim (((normal_equiv _ h).mpr nf.2.1) v fires)
  · exact h

end Tamarin.Rewriting
