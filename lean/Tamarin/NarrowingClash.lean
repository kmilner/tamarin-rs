import Tamarin.GroundACEquality
import Tamarin.SortClash

/-! Reject impossible narrowing queries before searching their AC components.
Heads are fixed except at variables. A rigid subtree which cannot inhabit a
required sort remains incompatible even if other variables narrow their sorts. -/
namespace Tamarin.NarrowingClash
variable {s : Signature}

private def possible : Term s → SortId → Bool
  | .var _, _ => true
  | .atom a, k => Subsort.check (s.atomSort a) k
  | .free f xs, k => Subsort.check (s.outputSort f) k &&
      (List.finRange (s.arity f)).all fun i => possible (xs i) (s.inputSort f i)
  | .comm f a b, k => Subsort.check (s.cSort f) k && possible a (s.cSort f) && possible b (s.cSort f)
  | .ac f a b, k => Subsort.check (s.acSort f) k && possible a (s.acSort f) && possible b (s.acSort f)

private theorem possible_of_instance (t : Term s) (σ : Substitution s) (k)
    (h : (σ.apply t).checkSort k) : possible t k := by
  induction t generalizing k with
  | var => rfl
  | atom => exact h
  | free f xs ih =>
    simp only [Substitution.apply,Term.subst,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at h
    exact Bool.and_eq_true_iff.mpr ⟨h.1,List.all_eq_true.mpr fun i hi => ih i _ (h.2 i hi)⟩
  | ac f a b ia ib | comm f a b ia ib =>
    simp only [Substitution.apply,Term.subst,Term.checkSort,Bool.and_eq_true] at h
    simp only [possible,Bool.and_eq_true]
    exact ⟨⟨h.1.1,ia _ h.1.2⟩,ib _ h.2⟩

private def sortClash (a b : Term s) := a.checkSort a.rootSort && !(possible b a.rootSort)

private theorem no_sort_clash (a b : Term s) (σ : Substitution s) (eq : EquivB (σ.apply a) (σ.apply b)) :
    sortClash a b = false := by
  apply Bool.eq_false_iff.mpr
  intro clash
  obtain ⟨typed,no⟩ := Bool.and_eq_true_iff.mp clash
  have same := SortClash.check_equiv eq a.rootSort
  have ok := Term.checkSort_complete ((Term.checkSort_sound a _ typed).subst σ.image σ.sorted)
  have yes := possible_of_instance b σ _ (same.symm.trans ok)
  simp [yes] at no

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def heads : Term s → Term s → Bool
  | .var _, _ | _, .var _ => true
  | .atom a,.atom b => decide (a = b)
  | .free f _,.free g _ => decide (f = g)
  | .comm f ..,.comm g .. => decide (f = g)
  | .ac f ..,.ac g .. => decide (f = g)
  | _,_ => false

private theorem heads_of_solution (a b : Term s) (σ : Substitution s)
    (eq : EquivB (σ.apply a) (σ.apply b)) : heads a b := by
  have root := eq.head_eq
  cases a <;> cases b <;> simp_all [heads,Substitution.apply,Term.subst,Model.eval,headModel]

private def impossible (e : Equation s) :=
  !(heads e.lhs e.rhs) || sortClash e.lhs e.rhs || sortClash e.rhs e.lhs

private theorem refutes {p : Problem s} (h : p.any impossible) : CompleteSet p [] := by
  apply (complete_empty_iff _).mpr
  rintro ⟨σ,sol⟩
  obtain ⟨e,he,bad⟩ := List.any_eq_true.mp h
  have eq := sol e he
  simp [impossible,heads_of_solution _ _ σ eq,no_sort_clash _ _ σ eq,no_sort_clash _ _ σ eq.symm] at bad

/-- A complete unifier with a verified early rejection for impossible
equations. The supplied solver handles the entire remaining conjunction. -/
def unifier (u : VerifiedUnifier s (fun _ => True)) : VerifiedUnifier s (fun _ => True) where
  solve p hp avoid := if p.any impossible then [] else u.solve p hp avoid
  correct p hp avoid := by split <;> first | exact refutes ‹_› | exact u.correct p hp avoid
  domain p hp avoid := by split <;> first | simp | exact u.domain p hp avoid
  fresh p hp avoid := by split <;> first | simp | exact u.fresh p hp avoid

end Tamarin.NarrowingClash
