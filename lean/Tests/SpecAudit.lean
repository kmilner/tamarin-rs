import Tamarin.VariableElimination
import Tamarin.Models
import Tamarin.FreshSubstitution
import Tamarin.FlatAC
import Tamarin.GroundConjunction

/-!
Adversarial checks of the boundary between mathematical unifiers and callers.
These are counterexamples to stronger interpretations of the current contracts,
not counterexamples to their stated mathematical soundness/completeness.
Run with `lake env lean Tests/SpecAudit.lean`.
-/
namespace Tamarin.SpecAudit

private abbrev sig : Signature where
  FreeSym := Empty
  CSym := Empty
  ACSym := Unit
  Atom := Unit
  arity := Empty.elim
  inputSort := fun f => Empty.elim f
  outputSort := Empty.elim
  cSort := Empty.elim
  acSort := fun _ => .msg
  atomSort := fun _ => .msg

private def x : Variable := ⟨0, .msg⟩
private def y : Variable := ⟨1, .msg⟩
private def z : Variable := ⟨2, .msg⟩
private def rhs (v : Variable) : Term sig := .ac () (.var v) (.atom ())
private theorem rhs_sorted (v : Variable) (hv : v.sort = .msg) :
    HasSort (rhs v) .msg := by
  apply HasSort.ac (sig := sig)
  · change HasSort (Term.var v) .msg
    rw [← hv]
    exact HasSort.var v
  · exact HasSort.atom (sig := sig) ()

private def ordinary : Substitution sig :=
  Substitution.binding x (rhs y) (rhs_sorted y rfl)

private def naiveFreshened : Substitution sig :=
  Substitution.binding x (rhs z) (rhs_sorted z rfl)

/-- This ordinary answer satisfies every output obligation of VerifiedUnifier,
including freshness for any context. Input y is intentionally not auxiliary. -/
theorem ordinary_complete :
    CompleteSet (VariableElimination.problem x (rhs y)) [ordinary] := by
  exact VariableElimination.binding_complete x (rhs y) (rhs_sorted y rfl)
    (by simp [rhs, Term.Occurs, x, y])

theorem ordinary_domain :
    DomainRestricted (VariableElimination.problem x (rhs y)) ordinary :=
  VariableElimination.binding_domain x (rhs y) (rhs_sorted y rfl)

theorem ordinary_fresh (avoid : List Variable) :
    FreshFor (VariableElimination.problem x (rhs y)) avoid ordinary :=
  VariableElimination.binding_fresh x (rhs y) (rhs_sorted y rfl) avoid

/-- Reinterpreting its range variable y as an independent fresh z breaks the
equation: x becomes z+a, while the original y remains y. A VFresh encoder must
close over retained input variables (e.g. include y -> z), not simply retag. -/
theorem naive_freshening_not_sound :
    ¬ (VariableElimination.problem x (rhs y)).Solves naiveFreshened := by
  intro h
  have he := h ⟨.var x, rhs y⟩ (by simp [VariableElimination.problem])
  have hm := he.eval_eq (weightModel sig) (fun v => if v = z then 1 else 0)
  simp [Substitution.apply, naiveFreshened, Substitution.binding,
    Term.subst, Model.eval, rhs, x, y, z] at hm

/-- The repaired reference packet keeps the observed y -> y entry. -/
example : (FreshAnswer.encode [x, y] ordinary).bindings =
    [(x, rhs y), (y, .var y)] := rfl

private def repaired : Substitution sig :=
  FreshAnswer.freshen (VariableElimination.problem x (rhs y)) [z] ordinary

private def witness : Variable := ⟨4, .msg⟩

example : repaired.image x = rhs witness := rfl
example : repaired.image y = .var witness := rfl
example : repaired.image z = .var z := rfl

/-- This is a full complete-set result with domain/freshness, not just a
check that the two sides of this particular equation evaluate alike. -/
theorem repaired_contextually_correct :
    (Outcome.complete [repaired]).CorrectIn
      (VariableElimination.problem x (rhs y)) [z] := by
  exact FreshAnswer.freshen_correct
    ⟨VariableElimination.problem x (rhs y), [z]⟩ [ordinary] ordinary_complete

private def unrelatedBinding : Substitution sig :=
  Substitution.binding z (.atom ()) (HasSort.atom (sig := sig) ())

/-- CompleteSet alone has no noninterference obligation outside input vars. -/
theorem external_binding_is_complete :
    CompleteSet ([] : Problem sig) [unrelatedBinding] := by
  constructor
  · intro σ _ e he
    exact False.elim (List.not_mem_nil he)
  · intro ρ _
    refine ⟨unrelatedBinding, by simp, Substitution.identity, ?_⟩
    intro v ⟨e, he, _⟩
    exact False.elim (List.not_mem_nil he)

theorem external_binding_not_domain_restricted :
    ¬ DomainRestricted ([] : Problem sig) unrelatedBinding := by
  intro h
  have hz := h z (by simp [Problem.Occurs])
  simp [unrelatedBinding, Substitution.binding] at hz

/-- Runtime refinement now excludes this complete but interfering answer. -/
theorem external_binding_not_contextually_correct (avoid : List Variable) :
    ¬ (Outcome.complete [unrelatedBinding]).CorrectIn ([] : Problem sig) avoid := by
  intro h
  exact external_binding_not_domain_restricted (h.domain unrelatedBinding (by simp [Outcome.answers]))

section TwoSided

private abbrev twoAtoms : Signature := { sig with Atom := Bool, atomSort := fun _ => .msg }
private def offsetEq : Equation twoAtoms :=
  ⟨.ac () (.var x) (.atom false), .ac () (.var y) (.atom true)⟩

private def withOffset (atom : Bool) : Term twoAtoms := .ac () (.var z) (.atom atom)

private theorem withOffset_sorted (b : Bool) : HasSort (withOffset b) .msg :=
  HasSort.ac (sig := twoAtoms) () _ _ (.var z) (HasSort.atom (sig := twoAtoms) b)

private def sharedOffset : Substitution twoAtoms :=
  (Substitution.binding y (withOffset false) (withOffset_sorted false)).compose
    (Substitution.binding x (withOffset true) (withOffset_sorted true))

private theorem sharedOffset_solves : Problem.Solves [offsetEq] sharedOffset := by
  intro e he
  obtain rfl := List.mem_singleton.mp he
  change EquivB (.ac () (withOffset true) (.atom false)) (.ac () (withOffset false) (.atom true))
  exact (EquivB.ac_assoc (sig := twoAtoms) _ _ _ _).trans
    ((EquivB.ac_congr _ (.refl _) (.ac_swap _ _ _)).trans (EquivB.ac_assoc _ _ _ _).symm)

/-- For x+a = y+b with distinct atoms, even an arbitrarily large collection
of ground bindings or identities misses the solution x=z+b, y=z+a. This
checks the scope of the native output restriction against CompleteSet itself. -/
theorem ground_or_identity_misses_shared_offset (answers : List (Substitution twoAtoms))
    (restricted : ∀ σ ∈ answers, (σ.image x).Ground ∨ σ.image x = .var x) :
    ¬ CompleteSet [offsetEq] answers := by
  intro hc
  obtain ⟨σ, hs, δ, hagree⟩ := hc.covers sharedOffset sharedOffset_solves
  rcases restricted σ hs with hg | hi
  · have eq := hagree x ⟨offsetEq, by simp, Or.inl (Or.inl rfl)⟩
    change EquivB (withOffset true) (δ.apply (σ.image x)) at eq
    rw [hg.apply_eq δ] at eq
    exact hg z ((eq.occurs_iff z).mp (Or.inl rfl))
  · have eq := hc.sound σ hs offsetEq (by simp)
    change EquivB (.ac () (σ.image x) (.atom false)) (.ac () (σ.image y) (.atom true)) at eq
    rw [hi] at eq
    have h := eq.eval_eq (FlatAC.atomCountModel (sig := twoAtoms) true) (fun _ => 0)
    exact Nat.noConfusion (show 0 = Nat.succ _ from h)

end TwoSided

end Tamarin.SpecAudit
