import Tamarin.Unification
import Tamarin.Models

/-!
# Checks of the specification

These are kernel-checked theorems about the contract, not solver tests or
claims that an AC algorithm has been verified. Negative examples use models
independently of the inductive presentation of B.
-/
namespace Tamarin.SpecChecks

variable {sig : Signature}

/-- Every self-equation is covered by identity, including AC/C-headed ones.
Maude's additional branches are a separate compatibility concern. -/
theorem self_equation_complete (t : Term sig) :
    CompleteSet [⟨t, t⟩] [Substitution.identity] := by
  constructor
  · intro σ _ e he
    have heq : e = ⟨t, t⟩ := by simpa using he
    subst e
    exact .refl _
  · intro ρ _
    refine ⟨Substitution.identity, by simp, ρ, ?_⟩
    intro v _
    exact .refl _

/-- The natural-number interpretation separates duplicate AC arguments. -/
theorem ac_not_idempotent (f : sig.ACSym) (x : Variable) :
    ¬ EquivB (.ac f (.var x) (.var x)) (.var x) := by
  intro h
  have hm := h.eval_eq (weightModel sig) (fun _ => 1)
  change (1 + 1 : Nat) = 1 at hm
  contradiction

/-- A named constant is not an AC unit merely because it is called zero/one. -/
theorem atom_not_ac_unit (f : sig.ACSym) (x : Variable) (a : sig.Atom) :
    ¬ EquivB (.ac f (.var x) (.atom a)) (.var x) := by
  intro h
  have hm := h.eval_eq (weightModel sig) (fun _ => 1)
  change (1 + 1 : Nat) = 1 at hm
  contradiction

/-- Commutativity alone does not permit reassociation. -/
theorem c_not_associative (f : sig.CSym) (x y : Variable) :
    ¬ EquivB
      (.comm f (.comm f (.var x) (.var y)) (.comm f (.var x) (.var y)))
      (.comm f (.var x) (.comm f (.var y) (.comm f (.var x) (.var y)))) := by
  intro h
  have hm := h.eval_eq (weightModel sig) (fun _ => 0)
  change (9 : Nat) = 25 at hm
  contradiction

/-- Finite trees and AC without a unit cannot solve this occurs-check case. -/
theorem ac_occurs_unsatisfiable (f : sig.ACSym) (x : Variable) (a : sig.Atom) :
    ¬ Problem.Satisfiable [⟨.var x, .ac f (.var x) (.atom a)⟩] := by
  intro ⟨σ, hσ⟩
  have h := hσ ⟨.var x, .ac f (.var x) (.atom a)⟩ (by simp)
  have hm := h.eval_eq (weightModel sig) (fun _ => 1)
  change (weightModel sig).eval (fun _ => 1) (σ.image x) =
    (weightModel sig).eval (fun _ => 1) (σ.image x) + 1 at hm
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hm

/-- No common subtype is silently invented for the incomparable base sorts. -/
theorem pub_fresh_no_common_subsort :
    ¬ ∃ s, Subsort s .pub ∧ Subsort s .fresh := by
  intro ⟨_, hp, hf⟩
  cases hp
  cases hf

theorem node_not_message : ¬ Subsort .node .msg := by
  intro h
  cases h

/-- An interrupted, empty enumeration has no completeness implication. -/
theorem stopped_empty_is_safe (p : Problem sig) (reason : StopReason) :
    (Outcome.stopped reason []).Correct p := by
  intro σ hσ
  exact False.elim (List.not_mem_nil hσ)

/-- In particular, a satisfiable problem may have an empty interrupted result. -/
theorem stopped_empty_can_be_satisfiable :
    (Outcome.stopped .resourceLimit []).Correct ([] : Problem sig) ∧
      Problem.Satisfiable ([] : Problem sig) := by
  refine ⟨stopped_empty_is_safe [] _, Substitution.identity, ?_⟩
  intro e he
  exact False.elim (List.not_mem_nil he)

/-- Requiring a single instantiating δ matters: one shared variable cannot
represent two distinct rigid constants, even if each is individually an
instance of a variable. -/
private abbrev checkSig : Signature where
  FreeSym := Empty
  CSym := Unit
  ACSym := Bool
  Atom := Nat
  arity := Empty.elim
  inputSort := fun f => Empty.elim f
  outputSort := Empty.elim
  cSort := fun _ => .msg
  acSort := fun isNat => if isNat then .nat else .msg
  atomSort := fun _ => .msg

theorem distinct_atoms_stay_distinct :
    ¬ EquivB (Term.atom (sig := checkSig) 0) (.atom 1) := by
  intro h
  let model : Model checkSig := { weightModel checkSig with atom := id }
  have hm := h.eval_eq model (fun _ => 1)
  change (0 : Nat) = 1 at hm
  contradiction

theorem shared_variable_cannot_match_distinct_atoms (t : Term checkSig) :
    ¬ (EquivB (sig := checkSig) (.atom 0) t ∧ EquivB (sig := checkSig) (.atom 1) t) := by
  intro ⟨ha, hb⟩
  exact distinct_atoms_stay_distinct (.trans ha hb.symm)

/-- A sort-narrowing substitution is admitted by the contract. -/
private def msgVar : Variable := ⟨0, .msg⟩
private def pubVar : Variable := ⟨1, .pub⟩

def narrowToPub : Substitution checkSig where
  image := fun v => if v = msgVar then .var pubVar else .var v
  support := [msgVar]
  outside := by
    intro v hv
    have hn : v ≠ msgVar := by simpa using hv
    simp [hn]
  sorted := by
    intro v
    split
    · next h => subst v; exact .widen (.var pubVar) .pub_msg
    · exact .var v

theorem narrowing_solves :
    Problem.Solves (sig := checkSig) [⟨.var msgVar, .var pubVar⟩] narrowToPub := by
  intro e he
  have heq : e = ⟨.var msgVar, .var pubVar⟩ := by simpa using he
  subst e
  simp only [Substitution.apply, Term.subst, narrowToPub]
  have hne : pubVar ≠ msgVar := by decide
  simp only [ite_true, ite_eq_right hne]
  exact .refl _

end Tamarin.SpecChecks
