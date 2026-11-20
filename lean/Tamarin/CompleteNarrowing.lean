import Tamarin.TablePositions
import Tamarin.KindACNarrowing
import Tamarin.MixedUnification
import Tamarin.NarrowingClash

/-! Narrowing at all positions of any arity-correct input tuple. The unifier
and the narrowing traversal are fixed executable references. The assumptions
for the four-command bundle concern only the active rewrite presentation. -/
namespace Tamarin.TableNarrowing
open Rewriting MaudeOperations ReferenceVariantFrontier
variable {s : Signature}
variable {rules : List (Equation s)} {n : Nat}

/-- A rewrite of a variable would specialize to a rewrite of every term of
its sort. Sort preservation would then give an infinite descent, contradicting
termination. This applies to tables admitting kind-level terms as well. -/
theorem variablesNormal (canonical : CanonicalPresentation (ruleRoot rules)) :
    Normalized (ruleRoot rules) Substitution.identity := by
  intro w rhs fire
  have impossible (t : Term s) : HasSort t w.sort → False := by
    induction t using canonical.terminating.induction with
    | h t smaller =>
      intro typed
      let σ := Substitution.binding w t typed
      have st := SpecializedFresh.stepModulo_subst rules σ fire
      have source : σ.apply (Substitution.identity.image w) = t := by simp [σ,Substitution.apply,
        Substitution.identity,Term.subst,Substitution.binding]
      rw [source] at st
      exact smaller _ st (canonical.sortPreserving st _ typed)
  exact impossible (.var w) (.var w)

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def groups (u : VerifiedUnifier s (fun _ => True)) (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) : Groups rules where
  branches := KindACNarrowing.roots u bound
  genuine := KindACNarrowing.roots_genuine u bound
  covers := fun f a t ρ _ st => KindACNarrowing.roots_cover u bound vars f a t ρ st

/-- Every specialized rewrite at an admissible tuple point has a genuine
branch, with a single further substitution explaining all inputs and values. -/
def narrower (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s) :
    FoldingNarrowing.Narrower rules query :=
  let u := NarrowingClash.unifier (MixedUnification.verified (s := s))
  positional u bound (groups u bound vars) query

/-- All four commands over a range-restricted finite rewrite table.
Canonicality and the finite variant property must hold on the admitted
kind-level terms. Neither supplies an external narrowing or unification oracle. -/
def reference (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) (finite : FiniteVariantProperty (ruleRoot rules)) :
    MaudeOperations.Reference s rules :=
  FoldingNarrowing.reference MixedUnification.solve MixedUnification.complete bound canonical
    (variablesNormal canonical) finite (fun q => narrower bound (variablesNormal canonical) (fun i => q[i.val]))

end Tamarin.TableNarrowing
