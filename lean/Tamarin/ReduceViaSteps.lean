import Tamarin.MaudeOperations
import Tamarin.ConstructorVariants

namespace Tamarin.MaudeOperations
open Rewriting
variable {s : Signature} {R : Root s}

/-- A strategy may pick any genuine rewrite. Reporting no step must rule out
all positions and all ways of exposing a redex modulo B. -/
structure StepFinder (R : Root s) where
  next : Term s → Option (Term s)
  stoppedAtNormal : ∀ t, next t = none → Normal R t
  step : ∀ t u, next t = some u → StepModulo R t u

private def normalize (theory : CanonicalPresentation R) (finder : StepFinder R)
    (t : Term s) : {u // NormalForm R t u} :=
  match h : finder.next t with
  | none => ⟨t, .basis (.refl _), finder.stoppedAtNormal t h, fun _ hs => hs⟩
  | some next =>
    have fired := finder.step t next h
    let result := normalize theory finder next
    ⟨result.val, .trans (.step fired) result.property.1, result.property.2.1,
      fun k hs => result.property.2.2 k (theory.sortPreserving fired k hs)⟩
termination_by theory.terminating.wrap t
decreasing_by exact finder.step t next h

/-- Confluence modulo B makes the endpoint independent of which redex was
chosen. The recursion follows the presentation's termination proof directly. -/
def reducerOfSteps (theory : CanonicalPresentation R) (finder : StepFinder R) : VerifiedReducer R where
  reduce t := (normalize theory finder t).val
  correct t := by
    have nf := (normalize theory finder t).property
    refine ⟨nf, fun _ other => ?_⟩
    obtain ⟨_, left, right⟩ := theory.confluent other.1 nf.1
    exact (normal_reduces_equiv left other.2.1).trans (normal_reduces_equiv right nf.2.1).symm

end Tamarin.MaudeOperations
