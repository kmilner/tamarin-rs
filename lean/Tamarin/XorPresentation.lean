import Tamarin.ActiveAC
import Tamarin.XorProductCanonical
import Tamarin.XorProductPaths
import Tamarin.XorTable

/-! Whole-table completeness for an exponent-two AC group with additional
constructor equations. All local results refer to the reconstructed table,
then agreement modulo C/AC transfers them to the original oriented rules. -/
namespace Tamarin.XorTable
open Rewriting ConstructorVariants MaudeOperations
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
  [DecidableEq s.ACSym] [DecidableEq s.Atom]

theorem accepts_sound {a : Schema s} {w fuel rs} (ok : accepts a w fuel rs) :
    ReferenceReduction.Bound rs ∧ CanonicalPresentation (ruleRoot rs) ∧ FiniteVariantProperty (ruleRoot rs) := by
  classical
  obtain ⟨T,e⟩ := accepts_evidence ok
  have xor : ActiveAC.Operator T.rules T.f := {
    product := BinaryXor.product T e.typed
    unique := fun r hr h => BinaryXor.uniqueRow T r hr h (e.typed r hr h)
    bounded := ⟨2,BinaryXor.kind_paths T (BinaryXor.redex_typed T e.typed)⟩ }
  obtain ⟨can,finite⟩ := ActiveAC.complete e.presentation e.scope (fun f active => by
    by_cases same : f = T.f
    · subst f; exact xor
    · exact (e.inactive f same active).elim) (fun r hr h => e.other r hr (h T.f))
  exact ⟨TablePresentation.bound_of_agrees e.agrees e.scope,
    (TablePresentation.canonical_iff e.agrees).mpr can,(TablePresentation.finite_iff e.agrees).mpr finite⟩

end Tamarin.XorTable
