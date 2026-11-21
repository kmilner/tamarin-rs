import Tamarin.NormalAlgebra
import Tamarin.MixedGroundRows
import Tamarin.ConstructorRowOverlaps
import Tamarin.SymbolWeight

/-! A finite checker for standalone constructor-pattern presentations.
The local row test also applies to other heads of a mixed theory. -/
namespace Tamarin.ConstructorRows
open Rewriting ConstructorVariants
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
  [DecidableEq s.ACSym] [DecidableEq s.Atom]

def checkedRow (rs : Problem s) (fuel : Nat) (r : Equation s) : Bool :=
  projectionRow rs r || groundRow rs fuel r || overlapRow rs r

private theorem row_obligations {rs : Problem s} {fuel r} (mem : r ∈ rs)
    (scope : ReferenceReduction.Bound rs) (checked : checkedRow rs fuel r) :
    SubtermVariants.ResultRow rs r ∧ ((∀ q ∈ rs, Application q.lhs) → NormalAlgebra.UniqueRow rs r) := by
  simp only [checkedRow,Bool.or_eq_true] at checked
  rcases checked with (hp | hg) | ho
  · have ok := (projectionRow_iff rs r mem).mp hp
    exact ⟨.inl (ok.subterm mem),fun apps σ norm _ _ l k =>
      (ok.result mem apps σ norm l).trans (ok.result mem apps σ norm k).symm⟩
  · have ok := groundRow_sound scope hg
    exact ⟨.inl (ok.subterm mem),fun apps σ norm _ _ => ok.unique mem apps σ norm⟩
  · obtain ⟨pat,inert⟩ := overlapRow_shape ho
    refine ⟨.inr ⟨?_,inert⟩,fun apps σ norm _ _ l k =>
      (overlapRow_result ho mem apps σ norm l).trans (overlapRow_result ho mem apps σ norm k).symm⟩
    cases h : r.lhs <;> simp_all [Pattern]

theorem checkedRow_sound {rs : Problem s} {fuel r} (mem : r ∈ rs)
    (scope : ReferenceReduction.Bound rs) (apps : ∀ q ∈ rs, Application q.lhs)
    (ok : checkedRow rs fuel r) : SubtermVariants.ResultRow rs r ∧ NormalAlgebra.UniqueRow rs r :=
  let h := row_obligations mem scope ok
  ⟨h.1,h.2 apps⟩

def accepts (w : Head s → Nat) (fuel : Nat) (rs : Problem s) : Bool :=
  SymbolWeight.decreasing w rs && TableDecrease.sorted rs && rs.all (checkedRow rs fuel)

/-- Without a builtin theory, the same per-row certificates prove both
convergence and the finite variant property for all open and kind-level tuples. -/
theorem accepts_sound {w fuel rs} (ok : accepts (s := s) w fuel rs) :
    ReferenceReduction.Bound rs ∧ MaudeOperations.CanonicalPresentation (ruleRoot rs) ∧
      MaudeOperations.FiniteVariantProperty (ruleRoot rs) := by
  obtain ⟨⟨wf,sorts⟩,rows⟩ := Bool.and_eq_true_iff.mp ok |>.imp_left Bool.and_eq_true_iff.mp
  have scope := SymbolWeight.bound wf
  have facts r (h : r ∈ rs) := row_obligations h scope (List.all_eq_true.mp rows r h)
  have shapes := fun r (hr : r ∈ rs) => (facts r hr).1
  have apps : ∀ r ∈ rs, Application r.lhs := fun r hr => (shapes r hr).application
  have base : NormalAlgebra.Presentation rs := ⟨apps,SymbolWeight.terminating wf,TableDecrease.sortPreserving sorts⟩
  have can := base.canonical_of_inert_ac (by
    intro f h
    obtain ⟨r,hr,headEq⟩ := List.mem_map.mp h
    exact (shapes r hr).not_ac f headEq)
    (fun r hr => (facts r hr).2 apps)
  exact ⟨scope,can,SubtermVariants.finiteResultVariants scope can shapes⟩

end Tamarin.ConstructorRows
