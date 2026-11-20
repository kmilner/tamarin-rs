import Tamarin.TableConfluence
import Tamarin.MaudeOperationRefinements

namespace Tamarin.TableConfluence.Tests
open Rewriting MaudeOperations

-- The certificate admits even kind-level mixed C/AC contexts with no rules.
example (s : Signature) : CanonicalPresentation (ruleRoot (sig := s) []) := by
  apply ofDecreasing rfl rfl
  intro t a _ sa _
  exact False.elim ((emptyReducer s).correct t |>.normalForm.2.1 a sa)

-- X + Y -> X is sorted, strictly decreasing, and has just one rule. Swapping
-- the AC operands exposes a peak whose two irreducible variables never join.
private abbrev S := Pairing.signature
private def x : Variable := ⟨0,.msg⟩
private def y : Variable := ⟨1,.msg⟩
private def lhs : Term S := .ac 0 (.var x) (.var y)
private def rules : List (Equation S) := [⟨lhs,.var x⟩]

example : TableDecrease.decreasing rules ∧ TableDecrease.sorted rules := ⟨rfl,rfl⟩

example : ¬ LocalConfluence (ruleRoot rules) := by
  intro peaks
  have hit (a b : Term S) (ha : HasSort a .msg) (hb : HasSort b .msg) :
      StepModulo (ruleRoot rules) (.ac 0 a b) a := by
    let σ := Pairing.parameters x y a b ha hb
    exact ⟨_,_,.refl _,.root ⟨_,List.mem_singleton_self _,σ,by rfl,by rfl⟩,.refl _⟩
  have ⟨l,r,start,fire,finish⟩ := hit (.var y) (.var x) (.var y) (.var x)
  have swap : StepModulo (ruleRoot rules) lhs (.var y) :=
    ⟨l,r,(EquivB.ac_swap (sig := S) 0 _ _).trans start,fire,finish⟩
  obtain ⟨w,left,right⟩ := peaks (hit (.var x) (.var y) (.var x) (.var y)) swap
  have vars := (ConstructorVariants.constructor_normal rules (fun _ hr => List.mem_singleton.mp hr ▸ trivial)).1
  have e := (normal_reduces_equiv left (vars x)).trans (normal_reduces_equiv right (vars y)).symm
  exact nomatch e.head_eq

end Tamarin.TableConfluence.Tests
