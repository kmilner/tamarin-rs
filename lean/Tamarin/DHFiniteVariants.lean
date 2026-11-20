import Tamarin.DHChurchRosser
import Tamarin.DHChurchRosserProduct

/-! Finite variants of Tamarin's thirteen DH rules for the full term kind.
The presentation permits arbitrary additional free, C, and AC constructors. -/
namespace Tamarin.Rewriting.DHPeer
open MaudeOperations ShortVariantPaths ConstructorVariants

variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- All root symbols have a uniformly short choice of normalization after
normalizing their children. This covers kind-level powers, inverses, products,
and any inert context the caller may introduce. -/
theorem ExactTable.operators [DecidableEq sig.ACSym] (tab : ExactTable E) :
    Operators (ruleRoot T.rules) where
  free := tab.free_paths
  comm f := ⟨0,fun a b na nb => ⟨_,.basis (.refl _),constructor_node_normal _ tab.apps (.comm f a b)
    (tab.absent (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)) ⟨na,nb⟩⟩⟩
  ac f := by
    by_cases same : f = s.mul
    · subst f
      exact kind_product_paths tab.inventory tab.product tab.inverse tab.unit
    · exact ⟨0,fun a b na nb => ⟨_,.basis (.refl _),constructor_node_normal _ tab.apps (.ac f a b)
        (tab.absent (fun eq => same (Head.ac.inj eq)) (by intro e; cases e) (by intro e; cases e)) ⟨na,nb⟩⟩⟩

theorem ExactTable.canonical (tab : ExactTable E) : CanonicalPresentation (ruleRoot T.rules) := by
  classical
  exact ChurchRosser.canonical_of_product tab (ChurchRosser.kindProduct tab)

/-- Every finite tuple admits a finite covering family for the exact DH table. -/
theorem ExactTable.finiteVariantProperty (tab : ExactTable E) : FiniteVariantProperty (ruleRoot T.rules) := by
  classical
  exact finiteVariantProperty_of_operators (SymbolWeight.bound tab.decreasing) tab.canonical tab.operators

end Tamarin.Rewriting.DHPeer
