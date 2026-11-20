import Tamarin.DHChurchRosser
import Tamarin.DHChurchRosserProduct

/-! Canonicality of a mixed DH table from its own termination and sort checks
and the normal forms of the additional root equations. Only normalized
substitution instances of these equations require a uniqueness proof. -/
namespace Tamarin.Rewriting.DHPeer.ChurchRosser
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

theorem Extension.of_checks (dh : ProtectedTable E) (w : Head sig → Nat)
    (decreasing : SymbolWeight.decreasing w T.rules) (sorted : TableDecrease.sorted T.rules)
    (neutral : Head.free s.neutral ∉ ruleHeads T.rules)
    (otherAC : ∀ f, f ≠ s.mul → Head.ac f ∉ ruleHeads T.rules) : Extension E where
  toProtectedTable := dh
  terminating := SymbolWeight.terminating decreasing
  sortPreserving := TableDecrease.sortPreserving sorted
  neutralNormal := constructor_node_normal _ dh.apps _ neutral (fun i => Fin.elim0 (s.neutralArity ▸ i))
  otherAC := otherAC

theorem Extension.canonical (ext : Extension E)
    (rows : ∀ r ∈ T.rules, ¬ DHHead s (head r.lhs) → UniqueRow T.rules r) :
    MaudeOperations.CanonicalPresentation (ruleRoot T.rules) := by
  classical
  exact ext.canonical_of_rows (protectedProduct ext.toProtectedTable) rows

end Tamarin.Rewriting.DHPeer.ChurchRosser
