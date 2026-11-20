import Tamarin.DHFiniteVariants
import Tamarin.DHWireData
import Tamarin.TablePresentation
import Tamarin.TableAmbient
import Tamarin.TableWire
import Tamarin.CheckedReduction

/-! The normal Rust table encoder records all five DH symbols, the complete
oriented rule table, and the five operator observations. Check the decoded
table modulo C/AC, preserving variable identities and direction on both
sides of each row. The variant command adds arbitrary ambient atoms. -/
namespace Tamarin.DHWire
open Rewriting DHPeer MaudeOperations TotalUnifyWire
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

private def packet := TableWire.input declarations nodes ruleRoots observationRoots
private def parsed := packet.get (by decide +kernel)
abbrev dict := parsed.1
abbrev rules := parsed.2.1
abbrev observations := parsed.2.2

theorem decoded : TableWire.input declarations nodes ruleRoots observationRoots =
    some ⟨dict,rules,observations⟩ := Option.some_get _ |>.symm

def symbols : Symbols dict.sig where
  pow := ⟨0,by decide +kernel⟩
  inv := ⟨1,by decide +kernel⟩
  one := ⟨2,by decide +kernel⟩
  neutral := ⟨3,by decide +kernel⟩
  mul := ⟨4,by decide +kernel⟩
  powArity := by decide +kernel
  invArity := by decide +kernel
  oneArity := by decide +kernel
  neutralArity := by decide +kernel
  powInput := by decide +kernel
  invInput := by decide +kernel
  powSort := by decide +kernel
  invSort := by decide +kernel
  oneSort := by decide +kernel
  neutralSort := by decide +kernel
  mulSort := by decide +kernel

def ambient : Symbols (TableAmbient.sig dict) :=
  ⟨.inl symbols.pow,.inl symbols.inv,.inl symbols.one,.inl symbols.neutral,.inl symbols.mul,
   symbols.powArity,symbols.invArity,symbols.oneArity,symbols.neutralArity,
   symbols.powInput,symbols.invInput,symbols.powSort,symbols.invSort,symbols.oneSort,symbols.neutralSort,symbols.mulSort⟩

private def v (i : Fin 3) : Variable := ⟨i.val,.msg⟩
private theorem typed (i : Fin 3) : (v i).sort = .msg := rfl
private theorem inj (i j : Fin 3) (h : v i = v j) : i = j := Fin.ext (congrArg Variable.id h)

theorem local_agrees : TablePresentation.Agrees rules (Schemas.rules symbols v) := by decide +kernel

theorem ambient_agrees :
    TablePresentation.Agrees (TableAmbient.liftRules rules) (Schemas.rules ambient v) := by decide +kernel

/-- Other Rust queries may number the same operators and rule variables
differently. Computing agreement in their own dictionaries suffices. -/
theorem complete_of_agrees {sig : Signature} [DecidableEq sig.FreeSym] [DecidableEq sig.CSym]
    [DecidableEq sig.ACSym] [DecidableEq sig.Atom] {p : Problem sig} (s : Symbols sig)
    (keys : Fin 3 → Variable) (types : ∀ i, (keys i).sort = .msg) (unique : ∀ i j, keys i = keys j → i = j)
    (check : TablePresentation.Agrees p (Schemas.rules s keys)) :
    CanonicalPresentation (ruleRoot p) ∧ FiniteVariantProperty (ruleRoot p) := by
  have tab := Schemas.exactTable s keys types unique
  exact ⟨(TablePresentation.canonical_iff check).mpr tab.canonical,
    (TablePresentation.finite_iff check).mpr tab.finiteVariantProperty⟩

theorem local_complete :
    CanonicalPresentation (ruleRoot rules) ∧ FiniteVariantProperty (ruleRoot rules) :=
  complete_of_agrees symbols v typed inj local_agrees

theorem ambient_complete :
    CanonicalPresentation (ruleRoot (TableAmbient.liftRules rules)) ∧
    FiniteVariantProperty (ruleRoot (TableAmbient.liftRules rules)) :=
  complete_of_agrees ambient v typed inj ambient_agrees

theorem ambient_bound : ReferenceReduction.Bound (TableAmbient.liftRules rules) :=
  (CheckedReduction.rangeBound_iff _).mp (by decide +kernel)

end Tamarin.DHWire
