import Tamarin.TableAmbient
import Tamarin.CheckedVariants

namespace Tamarin.TableAmbient.Tests
open Rewriting

private def d : TotalUnifyWire.Dictionary := ⟨[],[]⟩
private def x : Variable := ⟨4,.msg⟩
private abbrev termX : Term d.sig := .var x
private def unseen : Term (sig d) := .atom (.inr (UInt64.size + 7,.msg))
private def capture : Substitution (sig d) := Substitution.binding x unseen (.atom _)

-- An unseen name is available to a caller even with an empty packet
-- dictionary. It cannot be serialized as a concrete binding in an answer.
#guard (emit [termX] [⟨capture,[unseen]⟩]).isNone

-- The checked family still represents x = unseen by instantiating its
-- returned variable. The same substitution must explain the stored value.
#guard
  match CheckedVariants.solve (liftRules (d := d) []) [liftTerm termX] 1 2 with
  | none => false
  | some result =>
    (emit [termX] result.val).isSome &&
      result.val.any fun a =>
        ReferenceMatching.equal (capture.apply (a.subst.image x)) unseen &&
        match a.values with
        | [t] => ReferenceMatching.equal (capture.apply t) unseen
        | _ => false

end Tamarin.TableAmbient.Tests
