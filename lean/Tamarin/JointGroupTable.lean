import Tamarin.GroupTable
import Tamarin.MixedGroupPresentation

/-! The two-group entry point specializes the general table composition. -/
namespace Tamarin.JointGroupTable
open Rewriting DHPeer
variable {sig : Signature} [DecidableEq sig.FreeSym] [DecidableEq sig.CSym]
  [DecidableEq sig.ACSym] [DecidableEq sig.Atom]

def accepts (s : Symbols sig) (keys : Fin 3 → Variable) (x : XorTable.Schema sig)
    (w : Head sig → Nat) (fuel : Nat) (rs : Problem sig) : Bool :=
  GroupTable.accepts s keys [GroupTable.xor s x] (fun _ => w) fuel rs

theorem accepts_sound (s : Symbols sig) (keys : Fin 3 → Variable) (x : XorTable.Schema sig)
    (typed : ∀ i, (keys i).sort = .msg) (distinct : ∀ i j, keys i = keys j → i = j)
    {w fuel rs} (ok : accepts s keys x w fuel rs) :
    ReferenceReduction.Bound rs ∧ MaudeOperations.CanonicalPresentation (ruleRoot rs) ∧
      MaudeOperations.FiniteVariantProperty (ruleRoot rs) :=
  GroupTable.accepts_sound typed distinct ok

end Tamarin.JointGroupTable
