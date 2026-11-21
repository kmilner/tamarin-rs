import Tamarin.GroupPresentationParts
import Tamarin.BilinearTableSchema
import Tamarin.BilinearRowCanonical
import Tamarin.BilinearOperatorPaths

/-! A DH presentation can admit a list of additional certified components.
An extension proves its local laws in any table providing the requested DH
and local inventories. The same composition theorem handles all combinations. -/
namespace Tamarin.GroupTable
open Rewriting DHPeer ConstructorVariants PresentationComponents GroupPresentationParts
variable {sig : Signature}
variable [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]

structure Extension (s : Symbols sig) extends Part sig where
  localProof : ∀ {T : Table s} {E : ExtraTable T}, ProtectedTable E →
    Inventory toPart T.rules → ∀ h ∈ ruleHeads T.rules, owns h → Local T.rules h

def independent (s : Symbols sig) (c : Independent sig) : Extension s where
  toPart := c.toPart
  localProof dh inv := c.localProof inv dh.apps

def xor (s : Symbols sig) (x : XorTable.Schema sig) : Extension s where
  toPart := xorPart x
  localProof dh inc := xorLocal x inc dh.apps

def bilinear (s : Symbols sig) (b : BilinearTable.Schema sig) : Extension s where
  toPart := ⟨b.owns,b.rows s⟩
  localProof {T} {E} dh inc h _ owned := by
    let I := b.inventory s T.rules inc.present inc.only dh.apps
    cases h with
    | free f =>
      obtain rfl : f = b.ops.pmult := eq_of_beq owned
      exact ⟨fun r hr e => I.uniqueRow dh r hr (.inl e),I.free_bound dh⟩
    | comm f =>
      obtain rfl : f = b.ops.emap := eq_of_beq owned
      exact ⟨fun r hr e => I.uniqueRow dh r hr (.inr e),I.comm_bound dh⟩
    | _ => contradiction

def accepts (s : Symbols sig) (ks : Fin 3 → Variable) (es : List (Extension s)) (w : Problem sig → Head sig → Nat)
    (fuel : Nat) (rs : Problem sig) : Bool :=
  PresentationComponents.accepts (dhPart s ks :: es.map Extension.toPart) w fuel rs

theorem accepts_sound {s : Symbols sig} {ks : Fin 3 → Variable} {es : List (Extension s)}
    (typed : ∀ i, (ks i).sort = .msg) (inj : ∀ i j, ks i = ks j → i = j) {w fuel rs}
    (ok : accepts s ks es w fuel rs) : ReferenceReduction.Bound rs ∧
    MaudeOperations.CanonicalPresentation (ruleRoot rs) ∧ MaudeOperations.FiniteVariantProperty (ruleRoot rs) := by
  let facts := evidence ok
  have dhInc := facts.inventory _ List.mem_cons_self
  let dh := protectedDH dhInc typed inj facts.pres.apps
  apply facts.complete
  intro p hp h used owned
  rcases List.mem_cons.mp hp with rfl | extra
  · exact dhLocal dhInc typed inj facts.pres.apps h used owned
  · obtain ⟨ext,mem,rfl⟩ := List.mem_map.mp extra
    exact ext.localProof dh (facts.inventory _ (List.mem_cons_of_mem _ (List.mem_map_of_mem mem))) h used owned

end Tamarin.GroupTable
