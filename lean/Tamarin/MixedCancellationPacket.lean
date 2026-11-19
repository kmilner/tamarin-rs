import Tamarin.MixedCancellationVariants
import Tamarin.MixedCancellationRows

/-! Decode the four mask words in a shared, sorted witness scope, as in the
direct Rust adapter. The fold on numbered witnesses may be represented modulo B. -/
namespace Tamarin.Rewriting.MixedCancellation
variable {sig : Signature}

def decodeMask (T : BinaryXor.Table sig) (w : Names) (mask : UInt64) : Option (Term sig) :=
  if mask ≤ 7 then
    some (T.value (operands (mask &&& 1 != 0) (mask &&& 2 != 0) (mask &&& 4 != 0)
      (.var w.h) (.var w.i) (.var w.j)))
  else none

def decodeRow (T : BinaryXor.Table sig) (w : Names) (row : Array UInt64) :
    Option (Term sig × Term sig × Term sig × Term sig) :=
  match row.toList with
  | [a,b,x,o] => do return (← decodeMask T w a, ← decodeMask T w b, ← decodeMask T w x, ← decodeMask T w o)
  | _ => none

theorem decode_packet (T : BinaryXor.Table sig) (w : Names) (sh : Shape) :
    decodeRow T w sh.packet = some (w.images T sh) := by
  cases sh with
  | diagonal => rfl
  | separate l r tail => cases l <;> cases r <;> cases tail <;> rfl

structure PacketArm (q : Query sig) (row : Array UInt64) (arm : Variant sig) : Prop where
  outside : ∀ v, v ≠ q.a → v ≠ q.b → v ≠ q.x → arm.subst.image v = .var v
  terms : ∃ (w : Names) (a b x out : Term sig), decodeRow q.table w row = some (a,b,x,out) ∧
    EquivB (arm.subst.image q.a) a ∧ EquivB (arm.subst.image q.b) b ∧
    EquivB (arm.subst.image q.x) x ∧ ∃ actual, arm.values = [actual] ∧ EquivB actual out

theorem PacketArm.decodes {q : Query sig} {sh : Shape} {arm : Variant sig}
    (packet : PacketArm q sh.packet arm) : Decodes q sh arm := by
  obtain ⟨w,a,b,x,o,e,ha,hb,hx,v,hv,ho⟩ := packet.terms
  have decoded := Option.some.inj ((decode_packet q.table w sh).symm.trans e)
  refine ⟨packet.outside,w,v,hv,?_⟩
  rw [decoded]
  exact ⟨ha,hb,hx,ho⟩

theorem packetFamily_complete (q : Query sig) (rows : Array (Array UInt64)) (ok : RowsCorrect rows)
    (arms : List (Variant sig)) (all : ∀ row ∈ rows, ∃ a ∈ arms, PacketArm q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ rows, PacketArm q row a) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] := by
  apply complete q arms
  · intro sh
    obtain ⟨a,mem,arm⟩ := all sh.packet ((ok _).mpr ⟨sh,rfl⟩)
    exact ⟨a,mem,arm.decodes⟩
  · intro a mem
    obtain ⟨row,hr,arm⟩ := only a mem
    obtain ⟨sh,rfl⟩ := (ok _).mp hr
    exact ⟨sh,arm.decodes⟩

end Tamarin.Rewriting.MixedCancellation
