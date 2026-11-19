import Tamarin.DHPeerClassification

/-! Query variables belong to the caller. Only the three message witnesses
are reassigned when instantiating an arm. Thus every component, including
repeated powers and separately observed base/exponent variables, is
explained by the same normalized substitution. -/
namespace Tamarin.Rewriting.DHPeer
variable {sig : Signature}

def Slot.sort : Slot → SortId
  | .fresh => .fresh
  | _ => .msg

structure Names where
  var : Slot → Variable
  distinct : ∀ i j, var i = var j → i = j
  sorted : ∀ i, (var i).sort = i.sort

def Names.symbolic (q : Names) (i : Slot) : Term sig := .var (q.var i)

theorem Names.typed (q : Names) (i : Slot) : HasSort (q.symbolic (sig := sig) i) .msg := by
  have h : HasSort (q.symbolic (sig := sig) i) i.sort := q.sorted i ▸ HasSort.var (q.var i)
  cases i <;> first | exact h | exact .widen h .fresh_msg

inductive Observation (sig : Signature) where
  | power
  | context (t : Term sig)

def Names.witness (q : Names) (v : Variable) : Prop :=
  v = q.var .base ∨ v = q.var .pos ∨ v = q.var .neg

end Tamarin.Rewriting.DHPeer
