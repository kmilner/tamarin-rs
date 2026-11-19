import Tamarin.DHTowerSound
import Tamarin.DHTowerLinked
import Tamarin.DHTowerTuple

namespace Tamarin.Rewriting.DHTower.Caller
open DHPeer Packet
variable {sig : Signature}

structure Query (sig : Signature) extends Names where
  first : Term sig
  rest : List (Term sig)
  sortedFactors : ∀ t ∈ first :: rest, HasSort t .msg
  independent : ∀ t ∈ first :: rest, ¬t.Occurs (var .peer)
  disjoint : ∀ t ∈ first :: rest, ∀ v, t.Occurs v → ¬toNames.witness v

abbrev Query.fs (q : Query sig) := q.first :: q.rest
def Query.factor (q : Query sig) (i : Nat) : Term sig := q.fs[i]?.getD (q.symbolic .peer)
abbrev Query.op (q : Query sig) (s : Symbols sig) := Spine.tower s (q.symbolic .peer) q.first q.rest
abbrev Query.added (q : Query sig) (s : Symbols sig) := ACRepresentation.fold s.mul q.first q.rest

inductive Recipe where
  | unchanged | neutral | tower
  | cancel (mask : List Bool) (pos neg : Bool)
  deriving DecidableEq

def Recipe.Valid (n : Nat) : Recipe → Prop
  | .cancel m _ _ => m.length = n ∧ select m (List.range n) ≠ []
  | _ => True

/-- Associate a source template with precisely the rows whose postfix image
describes its selected occurrence positions and enabled witnesses. -/
inductive Reads (width : Nat) : Recipe → Packet.Image → Prop
  | unchanged : Reads width .unchanged (.var .peer)
  | neutral : Reads width .neutral .neutral
  | tower : Reads width .tower (.pow (.var .base) (.var .pos))
  | cancel {m p n i is} (size : m.length = width) (take : select m (List.range width) = i :: is) :
      Reads width (.cancel m p n) (Packet.cancel (Packet.product i is) p n)

def Recipe.base (q : Query sig) (s : Symbols sig) : Recipe → Term sig
  | .unchanged => q.symbolic .peer
  | .neutral => s.neutralTerm
  | .tower => s.power (q.symbolic .base) (q.symbolic .pos)
  | .cancel m p n => s.power (q.symbolic .base) (Balance.assemble s (parameter sig p (q.var .pos))
      (DHTower.append s (packed s (select m q.fs)) (parameter sig n (q.var .neg))))

def Recipe.value (q : Query sig) (s : Symbols sig) : Recipe → Term sig
  | .unchanged => s.power (q.symbolic .peer) (q.added s)
  | .neutral => s.neutralTerm
  | .tower => s.power (q.symbolic .base) (s.product.mul (q.symbolic .pos) (q.added s))
  | .cancel m p n => powerResult s (q.symbolic .base)
      (DHTower.append s (parameter sig p (q.var .pos)) (packed s (remaining m q.fs))) (parameter sig n (q.var .neg))

theorem Query.factorList (q : Query sig) : (List.range q.fs.length).map q.factor = q.fs := by
  apply List.ext_getElem <;> simp [Query.factor]
  intro i hi hi'; rw [getElem?_pos q.fs i hi']; rfl

end Tamarin.Rewriting.DHTower.Caller
