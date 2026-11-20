import Tamarin.BilinearTableSchema
import Tamarin.RuleSchema
import Tamarin.TableAmbient

/-! Infer a point-action and commutative map from the oriented transfer to
a DH power. Each candidate's complete three equations are reconstructed and
checked modulo the declared structural axioms. -/
namespace Tamarin.BilinearTable
open Rewriting DHPeer Bilinear TotalUnifyWire
variable {d : Dictionary}

private def candidate (dh : Symbols d.sig) (r : Equation d.sig) : Option (Operators d.sig) := do
  let .free pow _ := r.rhs | none
  guard (pow == dh.pow)
  let .comm emap l t := r.lhs | none
  let pmult ← match l,t with
    | .var _,.free p _ | .free p _,.var _ => some p
    | _,_ => none
  guard (pmult != dh.pow)
  if h : d.sig.arity pmult = 2 ∧ (∀ i, d.sig.inputSort pmult i = .msg) ∧
      d.sig.outputSort pmult = .msg ∧ d.sig.cSort emap = .msg then
    return ⟨pmult,emap,h.1,h.2.1,h.2.2.1,h.2.2.2⟩
  else none

def detect (dh : Symbols d.sig) (rs : Problem d.sig) : List (Schema d.sig) :=
  rs.filterMap fun r => do
    let ops ← candidate dh r
    let matchRow (k : Bilinear.Rule) (e : Equation d.sig) :=
      (RuleSchema.recover (n := 3) (fun _ => .msg) (fun vs => k.equation dh ops (fun i => .var (vs i))) e).map Subtype.val
    let extract ← matchRow .extract r
    let unit ← rs.findSome? (matchRow .one)
    let nested ← rs.findSome? (matchRow .nested)
    let keys : Bilinear.Rule → RuleSchema.Keys (n := 3) (fun _ => .msg)
      | .one => unit | .nested => nested | .extract => extract
    return ⟨ops,fun k => (keys k).atSlot,fun k => (keys k).typed,fun k => (keys k).distinct⟩

def liftSchema (a : Schema d.sig) : Schema (TableAmbient.sig d) where
  ops := ⟨.inl a.ops.pmult,.inl a.ops.emap,a.ops.arity,a.ops.inputs,a.ops.pointSort,a.ops.mapSort⟩
  keys := a.keys
  typed := a.typed
  distinct := a.distinct

end Tamarin.BilinearTable
