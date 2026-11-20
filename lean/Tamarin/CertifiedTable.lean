import Tamarin.ConstructorPresentation
import Tamarin.DHConstructorExtension
import Tamarin.DHWireSymbols
import Tamarin.SubtermDecrease

/-! Certify the decoded table in its full ambient signature. Symbol and variable
IDs may vary with the query. Matching a characteristic rule only proposes an
interpretation; the certificate checks the complete oriented rule table. -/
namespace Tamarin.CertifiedTable
open TotalUnifyWire Rewriting DHPeer MaudeOperations
variable {d : Dictionary}

private structure Tower (s : Signature) where
  pow : s.FreeSym
  mul : s.ACSym
  x : Variable
  y : Variable
  z : Variable

private def tower {s : Signature} [DecidableEq s.FreeSym] (r : Equation s) : Option (Tower s) := do
  let .free pow args := r.lhs | none
  let [.free inner pair,.var z] := List.ofFn args | none
  let [.var x,.var y] := List.ofFn pair | none
  let .free outer result := r.rhs | none
  let [.var base,.ac mul _ _] := List.ofFn result | none
  guard (inner == pow && outer == pow && base == x)
  return ⟨pow,mul,x,y,z⟩

private def unit {s : Signature} [DecidableEq s.FreeSym] (pow : s.FreeSym) (r : Equation s) : Option s.FreeSym := do
  let .free f args := r.lhs | none
  let [.var x,.free one _] := List.ofFn args | none
  let .var v := r.rhs | none
  guard (f == pow && x == v && s.arity one == 0)
  return one

private def neutral {s : Signature} [DecidableEq s.FreeSym] (pow : s.FreeSym) (r : Equation s) : Option s.FreeSym := do
  let .free f args := r.lhs | none
  let [.free n _,.var _] := List.ofFn args | none
  let .free rhs _ := r.rhs | none
  guard (f == pow && n == rhs && s.arity n == 0)
  return n

private def inverse {s : Signature} [DecidableEq s.FreeSym] (r : Equation s) : Option s.FreeSym := do
  let .free f args := r.lhs | none
  let [.free g xs] := List.ofFn args | none
  let [.var x] := List.ofFn xs | none
  let .var rhs := r.rhs | none
  guard (f == g && x == rhs)
  return f

private def detect (rs : Problem d.sig) : Option (Symbols d.sig × (Fin 3 → Variable)) := do
  let t ← rs.findSome? (tower (s := d.sig))
  let o ← rs.findSome? (unit t.pow)
  let n ← rs.findSome? (neutral t.pow)
  let i ← rs.findSome? (inverse (s := d.sig))
  let decl ← DHWire.readSymbols t.pow i o n t.mul
  return (decl,fun k => match k with | 0 => t.x | 1 => t.y | 2 => t.z)

private def weight {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] (base : Head s → Nat) (rs : Problem s) : Head s → Nat :=
  if SymbolWeight.decreasing base rs then base else SubtermDecrease.defaultWeight base rs

private def ordinary (rs : Problem (TableAmbient.sig d)) (fuel : Nat) :=
  ConstructorRows.accepts (weight (fun _ => 1) rs) fuel rs

private def dh (rs : Problem (TableAmbient.sig d)) (fuel : Nat)
    (s : Symbols d.sig) (ks : Fin 3 → Variable) : Bool :=
  decide (∀ i, (ks i).sort = .msg) && decide (∀ i j, ks i = ks j → i = j) &&
    ConstructorExtension.accepts (DHWire.liftSymbols s) ks (weight ExactTable.weight rs) fuel rs

def admits (rs : Problem d.sig) (fuel : Nat) : Bool :=
  let ambient := TableAmbient.liftRules rs
  if rs.any (fun r => match r.lhs with | .ac .. => true | _ => false) then
    (detect rs).any (fun (s,ks) => dh ambient fuel s ks)
  else ordinary ambient fuel

theorem admits_sound {rs : Problem d.sig} {fuel} (ok : admits rs fuel) :
    ReferenceReduction.Bound (TableAmbient.liftRules rs) ∧ CanonicalPresentation (ruleRoot (TableAmbient.liftRules rs)) ∧
      FiniteVariantProperty (ruleRoot (TableAmbient.liftRules rs)) := by
  unfold admits at ok
  dsimp only at ok
  split at ok
  · cases hit : detect rs with
    | none => simp [hit] at ok
    | some pair =>
      obtain ⟨s,ks⟩ := pair
      simp only [hit,Option.any_some,dh,Bool.and_eq_true,decide_eq_true_eq] at ok
      obtain ⟨⟨typed,distinct⟩,accepted⟩ := ok
      exact ConstructorExtension.accepts_sound _ _ typed distinct accepted
  · exact ConstructorRows.accepts_sound ok

end Tamarin.CertifiedTable
