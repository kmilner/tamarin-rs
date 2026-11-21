import Tamarin.ConstructorPresentation
import Tamarin.DHConstructorExtension
import Tamarin.DHWireSymbols
import Tamarin.SubtermDecrease
import Tamarin.XorPresentation
import Tamarin.XorTableWire
import Tamarin.GroupTable
import Tamarin.BilinearTableWire
import Tamarin.UserAC

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

private def components (xs : List (XorTable.Schema d.sig)) (units : List (UserAC.Schema d.sig)) :
    List (PresentationComponents.Independent (TableAmbient.sig d)) :=
  (xs.map fun x =>
    let a := XorTable.liftSchema x
    ⟨GroupPresentationParts.xorPart a,fun inv apps => GroupPresentationParts.xorLocal a inv apps⟩) ++
  units.map fun u =>
    let a := UserAC.liftSchema u
    ⟨a.part,a.localProof⟩

private def dh (rs : Problem d.sig) (fuel : Nat) (s : Symbols d.sig)
    (ks : Fin 3 → Variable) (xs : List (XorTable.Schema d.sig))
    (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) : Bool :=
  let ambient := TableAmbient.liftRules rs
  let dh := DHWire.liftSymbols s
  let extensions := parts.map (GroupTable.independent dh) ++
    (BilinearTable.detect s rs).map (fun b => GroupTable.bilinear dh (BilinearTable.liftSchema b))
  let base : Head (TableAmbient.sig d) → Nat
    | .ac (.inl f) => if xs.any (fun a => a.f == f) then 2 else 1
    | h => ExactTable.weight h
  let weights := fun (whole : Problem (TableAmbient.sig d)) =>
    let inferred := SubtermDecrease.proposeWeight (fun _ => 1) whole
    if SymbolWeight.decreasing inferred whole then inferred else SubtermDecrease.proposeWeight base whole
  decide (∀ i, (ks i).sort = .msg) && decide (∀ i j, ks i = ks j → i = j) &&
    GroupTable.accepts dh ks extensions weights fuel ambient

private def withoutDH (rs : Problem (TableAmbient.sig d)) (fuel : Nat)
    (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) : Bool :=
  PresentationComponents.accepts (parts.map PresentationComponents.Independent.toPart)
    (SubtermDecrease.proposeWeight (fun _ => 1)) fuel rs

def admits (rs : Problem d.sig) (fuel : Nat) : Bool :=
  let ambient := TableAmbient.liftRules rs
  if rs.any (fun r => match r.lhs with | .ac .. => true | _ => false) then
    let xs := XorTable.candidates rs
    let parts := components xs (UserAC.candidates rs)
    (detect rs).any (fun (s,ks) => dh rs fuel s ks xs parts) || withoutDH ambient fuel parts
  else withoutDH ambient fuel []

theorem admits_sound {rs : Problem d.sig} {fuel} (ok : admits rs fuel) :
    ReferenceReduction.Bound (TableAmbient.liftRules rs) ∧ CanonicalPresentation (ruleRoot (TableAmbient.liftRules rs)) ∧
      FiniteVariantProperty (ruleRoot (TableAmbient.liftRules rs)) := by
  unfold admits at ok
  dsimp only at ok
  split at ok
  · rcases Bool.or_eq_true_iff.mp ok with dhOK | otherOK
    · obtain ⟨⟨s,ks⟩,_,found⟩ := (Option.any_eq_true _ _).mp dhOK
      simp only [dh,Bool.and_eq_true,decide_eq_true_eq] at found
      obtain ⟨⟨typed,distinct⟩,accepted⟩ := found
      exact GroupTable.accepts_sound typed distinct accepted
    · exact PresentationComponents.independent_complete otherOK
  · exact PresentationComponents.independent_complete ok

end Tamarin.CertifiedTable
