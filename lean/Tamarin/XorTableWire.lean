import Tamarin.XorTable
import Tamarin.TableAmbient
import Tamarin.RuleSchema

/-! Infer the operator declarations and rule-local variables from an XOR
presentation. All guesses are checked against the full table by `accepts`. -/
namespace Tamarin.XorTable
open TotalUnifyWire
variable {d : Dictionary}

private theorem output_not_fresh {ds : List Whole.Decl} (h : ds.all (fun decl => sortOf decl.output != .fresh))
    {k} (f : Symbol ds k) : sortOf (info f).output ≠ .fresh := by
  have found : decl ds k f.val = some (info f) := (Option.some_get f.property).symm
  exact bne_iff_ne.mp (List.all_eq_true.mp h _ (List.mem_of_find?_eq_some found))

/-- An AC head is inferred from its duplicate rule. Each equation may use
its own variable numbering. Sorting requirements are checked on declarations. -/
def candidates (rs : Problem d.sig) : List (Schema d.sig) :=
  if clean : d.decls.all (fun decl => sortOf decl.output != .fresh) then
    rs.filterMap fun r => do
      let .ac f (.var v) (.var w) := r.lhs | none
      let .free z _ := r.rhs | none
      guard (v == w)
      if h : d.sig.arity z = 0 ∧ d.sig.outputSort z = .msg ∧ d.sig.acSort f = .msg ∧ v.sort = .msg then
        let unit ← rs.findSome? fun row => (RuleSchema.recover (n := 1) (fun _ => .msg)
          (fun vs => unitEquation f r.rhs (vs 0)) row).map Subtype.val
        let triple ← rs.findSome? fun row => (RuleSchema.recover (n := 2) (fun _ => .msg)
          (fun vs => cancelEquation f (vs 0) (vs 1)) row).map Subtype.val
        return ⟨f,z,h.1,h.2.1,h.2.2.1,v,unit.atSlot 0,triple.atSlot 0,triple.atSlot 1,h.2.2.2,
          unit.typed _,triple.typed _,triple.typed _,fun e => (by decide : (0 : Fin 2) ≠ 1) (triple.distinct e),
          output_not_fresh clean,output_not_fresh clean,output_not_fresh clean⟩
      else none
  else []

def detect (rs : Problem d.sig) := (candidates rs).head?

def liftSchema (a : Schema d.sig) : Schema (TableAmbient.sig d) where
  f := .inl a.f
  z := .inl a.z
  zeroArity := a.zeroArity
  zeroSort := a.zeroSort
  fSort := a.fSort
  doubleKey := a.doubleKey
  unitKey := a.unitKey
  pairKey := a.pairKey
  restKey := a.restKey
  doubleSort := a.doubleSort
  unitSort := a.unitSort
  pairSort := a.pairSort
  restSort := a.restSort
  distinct := a.distinct
  freeOutput := fun | .inl x => a.freeOutput x | .inr x => nomatch x
  commOutput := fun | .inl x => a.commOutput x | .inr x => nomatch x
  acOutput := fun | .inl x => a.acOutput x | .inr x => nomatch x

end Tamarin.XorTable
