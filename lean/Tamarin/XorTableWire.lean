import Tamarin.XorTable
import Tamarin.TableAmbient

/-! Infer the operator declarations and rule-local variables from an XOR
presentation. All guesses are checked against the full table by `accepts`. -/
namespace Tamarin.XorTable
open TotalUnifyWire
variable {d : Dictionary}

private def duplicate? (r : Equation d.sig) : Option (d.sig.ACSym × d.sig.FreeSym × Variable) := do
  let .ac f (.var v) (.var w) := r.lhs | none
  let .free z _ := r.rhs | none
  guard (v == w)
  return (f,z,v)

private def unit? (f : d.sig.ACSym) (r : Equation d.sig) : Option Variable := do
  let .ac g _ _ := r.lhs | none
  let .var v := r.rhs | none
  guard (g == f && (ACRepresentation.flatten f r.lhs).length == 2)
  return v

private def cancellation? (f : d.sig.ACSym) (r : Equation d.sig) : Option (Variable × Variable) := do
  let .ac g _ _ := r.lhs | none
  let .var rest := r.rhs | none
  guard (g == f && (ACRepresentation.flatten f r.lhs).length == 3)
  let pair ← r.lhs.variables.find? (· != rest)
  return (pair,rest)

private theorem output_not_fresh {ds : List Whole.Decl} (h : ds.all (fun decl => sortOf decl.output != .fresh))
    {k} (f : Symbol ds k) : sortOf (info f).output ≠ .fresh := by
  have found : decl ds k f.val = some (info f) := (Option.some_get f.property).symm
  exact bne_iff_ne.mp (List.all_eq_true.mp h _ (List.mem_of_find?_eq_some found))

/-- An AC head is inferred from its duplicate rule. Each equation may use
its own variable numbering. Sorting requirements are checked on declarations. -/
def detect (rs : Problem d.sig) : Option (Schema d.sig) := do
  let (f,z,v) ← rs.findSome? duplicate?
  let u ← rs.findSome? (unit? f)
  let (p,q) ← rs.findSome? (cancellation? f)
  if clean : d.decls.all (fun decl => sortOf decl.output != .fresh) then
    if h : d.sig.arity z = 0 ∧ d.sig.outputSort z = .msg ∧ d.sig.acSort f = .msg ∧
        v.sort = .msg ∧ u.sort = .msg ∧ p.sort = .msg ∧ q.sort = .msg ∧ p ≠ q then
      let ⟨arity,zs,fs,vs,us,ps,qs,ne⟩ := h
      return ⟨f,z,arity,zs,fs,v,u,p,q,vs,us,ps,qs,ne,
        output_not_fresh clean,output_not_fresh clean,output_not_fresh clean⟩
    else none
  else none

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
