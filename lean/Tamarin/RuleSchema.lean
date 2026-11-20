import Tamarin.ReferenceMatching
import Tamarin.FiniteOccurs
import Tamarin.VariablePermutation

/-! Recover a rule's own variable numbering from a finite oriented schema.
The structural matcher proposes assignments from the left side. Comparing both
sides modulo C/AC checks the direction and sharing of every occurrence. -/
namespace Tamarin.RuleSchema
variable {s : Signature} {n : Nat} (sort : Fin n → SortId)

structure Keys (sort : Fin n → SortId) where
  atSlot : Fin n → Variable
  typed : ∀ i, (atSlot i).sort = sort i
  distinct : Function.Injective atSlot

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Unused slots receive different fresh names above the rule's variables.
A successful result gives structural equivalence on both oriented sides. -/
def recover (instantiate : (Fin n → Variable) → Equation s) (r : Equation s) :
    Option {ks : Keys sort // EquivB (instantiate ks.atSlot).lhs r.lhs ∧
      EquivB (instantiate ks.atSlot).rhs r.rhs} := do
  let seed (i : Fin n) : Variable := ⟨i.val,sort i⟩
  let pattern := instantiate seed
  guard (FiniteOccurs.nodes pattern.lhs == FiniteOccurs.nodes r.lhs &&
         FiniteOccurs.nodes pattern.rhs == FiniteOccurs.nodes r.rhs)
  let fresh := VariablePermutation.freshBound r.lhs.variables
  (ReferenceMatching.branches pattern.lhs r.lhs).findSome? fun bindings => do
    let keys (i : Fin n) : Variable := match bindings.lookup (seed i) with
      | some (.var v) => v
      | _ => ⟨fresh + i.val,sort i⟩
    if valid : (∀ i, (keys i).sort = sort i) ∧ (∀ i j, keys i = keys j → i = j) then
      let e := instantiate keys
      if h : ReferenceMatching.equal e.lhs r.lhs && ReferenceMatching.equal e.rhs r.rhs then
        let ⟨l,k⟩ := Bool.and_eq_true_iff.mp h
        return ⟨⟨keys,valid.1,valid.2⟩,(ReferenceMatching.equal_iff ..).mp l,(ReferenceMatching.equal_iff ..).mp k⟩
      else none
    else none

end Tamarin.RuleSchema
