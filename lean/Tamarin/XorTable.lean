import Tamarin.XorFlat
import Tamarin.ConstructorPresentation
import Tamarin.TablePresentation
import Tamarin.TableAmbient

/-! Recognize the three oriented equations of an exponent-two AC group.
The normalized schemas share variables only within their own equation.
Rules at additional free or commutative heads see the full active table. -/
namespace Tamarin.XorTable
open Rewriting ConstructorVariants
variable {s : Signature}

structure Schema (s : Signature) where
  f : s.ACSym
  z : s.FreeSym
  zeroArity : s.arity z = 0
  zeroSort : s.outputSort z = .msg
  fSort : s.acSort f = .msg
  doubleKey : Variable
  unitKey : Variable
  pairKey : Variable
  restKey : Variable
  doubleSort : doubleKey.sort = .msg
  unitSort : unitKey.sort = .msg
  pairSort : pairKey.sort = .msg
  restSort : restKey.sort = .msg
  distinct : pairKey ≠ restKey
  freeOutput : ∀ g, s.outputSort g ≠ .fresh
  commOutput : ∀ g, s.cSort g ≠ .fresh
  acOutput : ∀ g, s.acSort g ≠ .fresh

def unitEquation (f : s.ACSym) (zero : Term s) (v : Variable) : Equation s :=
  ⟨.ac f (.var v) zero,.var v⟩

def cancelEquation (f : s.ACSym) (v w : Variable) : Equation s :=
  ⟨.ac f (.var v) (.ac f (.var v) (.var w)),.var w⟩

namespace Schema
variable (a : Schema s)

def zero : Term s := .free a.z fun i => Fin.elim0 (a.zeroArity ▸ i)

def duplicate : Equation s := ⟨.ac a.f (.var a.doubleKey) (.var a.doubleKey), a.zero⟩
def unit : Equation s := unitEquation a.f a.zero a.unitKey
def cancel : Equation s := cancelEquation a.f a.pairKey a.restKey

def rows (more : Problem s) := a.duplicate :: a.unit :: a.cancel :: more

def extraHead [DecidableEq s.FreeSym] : Head s → Bool
  | .free g => g != a.z
  | .comm _ => true
  | _ => false

private theorem zero_sorted : HasSort a.zero .msg :=
  a.zeroSort ▸ HasSort.free a.z _ (fun i => Fin.elim0 (a.zeroArity ▸ i))

private theorem row_heads {more : Problem s} [DecidableEq s.FreeSym]
    (extra : ∀ r ∈ more, a.extraHead (head r.lhs)) {r : Equation s} (h : r ∈ a.rows more) :
    head r.lhs = .ac a.f ∨ a.extraHead (head r.lhs) := by
  simp only [rows,List.mem_cons] at h
  rcases h with rfl | rfl | rfl | hr
  all_goals first | exact .inl rfl | exact .inr (extra _ hr)

private theorem active {more : Problem s} [DecidableEq s.FreeSym]
    (extra : ∀ r ∈ more, a.extraHead (head r.lhs)) (r : Equation s)
    (hr : r ∈ a.rows more) (h : head r.lhs = .ac a.f) :
    r = a.duplicate ∨ r = a.unit ∨ r = a.cancel := by
  simp only [rows,List.mem_cons] at hr
  rcases hr with e | e | e | hm
  · exact .inl e
  · exact .inr (.inl e)
  · exact .inr (.inr e)
  · have bad := extra r hm; simp [h,extraHead] at bad

theorem typedOfActive {r : Equation s} (active : r = a.duplicate ∨ r = a.unit ∨ r = a.cancel) :
    HasSort r.lhs .msg := by
  have sum {x y : Term s} (l : HasSort x .msg) (k : HasSort y .msg) : HasSort (.ac a.f x y) .msg := by
    rw [← a.fSort] at l k ⊢; exact .ac _ _ _ l k
  rcases active with rfl | rfl | rfl
  · exact sum (a.doubleSort ▸ HasSort.var _) (a.doubleSort ▸ HasSort.var _)
  · exact sum (a.unitSort ▸ HasSort.var _) a.zero_sorted
  · exact sum (a.pairSort ▸ HasSort.var _) (sum (a.pairSort ▸ HasSort.var _) (a.restSort ▸ HasSort.var _))

/-- The XOR operations depend only on the projection of the complete table to
their active head and on irreducibility of the zero constant. -/
def onTable (rs : Problem s) (dup : a.duplicate ∈ rs) (un : a.unit ∈ rs)
    (active : ∀ r ∈ rs, head r.lhs = .ac a.f → r = a.duplicate ∨ r = a.unit ∨ r = a.cancel)
    (apps : ∀ r ∈ rs, Application r.lhs) (inert : Head.free a.z ∉ ruleHeads rs) : FreshXor.Flat.Table s where
  rules := rs
  f := a.f
  fSort := a.fSort
  zero := a.zero
  zeroFree := ⟨_,_,rfl⟩
  zeroGround := fun _ ⟨i,_⟩ => Fin.elim0 (a.zeroArity ▸ i)
  zeroSort := a.zero_sorted
  zeroAbsent := by
    intro h hh used
    simp only [zero,operators,List.mem_cons,List.mem_flatten,List.mem_ofFn] at hh
    obtain rfl : h = .free a.z := hh.elim id (fun ⟨_,⟨i,_⟩,_⟩ => Fin.elim0 (a.zeroArity ▸ i))
    exact inert used
  apps := apps
  param := a.doubleKey
  paramSort := a.doubleSort
  duplicate := dup
  bucket := by
    intro r hr h
    rcases active r hr h with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl ⟨_,rfl⟩)
    · exact .inr (.inr (.inl ⟨_,_,rfl⟩))
  freeSort := a.freeOutput
  commSort := a.commOutput
  acSort := a.acOutput
  unitRule := ⟨a.unitKey,a.unitSort,un⟩
  inventory := by
    intro r hr h
    rcases active r hr h with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl ⟨_,rfl⟩)
    · exact .inr (.inr (.inl ⟨_,_,rfl⟩))

def table [DecidableEq s.FreeSym] (more : Problem s)
    (extra : ∀ r ∈ more, a.extraHead (head r.lhs)) : FreshXor.Flat.Table s :=
  a.onTable (a.rows more) List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) (a.active extra) (by
    intro r hr
    rcases a.row_heads extra hr with ac | ex
    · cases hs : r.lhs <;> simp_all [head,headModel,Model.eval,Application]
    · cases hs : r.lhs <;> simp_all [head,headModel,Model.eval,Application,extraHead]) (by
    intro used
    obtain ⟨r,hr,e⟩ := List.mem_map.mp used
    rcases a.row_heads extra hr with ac | ex
    · rw [e] at ac; cases ac
    · simp [e,extraHead] at ex)

end Schema

/-- A successful classification supplies all bookkeeping for composing the active
AC proof with the constructor rows. -/
structure Evidence (rs : Problem s) (T : FreshXor.Flat.Table s)
    [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] : Prop where
  agrees : TablePresentation.Agrees rs T.rules
  presentation : NormalAlgebra.Presentation T.rules
  scope : ReferenceReduction.Bound T.rules
  typed : ∀ r ∈ T.rules, head r.lhs = .ac T.f → HasSort r.lhs .msg
  inactive : ∀ f ≠ T.f, Head.ac f ∉ ruleHeads T.rules
  other : ∀ r ∈ T.rules, head r.lhs ≠ .ac T.f →
    SubtermVariants.Row r ∧ NormalAlgebra.UniqueRow T.rules r

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def accepts (a : Schema s) (w : Head s → Nat) (fuel : Nat) (rs : Problem s) : Bool :=
  let more := rs.filter fun r => a.extraHead (head r.lhs)
  let table := a.rows more
  TablePresentation.Agrees rs table && SymbolWeight.decreasing w table && TableDecrease.sorted table &&
    more.all (ConstructorRows.checkedRow table fuel)

theorem accepts_evidence {a : Schema s} {w fuel rs} (ok : accepts a w fuel rs) :
    ∃ T : FreshXor.Flat.Table s, Evidence rs T := by
  let more := rs.filter fun r => a.extraHead (head r.lhs)
  have extra : ∀ r ∈ more, a.extraHead (head r.lhs) := fun _ h => (List.mem_filter.mp h).2
  let T := a.table more extra
  obtain ⟨⟨⟨agree,weight⟩,sorts⟩,good⟩ := by simpa only [accepts,Bool.and_eq_true] using ok
  have scope : ReferenceReduction.Bound T.rules := SymbolWeight.bound weight
  refine ⟨T,agree,⟨T.apps,SymbolWeight.terminating weight,TableDecrease.sortPreserving sorts⟩,scope,
    (fun r hr h => a.typedOfActive (a.active extra r hr h)),?_,?_⟩
  · rintro f hf h; obtain ⟨r,hr,e⟩ := List.mem_map.mp h
    rcases a.row_heads extra hr with ac | ex
    · exact hf (Head.ac.inj (e.symm.trans ac))
    · simp [e,Schema.extraHead] at ex
  · intro r hr ne
    change r ∈ a.duplicate :: a.unit :: a.cancel :: more at hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hm
    · exact (ne rfl).elim
    · exact (ne rfl).elim
    · exact (ne rfl).elim
    · exact ConstructorRows.checkedRow_sound (rs := T.rules)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) scope T.apps
        (List.all_eq_true.mp good _ hm)

end Tamarin.XorTable
