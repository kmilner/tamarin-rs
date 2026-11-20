import Tamarin.SubtermDecrease
import Tamarin.DHCanonical

/-! Rank and sort certificates for a whole table containing the DH schemas
and user equations. User definitions may call DH and one another. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants MixedUnification
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- The five DH operators and rule variables occupy the base dependency level. -/
structure BaseLevel (s : Symbols sig) (level : Head sig → Nat) : Prop where
  vars : ∀ v, level (.var v) = 0
  pow : level (.free s.pow) = 0
  inv : level (.free s.inv) = 0
  one : level (.free s.one) = 0
  neutral : level (.free s.neutral) = 0
  mul : level (.ac s.mul) = 0

private theorem schema_level {level : Head sig → Nat} (fixed : BaseLevel s level)
    (keys : Fin 3 → Variable) (e : Expr (Fin 3)) :
    ∀ t ∈ subterms (e.eval s (fun i => .var (keys i))), level (head t) = 0 := by
  induction e with
  | var i => intro _ h; obtain rfl := List.mem_singleton.mp h; exact fixed.vars _
  | pow a b ia ib =>
    intro t h; rcases List.mem_cons.mp h with rfl | h
    · exact fixed.pow
    · obtain ⟨l,hl,ht⟩ := List.mem_flatten.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      dsimp only at ht
      split at ht <;> first | exact ia t ht | exact ib t ht
  | mul a b ia ib =>
    intro t h; rcases List.mem_cons.mp h with rfl | h
    · exact fixed.mul
    · exact (List.mem_append.mp h).elim (ia t) (ib t)
  | inv a ih =>
    intro t h; rcases List.mem_cons.mp h with rfl | h
    · exact fixed.inv
    · obtain ⟨l,hl,ht⟩ := List.mem_flatten.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl; exact ih t ht
  | one | neutral =>
    intro t h
    rcases List.mem_cons.mp h with rfl | h
    · first | exact fixed.one | exact fixed.neutral
    · obtain ⟨l,hl,_⟩ := List.mem_flatten.mp h; obtain ⟨i,_⟩ := List.mem_ofFn.mp hl
      first | exact Fin.elim0 (s.oneArity ▸ i) | exact Fin.elim0 (s.neutralArity ▸ i)

/-- This names exactly the instantiated rows accounted for by the builtin
inventory. Other rows are checked independently of their symbol or order. -/
def SchemaRow (E : ExtraTable T) (row : Equation sig) : Prop :=
  (∃ r : Rule, row = r.instantiate s (fun i => .var (T.actual r i))) ∨
    ∃ r : ExtraRule, row = r.instantiate s (fun i => .var (E.actual r i))

private theorem builtin_checks {level : Head sig → Nat} (fixed : BaseLevel s level)
    {row : Equation sig} (builtin : SchemaRow E row) :
    (∀ u ∈ subterms row.lhs ++ subterms row.rhs, level (head u) = 0) ∧
    SymbolWeight.rank ExactTable.weight row.rhs < SymbolWeight.rank ExactTable.weight row.lhs ∧
    (TableDecrease.nonduplicating row = true) ∧ (TableDecrease.sortRule row = true) := by
  rcases builtin with ⟨r,rfl⟩ | ⟨r,rfl⟩
  all_goals
    first
      | let tab := Schemas.exactTable s (T.actual r) (T.actualSort r) (T.distinct r)
        have mem := (Schemas.T s (T.actual r) (T.actualSort r) (T.distinct r)).present r
      | let tab := Schemas.exactTable s (E.actual r) (E.sorted r) (E.distinct r)
        have mem := (Schemas.E s (E.actual r) (E.sorted r) (E.distinct r)).present r
    have dec := Bool.and_eq_true_iff.mp (List.all_eq_true.mp tab.decreasing _ mem)
    refine ⟨fun u h => (List.mem_append.mp h).elim (schema_level fixed _ _ u) (schema_level fixed _ _ u),
      of_decide_eq_true dec.1,dec.2,List.all_eq_true.mp tab.sorted _ mem⟩

theorem mixed_decreasing {level : Head sig → Nat} (fixed : BaseLevel s level)
    (others : ∀ row ∈ T.rules, ¬ SchemaRow E row → SubtermDecrease.ExtensionRow level row) :
    SymbolWeight.decreasing (SubtermDecrease.weights ExactTable.weight T.rules level) T.rules := by
  apply SubtermDecrease.decreasing
  · intro h; cases h <;> simp [ExactTable.weight] <;> split <;> decide
  · intro r hr
    by_cases dh : SchemaRow E r
    · have ⟨levels,lt,counts,_⟩ := builtin_checks fixed dh
      exact .inl ⟨levels,lt,counts⟩
    · exact .inr (others r hr dh)

theorem mixed_sorted
    (others : ∀ row ∈ T.rules, ¬ SchemaRow E row → TableDecrease.sortRule row) :
    TableDecrease.sorted T.rules := by
  apply List.all_eq_true.mpr
  intro r hr
  by_cases dh : SchemaRow E r
  · exact (builtin_checks (level := fun _ => 0) ⟨fun _ => rfl,rfl,rfl,rfl,rfl,rfl⟩ dh).2.2.2
  · exact others r hr dh

end Tamarin.Rewriting.DHPeer
