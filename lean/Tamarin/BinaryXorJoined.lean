import Tamarin.BinaryXorVariants
import Tamarin.VariantJoinLeaf
import Tamarin.VariantJoinPacked

/-! A binary XOR leaf shares its caller-variable keys with the rest of a
packed query. Its unique normal value permits repeated observation slots,
including under a substitution that introduces additional XOR operands. -/
namespace Tamarin.Rewriting.BinaryXor
open VariantJoin
variable {sig : Signature}

private theorem Query.typed (q : Query sig) : HasSort q.term q.term.rootSort :=
  .ac q.table.f _ _ (q.table.fSort ▸ q.sx ▸ HasSort.var q.x) (q.table.fSort ▸ q.sy ▸ HasSort.var q.y)

/-- Each arm is opened before padding unrelated identity variables and each
value is reconstructed under the same substitution as the observed inputs. -/
theorem Query.leaf_of_complete (q : Query sig) {arms : List (Variant sig)}
    (family : CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term])
    {I : Type} (ids : I → Variable) (scope : ∀ v, q.term.Occurs v → ∃ i, ids i = v)
    (rows : List (Row sig I Unit))
    (all : ∀ a ∈ arms, ∃ out ∈ rows, DecodesLeaf q.table.R q.term ids a out)
    (only : ∀ out ∈ rows, ∃ a ∈ arms, DecodesLeaf q.table.R q.term ids a out) :
    Exact q.table.R ids (fun _ => q.term) rows ∧ ∀ out ∈ rows,
      (∀ i, HasSort (out.input i) (ids i).sort) ∧ out.IsNormal q.table.R := by
  have fact := leafSemantic q.table.rules q.term q.typed ids scope arms family.1 family.2 rows all only
  exact ⟨fact.1,fact.2 (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1⟩

theorem Query.leaf (q : Query sig) (arms : List (Variant sig))
    (all : ∀ sh, ∃ a ∈ arms, Decodes q sh a) (only : ∀ a ∈ arms, ∃ sh, Decodes q sh a)
    {I : Type} (ids : I → Variable) (scope : ∀ v, q.term.Occurs v → ∃ i, ids i = v)
    (rows : List (Row sig I Unit))
    (opens : ∀ a ∈ arms, ∃ out ∈ rows, DecodesLeaf q.table.R q.term ids a out)
    (comesFrom : ∀ out ∈ rows, ∃ a ∈ arms, DecodesLeaf q.table.R q.term ids a out) :
    Exact q.table.R ids (fun _ => q.term) rows ∧ ∀ out ∈ rows,
      (∀ i, HasSort (out.input i) (ids i).sort) ∧ out.IsNormal q.table.R :=
  q.leaf_of_complete (complete q arms all only) ids scope rows opens comesFrom

/-- Overlapping XOR leaf queries may share caller variables. The uniqueness
part of packing applies to any binary observation whose two operands have
normalized Msg images under every common normalized substitution. -/
theorem packed {A : Type} {keys : List Variable} (T : Table sig) (op : A → Term sig)
    (admit : ∀ a, ∃ l r, op a = .ac T.f l r ∧ ∀ ρ : Substitution sig, Normalized T.R ρ →
      Good T (ρ.apply l) ∧ Good T (ρ.apply r))
    (rows : List (Row sig (Key keys) A)) (family : Exact T.R Subtype.val op rows)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal T.R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (stable : ∀ t, .inr t ∈ slots → StableVariants.Representative T.R t (n t)) :
    CompleteVariants T.R (slots.map (packedInput op)) (packRows rows typed slots n) ∧
      ∀ a ∈ packRows rows typed slots n, a.Reconstructible T.R (slots.map (packedInput op)) := by
  apply family.packedRepresentatives (ConstructorVariants.constructor_normal T.rules T.apps).1
    typed normal slots used scope n stable
  intro ρ hn a u v nu nv
  obtain ⟨l,r,eq,children⟩ := admit a
  rw [eq] at nu nv
  exact unique T (children ρ hn).1 (children ρ hn).2 nu nv

end Tamarin.Rewriting.BinaryXor
