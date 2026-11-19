import Tamarin.MixedCancellationVariants
import Tamarin.VariantJoinPacked
import Tamarin.VariantPresentation

/-! Pack joint answers for any tree of cancellation sums with normalized Msg factors. -/
namespace Tamarin.Rewriting.MixedCancellation
open VariantJoin
variable {sig : Signature}

/-- A packed observation may combine arbitrary normalized factors at the
active cancellation symbol. Any B-equivalent representation is admitted. -/
inductive Observation (T : BinaryXor.Table sig) : Term sig → Prop where
  | factor (t : Term sig) (good : ∀ ρ : Substitution sig, Normalized T.R ρ → BinaryXor.Good T (ρ.apply t)) :
      Observation T t
  | sum {a b} (left : Observation T a) (right : Observation T b) : Observation T (.ac T.f a b)
  | equiv {s t} (layout : EquivB t s) (source : Observation T s) : Observation T t

theorem Observation.variable {T : BinaryXor.Table sig} (v : Variable) (sort : Subsort v.sort .msg) :
    Observation T (.var v) :=
  .factor _ fun ρ hn => ⟨(ρ.sorted v).widen sort,hn v⟩

theorem Observation.unique {T : BinaryXor.Table sig} {t : Term sig} (o : Observation T t)
    (ρ : Substitution sig) (hn : Normalized T.R ρ) {u v : Term sig}
    (nu : NormalForm T.R (ρ.apply t) u) (nv : NormalForm T.R (ρ.apply t) v) : EquivB u v := by
  have good : HasSort (ρ.apply t) .msg ∧ T.PureFrom (fun _ => True) (ρ.apply t) := by
    clear nu nv
    induction o with
    | factor t h =>
      have g := h ρ hn
      exact ⟨g.1,BinaryXor.pure_good T g⟩
    | sum l r gl gr =>
      exact ⟨T.fSort ▸ HasSort.ac _ _ _ (T.fSort ▸ gl.1) (T.fSort ▸ gr.1),(T.pure_ac ..).mpr ⟨gl.2,gr.2⟩⟩
    | equiv e _ g =>
      have eq := e.symm.subst ρ.image
      exact ⟨BinaryXor.sort_equiv eq g.1,(T.kept g.2 eq).1⟩
  exact BinaryXor.unique_of_pure T good.1 good.2 nu nv

/-- Exact joined rows solve the original observation tuple in its full
caller order, including repeated operations and stable slots. -/
theorem packed {A : Type} {keys : List Variable} (T : BinaryXor.Table sig) (op : A → Term sig)
    (admit : ∀ a, Observation T (op a))
    (rows : List (Row sig (Key keys) A)) (exactRows : Exact T.R Subtype.val op rows)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal T.R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (stable : ∀ t, .inr t ∈ slots → StableVariants.Representative T.R t (n t)) :
    CompleteVariants T.R (slots.map (packedInput op)) (packRows rows typed slots n) ∧
      ∀ a ∈ packRows rows typed slots n, a.Reconstructible T.R (slots.map (packedInput op)) :=
  exactRows.packedRepresentatives (ConstructorVariants.constructor_normal T.rules T.apps).1
    typed normal slots used scope n stable fun ρ hn a _ _ => (admit a).unique ρ hn

end Tamarin.Rewriting.MixedCancellation
