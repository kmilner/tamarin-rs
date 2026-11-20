import Tamarin.BinaryXorNormal
import Tamarin.OperatorVariantBounds

namespace Tamarin.Rewriting.BinaryXor
open Cancellation ACRepresentation ShortVariantPaths
variable {sig : Signature} (T : Table sig)

private theorem cancel_tail {h t : Term sig} (hs : HasSort h .msg) (ts : HasSort t .msg) :
    Path T.R 2 (.ac T.f h (.ac T.f h t)) t :=
  .step ⟨_,_,.symm (.ac_assoc ..),.ac_left T.f t (.root (dup_msg T hs)),.refl _⟩
    (.step ⟨_,_,.ac_swap ..,.root (T.unit ts),.refl _⟩ (.basis (.refl _)))

/-- The entire shared subproduct cancels in one duplicate step, independently
of its width. One unit step suffices to expose any remaining operands. -/
theorem shape_path (sh : Shape) {h i j : Term sig}
    (hs : HasSort h .msg) (is_ : HasSort i .msg) (js : HasSort j .msg) :
    let (a,b,out) := sh.images T h i j
    Path T.R 2 (.ac T.f a b) out := by
  cases sh with
  | disjoint => exact .basis (.refl _)
  | unitLeft => exact .step ⟨_,_,.ac_swap ..,.root (T.unit js),.refl _⟩ (.basis (.refl _))
  | unitRight => exact .step ⟨_,_,.refl _,.root (T.unit is_),.refl _⟩ (.basis (.refl _))
  | same => exact .step ⟨_,_,.refl _,.root (dup_msg T hs),.refl _⟩ (.basis (.refl _))
  | leftContains => exact (cancel_tail T hs is_).rebase (.ac_swap ..)
  | rightContains => exact cancel_tail T hs js
  | overlap =>
    exact (cancel_tail T hs (T.fSort ▸ HasSort.ac _ _ _ (T.fSort ▸ is_) (T.fSort ▸ js))).rebase
      ((EquivB.ac_assoc ..).trans (.ac_congr T.f (.refl h) (fold_swap T.f i h [j])))

theorem shape_reduces (sh : Shape) {h i j : Term sig}
    (hs : HasSort h .msg) (is_ : HasSort i .msg) (js : HasSort j .msg) :
    let (a,b,out) := sh.images T h i j
    Reduces T.R (.ac T.f a b) out := (shape_path T sh hs is_ js).reduces

private theorem var_good (v : Variable) (vs : v.sort = .msg) : Good T (.var v) :=
  ⟨vs ▸ HasSort.var v,(ConstructorVariants.constructor_normal T.rules T.apps).1 v⟩

private theorem var_pair_good (v w : Variable) (vs : v.sort = .msg) (ws : w.sort = .msg) (ne : v ≠ w) :
    Good T (.ac T.f (.var v) (.var w)) := by
  let a : Term sig := .var v
  let b : Term sig := .var w
  have fa := fact_of_mem T (var_good T v vs) (k := classOf a) (show classOf a ∈ [classOf a] from List.mem_cons_self)
  have fb := fact_of_mem T (var_good T w ws) (k := classOf b) (show classOf b ∈ [classOf b] from List.mem_cons_self)
  have bag : T.bag (.ac T.f a b) = [classOf a,classOf b] := flatten_ac T.f a b
  have diff : classOf a ≠ classOf b := fun eq => ne (Head.var.inj (Quotient.exact eq).head_eq)
  have nonUnit (v : Variable) : T.zeroClass ≠ classOf (.var v) := by
    obtain ⟨f,xs,h⟩ := T.zeroFree
    intro eq
    have e : EquivB T.zero (.var v) := Quotient.exact eq
    rw [h] at e; cases e.head_eq
  refine ⟨T.fSort ▸ HasSort.ac _ _ _ (T.fSort ▸ (var_good T v vs).1) (T.fSort ▸ (var_good T w ws).1),?_⟩
  apply normal_clean T
  · rw [bag]; simp [diff]
  · rw [bag]; simp [a,b,nonUnit]
  · intro k hk
    rw [bag] at hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact fa
    · obtain rfl := List.mem_singleton.mp hk; exact fb

theorem shape_normal (sh : Shape) (h i j : Variable) (hs : h.sort = .msg) (is_ : i.sort = .msg)
    (js : j.sort = .msg) (hi : h ≠ i) (hj : h ≠ j) (ij : i ≠ j) :
    let (a,b,out) := sh.images T (.var h) (.var i) (.var j)
    Good T a ∧ Good T b ∧ NormalForm T.R (.ac T.f a b) out := by
  have gh := var_good T h hs; have gi := var_good T i is_; have gj := var_good T j js
  have ghi := var_pair_good T h i hs is_ hi; have ghj := var_pair_good T h j hs js hj
  have gij := var_pair_good T i j is_ js ij
  have gz : Good T T.zero := ⟨T.zeroSort,T.toTable.zero_normal⟩
  have all : let (a,b,out) := sh.images T (.var h) (.var i) (.var j); Good T a ∧ Good T b ∧ Good T out := by
    cases sh <;> exact ⟨by assumption,by assumption,by assumption⟩
  exact ⟨all.1,all.2.1,shape_reduces T sh gh.1 gi.1 gj.1,all.2.2.2,
    fun _ sort => .widen all.2.2.1 (T.fSort ▸ Term.rootSort_le sort)⟩

end Tamarin.Rewriting.BinaryXor
