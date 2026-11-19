import Tamarin.MixedCancellationShape

namespace Tamarin.Rewriting.MixedCancellation
open Cancellation ACRepresentation
variable {sig : Signature} (T : BinaryXor.Table sig)

/-- Distinct variable factors form a normal sum, including the empty sum. -/
private theorem variables_good (vs : List Variable) (nd : vs.Nodup)
    (typed : ∀ v ∈ vs, HasSort (Term.var (sig := sig) v) .msg) :
    BinaryXor.Good T (T.value (vs.map Term.var)) := by
  cases vs with
  | nil => exact ⟨T.zeroSort,T.toTable.zero_normal⟩
  | cons v vs =>
    let key := fun w : Variable => classOf (Term.var (sig := sig) w)
    have layout : T.bag (T.value ((v :: vs).map Term.var)) = (v :: vs).map key := by
      change T.bag (ACRepresentation.fold T.f (.var v) (vs.map Term.var)) = _
      rw [BinaryXor.fold_classes T]
      · simp [List.map_map,key,Function.comp_def]
      · intro t ht
        change t ∈ (v :: vs).map Term.var at ht
        obtain ⟨w,_,rfl⟩ := List.mem_map.mp ht
        rfl
    refine ⟨BinaryXor.value_typed T _ ?_,BinaryXor.normal_clean T ?_ ?_ ?_⟩
    · intro t ht
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
      exact typed w hw
    · rw [layout]
      exact List.Pairwise.map key (fun _ _ ne eq => ne (Head.var.inj (Quotient.exact eq).head_eq)) nd
    · rw [layout]
      intro hz
      obtain ⟨w,_,eq⟩ := List.mem_map.mp hz
      have e : EquivB (.var w) T.zero := Quotient.exact eq
      obtain ⟨_,_,hz⟩ := T.zeroFree
      rw [hz] at e
      cases e.head_eq
    · intro k hk
      rw [layout] at hk
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hk
      exact BinaryXor.fact_of_mem T ⟨typed w hw,(ConstructorVariants.constructor_normal T.rules T.apps).1 w⟩
        (show key w ∈ [key w] from List.mem_cons_self)

private theorem cancel_pair {x y : Term sig} (hx : HasSort x .msg) (hy : HasSort y .msg) :
    Reduces T.R (.ac T.f x (.ac T.f x y)) y :=
  BinaryXor.shape_reduces T .rightContains hx hx hy

private theorem ac_typed {x y : Term sig} (hx : HasSort x .msg) (hy : HasSort y .msg) :
    HasSort (.ac T.f x y) .msg :=
  T.fSort ▸ HasSort.ac _ _ _ (T.fSort ▸ hx) (T.fSort ▸ hy)

/-- The reductions hold for arbitrary typed instantiations. Normality of
the displayed images only requires extra hypotheses when they are used
as variants themselves. -/
theorem shape_reduces (sh : Shape) {a b m : Term sig}
    (ha : HasSort a .msg) (hb : HasSort b .msg) (hm : HasSort m .msg) :
    let (l,k,x,out) := sh.images T a b m
    Reduces T.R (.ac T.f l (.ac T.f k x)) out := by
  have unit (v : Term sig) (hv : HasSort v .msg) : Reduces T.R (.ac T.f v T.zero) v :=
    .step ⟨_,_,.refl _,.root (T.unit hv),.refl _⟩
  have twice (v : Term sig) (hv : HasSort v .msg) : Reduces T.R (.ac T.f v v) T.zero :=
    .step ⟨_,_,.refl _,.root (BinaryXor.dup_msg T hv),.refl _⟩
  have keep (v : Term sig) : Reduces T.R v v := .basis (.refl _)
  have swap (v : Term sig) : EquivB (.ac T.f b (.ac T.f a v)) (.ac T.f a (.ac T.f b v)) :=
    fold_swap T.f b a [v]
  cases sh with
  | diagonal => exact cancel_pair T ha hm
  | separate left right residual =>
    cases left <;> cases right <;> cases residual
    · exact .ac _ (keep a) (unit b hb)
    · exact keep _
    · exact (Reduces.ac _ (keep a) (twice b hb)).trans (unit a ha)
    · exact .ac _ (keep a) (cancel_pair T hb hm)
    · exact (Reduces.basis (.ac_congr _ (.refl a) (.ac_swap _ b a))).trans (cancel_pair T ha hb)
    · exact (Reduces.basis (.ac_congr _ (.refl a) (swap m))).trans (cancel_pair T ha (ac_typed T hb hm))
    · exact (Reduces.basis (.ac_congr _ (.refl a) (swap b))).trans
        ((cancel_pair T ha (ac_typed T hb hb)).trans (twice b hb))
    · exact (Reduces.basis (.ac_congr _ (.refl a) (swap (.ac T.f b m)))).trans
        ((cancel_pair T ha (ac_typed T hb (ac_typed T hb hm))).trans (cancel_pair T hb hm))

theorem shape_normal (sh : Shape) (a b r : Variable) (ha : a.sort = .fresh)
    (hb : b.sort = .fresh) (hr : r.sort = .msg) (ab : a ≠ b) :
    let (l,k,x,out) := sh.images T (.var a) (.var b) (.var r)
    (HasSort l .fresh ∧ Normal T.R l) ∧ (HasSort k .fresh ∧ Normal T.R k) ∧
    BinaryXor.Good T x ∧ NormalForm T.R (.ac T.f l (.ac T.f k x)) out := by
  have af : HasSort (Term.var (sig := sig) a) .fresh := ha ▸ HasSort.var a
  have bf : HasSort (Term.var (sig := sig) b) .fresh := hb ▸ HasSort.var b
  have am := af.widen .fresh_msg
  have bm := bf.widen .fresh_msg
  have rm : HasSort (Term.var (sig := sig) r) .msg := hr ▸ HasSort.var r
  have nn := (ConstructorVariants.constructor_normal T.rules T.apps).1
  have ga := And.intro af (nn a)
  have gb := And.intro bf (nn b)
  have gr : BinaryXor.Good T (.var r) := ⟨rm,nn r⟩
  have ar : a ≠ r := fun e => by subst r; simp_all
  have br : b ≠ r := fun e => by subst r; simp_all
  have selected (l k t : Bool) : BinaryXor.Good T (T.value (operands l k t (.var a) (.var b) (.var r))) := by
    have map : operands l k t (Term.var (sig := sig) a) (.var b) (.var r) =
        (operands l k t a b r).map Term.var := by cases l <;> cases k <;> cases t <;> rfl
    rw [map]
    apply variables_good
    · cases l <;> cases k <;> cases t <;> simp [operands,pick,ab,ar,br]
    · intro v hv
      have one : v = a ∨ v = b ∨ v = r := by
        cases l <;> cases k <;> cases t <;> simp [operands,pick] at hv <;> grind
      rcases one with rfl|rfl|rfl <;> assumption
  have good : let (l,k,x,out) := sh.images T (.var a) (.var b) (.var r)
      (HasSort l .fresh ∧ Normal T.R l) ∧ (HasSort k .fresh ∧ Normal T.R k) ∧
      BinaryXor.Good T x ∧ BinaryXor.Good T out := by
    cases sh with
    | diagonal => exact ⟨ga,ga,gr,gr⟩
    | separate l k t => exact ⟨ga,gb,selected l k t,selected (!l) (!k) t⟩
  exact ⟨good.1,good.2.1,good.2.2.1,shape_reduces T sh am bm rm,good.2.2.2.2,
    fun _ typed => .widen good.2.2.2.1 (T.fSort ▸ Term.rootSort_le typed)⟩

end Tamarin.Rewriting.MixedCancellation
