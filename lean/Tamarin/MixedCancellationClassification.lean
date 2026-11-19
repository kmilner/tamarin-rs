import Tamarin.MixedCancellationShape

namespace Tamarin.Rewriting.MixedCancellation
open Cancellation BinaryXor
variable {sig : Signature} (T : Table sig)
noncomputable section
open Classical

private def parts {α : Type} (l r : Bool) (a b : α) (tail : List α) :=
  pick l a ++ (pick r b ++ tail)

/-- A Fresh image is a single nonunit class. Collecting the remaining factors
into one witness preserves their whole AC sum and introduces no empty product. -/
private theorem assemble_parts (l r : Bool) (a b : Term sig) (tail : List (Class sig)) :
    EquivB (assemble T (parts l r (classOf a) (classOf b) tail))
      (T.value (operands l r (!tail.isEmpty) a b (assemble T tail))) := by
  have ea : EquivB (rep (classOf a)) a := Quotient.exact (rep_key _)
  have eb : EquivB (rep (classOf b)) b := Quotient.exact (rep_key _)
  cases l <;> cases r <;> cases tail <;> first
    | exact .refl _
    | exact ea
    | exact eb
    | exact .ac_congr _ ea eb
    | exact .ac_congr _ ea (.refl _)
    | exact .ac_congr _ eb (.refl _)
    | exact .ac_congr _ ea (.ac_congr _ eb (.refl _))

private theorem pick_mem {α : Type} (flag : Bool) (a k : α) :
    k ∈ pick flag a ↔ k = a ∧ flag = true := by
  cases flag <;> simp [pick]

private theorem parts_nodup {α : Type} (l r : Bool) {a b : α} {t : List α}
    (ab : a ≠ b) (at' : a ∉ t) (bt : b ∉ t) (nd : t.Nodup) : (parts l r a b t).Nodup := by
  cases l <;> cases r <;> simp [parts,pick,ab,at',bt,nd]

private theorem toggle_parity {α : Type} [DecidableEq α] (l r : Bool) (a b k : α) (tail : List α) :
    (a :: b :: parts l r a b tail).count k % 2 =
      (parts (!l) (!r) a b tail).count k % 2 := by
  by_cases ak : a = k <;> by_cases bk : b = k <;> cases l <;> cases r <;>
    simp [parts,pick,ak,bk] <;> omega

private theorem typed {a b x : Term sig} (ga : Good T a) (gb : Good T b) (gx : Good T x) :
    HasSort (.ac T.f a (.ac T.f b x)) .msg :=
  T.fSort ▸ HasSort.ac _ _ _ (T.fSort ▸ ga.1)
    (HasSort.ac _ _ _ (T.fSort ▸ gb.1) (T.fSort ▸ gx.1))

theorem unique {a b x u v : Term sig} (ga : Good T a) (gb : Good T b) (gx : Good T x)
    (nu : NormalForm T.R (.ac T.f a (.ac T.f b x)) u)
    (nv : NormalForm T.R (.ac T.f a (.ac T.f b x)) v) : EquivB u v := by
  have pure := (T.pure_ac ..).mpr ⟨pure_good T ga,(T.pure_ac ..).mpr ⟨pure_good T gb,pure_good T gx⟩⟩
  exact unique_of_pure T (typed T ga gb gx) pure nu nv

/-- Test membership of each distinct Fresh class in the normalized Msg image.
The two membership bits flip in the result, while every other factor is preserved. -/
theorem classify {a b x out : Term sig} (ha : HasSort a .fresh ∧ Normal T.R a)
    (hb : HasSort b .fresh ∧ Normal T.R b) (gx : Good T x)
    (nf : NormalForm T.R (.ac T.f a (.ac T.f b x)) out) : ∃ sh, Instance T a b x out sh := by
  have ga : Good T a := ⟨ha.1.widen .fresh_msg,ha.2⟩
  have gb : Good T b := ⟨hb.1.widen .fresh_msg,hb.2⟩
  by_cases eq : classOf a = classOf b
  · obtain rfl := T.leaf_eq ha.1 (Quotient.exact eq)
    have red := shape_reduces T .rightContains ga.1 ga.1 gx.1
    have reach : NormalForm T.R (.ac T.f a (.ac T.f a x)) x :=
      ⟨red,gx.2,fun _ ty => .widen gx.1 (T.fSort ▸ Term.rootSort_le ty)⟩
    exact ⟨.diagonal,⟨a,a,x,ha,ha,gx,.refl _,.refl _,.refl _,unique T ga ga gx nf reach⟩⟩
  let A := classOf a
  let B := classOf b
  let X := pieces T x
  let tail := X.filter fun k => decide (k ≠ A ∧ k ≠ B)
  let l := decide (A ∈ X)
  let r := decide (B ∈ X)
  obtain ⟨dx,zx,fx⟩ := pieces_good T gx
  have mt k : k ∈ tail ↔ k ∈ X ∧ k ≠ A ∧ k ≠ B := by simp [tail]
  have dt : tail.Nodup := dx.filter _
  have ntA : A ∉ tail := fun h => ((mt _).mp h).2.1 rfl
  have ntB : B ∉ tail := fun h => ((mt _).mp h).2.2 rfl
  have nd (i j) := parts_nodup i j eq ntA ntB dt
  have perm : X.Perm (parts l r A B tail) := by
    apply (List.perm_ext_iff_of_nodup dx (nd l r)).mpr
    intro k
    simp only [parts,List.mem_append,pick_mem,mt,l,r,decide_eq_true_eq]
    constructor
    · intro hk
      by_cases ka : k = A
      · exact .inl ⟨ka,ka ▸ hk⟩
      by_cases kb : k = B
      · exact .inr (.inl ⟨kb,kb ▸ hk⟩)
      · exact .inr (.inr ⟨hk,ka,kb⟩)
    · rintro (⟨e,h⟩ | ⟨e,h⟩ | ⟨h,_,_⟩)
      · exact e ▸ h
      · exact e ▸ h
      · exact h
  have nz (i j) : T.zeroClass ∉ parts i j A B tail := by
    have za := Ne.symm (T.not_zero ha.1)
    have zb := Ne.symm (T.not_zero hb.1)
    simp only [parts,List.mem_append,pick_mem,mt]
    exact fun h => h.elim (fun e => za e.1) (fun e => e.elim (fun e => zb e.1) (fun e => zx e.1))
  have gt := assemble_good T (fun k hk => fx k ((mt _).mp hk).1) dt (fun hk => zx ((mt _).mp hk).1)
  let sh := Shape.separate l r (!tail.isEmpty)
  refine ⟨sh,⟨a,b,assemble T tail,ha,hb,gt,.refl _,.refl _,?_,?_⟩⟩
  · exact (assemble_input T gx).trans ((assemble_perm T perm).trans (assemble_parts T l r a b tail))
  · apply EquivB.trans _ (assemble_parts T (!l) (!r) a b tail)
    have bag : T.bag (.ac T.f a (.ac T.f b x)) = A :: B :: T.bag x := by
      rw [FreshXor.Flat.Table.bag,flatten_ac,flatten_ac]
      change T.bag a ++ (T.bag b ++ _) = _
      rw [T.bag_leaf ha.1,T.bag_leaf hb.1]; rfl
    apply (parity_normalForm T (typed T ga gb gx) T.fSort _ (nd (!l) (!r)) (nz (!l) (!r)) _ out).mp nf
    · intro k hk
      rw [bag] at hk
      rcases List.mem_cons.mp hk with e | hk
      · exact fact_of_mem T ga (by rw [T.bag_leaf ha.1,e]; exact List.mem_cons_self)
      rcases List.mem_cons.mp hk with e | hk
      · exact fact_of_mem T gb (by rw [T.bag_leaf hb.1,e]; exact List.mem_cons_self)
      · exact fact_of_mem T gx hk
    · intro k ne
      rw [bag]
      have count := (pieces_count T x k ne).symm.trans (perm.count_eq k)
      simpa only [List.count_cons,count] using (toggle_parity l r A B k tail)

end
end Tamarin.Rewriting.MixedCancellation
