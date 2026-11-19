import Tamarin.MixedCancellationClassification
import Tamarin.MixedCancellationSound
import Tamarin.XorFlatVariants
import Tamarin.VariantJoinLeaf

/-! The nine projections describe simultaneous variants of the three caller
variables and the observed value. The same witness substitution reconstructs
all four fields of each row. -/
namespace Tamarin.Rewriting.MixedCancellation
variable {sig : Signature}

structure Query (sig : Signature) where
  table : BinaryXor.Table sig
  a : Variable
  b : Variable
  x : Variable
  sa : a.sort = .fresh
  sb : b.sort = .fresh
  sx : x.sort = .msg
  distinct : a ≠ b

def Query.term (q : Query sig) :=
  Term.ac q.table.f (.var q.a) (.ac q.table.f (.var q.b) (.var q.x))

structure Names where
  h : Variable
  i : Variable
  j : Variable
  hs : h.sort = .fresh
  isFresh : i.sort = .fresh
  js : j.sort = .msg
  hi : h ≠ i

def Names.images (w : Names) (T : BinaryXor.Table sig) (sh : Shape) :=
  sh.images T (.var w.h) (.var w.i) (.var w.j)

structure Decodes (q : Query sig) (sh : Shape) (arm : Variant sig) : Prop where
  outside : ∀ v, v ≠ q.a → v ≠ q.b → v ≠ q.x → arm.subst.image v = .var v
  row : ∃ (w : Names) (value : Term sig), arm.values = [value] ∧
    EquivB (arm.subst.image q.a) (w.images q.table sh).1 ∧
    EquivB (arm.subst.image q.b) (w.images q.table sh).2.1 ∧
    EquivB (arm.subst.image q.x) (w.images q.table sh).2.2.1 ∧
    EquivB value (w.images q.table sh).2.2.2

private def Names.assign (w : Names) (h i j : Term sig)
    (th : HasSort h .fresh) (ti : HasSort i .fresh) (tj : HasSort j .msg) : Substitution sig where
  image v := if v = w.h then h else if v = w.i then i else if v = w.j then j else .var v
  support := [w.h,w.i,w.j]
  outside v hn := by simp_all
  sorted v := by
    split <;> rename_i e
    · simp [e,w.hs,th]
    split <;> rename_i e
    · simp [e,w.isFresh,ti]
    split <;> rename_i e
    · simp [e,w.js,tj]
    · exact .var _

private theorem Names.subst_images (w : Names) (T : BinaryXor.Table sig) (sh : Shape)
    (δ : Substitution sig) :
    let p := w.images T sh
    (δ.apply p.1,δ.apply p.2.1,δ.apply p.2.2.1,δ.apply p.2.2.2) =
      sh.images T (δ.image w.h) (δ.image w.i) (δ.image w.j) := by
  cases sh with
  | diagonal => rfl
  | separate l r t =>
    have map (i j k : Bool) :
        δ.apply (T.value (operands i j k (.var w.h) (.var w.i) (.var w.j))) =
        T.value (operands i j k (δ.image w.h) (δ.image w.i) (δ.image w.j)) := by
      rw [FreshXor.Flat.Table.subst_value]
      cases i <;> cases j <;> cases k <;> rfl
    simp only [Names.images,Shape.images,map]
    rfl

theorem Decodes.covers {q : Query sig} {sh : Shape} {arm : Variant sig} (cert : Decodes q sh arm)
    (ρ : Substitution sig) {out : Term sig}
    (inst : Instance q.table (ρ.image q.a) (ρ.image q.b) (ρ.image q.x) out sh) :
    arm.Covers q.table.R [q.term] ρ [out] := by
  obtain ⟨w,v,values,left,right,msg,o⟩ := cert.row
  obtain ⟨h,i,j,hh,hi,hj,hl,hr,hx,ho⟩ := inst.witnesses
  let δ := w.assign h i j hh.1 hi.1 hj.1
  have vars := (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1
  have hn : Normalized q.table.R δ := by
    intro x
    change Normal _ (if _ then _ else if _ then _ else if _ then _ else _)
    split; exact hh.2
    split; exact hi.2
    split; exact hj.2; exact vars _
  have hj' : w.j ≠ w.h := fun e => by have eq := congrArg Variable.sort e; simp [w.js,w.hs] at eq
  have ij' : w.j ≠ w.i := fun e => by have eq := congrArg Variable.sort e; simp [w.js,w.isFresh] at eq
  have hit : δ.image w.h = h ∧ δ.image w.i = i ∧ δ.image w.j = j := by
    simp [δ,Names.assign,Ne.symm w.hi,hj',ij']
  have obs := w.subst_images q.table sh δ
  rw [hit.1,hit.2.1,hit.2.2] at obs
  have el := congrArg Prod.fst obs
  have er := congrArg (fun p => p.2.1) obs
  have ex := congrArg (fun p => p.2.2.1) obs
  have eo := congrArg (fun p => p.2.2.2) obs
  refine ⟨δ,hn,?_,?_⟩
  · intro z hz
    obtain ⟨_,mem,occ⟩ := hz; obtain rfl := List.mem_singleton.mp mem
    change z = q.a ∨ z = q.b ∨ z = q.x at occ
    rcases occ with rfl|rfl|rfl
    · exact hl.trans (el ▸ (left.subst δ.image).symm)
    · exact hr.trans (er ▸ (right.subst δ.image).symm)
    · exact hx.trans (ex ▸ (msg.subst δ.image).symm)
  · rw [values]
    exact ⟨ho.trans (eo ▸ (o.subst δ.image).symm),trivial⟩

private theorem transport {s t : Term sig} (e : EquivB s t) {k} (h : HasSort s k) : HasSort t k :=
  Term.checkSort_sound _ _ (SortClash.check_equiv e k ▸ Term.checkSort_complete h)

theorem Decodes.sound {q : Query sig} {sh : Shape} {arm : Variant sig} (cert : Decodes q sh arm) :
    arm.Sound q.table.R [q.term] := by
  obtain ⟨w,v,vals,l,r,x,o⟩ := cert.row
  obtain ⟨hl,hr,hx,nf⟩ := shape_normal q.table sh w.h w.i w.j w.hs w.isFresh w.js w.hi
  have norm : Normalized q.table.R arm.subst := by
    intro z
    by_cases ha : z = q.a
    · subst z; exact (normal_equiv _ l).mpr hl.2
    by_cases hb : z = q.b
    · subst z; exact (normal_equiv _ r).mpr hr.2
    by_cases h : z = q.x
    · subst z; exact (normal_equiv _ x).mpr hx.2
    rw [cert.outside z ha hb h]
    exact (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1 z
  refine ⟨norm,?_⟩
  rw [vals]
  have e : EquivB (arm.subst.apply q.term) _ := .ac_congr _ l (.ac_congr _ r x)
  exact ⟨⟨(Reduces.basis e).trans (nf.1.trans (.basis o.symm)),(normal_equiv _ o).mpr nf.2.1,
    fun k typed => transport o.symm (nf.2.2 k (transport e typed))⟩,trivial⟩

theorem complete (q : Query sig) (arms : List (Variant sig))
    (all : ∀ sh, ∃ arm ∈ arms, Decodes q sh arm)
    (only : ∀ arm ∈ arms, ∃ sh, Decodes q sh arm) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ arm ∈ arms, arm.Reconstructible q.table.R [q.term] := by
  have sound arm (ha : arm ∈ arms) : arm.Sound q.table.R [q.term] := by
    obtain ⟨sh,cert⟩ := only arm ha
    exact cert.sound
  have input (ρ : Substitution sig) (hn : Normalized q.table.R ρ) :
      (HasSort (ρ.image q.a) .fresh ∧ Normal q.table.R (ρ.image q.a)) ∧
      (HasSort (ρ.image q.b) .fresh ∧ Normal q.table.R (ρ.image q.b)) ∧
      BinaryXor.Good q.table (ρ.image q.x) :=
    ⟨⟨q.sa ▸ ρ.sorted _,hn _⟩,⟨q.sb ▸ ρ.sorted _,hn _⟩,⟨q.sx ▸ ρ.sorted _,hn _⟩⟩
  refine ⟨⟨sound,?_⟩,?_⟩
  · intro ρ hn vals forms
    cases vals with
    | nil => exact False.elim forms
    | cons v vs => cases vs with
      | cons => exact False.elim forms.2
      | nil =>
        obtain ⟨ga,gb,gx⟩ := input ρ hn
        obtain ⟨sh,instanceOf⟩ := classify q.table ga gb gx forms.1
        obtain ⟨arm,mem,cert⟩ := all sh
        exact ⟨arm,mem,cert.covers ρ instanceOf⟩
  · intro arm mem
    have hs := sound arm mem
    apply Variant.reconstructible_of_unique hs
    intro t ht u v hu hv
    obtain rfl := List.mem_singleton.mp ht
    obtain ⟨ga,gb,gx⟩ := input _ hs.1
    exact unique q.table ⟨ga.1.widen .fresh_msg,ga.2⟩ ⟨gb.1.widen .fresh_msg,gb.2⟩ gx hu hv

open VariantJoin

/-- Reopen all four projections in a single scope before the packed caller
pads untouched input keys or joins this leaf with another observation. -/
theorem Query.leaf_of_complete (q : Query sig) {arms : List (Variant sig)}
    (family : CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term])
    {I : Type} (ids : I → Variable) (scope : ∀ v, q.term.Occurs v → ∃ i, ids i = v)
    (rows : List (Row sig I Unit))
    (all : ∀ a ∈ arms, ∃ out ∈ rows, DecodesLeaf q.table.R q.term ids a out)
    (only : ∀ out ∈ rows, ∃ a ∈ arms, DecodesLeaf q.table.R q.term ids a out) :
    Exact q.table.R ids (fun _ => q.term) rows ∧ ∀ out ∈ rows,
      (∀ i, HasSort (out.input i) (ids i).sort) ∧ out.IsNormal q.table.R := by
  have ma := (show HasSort (Term.var (sig := sig) q.a) .fresh from q.sa ▸ HasSort.var q.a).widen .fresh_msg
  have mb := (show HasSort (Term.var (sig := sig) q.b) .fresh from q.sb ▸ HasSort.var q.b).widen .fresh_msg
  have mx : HasSort (Term.var (sig := sig) q.x) .msg := q.sx ▸ HasSort.var q.x
  have typed : HasSort q.term q.term.rootSort :=
    .ac _ _ _ (q.table.fSort ▸ ma) (.ac _ _ _ (q.table.fSort ▸ mb) (q.table.fSort ▸ mx))
  have exactLeaf := leafSemantic q.table.rules q.term typed ids scope arms family.1 family.2 rows all only
  exact ⟨exactLeaf.1,exactLeaf.2 (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1⟩

end Tamarin.Rewriting.MixedCancellation
