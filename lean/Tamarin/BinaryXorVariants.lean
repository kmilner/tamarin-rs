import Tamarin.BinaryXorClassification
import Tamarin.SortClash

/-! Interpret each generated triple in a single scope. A candidate may use
any names or B-representatives. Coverage is a set property, independent of
the order in which narrowing discovered the rows. -/
namespace Tamarin.Rewriting.BinaryXor
variable {sig : Signature}

structure Query (sig : Signature) where
  table : Table sig
  x : Variable
  y : Variable
  sx : x.sort = .msg
  sy : y.sort = .msg
  distinct : x ≠ y

def Query.term (q : Query sig) := Term.ac q.table.f (.var q.x) (.var q.y)

structure Names where
  h : Variable
  i : Variable
  j : Variable
  hs : h.sort = .msg
  isMsg : i.sort = .msg
  js : j.sort = .msg
  hi : h ≠ i
  hj : h ≠ j
  ij : i ≠ j

def Names.images (w : Names) (T : Table sig) (sh : Shape) :=
  sh.images T (.var w.h) (.var w.i) (.var w.j)

structure Decodes (q : Query sig) (sh : Shape) (arm : Variant sig) : Prop where
  outside : ∀ v, v ≠ q.x → v ≠ q.y → arm.subst.image v = .var v
  row : ∃ (w : Names) (value : Term sig), arm.values = [value] ∧
    EquivB (arm.subst.image q.x) (w.images q.table sh).1 ∧
    EquivB (arm.subst.image q.y) (w.images q.table sh).2.1 ∧ EquivB value (w.images q.table sh).2.2

private def Names.assign (w : Names) (h i j : Term sig)
    (th : HasSort h .msg) (ti : HasSort i .msg) (tj : HasSort j .msg) : Substitution sig where
  image v := if v = w.h then h else if v = w.i then i else if v = w.j then j else .var v
  support := [w.h,w.i,w.j]
  outside v hn := by simp_all
  sorted v := by
    split <;> rename_i e
    · simp [e,w.hs,th]
    split <;> rename_i e
    · simp [e,w.isMsg,ti]
    split <;> rename_i e
    · simp [e,w.js,tj]
    · exact .var _

theorem Decodes.covers {q : Query sig} {sh : Shape} {arm : Variant sig} (cert : Decodes q sh arm)
    (ρ : Substitution sig) {out : Term sig} (inst : Instance q.table (ρ.image q.x) (ρ.image q.y) out sh) :
    arm.Covers q.table.R [q.term] ρ [out] := by
  obtain ⟨w,v,values,l,r,o⟩ := cert.row
  obtain ⟨h,i,j,hh,hi,hj,left,right,value⟩ := inst.witnesses
  let δ := w.assign h i j hh.1 hi.1 hj.1
  have vars := (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1
  have hn : Normalized q.table.R δ := by
    intro x
    change Normal _ (if _ then _ else if _ then _ else if _ then _ else _)
    split; exact hh.2
    split; exact hi.2
    split; exact hj.2; exact vars _
  have hits : δ.image w.h = h ∧ δ.image w.i = i ∧ δ.image w.j = j := by
    simp [δ,Names.assign,Ne.symm w.hi,Ne.symm w.hj,Ne.symm w.ij]
  have trans : (δ.apply (w.images q.table sh).1,δ.apply (w.images q.table sh).2.1,
      δ.apply (w.images q.table sh).2.2) = sh.images q.table h i j := by
    have H : δ.apply (.var w.h) = h := hits.1
    have I : δ.apply (.var w.i) = i := hits.2.1
    have J : δ.apply (.var w.j) = j := hits.2.2
    have ac (a b : Term sig) : δ.apply (.ac q.table.f a b) = .ac q.table.f (δ.apply a) (δ.apply b) := rfl
    cases sh <;> simp only [Names.images,Shape.images,ac,H,I,J,q.table.toTable.fixes_zero]
  have l' := l.subst δ.image
  have r' := r.subst δ.image
  have o' := o.subst δ.image
  change EquivB (δ.apply _) (δ.apply _) at l' r' o'
  have el := congrArg Prod.fst trans
  have er := congrArg (fun p => p.2.1) trans
  have eo := congrArg (fun p => p.2.2) trans
  refine ⟨δ,hn,?_,?_⟩
  · intro x hx
    obtain ⟨_,mem,occ⟩ := hx; obtain rfl := List.mem_singleton.mp mem
    change x = q.x ∨ x = q.y at occ
    rcases occ with rfl|rfl
    · exact left.trans (el ▸ l'.symm)
    · exact right.trans (er ▸ r'.symm)
  · rw [values]
    exact ⟨value.trans (eo ▸ o'.symm),trivial⟩

private theorem transport {s t : Term sig} (e : EquivB s t) {k} (h : HasSort s k) : HasSort t k :=
  Term.checkSort_sound _ _ (SortClash.check_equiv e k ▸ Term.checkSort_complete h)

theorem Decodes.sound {q : Query sig} {sh : Shape} {arm : Variant sig} (cert : Decodes q sh arm)
    (shapeForm : ∀ w : Names, let p := w.images q.table sh
      Good q.table p.1 ∧ Good q.table p.2.1 ∧ NormalForm q.table.R (.ac q.table.f p.1 p.2.1) p.2.2) :
    arm.Sound q.table.R [q.term] := by
  obtain ⟨w,v,vals,l,r,o⟩ := cert.row
  obtain ⟨hl,hr,nf⟩ := shapeForm w
  have norm : Normalized q.table.R arm.subst := by
    intro z
    by_cases hx : z = q.x
    · subst z; exact (normal_equiv _ l).mpr hl.2
    by_cases hy : z = q.y
    · subst z; exact (normal_equiv _ r).mpr hr.2
    rw [cert.outside z hx hy]
    exact (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1 z
  refine ⟨norm,?_⟩
  rw [vals]
  have e : EquivB (arm.subst.apply q.term) _ := .ac_congr q.table.f l r
  exact ⟨⟨(Reduces.basis e).trans (nf.1.trans (.basis o.symm)),(normal_equiv _ o).mpr nf.2.1,
    fun k typed => transport o.symm (nf.2.2 k (transport e typed))⟩,trivial⟩

/-- The generator is free to obtain rows by rule-table narrowing, reuse,
or direct enumeration. The finite membership checks are separate from the
classification and normalization obligations of the active equational theory. -/
theorem complete_of_classification (q : Query sig) (arms : List (Variant sig))
    (all : ∀ sh, ∃ arm ∈ arms, Decodes q sh arm) (only : ∀ arm ∈ arms, ∃ sh, Decodes q sh arm)
    (classify : ∀ {a b u}, Good q.table a → Good q.table b → NormalForm q.table.R (.ac q.table.f a b) u →
      ∃ sh, Instance q.table a b u sh)
    (valid : ∀ sh (w : Names), let p := w.images q.table sh
      Good q.table p.1 ∧ Good q.table p.2.1 ∧ NormalForm q.table.R (.ac q.table.f p.1 p.2.1) p.2.2)
    (unique : ∀ {a b u v}, Good q.table a → Good q.table b →
      NormalForm q.table.R (.ac q.table.f a b) u → NormalForm q.table.R (.ac q.table.f a b) v → EquivB u v) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ arm ∈ arms, arm.Reconstructible q.table.R [q.term] := by
  have sound arm (ha : arm ∈ arms) : arm.Sound q.table.R [q.term] := by
    obtain ⟨sh,cert⟩ := only arm ha
    exact cert.sound (valid sh)
  have input (ρ : Substitution sig) (hn : Normalized q.table.R ρ) :
      Good q.table (ρ.image q.x) ∧ Good q.table (ρ.image q.y) :=
    ⟨⟨q.sx ▸ ρ.sorted _,hn _⟩,⟨q.sy ▸ ρ.sorted _,hn _⟩⟩
  refine ⟨⟨sound,?_⟩,?_⟩
  · intro ρ hn vals forms
    cases vals with
    | nil => exact False.elim forms
    | cons v vs => cases vs with
      | cons => exact False.elim forms.2
      | nil =>
        obtain ⟨sh,instanceOf⟩ := classify (input ρ hn).1 (input ρ hn).2 forms.1
        obtain ⟨arm,mem,cert⟩ := all sh
        exact ⟨arm,mem,cert.covers ρ instanceOf⟩
  · intro arm mem
    have hs := sound arm mem
    apply Variant.reconstructible_of_unique hs
    intro t ht u v hu hv
    obtain rfl := List.mem_singleton.mp ht
    exact unique (input _ hs.1).1 (input _ hs.1).2 hu hv

/-- For the active XOR table the seven shapes are sound and exhaustive on
arbitrary normalized Msg images, including compounds from other theories. -/
theorem complete (q : Query sig) (arms : List (Variant sig))
    (all : ∀ sh, ∃ arm ∈ arms, Decodes q sh arm)
    (only : ∀ arm ∈ arms, ∃ sh, Decodes q sh arm) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ arm ∈ arms, arm.Reconstructible q.table.R [q.term] :=
  complete_of_classification q arms all only (classify q.table)
    (fun sh w => shape_normal q.table sh w.h w.i w.j w.hs w.isMsg w.js w.hi w.hj w.ij)
    (unique q.table)

end Tamarin.Rewriting.BinaryXor
