import Tamarin.MixedComponentEncoding
import Tamarin.MixedSolvedForm

/-! Independent local AC solutions on a common table of source slots. Their
parameters are private to an operator. No sort assumptions are made on the
source slot values. -/
namespace Tamarin.MixedUnification.LocalAnswers
open ComponentEncoding
variable {s : Signature}

def ref (i : Nat) : Variable := ⟨i,.msg⟩

/-- Coordinates at a single operator, before any local witness is introduced. -/
structure SumRow where
  out : Nat
  left : Nat
  right : Nat

def SumRow.matrix (r : SumRow) : ACSystem.Row :=
  ⟨⟨ref r.out,[]⟩,⟨ref r.left,[ref r.right]⟩⟩

def SumRow.keys (r : SumRow) := [r.out,r.left,r.right]

def rows [DecidableEq s.ACSym] (cs : List (Constraint s)) (f : s.ACSym) : List SumRow :=
  cs.filterMap fun c => match c with
    | .ac i g j k => if f = g then some ⟨i,j,k⟩ else none
    | _ => none

theorem mem_rows [DecidableEq s.ACSym] {cs : List (Constraint s)} {f : s.ACSym} {r : SumRow} :
    r ∈ rows cs f ↔ .ac r.out f r.left r.right ∈ cs := by
  constructor
  · intro h
    obtain ⟨c,hc,h⟩ := List.mem_filterMap.mp h
    cases c <;> simp_all
    obtain ⟨_,rfl⟩ := h; exact hc
  · intro h
    exact List.mem_filterMap.mpr ⟨_,h,by simp⟩

def keys (rs : List SumRow) := (rs.flatMap SumRow.keys).eraseDups

theorem at_row {rs : List SumRow} {r} (hr : r ∈ rs) {i} (hi : i ∈ r.keys) : i ∈ keys rs :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨r,hr,hi⟩)

private theorem live (rs : List SumRow) (v : Variable) :
    v ∈ ACSystem.variables (rs.map SumRow.matrix) ↔ ∃ i ∈ keys rs, v = ref i := by
  simp [ACSystem.variables,SumRow.matrix,ACSystem.Side.vars,keys,SumRow.keys,List.mem_flatMap]
  grind

structure Arm (s : Signature) (f : s.ACSym) (rs : List SumRow) where
  image : Nat → Term s
  shape : ∀ i, (∃ w, image i = .var w) ∨ ∃ a b, image i = .ac f a b
  solves : ∀ r ∈ rs, EquivB (image r.out) (.ac f (image r.left) (image r.right))

private theorem sorted (rs : List SumRow) (f : s.ACSym) :
    ∀ v ∈ ACSystem.variables (rs.map SumRow.matrix), v.sort = (uniform s).acSort f := by
  intro v hv
  obtain ⟨_,_,rfl⟩ := (live ..).mp hv
  rfl

def arms (f : s.ACSym) (rs : List SumRow) : List (Arm s f rs) :=
  let matrix := rs.map SumRow.matrix
  let answers := ACSystem.Reference.solve (sig := uniform s) f matrix (sorted rs f) []
  answers.attach.map fun ans => {
    image := fun i => read Term.var (ans.val.image (ref i))
    shape := fun i => by
      rcases ACSystem.Reference.image_shape ans.property (ref i) with ⟨w,h⟩ | ⟨a,b,h⟩
      · exact .inl ⟨w,by rw [h]; rfl⟩
      · exact .inr ⟨_,_,by rw [h]; rfl⟩
    solves := fun r hr => by
      have sound := (ACSystem.Reference.correct (sig := uniform s) f matrix (sorted rs f) []).mathematical.sound
      exact read_equiv Term.var (sound _ ans.property _ (List.mem_map_of_mem
        (f := fun r => ACSystem.Row.equation (sig := uniform s) r f) (List.mem_map_of_mem (f := SumRow.matrix) hr))) }

/-- Every source model factors through one local arm, with one common
instantiation for all its coordinates, including coordinates of alien sort. -/
theorem covers (f : s.ACSym) (rs : List SumRow) (V : Nat → Term s)
    (model : ∀ r ∈ rs, EquivB (V r.out) (.ac f (V r.left) (V r.right))) :
    ∃ arm ∈ arms f rs, ∃ μ : SolvedForm.Env s, ∀ i ∈ keys rs,
      EquivB (V i) ((arm.image i).subst μ) := by
  let obs := (keys rs).map ref
  let ρ := reserve obs V
  have known (i) (hi : i ∈ keys rs) : ρ.image (ref i) = encode (V i) :=
    ite_eq_left ⟨List.mem_map_of_mem hi,rfl⟩
  let matrix := rs.map SumRow.matrix
  have solution : (ACSystem.problem (sig := uniform s) f matrix).Solves ρ := by
    intro e he
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    change EquivB (ρ.image (ref r.out)) (.ac f (ρ.image (ref r.left)) (ρ.image (ref r.right)))
    rw [known _ (at_row hr (by simp [SumRow.keys])),known _ (at_row hr (by simp [SumRow.keys])),
      known _ (at_row hr (by simp [SumRow.keys]))]
    exact encode_equiv (model r hr)
  obtain ⟨σ,hσ,δ,agree⟩ := (ACSystem.Reference.correct (sig := uniform s) f matrix (sorted rs f)
    []).mathematical.covers ρ solution
  refine ⟨_,List.mem_map_of_mem (List.mem_attach _ ⟨σ,hσ⟩),fun v => read (.var ∘ original) (δ.image v),?_⟩
  intro i hi
  have occ := (ACSystem.occurs_iff_mem (sig := uniform s) f matrix (ref i)).mpr
    ((live ..).mpr ⟨i,hi,rfl⟩)
  have eq := read_equiv (s := s) (.var ∘ original) (agree _ occ)
  change EquivB (read _ (ρ.image (ref i))) (read _ (δ.apply (σ.image (ref i)))) at eq
  rw [known i hi,read_encode,read_subst] at eq
  exact eq

end Tamarin.MixedUnification.LocalAnswers
