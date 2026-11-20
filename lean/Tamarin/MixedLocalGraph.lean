import Tamarin.MixedLocalAnswers

/-! A singleton local image names its entire original slot. Substitute that
slot back for the witness everywhere in this arm. For a model which separates
the slots, a singleton witness has at most one such owner. The remaining
definitions all have this operator as their outer constructor. -/
namespace Tamarin.MixedUnification.LocalAnswers.Arm
open SolvedForm
variable {s : Signature} {f : s.ACSym} {rs : List SumRow}
variable (a : Arm s f rs)

private def singleton (i : Nat) := match a.image i with | .var w => some w | _ => none

private theorem singleton_iff {i w} : a.singleton i = some w ↔ a.image i = .var w := by
  unfold singleton
  cases a.image i <;> simp

private def owner (w : Variable) := (keys rs).find? fun i => a.singleton i == some w

def link (tag : Variable → Variable) (w : Variable) := match a.owner w with
  | some i => ref i
  | none => tag w

def body (tag : Variable → Variable) (i : Nat) : Term s :=
  (a.image i).subst (.var ∘ a.link tag)

def graph (tag : Variable → Variable) : List (Row s) :=
  ((keys rs).filter (fun i => (a.singleton i).isNone)).map fun i => (ref i,a.body tag i)

theorem entry {tag d} (h : d ∈ a.graph tag) : ∃ i ∈ keys rs, d = (ref i,a.body tag i) ∧
    ∃ l r, a.body tag i = .ac f l r := by
  obtain ⟨i,hm,rfl⟩ := List.mem_map.mp h
  obtain ⟨hi,hn⟩ := List.mem_filter.mp hm
  refine ⟨_,hi,rfl,?_⟩
  rcases a.shape i with ⟨w,eq⟩|⟨l,r,eq⟩
  · rw [(a.singleton_iff.mpr eq)] at hn; contradiction
  · unfold body; rw [eq]; exact ⟨_,_,rfl⟩

variable {V : Nat → Term s} {μ : Env s}

private theorem owner_eq
    (covers : ∀ i ∈ keys rs, EquivB (V i) ((a.image i).subst μ))
    (separates : ∀ i ∈ keys rs, ∀ j ∈ keys rs, EquivB (V i) (V j) → i = j)
    {i w} (hi : i ∈ keys rs) (h : a.image i = .var w) : a.owner w = some i := by
  cases search : a.owner w with
  | none =>
    have no := List.find?_eq_none.mp search i hi
    simp [a.singleton_iff.mpr h] at no
  | some j =>
    have hj := List.mem_of_find?_eq_some search
    have ok : (a.singleton j == some w) = true := List.find?_some (p := fun i => a.singleton i == some w) search
    have hit := a.singleton_iff.mp (beq_iff_eq.mp ok)
    have left := covers i hi
    have right := covers j hj
    rw [h] at left; rw [hit] at right
    rw [separates i hi j hj (left.trans right.symm)]

theorem graph_model (tag) (W : Env s)
    (slotW : ∀ i, W (ref i) = V i) (tagW : ∀ w, W (tag w) = μ w)
    (covers : ∀ i ∈ keys rs, EquivB (V i) ((a.image i).subst μ)) :
    Models (a.graph tag) W := by
  intro d hd
  obtain ⟨i,hi,rfl,_⟩ := a.entry hd
  change EquivB (W (ref i)) (((a.image i).subst _).subst W)
  rw [slotW,Term.subst_comp]
  apply (covers i hi).trans
  apply Term.subst_equiv
  intro w _
  change EquivB (μ w) (W (a.link tag w))
  unfold link
  split
  next j eq =>
    have ok : (a.singleton j == some w) = true := List.find?_some (p := fun i => a.singleton i == some w) eq
    have eqv := a.singleton_iff.mp (beq_iff_eq.mp ok)
    have hit := covers j (List.mem_of_find?_eq_some eq)
    rw [eqv] at hit
    rw [slotW]; exact hit.symm
  next => rw [tagW]; exact .refl _

theorem graph_solves (tag) (θ : Env s) (model : Models (a.graph tag) θ)
    (covers : ∀ i ∈ keys rs, EquivB (V i) ((a.image i).subst μ))
    (separates : ∀ i ∈ keys rs, ∀ j ∈ keys rs, EquivB (V i) (V j) → i = j)
    (r : SumRow) (hr : r ∈ rs) :
    EquivB (θ (ref r.out)) (.ac f (θ (ref r.left)) (θ (ref r.right))) := by
  let κ := fun w => θ (a.link tag w)
  have value (i) (hi : i ∈ keys rs) : EquivB (θ (ref i)) ((a.image i).subst κ) := by
    cases eq : a.singleton i with
    | some w =>
      have hit := a.singleton_iff.mp eq
      rw [hit]
      change EquivB _ (θ (a.link tag w))
      rw [link,a.owner_eq covers separates hi hit]
      exact .refl _
    | none =>
      have hm := model _ (List.mem_map_of_mem (f := fun i => (ref i,a.body tag i))
        (show i ∈ (keys rs).filter (fun j => (a.singleton j).isNone) from List.mem_filter.mpr ⟨hi,by simp [eq]⟩))
      change EquivB _ (((a.image i).subst _).subst θ) at hm
      rw [Term.subst_comp] at hm; exact hm
  apply (value r.out (at_row hr (by simp [SumRow.keys]))).trans
  apply ((a.solves r hr).subst κ).trans
  exact .ac_congr f (value _ (at_row hr (by simp [SumRow.keys]))).symm
    (value _ (at_row hr (by simp [SumRow.keys]))).symm

end Tamarin.MixedUnification.LocalAnswers.Arm
