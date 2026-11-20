import Tamarin.DestructorTable
import Tamarin.BoundedVariants
import Tamarin.CheckedVariantOverlap

/-! Normal substitutions can contain arbitrarily many stuck destructors.
Count free applications with a possible rewrite anywhere underneath them.
This measure is zero on normal images and invariant under C/AC regrouping. -/
namespace Tamarin.DestructorTable
open Rewriting MaudeOperations
variable {s : Signature} {rs : Problem s}

private noncomputable def active (R : Root s) (t : Term s) : Nat := by
  classical exact if Normal R t then 0 else 1

private noncomputable def rank (R : Root s) : Term s → Nat
  | .var _ | .atom _ => 0
  | t@(.free _ xs) => (List.ofFn fun i => rank R (xs i)).sum + active R t
  | .comm _ a b | .ac _ a b => rank R a + rank R b

private theorem rank_basis {R : Root s} {a b : Term s} (eq : EquivB a b) : rank R a = rank R b := by
  induction eq with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ l r => exact l.trans r
  | free f xs ys e ih =>
    have norm := propext (normal_equiv R (EquivB.free f xs ys e))
    simp only [rank,funext ih,active]; rw [norm]
  | comm_congr f _ _ l r | ac_congr f _ _ l r => simp [rank,l,r]
  | comm_swap | ac_swap => simp [rank,Nat.add_comm]
  | ac_assoc => simp [rank,Nat.add_assoc]

private theorem rank_path {R : Root s} {a b : Term s} {p} (atPos : atPath a p = some b) :
    rank R b ≤ rank R a := by
  induction p generalizing a with
  | nil => simp_all [atPath]
  | cons i p ih =>
    cases a <;> simp only [atPath] at atPos <;> try contradiction
    split at atPos <;> try contradiction
    next f xs hi =>
      exact Nat.le_trans (ih atPos) (Nat.le_trans (FiniteOccurs.le_sum _ _ (List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩))
        (Nat.le_add_right (List.ofFn (fun j => rank R (xs j))).sum _))

variable [DecidableEq s.FreeSym]

omit [DecidableEq s.FreeSym] in
private theorem rank_step (cls : Presentation rs) {a b : Term s} (step : Step (ruleRoot rs) a b) :
    rank (ruleRoot rs) b < rank (ruleRoot rs) a := by
  let R := ruleRoot rs
  have on {t u} (st : Step R t u) : active R t = 1 := by
    have hn : ¬ Normal R t := fun nf => nf u ⟨_,_,.refl _,st,.refl _⟩
    simp [active,hn]
  induction step with
  | root fire =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := fire
    obtain ⟨f,xs,src,_⟩ := cls.patterns r hr
    obtain ⟨p,ne,hp⟩ := cls.positions r hr
    have pos := apply_path σ (hp r hr rfl)
    have source := on (Step.root (root := R) ⟨r,hr,σ,rfl,rfl⟩)
    rw [src] at pos source ⊢
    cases p with
    | nil => contradiction
    | cons i p =>
      simp only [atPath,Substitution.apply,Term.subst] at pos
      split at pos <;> try contradiction
      next hi =>
        have child := rank_path (R := R) pos
        have size := FiniteOccurs.le_sum _ _ ((List.mem_ofFn (f := fun j => rank R (σ.apply (xs j)))).mpr ⟨⟨i,hi⟩,rfl⟩)
        change _ < _ + active R (σ.apply (.free f xs))
        rw [source]
        exact Nat.lt_succ_of_le (Nat.le_trans child size)
  | @free f xs i u st ih =>
    change _ + active R _ < _ + active R _
    rw [on (Step.free f xs i st)]
    have child := TableDecrease.sum_lt i (fun j => rank R (xs j))
      (fun j => rank R (if j = i then u else xs j)) (by simpa using ih) (by intro j ne; simp [ne])
    have cap (t : Term s) : active R t ≤ 1 := by unfold active; split <;> decide
    exact Nat.add_lt_add_of_lt_of_le child (cap _)
  | comm_left f _ _ ih | ac_left f _ _ ih => exact Nat.add_lt_add_right ih _
  | comm_right f _ _ ih | ac_right f _ _ ih => exact Nat.add_lt_add_left ih _

omit [DecidableEq s.FreeSym] in
private theorem normal_zero {R : Root s} (t : Term s) (nf : Normal R t) : rank R t = 0 := by
  induction t with
  | var | atom => rfl
  | free f xs ih =>
    simp [rank,active,nf,List.sum_eq_zero_iff_forall_eq_nat,fun i => ih i (normal_free_child f xs nf i)]
  | comm f a b l r =>
    obtain ⟨ha,hb⟩ := normal_comm_children f nf
    simp [rank,l ha,r hb]
  | ac f a b l r =>
    obtain ⟨ha,hb⟩ := normal_ac_children f nf
    simp [rank,l ha,r hb]

omit [DecidableEq s.FreeSym] in
private theorem uniform {R : Root s} (t : Term s) (σ : Substitution s) (nf : Normalized R σ) :
    rank R (σ.apply t) ≤ FiniteOccurs.nodes t := by
  induction t with
  | var v => exact (normal_zero _ (nf v)) ▸ Nat.zero_le _
  | atom => exact Nat.zero_le _
  | free f xs ih =>
    change _ + active R _ ≤ (List.ofFn (fun i => FiniteOccurs.nodes (xs i))).sum + 1
    apply Nat.add_le_add (FoldingNarrowing.sum_mono ih)
    unfold active; split <;> decide
  | comm f a b l r | ac f a b l r =>
    change _ + _ ≤ FiniteOccurs.nodes a + FiniteOccurs.nodes b + 1
    exact Nat.le_trans (Nat.add_le_add l r) (Nat.le_succ _)

variable [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

theorem finiteVariants (cls : Presentation rs) (dec : TableDecrease.decreasing rs)
    (sorted : TableDecrease.sorted rs) : FiniteVariantProperty (ruleRoot rs) :=
  BoundedVariants.finiteVariantProperty (TableDecrease.bound dec) (canonical cls dec sorted) (rank _)
    (fun ⟨_,_,l,step,r⟩ => by rw [rank_basis l,← rank_basis r]; exact rank_step cls step)
    (fun t => ⟨_,uniform t⟩)

/-- Use the structural reducer for the initial tuple and each narrowing point.
The finite-variant proof supplies termination of the generic folding search. -/
def variants (cls : Presentation rs) (dec : TableDecrease.decreasing rs) (sorted : TableDecrease.sorted rs)
    (q : List (Term s)) : {rows // CheckedVariants.Reply (ruleRoot rs) q rows} := by
  let r : VerifiedReducer (ruleRoot rs) := ⟨fold rs,reductionReply cls dec sorted⟩
  let bound := TableDecrease.bound dec
  let can := canonical cls dec sorted
  let vars := TableNarrowing.variablesNormal can
  let narrow := TableNarrowing.narrower bound vars (fun i : Fin q.length => q[i.val])
  let exp := FoldingNarrowing.expansion bound can vars r narrow
  let out := VariantSaturation.solve exp can vars r (by simpa using finiteVariants cls dec sorted q) []
  refine ⟨out.val,⟨by simpa using out.property,?_⟩⟩
  intro σ _ xs ys left right
  induction q generalizing xs ys with
  | nil => cases xs <;> cases ys <;> simp_all [Aligned]
  | cons t ts ih =>
    cases xs with
    | nil => exact left.elim
    | cons x xs =>
      cases ys with
      | nil => exact right.elim
      | cons y ys =>
        have uniq := (r.correct (σ.apply t)).unique
        exact ⟨(uniq _ left.1).trans (uniq _ right.1).symm,ih _ _ left.2 right.2⟩

end Tamarin.DestructorTable
