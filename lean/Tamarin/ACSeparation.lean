import TamarinRuntime.ACSeparation
import Tamarin.ACDirectFeasibility

namespace Tamarin.ACFeasibility.Separation
open ACBasis
variable {n : Nat}

/-- The sum of the signed coefficients of the original rows at a column,
each multiplied by its corresponding certificate weight. -/
def combination (pairs : List (Int × Row n)) (i : Fin n) : Int :=
  (pairs.map fun (w,r) => w * ((r.pos i : Int) - r.neg i)).sum

/-- Strict positivity at one coordinate suffices since every unification
variable must have a nonempty image. -/
def Certificate (rows : List (Row n)) (weights : List Int) : Prop :=
  weights.length = rows.length ∧
  (∀ i, 0 ≤ combination (weights.zip rows) i) ∧ ∃ i, 0 < combination (weights.zip rows) i

theorem column_eq (pairs : List (Int × Row n)) (i : Fin n) : column pairs i = combination pairs i := by
  have sum (acc : Int) : pairs.foldl (fun acc (w,r) => acc + w * ((r.pos i : Int) - r.neg i)) acc =
      acc + combination pairs i := by
    induction pairs generalizing acc with
    | nil => simp [combination]
    | cons a rest ih =>
      simp only [List.foldl_cons,ih,combination,List.map_cons,List.sum_cons,Int.add_assoc]
  simpa [column] using sum 0

private theorem skip_zero (pairs : List (Int × Row n)) (i : Fin n) :
    combination (pairs.filter (fun (w,_) => w != 0)) i = combination pairs i := by
  induction pairs with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨w,r⟩ := a
    by_cases h : w = 0 <;> simp [combination,h] at ih ⊢ <;> rw [ih]

private theorem scan_iff (pairs : List (Int × Row n)) (is : List (Fin n)) (seen : Bool) :
    scan pairs is seen = true ↔
      (∀ i ∈ is, 0 ≤ combination pairs i) ∧ (seen = true ∨ ∃ i ∈ is, 0 < combination pairs i) := by
  induction is generalizing seen with
  | nil => simp [scan]
  | cons i is ih =>
    rw [scan,column_eq]
    by_cases negative : combination pairs i < 0
    · simp [negative,Int.not_le.mpr negative]
    · simp only [negative,↓reduceIte,ih,List.forall_mem_cons,Bool.or_eq_true,
        decide_eq_true_eq]
      have nonneg := Int.not_lt.mp negative
      grind

theorem separates_iff (rows : List (Row n)) (weights : List Int) :
    separates rows weights = true ↔ Certificate rows weights := by
  simp [separates,Certificate,scan_iff,skip_zero]

private def eval (is : List (Fin n)) (a : Fin n → Int) (x : Vec n) :=
  (is.map (fun i => a i * (x i : Int))).sum

private theorem row_eval (r : Row n) (x : Vec n) (holds : r.Holds x) :
    eval (List.finRange n) (fun i => (r.pos i : Int) - r.neg i) x = 0 := by
  have sub (is : List (Fin n)) :
      eval is (fun i => (r.pos i : Int) - r.neg i) x =
        (((is.map (fun i => r.pos i * x i)).sum : Nat) : Int) - (is.map (fun i => r.neg i * x i)).sum := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [eval,List.map_cons,List.sum_cons,Int.natCast_add,Int.natCast_mul] at ih ⊢
      rw [ih]; grind
  rw [sub]
  simp only [List.finRange,List.map_ofFn,Function.comp_def]
  change (dot r.pos x : Int) - dot r.neg x = 0
  rw [show dot r.pos x = dot r.neg x from holds,Int.sub_self]

private theorem eval_cons (w : Int) (r : Row n) (pairs : List (Int × Row n)) (x : Vec n) (is : List (Fin n)) :
    eval is (combination ((w,r)::pairs)) x =
      w * eval is (fun i => (r.pos i : Int) - r.neg i) x + eval is (combination pairs) x := by
  induction is with
  | nil => simp [eval]
  | cons i is ih =>
    simp only [eval,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    change (w * ((r.pos i : Int) - r.neg i) + combination pairs i) * _ + _ = _
    grind

private theorem eval_zero (pairs : List (Int × Row n)) (x : Vec n) (agree : ∀ p ∈ pairs, p.2.Holds x) :
    eval (List.finRange n) (combination pairs) x = 0 := by
  induction pairs with
  | nil => simp [eval,combination,List.map_const',List.sum_replicate_int]
  | cons p pairs ih =>
    rcases p with ⟨w,r⟩
    rw [eval_cons,row_eval r x (agree _ List.mem_cons_self),ih (fun p hp => agree p (List.mem_cons_of_mem _ hp))]
    simp

private theorem eval_nonneg (is : List (Fin n)) (a : Fin n → Int) (x : Vec n) (ok : ∀ i, 0 ≤ a i) :
    0 ≤ eval is a x := by
  induction is with
  | nil => simp [eval]
  | cons i is ih => exact Int.add_nonneg (Int.mul_nonneg (ok i) (Int.natCast_nonneg _)) ih

private theorem eval_pos (is : List (Fin n)) (a : Fin n → Int) (x : Vec n) (nonneg : ∀ i, 0 ≤ a i)
    (positive : ∀ i, 0 < x i) (somePos : ∃ i ∈ is, 0 < a i) : 0 < eval is a x := by
  induction is with
  | nil => simp at somePos
  | cons i is ih =>
    have alt : 0 < a i ∨ ∃ k ∈ is, 0 < a k := by grind
    rcases alt with here | tail
    · exact Int.add_pos_of_pos_of_nonneg (Int.mul_pos here (by exact_mod_cast positive i)) (eval_nonneg is a x nonneg)
    · exact Int.add_pos_of_nonneg_of_pos (Int.mul_nonneg (nonneg i) (Int.natCast_nonneg _)) (ih tail)

theorem separates_refutes {rows : List (Row n)} {weights : List Int} (checked : separates rows weights = true) :
    ¬ Feasible rows := by
  obtain ⟨_,nonneg,i,strict⟩ := (separates_iff ..).mp checked
  rintro ⟨x,holds,positive⟩
  have zero := eval_zero (weights.zip rows) x (fun p hp => holds p.2 (List.of_mem_zip hp).2)
  have greater := eval_pos (List.finRange n) _ x nonneg positive ⟨i,List.mem_finRange i,strict⟩
  omega

end Tamarin.ACFeasibility.Separation
