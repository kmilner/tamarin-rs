import Tamarin.ACRowReductionCoverage
import Tamarin.ACReducedFeasibility

/-! A structural positive-feasibility floor for back substitution. Each pivot
is alone on its side, the opposite side is nonempty, and later equations
omit that pivot. Clearing a denominator may scale all coordinates. A fixed
product of row bounds controls the entire construction before it runs. -/
namespace Tamarin.ACFeasibility.Adjustment
open ACBasis
variable {n : Nat}

private def first (r : Row n) :=
  (List.finRange n).find? (fun i => 0 < r.pos i || 0 < r.neg i)

def side (r : Row n) (j : Fin n) : Vec n := if r.neg j = 0 then r.pos else r.neg
def opposite (r : Row n) (j : Fin n) : Vec n := if r.neg j = 0 then r.neg else r.pos

/-- A zero row imposes no condition. For a nonzero row the least nonzero
column is reserved for solving this equation without changing any later
equation except by a common positive multiple. -/
def Triangular : List (Row n) → Prop
  | [] => True
  | r :: rs => Triangular rs ∧ match first r with
    | none => True
    | some j =>
      side r j = spike j (r.pos j + r.neg j) ∧ (∃ i, 0 < opposite r j i) ∧
      ∀ t ∈ rs, t.pos j = 0 ∧ t.neg j = 0

def growth (r : Row n) := max 1 (total r.pos + total r.neg)

def Within (rs : List (Row n)) : Prop :=
  let out := RowReduction.Reference.output rs.length rs
  n*rs.length*rs.length ≤ 524288 ∧ RowReduction.Reference.coefficientsFit rs.length rs ∧
    Triangular out ∧ (out.map growth).prod < 2^128

private def coord (x : Vector Nat n) : Vec n := fun i => x[i]

private theorem prod_bound (u v : Vec n) {b : Nat} (hv : ∀ i, v i ≤ b) : dot u v ≤ total u * b := by
  induction n with
  | zero => simp [dot,total]
  | succ n ih =>
    simp only [dot,total,List.ofFn_succ,List.sum_cons,Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (hv 0)) (ih _ _ (fun i => hv i.succ))

private theorem total_bound (w : Vec n) (j : Fin n) : w j ≤ total w := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [total,List.ofFn_succ,List.sum_cons]
    cases j using Fin.cases with
    | zero => omega
    | succ j => exact Nat.le_trans (ih (fun i => w i.succ) j) (Nat.le_add_left ..)

private theorem scaled (u v : Vec n) (s : Nat) :
    dot u (fun i => s * v i) = s * dot u v := by
  induction n with
  | zero => simp [dot,total]
  | succ n ih =>
    simp only [dot,total,List.ofFn_succ,List.sum_cons,Nat.mul_add]
    have e := ih (fun i => u i.succ) (fun i => v i.succ)
    rw [show u 0 * (s * v 0) = s * (u 0 * v 0) by ac_rfl]
    exact congrArg (_ + ·) e

private theorem spike_dot (j : Fin n) (a : Nat) (v : Vec n) : dot (spike j a) v = a * v j := by
  calc
    _ = dot v (spike j a) := by simp only [dot,Nat.mul_comm]
    _ = _ := by simp [dot_spike,Nat.mul_comm]

private def assign (j : Fin n) (value scale : Nat) (x : Vector Nat n) : Vector Nat n :=
  Vector.ofFn (fun i => if i = j then value else scale*x[i])

private theorem scale_untouched (v : Vec n) (j : Fin n) (z scale : Nat) (x : Vector Nat n)
    (absent : v j = 0) : dot v (coord (assign j z scale x)) = scale * dot v (coord x) := by
  rw [←scaled]
  unfold dot
  apply congrArg total
  funext i
  by_cases h : i = j <;> simp [coord,assign,h,absent]

private theorem row_step (r : Row n) (ts : List (Row n)) (j : Fin n) (x : Vector Nat n)
    (picked : first r = some j) (single : side r j = spike j (r.pos j + r.neg j))
    (other : ∃ i, 0 < opposite r j i) (untouched : ∀ t ∈ ts, t.pos j = 0 ∧ t.neg j = 0)
    (pos : ∀ i, 0 < coord x i) {b : Nat} (bound : ∀ i, coord x i ≤ b)
    (fits : growth r * b < 2^128) (holds : SystemHolds ts (coord x)) :
    ∃ y, adjust r x = some y ∧ SystemHolds (r::ts) (coord y) ∧
      (∀ i, 0 < coord y i) ∧ ∀ i, coord y i ≤ growth r*b := by
  let a := r.pos j + r.neg j
  let opp := opposite r j
  let target := dot opp (coord x)
  have pa : 0 < a := by
    have h := List.find?_some picked
    simp at h
    dsimp only [a]; omega
  have ot : 0 < target := by
    obtain ⟨i,pi⟩ := other
    exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,Nat.mul_pos pi (pos i)⟩
  have share (v : Vec n) : dot (side r j) v = a*v j := by rw [single,spike_dot]
  have flip (v : Vec n) : r.Holds v ↔ dot (side r j) v = dot opp v := by
    dsimp only [side,opp,opposite,Row.Holds]; split <;> first | rfl | exact eq_comm
  have os : opp j = 0 := by
    by_cases h : r.neg j = 0
    · simp [opp,opposite,h]
    · simp [opp,opposite,h,(r.disjoint j).resolve_right h]
  have ba : a ≤ growth r := by
    exact Nat.le_trans (Nat.add_le_add (total_bound r.pos j) (total_bound r.neg j)) (Nat.le_max_right ..)
  have bo : total opp ≤ growth r := by
    dsimp only [growth,opp,opposite]
    split <;> omega
  have upper : target ≤ growth r*b := Nat.le_trans (prod_bound _ _ bound) (Nat.mul_le_mul_right b bo)
  by_cases equal : r.Holds (coord x)
  · have h : dot r.pos (fun i => x[i]) = dot r.neg (fun i => x[i]) := equal
    refine ⟨x,by simp only [adjust,h,ite_true]; rfl,?_,pos,fun i => Nat.le_trans (bound i) ?_⟩
    · simpa [SystemHolds] using (And.intro equal holds)
    · simpa only [growth,Nat.one_mul] using Nat.mul_le_mul_right b (Nat.le_max_left 1 (total r.pos+total r.neg))
  · let d := a.gcd target
    let scale := a / d
    let value := target / d
    let y := assign j value scale x
    have sd : 0 < d := Nat.gcd_pos_of_pos_left _ pa
    have sf : 0 < scale := Nat.div_pos (Nat.le_of_dvd pa (Nat.gcd_dvd_left ..)) sd
    have vp : 0 < value := Nat.div_pos (Nat.le_of_dvd ot (Nat.gcd_dvd_right ..)) sd
    have mul : a*value = scale*target := by
      have ha : scale*d = a := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
      have ht : value*d = target := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
      calc
        a*value = (scale*d)*value := congrArg (· * value) ha.symm
        _ = scale*(value*d) := by ac_rfl
        _ = _ := congrArg (scale * ·) ht
    have sy : ∀ i, 0 < coord y i := by
      intro i
      by_cases h : i = j
      · simpa [coord,y,assign,h] using vp
      · simpa [coord,y,assign,h] using Nat.mul_pos sf (pos i)
    have by' : ∀ i, coord y i ≤ growth r*b := by
      intro i
      by_cases h : i = j
      · simpa [coord,y,assign,h] using Nat.le_trans (Nat.div_le_self target d) upper
      · simpa [coord,y,assign,h] using Nat.mul_le_mul (Nat.le_trans (Nat.div_le_self a d) ba) (bound i)
    have ys : y.all (· < 2^128) = true := by
      apply Vector.all_eq_true.mpr
      intro i hi
      exact decide_eq_true (Nat.lt_of_le_of_lt (by' ⟨i,hi⟩) fits)
    have adjustOk : adjust r x = some y := by
      have miss : ¬ dot r.pos (fun i => x[i]) = dot r.neg (fun i => x[i]) := equal
      have pair : (if r.neg j = 0 then (dot r.neg (coord x),dot r.pos (coord x))
            else (dot r.pos (coord x),dot r.neg (coord x))) = (target,a*x[j]) := by
        have sp := share (coord x)
        by_cases z : r.neg j = 0
        · simpa only [z,ite_true,side,target,opp,opposite,Prod.mk.injEq,true_and] using
            (show dot (side r j) (coord x) = a*x[j] from sp)
        · simpa only [z,ite_false,side,target,opp,opposite,Prod.mk.injEq,true_and] using
            (show dot (side r j) (coord x) = a*x[j] from sp)
      have pick : (List.finRange n).find? (fun i => 0 < r.pos i || 0 < r.neg i) = some j := picked
      unfold adjust
      simp only [miss,ite_false,pick,Option.bind_eq_bind,Option.bind_some]
      unfold coord at pair
      simp only [pair]
      simp only [a]
      simp only [Nat.add_sub_cancel_right]
      change (do guard (0 < target); guard (y.all (· < 2^128)); pure y) = some y
      simp [ot,ys,guard]
    refine ⟨y,adjustOk,?_,sy,by'⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | member
    · apply (flip (coord y)).mpr
      rw [share,scale_untouched _ _ _ _ _ os]
      simpa [coord,y,assign] using mul
    · obtain ⟨p,q⟩ := untouched t member
      unfold Row.Holds
      rw [scale_untouched _ _ _ _ _ p,scale_untouched _ _ _ _ _ q,holds t member]

private theorem grow_le (r : Row n) (b : Nat) : b ≤ growth r*b := by
  simpa only [growth,Nat.one_mul] using Nat.mul_le_mul_right b (Nat.le_max_left 1 (total r.pos+total r.neg))

private theorem fold_positive (out : List (Row n)) (tri : Triangular out)
    (fits : (out.map growth).prod < 2^128) :
    ∃ y, out.foldrM adjust (Vector.replicate n 1) = some y ∧
       SystemHolds out (coord y) ∧ (∀ i, 0 < coord y i) ∧ ∀ i, coord y i ≤ (out.map growth).prod := by
  induction out with
  | nil => exact ⟨_,rfl,by simp [SystemHolds],by simp [coord],by simp [coord]⟩
  | cons r ts ih =>
    simp only [List.map_cons,List.prod_cons] at fits ⊢
    obtain ⟨tail,scope⟩ := tri
    obtain ⟨x,run,holds,pos,bound⟩ := ih tail (Nat.lt_of_le_of_lt (grow_le _ _) fits)
    simp only [List.foldrM_cons,run,Option.bind_eq_bind,Option.bind_some]
    cases pick : first r with
    | some j =>
      rw [pick] at scope
      exact row_step r ts j x pick scope.1 scope.2.1 scope.2.2 pos bound fits holds
    | none =>
      have zero (i : Fin n) : r.pos i = 0 ∧ r.neg i = 0 := by
        have falseAt := List.find?_eq_none.mp pick i (List.mem_finRange i)
        simp at falseAt
        omega
      have eq : r.Holds (coord x) := by
        unfold Row.Holds
        rw [show r.pos = r.neg from funext fun i => (zero i).1.trans (zero i).2.symm]
      have same : dot r.pos (fun i => x[i]) = dot r.neg (fun i => x[i]) := eq
      exact ⟨x,by simp only [adjust,same,ite_true]; rfl,by
        simpa [SystemHolds] using And.intro eq holds,pos,fun i => Nat.le_trans (bound i) (grow_le _ _)⟩

/-- For every admitted input the trial completes and gives a strictly
positive 128-bit assignment satisfying all original equations. -/
theorem trial (rs : List (Row n)) (h : Within rs) :
    let out := RowReduction.Reference.output rs.length rs
    ∃ y, out.foldrM adjust (Vector.replicate n 1) = some y ∧
      SystemHolds rs (fun i => y[i]) ∧ ∀ i : Fin n, 0 < y[i] ∧ y[i] < 2^128 := by
  obtain ⟨_,safe,tri,fits⟩ := h
  obtain ⟨y,run,balanced,pos,bound⟩ := fold_positive _ tri fits
  exact ⟨y,run,(RowReduction.echelon_iff _ _ _ (RowReduction.Reference.echelon_eq _ _ safe) _).mp balanced,
    fun i => ⟨pos i,Nat.lt_of_le_of_lt (bound i) fits⟩⟩

theorem completes (rs : List (Row n)) (h : Within rs) : reducedFeasible rs = some true := by
  obtain ⟨y,run,holds,pos⟩ := trial rs h
  have done := RowReduction.Reference.echelon_eq _ _ h.2.1
  have verified := (positiveCertificate_iff rs y).mpr ⟨fun i => (pos i).1,holds⟩
  cases quick : direct (RowReduction.Reference.output rs.length rs) with
  | none => simp [reducedFeasible,h.1,guard,done,quick,run,verified]
  | some b =>
    have answer := (direct_sound _ b quick).mpr
      ⟨_,(RowReduction.echelon_iff _ _ _ done _).mpr holds,fun i => (pos i).1⟩
    simp [reducedFeasible,h.1,guard,done,quick,answer]

section

-- All 48 columns take part. Neither of these constraints can be solved using
-- the other's first-row witness or the all-ones assignment.
private def link : Row 48 where
  pos i := if i = 0 then 2 else 0
  neg i := if i = 1 then 3 else 0
  disjoint i := by by_cases h : i = 0 <;> simp [h]

private def fan : Row 48 where
  pos i := if i.val ≥ 2 then 1 else 0
  neg i := if i = 1 then 5 else 0
  disjoint i := by by_cases h : i = 1 <;> simp [h]

theorem wide_positive :
    let rs := [link, fan]
    Within rs ∧ direct (RowReduction.Reference.output rs.length rs) = none ∧
      reducedFeasible rs = some true := by
  let rs := [link,fan]
  have p : RowReduction.Reference.pivot link = some 0 := by decide
  have q : RowReduction.Reference.pivot fan = some 1 := by decide
  have unchanged : RowReduction.Reference.signed fan 0 = 0 := by decide
  have out : RowReduction.Reference.output rs.length rs = rs := by
    simp [rs,RowReduction.Reference.output,p,q,RowReduction.Reference.step,unchanged]
  have safe : RowReduction.Reference.coefficientsFit rs.length rs := by
    simp [rs,RowReduction.Reference.coefficientsFit,p,q,RowReduction.Reference.step,unchanged]
  have admissible : Within rs := by
    refine ⟨by decide,safe,?_,?_⟩ <;> rw [out]
    · have p' : first link = some 0 := by decide
      have q' : first fan = some 1 := by decide
      simp only [rs,Triangular,p',q',List.mem_cons,List.not_mem_nil,or_false,forall_eq,
        forall_false,implies_true,true_and,and_true]
      refine ⟨⟨?_,⟨2,by decide⟩⟩,?_,⟨1,by decide⟩,?_,?_⟩
      · funext i; decide +revert
      · funext i; decide +revert
      all_goals decide
    · decide
  exact ⟨admissible,by rw [out]; decide,completes rs admissible⟩

end
end Tamarin.ACFeasibility.Adjustment
