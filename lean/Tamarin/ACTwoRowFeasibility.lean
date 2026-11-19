import Tamarin.ACPositivePullback
import TamarinRuntime.ACTwoRowFeasibility

namespace Tamarin.ACFeasibility.TwoRow
open ACBasis

private def Encloses (r : Option Bounds) (P : Rat → Prop) : Prop :=
  match r with
  | none => ∀ x, ¬ P x
  | some b => P b.lo ∧ P b.hi ∧ ∀ x, P x → b.lo ≤ x ∧ x ≤ b.hi

private theorem encloses_insert {r P} (h : Encloses r P) (x : Rat) :
    Encloses (extend r x) (fun a => x = a ∨ P a) := by
  cases r with
  | none =>
    change ∀ y, ¬P y at h
    refine ⟨.inl rfl,.inl rfl,?_⟩
    rintro y (rfl | py)
    · exact ⟨Rat.le_refl,Rat.le_refl⟩
    · exact False.elim (h _ py)
  | some b =>
    obtain ⟨hl,hh,bounds⟩ := h
    refine ⟨?_,?_,?_⟩
    · rcases Std.min_eq_or (a := b.lo) (b := x) with e|e
      · exact .inr (e.symm ▸ hl)
      · exact .inl e.symm
    · rcases Std.max_eq_or (a := b.hi) (b := x) with e|e
      · exact .inr (e.symm ▸ hh)
      · exact .inl e.symm
    · rintro y (rfl | py)
      · exact ⟨Std.min_le_right ..,Std.right_le_max ..⟩
      · exact ⟨Rat.le_trans (Std.min_le_left ..) (bounds _ py).1,
          Rat.le_trans (bounds _ py).2 (Std.left_le_max ..)⟩

private structure Records (s : Scan) (P : Column → Prop) : Prop where
  left : Encloses s.pos (fun x => P (.positive x))
  right : Encloses s.neg (fun x => P (.negative x))
  upward : s.up = true ↔ P .up
  downward : s.down = true ↔ P .down

private theorem records_insert {s P} (h : Records s P) (col : Column) :
    Records (s.insert col) (fun c => col = c ∨ P c) := by
  cases col with
  | positive x => exact ⟨by simpa [Scan.insert] using encloses_insert h.left x,
      by simpa [Scan.insert] using h.right,by simpa [Scan.insert] using h.upward,
      by simpa [Scan.insert] using h.downward⟩
  | negative x => exact ⟨by simpa [Scan.insert] using h.left,
      by simpa [Scan.insert] using encloses_insert h.right x, by simpa [Scan.insert] using h.upward,
      by simpa [Scan.insert] using h.downward⟩
  | up => exact ⟨by simpa [Scan.insert] using h.left,by simpa [Scan.insert] using h.right,
      by simp [Scan.insert],by simpa [Scan.insert] using h.downward⟩
  | down => exact ⟨by simpa [Scan.insert] using h.left,by simpa [Scan.insert] using h.right,
      by simpa [Scan.insert] using h.upward,by simp [Scan.insert]⟩
  | zero => exact ⟨by simpa [Scan.insert] using h.left,by simpa [Scan.insert] using h.right,
      by simpa [Scan.insert] using h.upward,by simpa [Scan.insert] using h.downward⟩

private theorem fold_records {n} (f : Fin n → Column) {s P} (h : Records s P) :
    Records (Fin.foldl n (fun s i => s.insert (f i)) s) (fun c => P c ∨ ∃ i, f i = c) := by
  induction n generalizing s P with
  | zero => simpa using h
  | succ n ih =>
    rw [Fin.foldl_succ]
    have step := ih (fun i => f i.succ) (records_insert h (f 0))
    have eq : (fun c => (f 0 = c ∨ P c) ∨ ∃ i : Fin n, f i.succ = c) =
        (fun c => P c ∨ ∃ i : Fin (n+1), f i = c) := by
      funext c; apply propext; rw [Fin.exists_fin_succ]; grind
    exact eq ▸ step

private theorem span_exists {r P} (h : Encloses r P) : r.isSome = true ↔ ∃ x, P x := by
  cases r with
  | none => change false = true ↔ _; simp [show ∀ x, ¬P x from h]
  | some b => exact iff_of_true rfl ⟨b.lo,h.1⟩

private theorem span_above {p q P Q} (hp : Encloses p P) (hq : Encloses q Q) :
    above p q = true ↔ ∃ a b, P a ∧ Q b ∧ b < a := by
  cases p with
  | none => simp [above,show ∀ x, ¬P x from hp]
  | some l =>
    cases q with
    | none => simp [above,show ∀ x, ¬Q x from hq]
    | some r =>
      simp only [above,decide_eq_true_eq]
      exact ⟨fun h => ⟨l.hi,r.lo,hp.2.1,hq.1,h⟩,fun ⟨a,b,x,y,h⟩ =>
        Std.lt_of_le_of_lt (hq.2.2 _ y).1 (Std.lt_of_lt_of_le h (hp.2.2 _ x).2)⟩

private def Seen {n} (f : Fin n → Column) (c : Column) := ∃ i, f i = c

private theorem scan_iff {n} (p q : Row n) :
    let seen := Seen (classify p q)
    decidePair p q = true ↔
      ((∃ x, seen (.positive x)) ↔ (∃ x, seen (.negative x))) ∧
      ((seen .up ∨ ∃ a b, seen (.positive a) ∧ seen (.negative b) ∧ b < a) ↔
       (seen .down ∨ ∃ b a, seen (.negative b) ∧ seen (.positive a) ∧ a < b)) := by
  let f := classify p q
  let s := Fin.foldl n (fun s i => Scan.insert s (f i)) {}
  have empty : Records {} (fun _ => False) := ⟨by simp [Encloses],by simp [Encloses],by simp,by simp⟩
  have good : Records s (Seen f) := by
    change Records s (fun c => ∃ i, f i = c); simpa [s] using fold_records f empty
  change (s.verdict = true) ↔ _
  have beq (a b : Bool) : (a == b) = true ↔ (a = true ↔ b = true) := by cases a <;> cases b <;> decide
  simp only [Scan.verdict,Bool.and_eq_true_iff,beq,
    Bool.or_eq_true_iff,span_exists good.left,span_exists good.right,span_above good.left good.right,
    span_above good.right good.left,good.upward,good.downward]
  rfl
private def coefficient {n} (q : Row n) (i : Fin n) : Int := (q.pos i : Int) - q.neg i
private def score {n} (q : Row n) (v : Vec n) : Int := (dot q.pos v : Int) - dot q.neg v
private def high {n} (p q : Row n) (i : Fin n) : Rat := (coefficient q i : Rat) / (p.pos i : Rat)
private def low {n} (p q : Row n) (j : Fin n) : Rat := ((-coefficient q j : Int) : Rat) / (p.neg j : Rat)

private theorem frac_lt (a b : Int) (u v : Nat) (hu : 0 < u) (hv : 0 < v) :
    (a : Rat) / (u : Rat) < (b : Rat) / (v : Rat) ↔ a * (v : Int) < b * (u : Int) := by
  have up : 0 < (u : Rat) := Rat.natCast_pos.mpr hu
  have vp : 0 < (v : Rat) := Rat.natCast_pos.mpr hv
  have rearrange (c e d : Rat) : (c / d) * e = (c * e) / d := by
    rw [Rat.div_def,Rat.div_def,Rat.mul_assoc,Rat.mul_assoc,Rat.mul_comm d⁻¹ e]
  rw [Rat.lt_div_iff vp,rearrange,Rat.div_lt_iff up]
  exact_mod_cast Rat.intCast_lt_intCast

private theorem score_pair {n} (p q : Row n) (i j : Fin n) :
    score q (Cone.pair p i j) = coefficient q i * (p.neg j : Int) + coefficient q j * (p.pos i : Int) := by
  have eval (v : Vec n) : dot v (Cone.pair p i j) = v i * p.neg j + v j * p.pos i := by
    unfold Cone.pair dot
    simp only [Nat.mul_add,total_add]
    change dot v (spike i _) + dot v (spike j _) = _
    simp only [dot_spike]
  simp only [score,eval,coefficient,Int.natCast_add,Int.natCast_mul]; grind

private theorem seen_positive {n} (p q : Row n) (x) :
    Seen (classify p q) (.positive x) ↔ ∃ i, 0 < p.pos i ∧ high p q i = x := by
  apply exists_congr; intro i; by_cases a : 0 < p.pos i
  · simp [classify,a,high,coefficient]
  · simp [classify,a]; grind

private theorem seen_negative {n} (p q : Row n) (x) :
    Seen (classify p q) (.negative x) ↔ ∃ i, 0 < p.neg i ∧ low p q i = x := by
  apply exists_congr; intro i; by_cases a : 0 < p.pos i
  · have e := (p.disjoint i).resolve_left (Nat.ne_of_gt a); simp [classify,a,e]
  · by_cases b : 0 < p.neg i
    · simp [classify,a,b,low,coefficient]
    · simp [classify,a,b]; grind

private def wanted (pos : Bool) (v : Int) : Prop := if pos then 0 < v else v < 0

private theorem axis {n} (p q : Row n) (pos : Bool) :
    Seen (classify p q) (if pos then .up else .down) ↔
      ∃ i, p.pos i = 0 ∧ p.neg i = 0 ∧ wanted pos (coefficient q i) := by
  apply exists_congr; intro i
  by_cases a : 0 < p.pos i <;> by_cases b : 0 < p.neg i <;>
    by_cases c : 0 < coefficient q i <;> by_cases d : coefficient q i < 0 <;> cases pos <;>
    simp_all [classify,wanted,coefficient] <;> grind

private def rays {n} (p : Row n) :=
  ((List.finRange n).filter (fun i => p.pos i == 0 && p.neg i == 0)).map (spike · 1) ++
  ((List.finRange n).filter (fun i => 0 < p.pos i)).flatMap fun i =>
    ((List.finRange n).filter (fun j => 0 < p.neg j)).map (Cone.pair p i)

private theorem ray_table {n} (p : Row n) (v : Vec n) : v ∈ rays p ↔ Cone.Ray p v := by
  simp [rays,Cone.Ray]; grind

private def raySign {n} (p q : Row n) (pos : Bool) : Prop :=
  ∃ v, Cone.Ray p v ∧ wanted pos (score q v)

private theorem slopes {n} (p q : Row n) (i j : Fin n) (hi : 0 < p.pos i) (hj : 0 < p.neg j)
    (pos : Bool) :
    (if pos then low p q j < high p q i else high p q i < low p q j) ↔
      wanted pos (score q (Cone.pair p i j)) := by
  rw [score_pair]; cases pos
  · change ((coefficient q i : Rat) / (p.pos i : Rat) < ((-coefficient q j : Int) : Rat) / (p.neg j : Rat)) ↔ _
    rw [frac_lt _ _ _ _ hi hj]; simp only [wanted,Bool.false_eq_true,↓reduceIte,Int.neg_mul]; omega
  · change (((-coefficient q j : Int) : Rat) / (p.neg j : Rat) < (coefficient q i : Rat) / (p.pos i : Rat)) ↔ _
    rw [frac_lt _ _ _ _ hj hi]; simp only [wanted,↓reduceIte,Int.neg_mul]; omega

private theorem signs {n} (p q : Row n) (pos : Bool) :
    raySign p q pos ↔ Seen (classify p q) (if pos then .up else .down) ∨
      ∃ a b, Seen (classify p q) (.positive a) ∧ Seen (classify p q) (.negative b) ∧
        (if pos then b < a else a < b) := by
  rw [axis]; simp only [seen_positive,seen_negative]
  constructor
  · rintro ⟨v,ray,sgn⟩
    rcases ray with ⟨i,hi,hj,rfl⟩|⟨i,j,hi,hj,rfl⟩
    · exact .inl ⟨i,hi,hj,by simpa [score,coefficient,dot_spike] using sgn⟩
    · exact .inr ⟨_,_,⟨i,hi,rfl⟩,⟨j,hj,rfl⟩,(slopes p q i j hi hj pos).mpr sgn⟩
  · rintro (⟨i,hi,hj,w⟩ | ⟨_,_,⟨i,hi,rfl⟩,⟨j,hj,rfl⟩,w⟩)
    · exact ⟨_,.inl ⟨i,hi,hj,rfl⟩,by simpa [score,coefficient,dot_spike] using w⟩
    · exact ⟨_,.inr ⟨i,j,hi,hj,rfl⟩,(slopes p q i j hi hj pos).mp w⟩

private theorem pull_sign {n} (p q : Row n) (pos : Bool) :
    (∃ j, 0 < (if pos then (q.pullback (rays p).get).pos j else (q.pullback (rays p).get).neg j)) ↔
      raySign p q pos := by
  have one j :
      0 < (if pos then (q.pullback (rays p).get).pos j else (q.pullback (rays p).get).neg j) ↔
      wanted pos (score q ((rays p).get j)) := by
    cases pos <;> simp [wanted,score,Row.pullback,Row.ofWeights] <;> omega
  constructor
  · rintro ⟨j,h⟩
    exact ⟨_,(ray_table ..).mp (List.get_mem _ j),(one j).mp h⟩
  · rintro ⟨v,hv,sgn⟩
    obtain ⟨j,rfl⟩ := List.get_of_mem ((ray_table ..).mpr hv)
    exact ⟨j,(one j).mpr sgn⟩

theorem decidePair_iff {n} (p q : Row n) : decidePair p q = true ↔ Feasible [p,q] := by
  have basis := Cone.row_correct p (rays p) (ray_table p)
  have reduce := PositivePullback.feasible_iff [p] [q] (rays p) basis
  have swap : Feasible [q,p] ↔ Feasible [p,q] := by
    have perm : [q,p].Perm [p,q] := List.Perm.swap _ _ _
    constructor
    · rintro ⟨x,h,pos⟩; exact ⟨x,fun r hr => h r (perm.mem_iff.mpr hr),pos⟩
    · rintro ⟨x,h,pos⟩; exact ⟨x,fun r hr => h r (perm.mem_iff.mp hr),pos⟩
  simp only [List.cons_append,List.nil_append,List.map_cons,List.map_nil,PositivePullback.one_iff] at reduce
  have scan := scan_iff p q
  dsimp only at scan
  rw [←swap,reduce,scan]
  have plus := (pull_sign p q true).trans (signs p q true)
  have minus := (pull_sign p q false).trans (signs p q false)
  simp only [↓reduceIte,Bool.false_eq_true] at plus minus
  have image (b : Fin n → Prop) (slope : Fin n → Rat) :
      (∃ a i, b i ∧ slope i = a) ↔ ∃ i, b i :=
    ⟨fun ⟨_,i,h,_⟩ => ⟨i,h⟩,fun ⟨i,h⟩ => ⟨_,i,h,rfl⟩⟩
  have lhs : (∃ a, Seen (classify p q) (.positive a)) ↔ ∃ i, 0 < p.pos i := by
    simp only [seen_positive]; exact image _ _
  have rhs : (∃ a, Seen (classify p q) (.negative a)) ↔ ∃ i, 0 < p.neg i := by
    simp only [seen_negative]; exact image _ _
  rw [lhs,rhs]
  grind

end Tamarin.ACFeasibility.TwoRow
