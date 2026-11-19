import Tamarin.ACRowReduction
import Tamarin.ACDirectFeasibility

/-! Fixed arithmetic reference for mandatory completion of the reversible
row reducer. It uses signed coefficients, a least-index pivot, and exact
primitive normalization. Intermediate coefficient limits apply to rows that
are updated. No verdict or success flag from a candidate defines this domain. -/
namespace Tamarin.ACBasis.RowReduction
variable {n : Nat}

namespace Reference

def signed (r : Row n) (i : Fin n) : Int := (r.pos i : Int) - r.neg i

def pivot (r : Row n) : Option (Fin n) :=
  ((List.finRange n).filter (fun i => signed r i != 0)).head?

private def magnitude (r : Row n) (j : Fin n) := r.pos j + r.neg j

private def directed (r : Row n) (j i : Fin n) : Int :=
  if signed r j < 0 then -signed r i else signed r i

private def primitive (v : Fin n → Int) : Row n :=
  let p := fun i => (v i).toNat
  let q := fun i => (-(v i)).toNat
  let gcd := max 1 ((List.ofFn p ++ List.ofFn q).foldr Nat.gcd 0)
  { pos := fun i => p i / gcd, neg := fun i => q i / gcd
    disjoint := fun i => by
      by_cases h : v i ≤ 0
      · exact .inl (by simp [p,Int.toNat_eq_zero.mpr h])
      · exact .inr (by simp [q,Int.toNat_eq_zero.mpr (by omega : -(v i) ≤ 0)]) }

/-- Cross multiply row coefficients over the integers, with both selected
pivot entries oriented positively. An untouched row retains its previous scale. -/
def step (p t : Row n) (j : Fin n) : Row n :=
  if signed t j = 0 then t else
    primitive fun i => (magnitude p j : Int) * directed t j i - (magnitude t j : Int) * directed p j i

def output : Nat → List (Row n) → List (Row n)
  | 0, rs => rs
  | _+1, [] => []
  | k+1, p::ts => p :: output k (match pivot p with | none => ts | some j => ts.map (step p · j))

def coefficientsFit : Nat → List (Row n) → Prop
  | 0, _ | _+1, [] => True
  | k+1, p::ts => match pivot p with
    | none => coefficientsFit k ts
    | some j =>
      (∀ t ∈ ts, signed t j ≠ 0 → ∀ i, (step p t j).pos i < 2^128 ∧ (step p t j).neg i < 2^128) ∧
      coefficientsFit k (ts.map (step p · j))

private theorem signed_zero (r : Row n) (j : Fin n) : signed r j = 0 ↔ r.pos j = 0 ∧ r.neg j = 0 := by
  have := r.disjoint j
  unfold signed
  omega

private theorem pivot_eq (p : Row n) :
    pivot p = (List.finRange n).find? (fun i => 0 < p.pos i || 0 < p.neg i) := by
  unfold pivot
  rw [List.head?_filter]
  apply congrArg (fun pred => (List.finRange n).find? pred)
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [signed_zero]; omega

private theorem magnitude_eq (p : Row n) (j : Fin n) : magnitude p j = (orient p j).pos j := by
  unfold magnitude orient
  split <;> have := p.disjoint j <;> try dsimp only
  all_goals omega

private theorem directed_eq (p : Row n) (j i : Fin n) :
    directed p j i = signed (orient p j) i := by
  unfold directed orient signed
  have := p.disjoint j
  split <;> split <;> simp_all <;> omega

private theorem primitive_eq (a b : Vec n) :
    primitive (fun i => (a i : Int) - b i) = (Row.ofWeights a b).primitive := by
  simp only [primitive,Row.primitive,Row.divisor,Row.ofWeights,Int.neg_sub,Int.toNat_sub]

private theorem step_eq (p t : Row n) (j : Fin n) (piv : signed p j ≠ 0) (touch : signed t j ≠ 0) :
    step p t j = (cancel p t j).primitive := by
  have nz (r : Row n) (h : signed r j ≠ 0) : (orient r j).pos j ≠ 0 := by
    rw [←magnitude_eq]; unfold magnitude; have e := signed_zero r j; omega
  let a := orient p j
  let b := orient t j
  let u := a.pos j
  let v := b.pos j
  have cross (i) : (magnitude p j : Int) * directed t j i - (magnitude t j : Int) * directed p j i =
      ((u * b.pos i + v * a.neg i : Nat) : Int) - ((u * b.neg i + v * a.pos i : Nat) : Int) := by
    simp only [magnitude_eq,directed_eq,signed,Int.natCast_add,Int.natCast_mul,u,v,a,b]
    grind
  unfold step cancel
  rw [ite_eq_right touch,ite_eq_right (not_or_intro (nz p piv) (nz t touch)),funext cross]
  exact primitive_eq ..

private theorem stored_id (r : Row n) : stored r = r := by cases r; simp [stored]

private theorem cap_small (r : Row n) (bounded : ∀ i, r.pos i < 2^128 ∧ r.neg i < 2^128) :
    r.cap < 2^128 := by
  have member : r.cap ∈ 1 :: (List.ofFn r.pos ++ List.ofFn r.neg) := List.max_mem (by simp)
  simp only [List.mem_cons,List.mem_append,List.mem_ofFn] at member
  rcases member with he | ⟨i,he⟩ | ⟨i,he⟩
  · rw [he]; decide
  · rw [←he]; exact (bounded i).1
  · rw [←he]; exact (bounded i).2

private theorem step_run (p t : Row n) (j : Fin n) (piv : signed p j ≠ 0)
    (bounds : signed t j ≠ 0 → ∀ i, (step p t j).pos i < 2^128 ∧ (step p t j).neg i < 2^128) :
    reduceAt p j t = some (step p t j) := by
  by_cases z : signed t j = 0
  · obtain ⟨zp,zn⟩ := (signed_zero ..).mp z
    simp [reduceAt,zp,zn,step,z]
  · have active : ¬ (t.pos j = 0 ∧ t.neg j = 0) := fun both => z ((signed_zero t j).mpr both)
    have small := cap_small _ (bounds z)
    rw [step_eq p t j piv z] at small ⊢
    simp [reduceAt,stored_id,small,guard]; exact fun a b => False.elim (active ⟨a,b⟩)

private theorem map_steps (p : Row n) (j : Fin n) (piv : signed p j ≠ 0) (ts : List (Row n))
    (bounds : ∀ t ∈ ts, signed t j ≠ 0 → ∀ i, (step p t j).pos i < 2^128 ∧ (step p t j).neg i < 2^128) :
    ts.mapM (reduceAt p j) = some (ts.map (step p · j)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [step_run p t j piv (bounds t List.mem_cons_self),
      ih (fun a h => bounds a (List.mem_cons_of_mem t h))]

theorem echelon_eq (k : Nat) (rs : List (Row n)) (safe : coefficientsFit k rs) :
    echelon k rs = some (output k rs) := by
  induction k generalizing rs with
  | zero => rfl
  | succ k ih =>
    cases rs with
    | nil => rfl
    | cons p ts =>
      cases e : pivot p with
      | none =>
        simp only [coefficientsFit,e] at safe
        simp [echelon,output,←pivot_eq,e,ih ts safe]
      | some j =>
        have used := List.find?_some ((pivot_eq p).symm.trans e)
        have piv : signed p j ≠ 0 := by simp [signed_zero]; simp at used; omega
        simp only [coefficientsFit,e] at safe
        simp [echelon,output,←pivot_eq,e,map_steps p j piv ts safe.1,ih _ safe.2]

end Reference

def Within (rs : List (Row n)) : Prop :=
  n*rs.length*rs.length ≤ 524288 ∧ Reference.coefficientsFit rs.length rs ∧
    ACFeasibility.DirectWithin (Reference.output rs.length rs)

theorem echelon_complete (rs : List (Row n)) (within : Within rs) :
    ∃ out, echelon rs.length rs = some out ∧ ACFeasibility.DirectWithin out :=
  ⟨_,Reference.echelon_eq _ _ within.2.1,within.2.2⟩

section
-- Both sides of both original equations are live. Cancelling their shared
-- first column leaves the sum of 47 strictly positive coordinates equal to zero.
private def wideRow (a : Nat) : Row 48 where
  pos i := if i = 0 then a else 0
  neg i := if i = 0 then 0 else 1
  disjoint i := by by_cases h : i = 0 <;> simp [h]

private def obstruction : Row 48 where
  pos i := if i = 0 then 0 else 1
  neg _ := 0
  disjoint _ := .inr rfl

private theorem firstPivot : Reference.pivot (wideRow 2) = some 0 := by decide
private theorem reducedWide : Reference.step (wideRow 2) (wideRow 3) 0 = obstruction := by
  have p : ∀ i, (Reference.step (wideRow 2) (wideRow 3) 0).pos i = obstruction.pos i := by decide
  have q : ∀ i, (Reference.step (wideRow 2) (wideRow 3) 0).neg i = obstruction.neg i := by decide
  exact Row.mk.injEq .. |>.mpr ⟨funext p,funext q⟩

/-- A wide common-pivot contradiction is inside the independent work
envelope even though the original rows miss every direct completion floor. -/
theorem wide_refutation :
    let rs := [wideRow 2,wideRow 3]
    Within rs ∧ ¬ ACFeasibility.DirectWithin rs ∧ ¬ ACFeasibility.Feasible rs := by
  let rs := [wideRow 2,wideRow 3]
  have pivot : Reference.pivot obstruction = some 1 := by decide
  have safe : Reference.coefficientsFit rs.length rs := by
    simp [rs,Reference.coefficientsFit,firstPivot,reducedWide,pivot]
    intro i; decide +revert
  have out : Reference.output rs.length rs = [wideRow 2,obstruction] := by
    simp [rs,Reference.output,firstPivot,reducedWide,pivot]
  have noSide : total obstruction.pos = 47 ∧ total obstruction.neg = 0 := by decide
  have direct : ACFeasibility.DirectWithin (Reference.output rs.length rs) := by
    rw [out]
    exact .inr (.inl ⟨obstruction,by simp,fun eq => by
      have h := eq.mpr noSide.2
      omega⟩)
  have blocked : ¬ ACFeasibility.DirectWithin rs := by
    simp [rs,ACFeasibility.DirectWithin]
    decide
  refine ⟨⟨by decide,safe,direct⟩,blocked,?_⟩
  rintro ⟨x,hx,pos⟩
  have eq := Reference.echelon_eq _ _ safe
  rw [out] at eq
  have falseVerdict : ACFeasibility.direct [wideRow 2,obstruction] = some false := by decide
  exact Bool.noConfusion ((ACFeasibility.direct_sound _ _ falseVerdict).mpr
    ⟨x,(echelon_iff _ _ _ eq x).mpr hx,pos⟩)

end
end Tamarin.ACBasis.RowReduction
