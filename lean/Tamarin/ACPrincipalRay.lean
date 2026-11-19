import TamarinRuntime.ACPrincipalRay
import Tamarin.ACAdjustmentCoverage
import Tamarin.ACNeutralBasis
import Tamarin.ACRationalProjection

namespace Tamarin.ACBasis.PrincipalRay
open ACFeasibility
variable {n : Nat}

def gcdOf (x : Vec n) : Nat := (List.ofFn x).foldr Nat.gcd 0

private theorem gcd_map {α} (xs : List α) (f : α → Nat) (s : Nat) :
    (xs.map (fun a => s*f a)).foldr Nat.gcd 0 = s * (xs.map f).foldr Nat.gcd 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.foldr_cons,ih,Nat.gcd_mul_left]

private theorem gcd_scale (s : Nat) (x : Vec n) : gcdOf (fun i => s*x i) = s*gcdOf x := by
  simpa [List.finRange,List.map_ofFn,Function.comp_def,gcdOf] using gcd_map (List.finRange n) x s

/-- Exact arithmetic of a primitive ray: clearing a nonzero common
denominator cannot create extra integral directions. The scalar is the gcd
of the integer solution, even when the primitive vector contains no ones. -/
theorem primitive_multiple {x y : Vec n} (primitive : gcdOf x = 1)
    {d t : Nat} (nz : 0 < d) (proportional : ∀ i, d*y i = t*x i) :
    ∀ i, y i = gcdOf y * x i := by
  have same := congrArg gcdOf (funext proportional)
  rw [gcd_scale,gcd_scale,primitive,Nat.mul_one] at same
  intro i
  apply Nat.eq_of_mul_eq_mul_left nz
  rw [proportional i,←same,Nat.mul_assoc]

/-- A positive primitive solution spanning the nonnegative kernel is the
entire ordered Hilbert basis, not just one member or a redundant generator. -/
theorem basis_of_principal {rows : List (Row n)} {x : Vec n} (root : Fin n)
    (positive : ∀ i, 0 < x i) (primitive : gcdOf x = 1) (sol : SystemHolds rows x)
    (ray : ∀ y, SystemHolds rows y → ∃ d t : Nat, 0 < d ∧ ∀ i, d*y i = t*x i) :
    generate rows = [x] := by
  have factor y (h : SystemHolds rows y) : ∀ i, y i = gcdOf y * x i := by
    obtain ⟨d,t,hn,eq⟩ := ray y h
    exact primitive_multiple primitive hn eq
  have mem : x ∈ generate rows := by
    apply (mem_generate ..).mpr
    refine ⟨sol,⟨root,positive root⟩,?_⟩
    intro y hy live le
    obtain ⟨i,hi⟩ := live
    have gpos := Nat.pos_of_mul_pos_right ((factor y hy i) ▸ hi)
    have atRoot := le root
    rw [factor y hy root] at atRoot
    have one : gcdOf y = 1 := by
      have := (Nat.le_of_mul_le_mul_right (c := x root) (by simpa using atRoot) (positive root) : gcdOf y ≤ 1)
      omega
    funext j
    rw [factor y hy j,one,Nat.one_mul]
  have all y (hy : y ∈ generate rows) : y = x := by
    obtain ⟨holds,⟨i,hi⟩,minimal⟩ := (mem_generate ..).mp hy
    have pos := Nat.pos_of_mul_pos_right ((factor y holds i) ▸ hi)
    have le j : x j ≤ y j := by
      rw [factor y holds j]
      simpa using Nat.mul_le_mul_right (x j) pos
    exact (minimal x sol ⟨root,positive root⟩ le).symm
  have nd := generate_distinct rows
  generalize generate rows = gs at mem all nd ⊢
  cases gs with
  | nil => contradiction
  | cons y ys =>
    obtain rfl := all y List.mem_cons_self
    cases ys with
    | nil => rfl
    | cons z zs =>
      have same := all z (List.mem_cons_of_mem _ List.mem_cons_self)
      exact False.elim ((List.nodup_cons.mp nd).1 (same ▸ List.mem_cons_self))

/-- The first nonzero signed coefficient of an equation, independent of the
candidate's pivot search. -/
def Leading (r : Row n) (i : Fin n) : Prop :=
  r.pos i ≠ r.neg i ∧ ∀ j < i, r.pos j = r.neg j

private theorem leading_iff (r : Row n) (i : Fin n) : leading r = some i ↔ Leading r i := by
  rw [leading,List.find?_eq_some_iff_getElem]
  simp only [bne_iff_ne,List.length_finRange,List.getElem_finRange,Bool.not_eq_true',
    bne_eq_false_iff_eq]
  constructor
  · rintro ⟨nonzero,k,bound,rfl,smaller⟩
    exact ⟨nonzero,fun j hj => smaller j.val hj⟩
  · rintro ⟨nonzero,smaller⟩
    exact ⟨nonzero,i.val,i.isLt,rfl,fun j hj => smaller ⟨j,by omega⟩ hj⟩

/-- The signed row equations determine every coordinate from this one:
every other column is the first nonzero coefficient of some equation. -/
def Anchor (rows : List (Row n)) (root : Fin n) : Prop :=
  ∀ i, i = root ↔ ¬ ∃ r ∈ rows, Leading r i

private theorem free_mem (rows : List (Row n)) (i : Fin n) :
    i ∈ freeColumns rows ↔ ¬ ∃ r ∈ rows, Leading r i := by
  simp [freeColumns,List.mem_filterMap,leading_iff]

private theorem one_free (rows : List (Row n)) : (freeColumns rows).length = 1 ↔ ∃ root, Anchor rows root := by
  constructor
  · intro size
    obtain ⟨root,h⟩ := List.length_eq_one_iff.mp size
    exact ⟨root,fun i => by rw [←free_mem,h]; simp⟩
  · rintro ⟨root,prop⟩
    have mem := (free_mem rows root).mpr ((prop root).mp rfl)
    have all i (h : i ∈ freeColumns rows) := (prop i).mpr ((free_mem ..).mp h)
    have nd : (freeColumns rows).Nodup := (List.nodup_finRange n).filter _
    generalize freeColumns rows = free at mem all nd ⊢
    cases free with
    | nil => contradiction
    | cons a tail =>
      have eq := all a List.mem_cons_self
      cases tail with
      | nil => rfl
      | cons b bs =>
        have same := (all b (List.mem_cons_of_mem _ List.mem_cons_self)).trans eq.symm
        exact False.elim ((List.nodup_cons.mp nd).1 (same ▸ List.mem_cons_self))

private theorem scale_holds {r : Row n} {x : Vec n} (d : Nat) (h : r.Holds x) :
    r.Holds (Cone.scale d x) := by
  unfold Row.Holds
  rw [Cone.dot_scale,Cone.dot_scale,h]

private theorem exchange (a u v : Vec n) (i : Fin n) (same : ∀ j, j ≠ i → a j ≠ 0 → u j = v j) :
    dot a u + a i * v i = dot a v + a i * u i := by
  rw [←dot_spike a i (v i),←dot_spike a i (u i)]
  simp only [dot,←total_add]
  apply congrArg total
  funext j
  by_cases here : j = i
  · subst j; simp [spike,Nat.add_comm]
  · by_cases zero : a j = 0 <;> simp_all [spike]

private theorem forced (rows : List (Row n)) (root : Fin n) (anchor : Anchor rows root) (u v : Vec n)
    (hu : SystemHolds rows u) (hv : SystemHolds rows v) (free : u root = v root) (i : Fin n) : u i = v i := by
  by_cases same : i = root
  · exact same ▸ free
  · obtain ⟨r,hr,nz,prior⟩ := Classical.not_not.mp (fun none => same ((anchor i).mpr none))
    have others (j : Fin n) (diff : j ≠ i) (live : r.pos j ≠ 0 ∨ r.neg j ≠ 0) : u j = v j := by
      by_cases lt : j < i
      · have equal := prior j lt
        have disj := r.disjoint j
        omega
      · have after : i < j := by omega
        exact forced rows root anchor u v hu hv free j
    have left := exchange r.pos u v i (fun j hj live => others j hj (.inl live))
    have right := exchange r.neg u v i (fun j hj live => others j hj (.inr live))
    rw [show dot r.pos u = dot r.neg u from hu r hr,show dot r.pos v = dot r.neg v from hv r hr] at left
    rcases r.disjoint i with noPos|noNeg
    · rw [noPos] at left
      simp only [Nat.zero_mul,Nat.add_zero] at left
      rw [left,Nat.add_left_cancel_iff] at right
      exact ((Nat.mul_right_inj (by omega : r.neg i ≠ 0)).mp right).symm
    · rw [noNeg] at right
      simp only [Nat.zero_mul,Nat.add_zero] at right
      rw [right,Nat.add_left_cancel_iff] at left
      exact ((Nat.mul_right_inj (by omega : r.pos i ≠ 0)).mp left).symm
termination_by n - i.val
decreasing_by omega

private theorem anchored_proportional (rows : List (Row n)) (root : Fin n) (anchor : Anchor rows root)
    (x y : Vec n) (hx : SystemHolds rows x) (hy : SystemHolds rows y) (i : Fin n) :
    x root*y i = y root*x i :=
  forced rows root anchor (Cone.scale (x root) y) (Cone.scale (y root) x)
    (fun r hr => scale_holds _ (hy r hr)) (fun r hr => scale_holds _ (hx r hr)) (Nat.mul_comm ..) i

private theorem coord_list (v : Vector Nat n) : List.ofFn (fun i : Fin n => v[i]) = v.toList := by
  apply List.ext_getElem <;> simp

private def Certified (rows : List (Row n)) (v : Vector Nat n) : Prop :=
  ∃ root : Fin n, (∀ i : Fin n, 0 < v[i]) ∧ gcdOf (fun i : Fin n => v[i]) = 1 ∧ SystemHolds rows (fun i => v[i]) ∧
    ∀ y, SystemHolds rows y → ∀ i : Fin n, v[root]*y i = y root*v[i]

private theorem check_certified {rows : List (Row n)} {v : Vector Nat n} (h : check rows = some v) :
    Certified rows v := by
  unfold check at h
  by_cases free : (freeColumns rows).length = 1
  · cases t : rows.foldrM adjust (Vector.replicate n 1) with
    | none => simp [free,t,guard] at h
    | some trial =>
      let ray := RationalProjection.primitive (fun i : Fin n => trial[i])
      simp only [free,t,guard,↓reduceIte,pure,Option.bind_eq_bind,Option.bind_some] at h
      change (if positiveCertificate rows ray && ray.toList.foldr Nat.gcd 0 == 1 then some ray else none) = some v at h
      split at h
      · rename_i verified
        obtain rfl := Option.some.inj h
        obtain ⟨good,gcd⟩ := Bool.and_eq_true_iff.mp verified
        obtain ⟨root,anchor⟩ := (one_free rows).mp free
        obtain ⟨pos,balanced⟩ := (positiveCertificate_iff ..).mp good
        exact ⟨root,pos,by simpa only [gcdOf,coord_list] using (eq_of_beq gcd),balanced,
          fun y hy => anchored_proportional rows root anchor _ y balanced hy⟩
      · contradiction
  · simp [free,guard,failure] at h

private theorem run_certified {rs : List (Row n)} {v : Vector Nat n} (h : run rs = some v) : Certified rs v := by
  unfold run at h
  by_cases room : n > 0 ∧ n*max 1 rs.length*max 1 rs.length ≤ 524288
  · cases direct : check rs with
    | some found =>
      obtain rfl : found = v := by simpa [room,guard,direct] using h
      exact check_certified direct
    | none =>
      obtain ⟨out,red,got⟩ := Option.bind_eq_some_iff.mp (show (RowReduction.echelon rs.length rs >>= check) = some v by
        simpa [room,guard,direct] using h)
      obtain ⟨root,pos,gcd,sol,unique⟩ := check_certified got
      exact ⟨root,pos,gcd,(RowReduction.echelon_iff _ _ _ red _).mp sol,fun y hy =>
        unique y ((RowReduction.echelon_iff _ _ _ red _).mpr hy)⟩
  · simp [room,guard,failure] at h

theorem run_sound {rs : List (Row n)} {ray : Vector Nat n} (got : run rs = some ray) :
    generate rs = [fun i => ray[i]] ∧ ∀ i : Fin n, 0 < ray[i] := by
  obtain ⟨root,pos,gcd,sol,unique⟩ := run_certified got
  exact ⟨basis_of_principal root pos gcd sol (fun y hy => ⟨_,_,pos root,unique y hy⟩),pos⟩

theorem multiples_of_run {rs : List (Row n)} {ray : Vector Nat n} (got : run rs = some ray)
    (y : Vec n) (hy : SystemHolds rs y) : ∀ i : Fin n, y i = gcdOf y * ray[i] := by
  obtain ⟨root,pos,gcd,_,unique⟩ := run_certified got
  exact primitive_multiple gcd (pos root) (unique y hy)

private theorem divisor {xs : List Nat} {u : Nat} (mem : u ∈ xs) : xs.foldr Nat.gcd 0 ∣ u := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    rcases List.mem_cons.mp mem with rfl | m
    · exact Nat.gcd_dvd_left ..
    · exact Nat.dvd_trans (Nat.gcd_dvd_right ..) (ih m)

private theorem normalized {rows : List (Row n)} (j : Fin n) (x : Vec n) (sol : SystemHolds rows x)
    (positive : ∀ i, 0 < x i) :
    let v := RationalProjection.primitive x
    positiveCertificate rows v = true ∧ v.toList.foldr Nat.gcd 0 = 1 := by
  let d := gcdOf x
  have dvd i : d ∣ x i := divisor (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have nz : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro z
    have := dvd j
    rw [z,Nat.zero_dvd] at this
    have := positive j
    omega
  let v := RationalProjection.primitive x
  let y : Vec n := fun i => v[i]
  have scale : Cone.scale d y = x := by
    funext i
    change d * (RationalProjection.primitive x)[i] = x i
    change d * (if max 1 ((Vector.ofFn x).toList.foldr Nat.gcd 0) == 1 then Vector.ofFn x else
      (Vector.ofFn x).map (· / max 1 ((Vector.ofFn x).toList.foldr Nat.gcd 0)))[i] = x i
    rw [show (Vector.ofFn x).toList.foldr Nat.gcd 0 = d by simp only [Vector.toList_ofFn,d,gcdOf],Nat.max_eq_right nz]
    simp only [beq_iff_eq]
    split
    · rename_i one; simp [one]
    · simpa using
        (Nat.mul_comm ..).trans (Nat.div_mul_cancel (dvd i))
  have gcd : d*gcdOf y = d := by rw [←gcd_scale]; exact congrArg gcdOf scale
  have one : gcdOf y = 1 := Nat.mul_left_cancel nz (by simpa using gcd)
  refine ⟨(positiveCertificate_iff ..).mpr ⟨?_,?_⟩,by simpa only [gcdOf,coord_list,y] using one⟩
  · intro i
    have pos := positive i
    rw [←scale] at pos
    exact Nat.pos_of_mul_pos_left pos
  · intro r hr
    have h := sol r hr
    rw [←scale] at h
    unfold Row.Holds at h
    rw [Cone.dot_scale,Cone.dot_scale] at h
    exact Nat.mul_left_cancel nz h

/-- The ordinary arithmetic echelon can back-solve a bounded positive vector
and every column other than one is the leading entry in a reduced equation.
No test performed by the principal-ray candidate appears in this floor. -/
def Within (rows : List (Row n)) : Prop :=
  n * max 1 rows.length * max 1 rows.length ≤ 524288 ∧ Adjustment.Within rows ∧
    ∃ root : Fin n, Anchor (RowReduction.Reference.output rows.length rows) root

theorem run_complete (rs : List (Row n)) (within : Within rs) : (run rs).isSome := by
  obtain ⟨budget,adjustable,root,anchor⟩ := within
  let out := RowReduction.Reference.output rs.length rs
  have reduction : RowReduction.echelon rs.length rs = some out :=
    RowReduction.Reference.echelon_eq _ _ adjustable.2.1
  obtain ⟨trial,got,sol,pos⟩ := Adjustment.trial rs adjustable
  change out.foldrM adjust (Vector.replicate n 1) = some trial at got
  have free := (one_free out).mpr ⟨root,anchor⟩
  have verified := normalized root (fun i : Fin n => trial[i]) ((RowReduction.echelon_iff _ _ _ reduction _).mpr sol)
    (fun i => (pos i).1)
  have completed : (check out).isSome := by
    have norm := verified.1
    have gcd := verified.2
    simp only [check,free,guard,↓reduceIte,pure,Option.bind_eq_bind,Option.bind_some,got,norm,gcd,
      beq_self_eq_true,Bool.and_self,Option.isSome_some]
  have room : 0 < n ∧ n * max 1 rs.length * max 1 rs.length ≤ 524288 := ⟨by have := root.isLt; omega,budget⟩
  cases direct : check rs <;> simp [run,room,guard,direct,reduction,completed]

section
private def star (width : Nat) (flip : Bool) : List (Row width) :=
  (List.range (width-1)).map fun t =>
    let p : Vec width := fun i => if i.val = t+1 then 2 else 0
    let q : Vec width := fun i => if i.val = 0 then 3 else 0
    if flip && t%2 == 0 then Row.ofWeights q p else Row.ofWeights p q

-- A complete single MGU for the public 36-variable family: even its
-- primitive vector has no unit coordinate.
#guard [false,true].all fun flip =>
  let rs := star 36 flip
  let expected : Vector Nat 36 := Vector.ofFn fun i => if i.val = 0 then 2 else 3
  run rs == some expected && run rs.reverse == some expected
-- Omitting one equation leaves an extra free variable, and appending
-- an inconsistent ratio prevents any positive solution.
#guard (run ((star 36 false).drop 1)).isNone
#guard (run (star 36 true ++ [Row.ofWeights (fun i => if i.val = 1 then 1 else 0)
  (fun i => if i.val = 0 then 4 else 0)])).isNone
#guard run (n := 1) [] == some #v[1]
#guard (run (n := 2) []).isNone
#guard (run (n := 0) []).isNone

-- The first row genuinely uses three terms, so its pivot is forced by
-- an entire tail of known ratios, not by a pairwise ratio shortcut.
private def row₃ (a b c : Nat) (u v w : Nat) : Row 3 :=
  Row.ofWeights (fun i => #v[a,b,c][i]) (fun i => #v[u,v,w][i])

#guard run [row₃ 2 0 0 0 1 1, row₃ 0 2 0 0 0 3] == some #v[5,6,4]
#guard (run [row₃ 1 2 0 0 0 0,row₃ 0 1 0 0 0 1]).isNone
end

end Tamarin.ACBasis.PrincipalRay
