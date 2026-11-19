import TamarinRuntime.ACSpanCertificate
import Tamarin.ACSeparation

namespace Tamarin.ACBasis.SpanCertificate
open ACFeasibility
variable {n : Nat}

/-- An integral multiple of the requested row equals a signed combination
of precisely the supplied original rows, column by column. -/
def Valid (rs : List (Row n)) (q : Row n) (c : Certificate) : Prop :=
  c.scale ≠ 0 ∧ c.weights.length = rs.length ∧ ∀ i,
    c.scale * LowRank.coeff q i = Separation.combination (c.weights.zip rs) i

theorem check_iff (rs : List (Row n)) (q : Row n) (c : Certificate) :
    check rs q c = true ↔ Valid rs q c := by
  simp [check,Valid,Separation.column_eq,and_assoc]

theorem run_sound {rs : List (Row n)} {q c} (h : run rs q = some c) : Valid rs q c := by
  simp only [run,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨_,_,v,_,_,ok,eq⟩ := h
  cases eq
  exact (check_iff ..).mp (by simpa [guard] using ok)

def Witness (rs : List (ZRow n)) (q : ZRow n) (c : Certificate) : Prop :=
  c.scale ≠ 0 ∧ c.weights.length = rs.length ∧ ∀ i, c.scale*q[i] = linear c.weights rs i

private theorem linear_original (ws : List Int) (rs : List (Row n)) (i : Fin n) :
    linear ws (rs.map signed) i = Separation.combination (ws.zip rs) i := by
  induction ws generalizing rs with
  | nil => rfl
  | cons w ws ih =>
    cases rs with
    | nil => rfl
    | cons r rs => simp [linear,signed,Separation.combination,LowRank.coeff,ih]

theorem original (rs : List (Row n)) (q : Row n) (c : Certificate) :
    Witness (rs.map signed) (signed q) c ↔ Valid rs q c := by
  simp [Witness,Valid,signed,linear_original]

private theorem scaled (ws : List Int) (rs : List (ZRow n)) (u : Int) (i : Fin n) :
    linear (ws.map (u*·)) rs i = u * linear ws rs i := by
  induction ws generalizing rs with
  | nil => simp [linear]
  | cons w ws ih =>
    cases rs with
    | nil => simp [linear]
    | cons r rs => simp only [List.map_cons,linear,ih]; grind

private theorem eliminated (p : ZRow n) (j : Fin n) (ws : List Int) (rs : List (ZRow n)) (i : Fin n) :
    linear ws (rs.map (eliminate p j)) i = p[j]*linear ws rs i - p[i]*linear ws rs j := by
  induction ws generalizing rs with
  | nil => simp [linear]
  | cons w ws ih =>
    cases rs with
    | nil => simp [linear]
    | cons r rs => simp only [List.map_cons,linear,eliminate,ih]; grind

theorem drop_pivot (p : ZRow n) (j : Fin n) (q : ZRow n) (rs : List (ZRow n))
    {c} (h : Witness (p::rs) q c) :
    ∃ d, Witness (rs.map (eliminate p j)) (eliminate p j q) d := by
  obtain ⟨nz,len,eq⟩ := h
  cases e : c.weights with
  | nil => simp [e] at len
  | cons w ws =>
    refine ⟨⟨c.scale,ws⟩,nz,by simpa [e] using len,?_⟩
    intro i
    have hi := eq i
    have hj := eq j
    simp only [e,linear] at hi hj
    simp only [eliminated,eliminate]
    grind

theorem lift_witness (p : ZRow n) (j : Fin n) (nz : p[j] ≠ 0) (rs : List (ZRow n))
    (q : ZRow n) {c} (h : Witness (rs.map (eliminate p j)) (eliminate p j q) c) :
    Witness (p::rs) q (lift p j rs q c) := by
  obtain ⟨nonzero,len,eq⟩ := h
  refine ⟨Int.mul_ne_zero nonzero nz,by simpa [lift] using len,?_⟩
  intro i
  have hi := eq i
  simp only [eliminated,eliminate] at hi
  simp only [lift,linear,scaled]
  grind

theorem zero_coeffs (rs : List (ZRow n)) (i : Fin n) :
    linear (List.replicate rs.length 0) rs i = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [List.replicate_succ,linear,ih]

theorem no_pivot (p : ZRow n) : pivot p = none ↔ ∀ i : Fin n, p[i] = 0 := by
  simp [pivot,List.find?_eq_none]

/-- A fixed arithmetic work envelope on the input tableau. Each column
available as a pivot is allowed by this specification. Arrays admitted
at one stage must also fit before their entries can be multiplied again. -/
def StageWithin : Nat → List (ZRow n) → ZRow n → Prop
  | k,rs,q =>
    (∀ r ∈ q::rs, ∀ i : Fin n, r[i].natAbs < 2^256) ∧
      match k,rs with
      | k+1,p::ps =>
        ((∀ i : Fin n, p[i] = 0) → StageWithin k ps q) ∧
        ∀ j : Fin n, p[j] ≠ 0 →
          StageWithin k (ps.map fun r => Vector.ofFn (fun i => p[j]*r[i] - r[j]*p[i]))
            (Vector.ofFn fun i => p[j]*q[i] - q[j]*p[i])
      | _,_ => True

def Within (rs : List (Row n)) (q : Row n) : Prop :=
  n ≤ 4096 ∧ rs.length ≤ 64 ∧ (n+1)*(rs.length+1)*(rs.length+1) ≤ 524288 ∧
    StageWithin rs.length (rs.map fun r => Vector.ofFn (LowRank.coeff r)) (Vector.ofFn (LowRank.coeff q))

/-- A simpler sufficient bound in terms of just the input coefficient
maximum and the number of observations. No pivots need to be predicted. -/
def MagnitudesFit : Nat → Nat → Prop
  | 0,b => b < 2^256
  | k+1,b => b < 2^256 ∧ MagnitudesFit k (b + 2*b*b)

/-- Four observations with up to 4,096 occurrences per coefficient always
fit the arithmetic envelope, independent of pivots and row orientation. -/
theorem four_magnitudes (m : Nat) (bound : m ≤ 4) : MagnitudesFit m 4096 := by
  match m with
  | 0 | 1 | 2 | 3 | 4 => simp +decide [MagnitudesFit]
  | _+5 => omega

private theorem uniform_stage (k b : Nat) (rs : List (ZRow n)) (q : ZRow n)
    (small : ∀ r ∈ q::rs, ∀ i : Fin n, r[i].natAbs ≤ b)
    (fit : MagnitudesFit k b) : StageWithin k rs q := by
  induction k generalizing b rs q with
  | zero => exact ⟨fun r hr i => Nat.lt_of_le_of_lt (small r hr i) fit,trivial⟩
  | succ k ih =>
    cases rs with
    | nil => exact ⟨fun r hr i => Nat.lt_of_le_of_lt (small r hr i) fit.1,trivial⟩
    | cons p tail =>
      refine ⟨fun r hr i => Nat.lt_of_le_of_lt (small r hr i) fit.1,?_⟩
      have tall (r : ZRow n) (mem : r ∈ q :: tail) (i : Fin n) : r[i].natAbs ≤ b := by
        rcases List.mem_cons.mp mem with rfl | e
        · exact small _ List.mem_cons_self _
        · exact small _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e)) _
      have point := small p (List.mem_cons_of_mem q List.mem_cons_self)
      have cross (r : ZRow n) (mem : r ∈ q :: tail) (i j : Fin n) :
          (p[j]*r[i] - r[j]*p[i]).natAbs ≤ b + 2*b*b := by
        have z := Int.natAbs_sub_le (p[j]*r[i]) (r[j]*p[i])
        rw [Int.natAbs_mul,Int.natAbs_mul] at z
        have u := Nat.mul_le_mul (point j) (tall r mem i)
        have v := Nat.mul_le_mul (point i) (tall r mem j)
        rw [Nat.mul_comm p[i].natAbs] at v
        rw [Nat.mul_assoc]
        omega
      constructor
      · intro _
        exact ih _ _ _ (fun r hr i => Nat.le_trans (tall r hr i) (Nat.le_add_right ..)) fit.2
      · intro j _
        apply ih _ _ _ _ fit.2
        intro r hr i
        rcases List.mem_cons.mp hr with rfl | rest
        · simpa using cross q List.mem_cons_self i j
        · obtain ⟨a,mem,rfl⟩ := List.mem_map.mp rest
          simpa using cross a (List.mem_cons_of_mem _ mem) i j

theorem within_of_bound (rs : List (Row n)) (q : Row n) (b : Nat)
    (size : n ≤ 4096 ∧ rs.length ≤ 64 ∧ (n+1)*(rs.length+1)*(rs.length+1) ≤ 524288)
    (small : ∀ r ∈ q :: rs, ∀ i, (LowRank.coeff r i).natAbs ≤ b)
    (fit : MagnitudesFit rs.length b) : Within rs q := by
  refine ⟨size.1,size.2.1,size.2.2,uniform_stage _ _ _ _ ?_ fit⟩
  intro r hr i
  rcases List.mem_cons.mp hr with rfl | rest
  · simpa using small q List.mem_cons_self i
  · obtain ⟨a,mem,rfl⟩ := List.mem_map.mp rest
    simpa using small a (List.mem_cons_of_mem _ mem) i

private theorem fits {p : ZRow n} (h : ∀ i : Fin n, p[i].natAbs < 2^256) : bounded p = true := by
  simp only [bounded,Array.all_eq_true]
  intro j hj
  exact decide_eq_true (h ⟨j,by simpa using hj⟩)

private theorem search_complete (k : Nat) (rs : List (ZRow n)) (q : ZRow n)
    (enough : rs.length ≤ k) (safe : StageWithin k rs q) (span : ∃ c, Witness rs q c) :
    ∃ c, search k rs q = some c ∧ Witness rs q c := by
  have current : ∀ r ∈ q::rs, ∀ i : Fin n, r[i].natAbs < 2^256 := by
    cases k <;> cases rs <;> exact safe.1
  have room : (bounded q && rs.all bounded) = true := by
    rw [Bool.and_eq_true]
    exact ⟨fits (current _ List.mem_cons_self),
      List.all_eq_true.mpr (fun r hr => fits (current r (List.mem_cons_of_mem _ hr)))⟩
  cases zero : pivot q with
  | none =>
    refine ⟨⟨1,List.replicate rs.length 0⟩,?_,Int.one_ne_zero,by simp,?_⟩
    · cases k <;> cases rs <;> simp only [search,room,zero,Option.isNone_none,ite_true,guard,pure,bind,Option.bind]
    intro i
    simp [(no_pivot q).mp zero i,zero_coeffs]
  | some active =>
    have live : q[active] ≠ 0 := by simpa [pivot] using List.find?_some zero
    cases k with
    | zero =>
      have empty := List.length_eq_zero_iff.mp (by omega : rs.length = 0)
      subst rs
      obtain ⟨c,nz,len,eq⟩ := span
      have e := eq active
      have ws := List.length_eq_zero_iff.mp len
      rw [ws] at e
      exact False.elim (live ((Int.mul_eq_zero.mp e).resolve_left nz))
    | succ k =>
      cases rs with
      | nil =>
        obtain ⟨c,nz,len,eq⟩ := span
        have ws := List.length_eq_zero_iff.mp len
        have e := eq active
        rw [ws] at e
        exact False.elim (live ((Int.mul_eq_zero.mp e).resolve_left nz))
      | cons p ps =>
        simp only [Bool.and_eq_true,List.all_cons,List.all_eq_true] at room
        cases pk : pivot p with
        | none =>
          have pz := (no_pivot p).mp pk
          have tail : ∃ c, Witness ps q c := by
            obtain ⟨c,nz,len,eq⟩ := span
            cases w : c.weights with
            | nil => simp [w] at len
            | cons a ws =>
              exact ⟨⟨c.scale,ws⟩,nz,by simpa [w] using len,fun i => by simpa [w,linear,pz i] using eq i⟩
          have slim : StageWithin k ps q := safe.2.1 pz
          obtain ⟨c,done,good⟩ := search_complete k ps q (by simpa using enough) slim tail
          refine ⟨⟨c.scale,0::c.weights⟩,by simp [search,room.1,room.2.1,ite_eq_left room.2.2,zero,pk,done,guard],good.1,by simp [good.2.1],?_⟩
          intro i; simpa [linear] using good.2.2 i
        | some j =>
          have nonzero : p[j] ≠ 0 := by simpa [pivot] using List.find?_some pk
          obtain ⟨c,h⟩ := span
          have tail := drop_pivot p j q ps h
          obtain ⟨d,done,good⟩ := search_complete k (ps.map (eliminate p j)) (eliminate p j q)
            (by simpa using enough) (safe.2.2 j nonzero) tail
          exact ⟨_,by simp [search,room.1,room.2.1,ite_eq_left room.2.2,zero,pk,done,guard],lift_witness p j nonzero ps q good⟩
termination_by k

/-- Whenever a target lies in the rational row span and the independent
arithmetic envelope fits, an exact certificate on the original rows returns. -/
theorem run_complete (rs : List (Row n)) (q : Row n) (within : Within rs q)
    (span : ∃ c, Valid rs q c) : (run rs q).isSome := by
  obtain ⟨width,rows,work,safe⟩ := within
  obtain ⟨c,ok⟩ := span
  obtain ⟨c,done,good⟩ := search_complete rs.length (rs.map signed) (signed q) (by simp) safe
    ⟨c,(original ..).mpr ok⟩
  have checked := (check_iff ..).mpr ((original ..).mp good)
  simp [run,dimensions,width,rows,work,done,checked,guard]

theorem isSome_iff (rs : List (Row n)) (q : Row n) (within : Within rs q) :
    (run rs q).isSome ↔ ∃ c, Valid rs q c := by
  constructor
  · intro done
    obtain ⟨c,returned⟩ := Option.isSome_iff_exists.mp done
    exact ⟨c,run_sound returned⟩
  · exact run_complete rs q within

/-- A replacement may choose any valid scale or multipliers and may extend
the certified coverage envelope. -/
structure Correct (candidate : {n : Nat} → List (Row n) → Row n → Option Certificate) : Prop where
  sound : ∀ {n} (rs : List (Row n)) q c, candidate rs q = some c → Valid rs q c
  complete : ∀ {n} (rs : List (Row n)) q, Within rs q → (∃ c, Valid rs q c) → (candidate rs q).isSome

theorem run_correct : Correct @run := ⟨fun _ _ _ => run_sound,run_complete⟩

end Tamarin.ACBasis.SpanCertificate
