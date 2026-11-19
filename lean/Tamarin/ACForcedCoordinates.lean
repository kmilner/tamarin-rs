import TamarinRuntime.ACForcedCoordinates
import Tamarin.ACSpanCertificate
import Tamarin.ACLinearConsequence

namespace Tamarin.ACBasis.ForcedCoordinates
open SpanCertificate ACFeasibility
variable {n : Nat}

private inductive Reduction : List (ZRow n) → List (Step n) → Prop where
  | nil : Reduction [] []
  | skip {p rs steps} : (∀ i : Fin n, p[i] = 0) → Reduction rs steps → Reduction (p :: rs) steps
  | pivot {p j rs steps} : p[j] ≠ 0 → Reduction (rs.map (eliminate p j)) steps → Reduction (p::rs) ((p,j)::steps)

private theorem prepared (k : Nat) (rs : List (ZRow n)) {steps} (ok : prepare k rs = some steps) :
    Reduction rs steps := by
  induction k generalizing rs steps with
  | zero => cases rs <;> simp [prepare] at ok; subst steps; exact .nil
  | succ k ih =>
    cases rs with
    | nil => simp [prepare] at ok; subst steps; exact .nil
    | cons p rs =>
      cases hp : pivot p with
      | none =>
        simp only [prepare,hp,Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
        obtain ⟨_,_,h⟩ := ok
        exact .skip ((no_pivot _).mp hp) (ih _ h)
      | some j =>
        have nz : p[j] ≠ 0 := by simpa [pivot] using List.find?_some hp
        simp only [prepare,hp,Option.bind_eq_bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at ok
        obtain ⟨_,_,tail,h,rfl⟩ := ok
        exact .pivot nz (ih _ h)

private def sub (a b : ZRow n) : ZRow n := Vector.ofFn fun i => a[i] - b[i]

private theorem sub_elim (p : ZRow n) (j : Fin n) (a b : ZRow n) :
    eliminate p j (sub a b) = sub (eliminate p j a) (eliminate p j b) := by
  ext i h
  simp [sub,eliminate]
  grind

private theorem project_sub (ss : List (Step n)) (a b : ZRow n) :
    project ss (sub a b) = sub (project ss a) (project ss b) := by
  induction ss generalizing a b with
  | nil => rfl
  | cons t ss ih =>
    change project ss (eliminate _ _ (sub a b)) = sub (project ss _) (project ss _)
    rw [sub_elim,ih]

private theorem skip_iff (p : ZRow n) (rs : List (ZRow n)) (q : ZRow n)
    (zero : ∀ i : Fin n, p[i] = 0) :
    (∃ c, Witness (p::rs) q c) ↔ ∃ c, Witness rs q c := by
  constructor
  · rintro ⟨c,nonzero,len,eq⟩
    cases w : c.weights with
    | nil => simp [w] at len
    | cons a ws =>
      exact ⟨⟨c.scale,ws⟩,nonzero,by simpa [w] using len,fun i => by simpa [w,linear,zero] using eq i⟩
  · rintro ⟨c,nz,len,eq⟩
    exact ⟨⟨c.scale,0::c.weights⟩,nz,by simp [len],fun i => by simpa [linear] using eq i⟩

private theorem zero_iff {rs : List (ZRow n)} {ss} (plan : Reduction rs ss) (v : ZRow n) :
    (∀ i : Fin n, (project ss v)[i] = 0) ↔ ∃ c, Witness rs v c := by
  induction plan generalizing v with
  | nil =>
    constructor
    · intro zero
      exact ⟨⟨1,[]⟩,Int.one_ne_zero,rfl,fun i => by simpa [project,linear] using zero i⟩
    · rintro ⟨c,nz,len,eq⟩ i
      have ws := List.length_eq_zero_iff.mp len
      have e := eq i
      rw [ws] at e
      exact (Int.mul_eq_zero.mp e).resolve_left nz
  | skip zero _ ih => exact (ih v).trans (skip_iff _ _ v zero).symm
  | pivot nz _ ih =>
    change (∀ i : Fin n, (project _ (eliminate _ _ v))[i] = 0) ↔ _
    rw [ih]
    exact ⟨fun ⟨c,h⟩ => ⟨_,lift_witness _ _ nz _ _ h⟩,fun ⟨c,h⟩ => drop_pivot _ _ _ _ h⟩

private theorem signed_eq (i j : Fin n) : signed (equation i j) = sub (unit i) (unit j) := by
  ext k hk
  simp only [signed,equation,LowRank.coeff,Row.ofWeights,spike,sub,unit,Vector.getElem_ofFn]
  split <;> split <;> simp_all

private theorem project_iff {rs : List (Row n)} {ss} (plan : Reduction (rs.map signed) ss) (i j : Fin n) :
    project ss (unit i) = project ss (unit j) ↔ ∃ c, Valid rs (equation i j) c := by
  have zero := zero_iff plan (signed (equation i j))
  rw [signed_eq,project_sub] at zero
  constructor
  · intro eq
    obtain ⟨c,h⟩ := zero.mp (fun k => by simp [sub,eq])
    exact ⟨c,(original ..).mp (by simpa only [signed_eq] using h)⟩
  · rintro ⟨c,h⟩
    have byCol := zero.mpr ⟨c,by simpa only [signed_eq] using (original rs (equation i j) c).mpr h⟩
    ext k hk
    have e := byCol ⟨k,hk⟩
    simpa [sub,Int.sub_eq_zero] using e

private def oneColumn (i : Fin n) (a : Int) : ZRow n := Vector.ofFn fun j => if j = i then a else 0

private theorem nonpivot (ss : List (Step n)) (i : Fin n) (a : Int) (h : i ∉ ss.map Prod.snd) :
    project ss (oneColumn i a) = oneColumn i (scale ss * a) := by
  induction ss generalizing a with
  | nil => simp [project,scale]
  | cons t ss ih =>
    obtain ⟨p,j⟩ := t
    simp only [List.map_cons,List.mem_cons] at h
    have ne : j ≠ i := fun eq => h (Or.inl eq.symm)
    have next : eliminate p j (oneColumn i a) = oneColumn i (p[j]*a) := by
      ext k hk
      simp [eliminate,oneColumn,ne]
      split <;> simp
    change project ss (eliminate p j _) = _
    rw [next,ih _ (fun e => h (.inr e))]
    simp [scale,Int.mul_left_comm,Int.mul_assoc]

private theorem scale_nz {rs : List (ZRow n)} {ss} (h : Reduction rs ss) : scale ss ≠ 0 := by
  induction h with
  | nil => exact Int.one_ne_zero
  | skip _ _ ih => exact ih
  | pivot ne _ ih => simpa [scale] using Int.mul_ne_zero ne ih

private theorem sparse_at (v : ZRow n) (i : Fin n) (z : Int) :
    (i,z) ∈ sparse v ↔ v[i] ≠ 0 ∧ v[i] = z := by
  simp only [sparse,List.mem_filterMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,h⟩
    split at h
    · contradiction
    · cases h; exact ⟨by assumption,rfl⟩
  · rintro ⟨nz,rfl⟩
    exact ⟨i,by rw [ite_eq_right nz]⟩

private theorem sparse_inj : Function.Injective (@sparse n) := by
  intro a b eq
  ext i hi
  let j : Fin n := ⟨i,hi⟩
  by_cases za : a[j] = 0
  · by_cases zb : b[j] = 0
    · exact za.trans zb.symm
    · have mem := (sparse_at b j _).mpr ⟨zb,rfl⟩
      rw [← eq] at mem
      exact ((sparse_at ..).mp mem).2
  · have mem := (sparse_at a j _).mpr ⟨za,rfl⟩
    rw [eq] at mem
    exact ((sparse_at ..).mp mem).2.symm

private theorem sparse_one (i : Fin n) (a : Int) (nz : a ≠ 0) :
    sparse (oneColumn i a) = [(i,a)] := by
  have f : (fun j : Fin n => if (oneColumn i a)[j] = 0 then none else some (j,(oneColumn i a)[j])) =
      fun j : Fin n => if j = i then some (j,a) else none := by
    funext j
    by_cases h : j = i <;> simp [oneColumn,h,nz]
  rw [sparse,f]
  have g (is : List (Fin n)) : (is.filterMap fun j => if j = i then some (j,a) else none) =
      (is.filter (· == i)).map fun j => (j,a) := by
    induction is with
    | nil => rfl
    | cons j js ih => by_cases e : j = i <;> simp [e,ih]
  rw [g,List.filter_beq,(List.nodup_finRange n).count_of_mem (List.mem_finRange i)]
  rfl

private theorem signatures_at {rs : List (ZRow n)} {ss} (plan : Reduction rs ss) (i : Fin n) :
    (signatures ss)[i] = sparse (project ss (unit i)) := by
  by_cases h : i ∈ ss.map Prod.snd
  · simp [signatures,h]
  · have ee : unit i = oneColumn i 1 := rfl
    simp [signatures,h,ee,nonpivot ss i 1 h,sparse_one _ _ (scale_nz plan)]

private theorem indexed (ks : Vector (Key n) n) (is : List (Fin n)) (key : Key n) (mem : ∃ i ∈ is, ks[i] = key) :
    ∃ j, (origins ks is)[key]? = some j ∧ ks[j] = key := by
  induction is with
  | nil => simp at mem
  | cons i is ih =>
    by_cases eq : ks[i.val] = key
    · exact ⟨i,by simp [origins,eq],eq⟩
    · have old : ∃ j ∈ is, ks[j] = key := by
        obtain ⟨j,atj,same⟩ := mem
        rcases List.mem_cons.mp atj with rfl | rest
        · contradiction
        · exact ⟨j,rest,same⟩
      obtain ⟨j,found,same⟩ := ih old
      exact ⟨j,by simpa [origins,Std.HashMap.getElem?_insert,eq] using found,same⟩

private theorem labels_iff (ks : Vector (Key n) n) (i j : Fin n) :
    (labels ks)[i] = (labels ks)[j] ↔ ks[i] = ks[j] := by
  obtain ⟨a,la,ka⟩ := indexed ks (List.finRange n) ks[i] ⟨i,List.mem_finRange _,rfl⟩
  obtain ⟨b,lb,kb⟩ := indexed ks (List.finRange n) ks[j] ⟨j,List.mem_finRange _,rfl⟩
  simp only [labels,Fin.getElem_fin,Vector.getElem_ofFn] at *
  constructor
  · intro e; rw [la,lb] at e
    have same : a = b := Fin.ext e
    exact ka.symm.trans (same ▸ kb)
  · intro e; rw [e]

theorem run_class_iff {rs : List (Row n)} {out} (returned : run rs = some out) (i j : Fin n) :
    out[i] = out[j] ↔ ∃ c, Valid rs (equation i j) c := by
  simp only [run,Option.bind_eq_bind,Option.bind_eq_some_iff] at returned
  obtain ⟨_,_,ss,got,eq⟩ := returned
  cases eq
  have plan := prepared _ _ got
  rw [labels_iff,signatures_at plan,signatures_at plan]
  exact ⟨fun eq => (project_iff plan i j).mp (sparse_inj eq),
    fun h => congrArg sparse ((project_iff plan i j).mpr h)⟩

theorem run_labels_lt {rs : List (Row n)} {out} (returned : run rs = some out) (i : Fin n) :
    out[i] < n := by
  simp only [run,Option.bind_eq_bind,Option.bind_eq_some_iff] at returned
  obtain ⟨_,_,ss,_,eq⟩ := returned
  cases eq
  let ks := signatures ss
  obtain ⟨origin,found,_⟩ := indexed ks (List.finRange n) ks[i] ⟨i,List.mem_finRange _,rfl⟩
  change (labels ks)[i] < n
  simp only [labels,Fin.getElem_fin,Vector.getElem_ofFn] at *
  rw [found]
  exact origin.isLt

/-- The independent arithmetic envelope for reduction of the original
rows. No projected coordinate, target-pair search or output label appears
in the coverage requirement. -/
def Within (rs : List (Row n)) : Prop :=
  SpanCertificate.Within rs (Row.ofWeights (fun _ => 0) (fun _ => 0))

private theorem bounded_iff (p : ZRow n) : bounded p = true ↔ ∀ i : Fin n, p[i].natAbs < 2^256 := by
  simp only [bounded,Array.all_eq_true,decide_eq_true_eq]
  exact ⟨fun h i => h i.val (by simp),fun h i hi => h ⟨i,by simpa using hi⟩⟩

private theorem prepares (k : Nat) (rs : List (ZRow n)) (q : ZRow n) (len : rs.length ≤ k)
    (safe : StageWithin k rs q) : (prepare k rs).isSome := by
  induction k generalizing rs q with
  | zero =>
    have eq := List.length_eq_zero_iff.mp (by omega : rs.length = 0)
    simp [prepare,eq]
  | succ k ih =>
    cases rs with
    | nil => rfl
    | cons p ps =>
      have b : bounded p = true := (bounded_iff p).mpr (safe.1 p (by simp))
      have bs : ps.all bounded = true := List.all_eq_true.mpr fun r mem =>
        (bounded_iff r).mpr (safe.1 r (by simp [mem]))
      have guard_ok : (bounded p && ps.all bounded) = true := by rw [b,bs]; rfl
      have shorter : ps.length ≤ k := by simpa using len
      cases picked : pivot p with
      | none =>
        have yes := ih ps q shorter (safe.2.1 ((no_pivot p).mp picked))
        simpa only [prepare,guard_ok,picked,guard,pure,ite_true,bind,Option.bind] using yes
      | some j =>
        have nz : p[j] ≠ 0 := by simpa [pivot] using List.find?_some picked
        obtain ⟨tail,done⟩ := Option.isSome_iff_exists.mp (ih _ (eliminate p j q) (by simpa) (safe.2.2 j nz))
        change prepare k (ps.map (eliminate p j)) = some tail at done
        simp only [prepare,guard_ok,picked,guard,pure,ite_true,bind,Option.bind,done,Option.isSome_some]

theorem run_complete (rs : List (Row n)) (within : Within rs) : (run rs).isSome := by
  obtain ⟨width,num,work,arith⟩ := within
  obtain ⟨ss,ok⟩ := Option.isSome_iff_exists.mp (prepares rs.length (rs.map signed) _ (by simp) arith)
  simp [run,dimensions,width,num,work,ok,guard]

/-- Every intermediate vector is bounded, including columns projected
through a large number of small pivots. Only coordinates used as pivots
require a dense vector; at most one such coordinate per observed row. -/
theorem project_bound {rs : List (ZRow n)} {ss} (k : Nat) (done : prepare k rs = some ss)
    (v : ZRow n) (b : Nat) (input : ∀ i : Fin n, v[i].natAbs ≤ b) :
    ∀ i : Fin n, (project ss v)[i].natAbs ≤ (2*2^256)^k * b := by
  induction k generalizing rs ss v b with
  | zero => cases rs <;> simp [prepare] at done; subst ss; simpa [project] using input
  | succ k ih =>
    cases rs with
    | nil =>
      simp [prepare] at done; subst ss
      exact fun i => Nat.le_trans (input i) (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0 < 2*2^256)))
    | cons p ps =>
      simp only [prepare,Option.bind_eq_bind,Option.bind_eq_some_iff] at done
      obtain ⟨_,room,done⟩ := done
      have small : (bounded p && ps.all bounded) = true := by simpa [guard] using room
      have bound := (bounded_iff p).mp (Bool.and_eq_true_iff.mp small).1
      cases picked : pivot p with
      | none =>
        simp only [picked] at done
        intro i
        have result := ih done v b input i
        have grow : (2*2^256)^k * b ≤ (2*2^256)^(k+1) * b :=
          Nat.mul_le_mul_right b (Nat.pow_le_pow_right (by decide) (by omega))
        exact Nat.le_trans result grow
      | some j =>
        simp only [picked,Option.bind_eq_some_iff,pure,Option.some.injEq] at done
        obtain ⟨tail,found,rfl⟩ := done
        have next (i : Fin n) : (eliminate p j v)[i].natAbs ≤ (2*2^256)*b := by
          have z := Int.natAbs_sub_le (p[j]*v[i]) (v[j]*p[i])
          rw [Int.natAbs_mul,Int.natAbs_mul] at z
          have u := Nat.mul_le_mul (Nat.le_of_lt (bound j)) (input i)
          have w := Nat.mul_le_mul (input j) (Nat.le_of_lt (bound i))
          rw [Nat.mul_comm b] at w
          simp only [eliminate,Fin.getElem_fin,Vector.getElem_ofFn]
          exact Nat.le_trans z (by rw [Nat.mul_assoc 2]; omega)
        intro i
        rw [Nat.pow_succ (2*2^256) k,Nat.mul_assoc]
        exact ih found _ _ next i

theorem equation_holds (i j : Fin n) (x : Vec n) : (equation i j).Holds x ↔ x i = x j := by
  have one (k : Fin n) : dot (spike k 1) x = x k := by
    rw [show dot (spike k 1) x = dot x (spike k 1) from by simp only [dot,Nat.mul_comm],dot_spike,Nat.mul_one]
  rw [equation,Row.ofWeights_holds,one,one]

/-- The public semantic condition concerns all nonnegative factor counts.
Implementations may use implications beyond rational span; the span
criterion specifies the minimum collection of equalities to report. -/
structure Correct (candidate : {n : Nat} → List (Row n) → Option (Vector Nat n)) : Prop where
  labels_lt : ∀ {n} (rs : List (Row n)) out, candidate rs = some out → ∀ i : Fin n, out[i] < n
  sound : ∀ {n} (rs : List (Row n)) out, candidate rs = some out → ∀ i j : Fin n,
    out[i] = out[j] → ∀ x : Vec n, (∀ r ∈ rs, r.Holds x) → x i = x j
  complete : ∀ {n} (rs : List (Row n)), Within rs → ∃ out, candidate rs = some out ∧
    ∀ i j : Fin n, (∃ c, Valid rs (equation i j) c) → out[i] = out[j]

theorem run_correct : Correct @run where
  labels_lt := fun _ _ returned => run_labels_lt returned
  sound := by
    intro n rs out returned i j eq x common
    obtain ⟨c,v⟩ := (run_class_iff returned i j).mp eq
    exact (equation_holds i j x).mp (ACLinearConsequence.holds_of_combination rs _ c.weights c.scale v.1 v.2.2 x common)
  complete := by
    intro n rs within
    obtain ⟨out,returned⟩ := Option.isSome_iff_exists.mp (run_complete rs within)
    exact ⟨out,returned,fun i j => (run_class_iff returned i j).mpr⟩

end Tamarin.ACBasis.ForcedCoordinates
