import Tamarin.ACDirectFeasibility
import Tamarin.ACRationalCone
/-! Strict positive homogeneous feasibility as a single nonnegative cone-membership
problem. A common positive denominator keeps every certificate integral. -/
namespace Tamarin.ACFeasibility.ColumnCone
open ACBasis

/-- With signed column matrix A, the equation for a correction is
A z = d (-A · 1). The full positive witness then has coordinates d + zᵢ. -/
def Correction {n} (rs : List (Row n)) (d : Nat) (z : Vec n) : Prop :=
  ∀ r ∈ rs, d * total r.pos + dot r.pos z = d * total r.neg + dot r.neg z

private theorem dot_shift {n} (v : Vec n) (d : Nat) (z : Vec n) :
    dot v (fun i => d + z i) = d * total v + dot v z := by
  have shift : dot v (fun _ => d) = d * total v := by
    simpa [Cone.scale, dot] using Cone.dot_scale v d (fun _ => 1)
  simp only [dot, Nat.mul_add, total_add] at shift ⊢
  rw [shift]

theorem correction_iff {n} (rs : List (Row n)) (d : Nat) (z : Vec n) :
    Correction rs d z ↔ SystemHolds rs (fun i => d + z i) := by
  simp only [Correction,SystemHolds,Row.Holds,dot_shift]

theorem feasible_iff_correction {n} (rs : List (Row n)) :
    Feasible rs ↔ ∃ d > 0, ∃ z : Vec n, Correction rs d z := by
  constructor
  · rintro ⟨x, sol, live⟩
    refine ⟨1, by decide, fun i => x i - 1, (correction_iff ..).mpr ?_⟩
    have eq : (fun i => 1 + (x i - 1)) = x := funext fun i => by have := live i; omega
    rwa [eq]
  · rintro ⟨d, hd, z, cert⟩
    exact ⟨_, (correction_iff ..).mp cert, fun i => Nat.add_pos_left hd _⟩
abbrev IVec (n : Nat) := Fin n → Int

def rowValue {n} (r : Row n) (v : IVec n) : Int :=
  (List.ofFn fun i => ((r.pos i : Int) - r.neg i) * v i).sum

private theorem sum_linear {n} (u v : IVec n) (a b : Int) :
    (List.ofFn fun i => a * u i - b * v i).sum =
    a * (List.ofFn u).sum - b * (List.ofFn v).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, ih (fun i => u i.succ) (fun i => v i.succ)]
    grind

theorem rowValue_linear {n} (r : Row n) (u v : IVec n) (a b : Int) :
    rowValue r (fun i => a * u i - b * v i) = a * rowValue r u - b * rowValue r v := by
  unfold rowValue
  rw [←sum_linear]
  congr 2
  funext i
  grind

def Vanishes {n} (rs : List (Row n)) (v : IVec n) : Prop := ∀ r ∈ rs, rowValue r v = 0

def Supported {n} (S : List (Fin n)) (v : IVec n) : Prop := ∀ i, i ∉ S → v i = 0

def Independent {n} (rs : List (Row n)) (S : List (Fin n)) : Prop :=
  ∀ v, Supported S v → Vanishes rs v → ∀ i, v i = 0

private theorem eliminate {n} (rows : List (Row n)) (old : List (Row n))
    (S keys : List (Fin n)) (g : Fin n → IVec n) (enough : rows.length < keys.length)
    (uniq : keys.Nodup) (support : ∀ i ∈ keys, Supported S (g i))
    (closed : ∀ i ∈ keys, Vanishes old (g i))
    (diagonal : ∀ i ∈ keys, g i i ≠ 0)
    (off : ∀ i ∈ keys, ∀ j ∈ keys, i ≠ j → g i j = 0) :
    ∃ v, Supported S v ∧ Vanishes old v ∧ Vanishes rows v ∧ ∃ i, v i ≠ 0 := by
  induction rows generalizing old keys g with
  | nil =>
    obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil _ (show keys ≠ [] by intro e; simp [e] at enough)
    exact ⟨g k, support k hk, closed k hk, by simp [Vanishes], k, diagonal k hk⟩
  | cons row rows ih =>
    let score := fun i => rowValue row (g i)
    have finish (data : ∃ v, Supported S v ∧ Vanishes (row::old) v ∧ Vanishes rows v ∧ ∃ i, v i ≠ 0) :
        ∃ v, Supported S v ∧ Vanishes old v ∧ Vanishes (row::rows) v ∧ ∃ i, v i ≠ 0 := by
      obtain ⟨v,s,h,t,w⟩ := data
      exact ⟨v,s,fun r hr => h r (List.mem_cons_of_mem _ hr),fun r hr => by
        rcases List.mem_cons.mp hr with rfl|hr
        · exact h r List.mem_cons_self
        · exact t r hr,w⟩
    apply finish
    by_cases pivot : ∃ p ∈ keys, score p ≠ 0
    · obtain ⟨p,hp,nonzero⟩ := pivot
      let rest := keys.erase p
      have live {i} (hi : i ∈ rest) : i ∈ keys := List.mem_of_mem_erase hi
      have diff {i} (hi : i ∈ rest) : p ≠ i := by
        rintro rfl
        exact uniq.not_mem_erase hi
      -- The nonpivot diagonal stays nonzero after fraction-free elimination.
      let next := fun i j => score p * g i j - score i * g p j
      have elimEq i r : rowValue r (next i) = score p * rowValue r (g i) - score i * rowValue r (g p) :=
        rowValue_linear ..
      apply ih (row::old) rest next
      · have n := List.length_erase_of_mem hp
        simp [rest,n]
        simp only [List.length_cons] at enough
        omega
      · exact uniq.erase p
      · intro i hi j hj
        simp [next,support i (live hi) j hj,support p hp j hj]
      · intro i hi r hr
        rw [elimEq]; rcases List.mem_cons.mp hr with rfl|hr
        · simp [score,Int.mul_comm]
        · simp [closed i (live hi) r hr,closed p hp r hr]
      · intro i hi
        simpa [next,off p hp i (live hi) (diff hi)] using
          Int.mul_ne_zero nonzero (diagonal i (live hi))
      · intro i hi j hj different
        simp [next,off i (live hi) j (live hj) different,off p hp j (live hj) (diff hj)]
    · apply ih (row::old) keys g (by simp only [List.length_cons] at enough; omega) uniq support
      · intro i hi r hr
        rcases List.mem_cons.mp hr with rfl|hr
        · exact Classical.byContradiction fun bad => pivot ⟨i,hi,bad⟩
        · exact closed i hi r hr
      · exact diagonal
      · exact off

/-- Eliminate one distinct pivot coordinate per row from a family of signed
unit columns. A surviving coordinate witnesses a nonzero kernel direction
entirely inside the original support. -/
theorem dependent_of_more_columns {n} (rs : List (Row n)) (S : List (Fin n))
    (uniq : S.Nodup) (more : rs.length < S.length) :
    ∃ v, Supported S v ∧ Vanishes rs v ∧ ∃ i, v i ≠ 0 := by
  let unit := fun (i j : Fin n) => if i = j then (1 : Int) else 0
  obtain ⟨v,hs,_,hr,live⟩ := eliminate rs [] S S unit more uniq
    (fun i hi j hj => by have h : i ≠ j := fun e => hj (e ▸ hi); simp [unit,h])
    (by simp [Vanishes]) (by simp [unit]) (by simp +contextual [unit])
  exact ⟨v,hs,hr,live⟩

theorem independent_length_le {n} (rs : List (Row n)) (S : List (Fin n))
    (uniq : S.Nodup) (ind : Independent rs S) : S.length ≤ rs.length := by
  apply Nat.le_of_not_gt
  intro h
  obtain ⟨v,hs,hv,i,ne⟩ := dependent_of_more_columns rs S uniq (by omega)
  exact ne (ind v hs hv i)

private theorem rowValue_nat {n} (r : Row n) (x : Vec n) :
    rowValue r (fun i => (x i : Int)) = (dot r.pos x : Int) - dot r.neg x := by
  let formula {k} (p q y : Vec k) := (List.ofFn fun i => ((p i : Int) - q i) * (y i : Int)).sum =
    (dot p y : Int) - dot q y
  have lin {k} (p q y : Vec k) : formula p q y := by
    induction k with
    | zero => simp [formula,dot,total]
    | succ k ih =>
      have h := ih (fun i => p i.succ) (fun i => q i.succ) (fun i => y i.succ)
      simp only [formula,dot,total,List.ofFn_succ,List.sum_cons,Int.natCast_add,Int.natCast_mul] at h ⊢
      grind
  exact lin ..

private theorem vanishes_nat {n} {rs : List (Row n)} {x : Vec n} :
    Vanishes rs (fun i => (x i : Int)) ↔ SystemHolds rs x := by
  simp only [Vanishes,SystemHolds,Row.Holds,rowValue_nat,Int.sub_eq_zero,Int.natCast_inj]

private theorem cross_trans {a b c p q r : Int} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (ab : a*q ≤ b*p) (bc : b*r ≤ c*q) : a*r ≤ c*p := by
  apply Int.le_of_not_gt
  intro rev
  have h1 := Int.mul_le_mul_of_nonneg_right ab (Int.le_of_lt hr)
  have h2 := Int.mul_le_mul_of_nonneg_right bc (Int.le_of_lt hp)
  have h3 := Int.mul_lt_mul_of_pos_right rev hq
  grind

private theorem smallest {n} (z : Vec n) (u : IVec n) (ks : List (Fin n))
    (pos : ∀ i ∈ ks, 0 < u i) (live : ks ≠ []) :
    ∃ j ∈ ks, ∀ i ∈ ks, (z j : Int) * u i ≤ (z i : Int) * u j := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
    by_cases empty : ks = []
    · subst ks; exact ⟨k,by simp,by simp⟩
    obtain ⟨j,hj,best⟩ := ih (fun i hi => pos i (List.mem_cons_of_mem _ hi)) empty
    by_cases before : (z k : Int) * u j ≤ (z j : Int) * u k
    · refine ⟨k,List.mem_cons_self,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · exact Int.le_refl _
      · exact cross_trans (pos k List.mem_cons_self) (pos j (List.mem_cons_of_mem _ hj))
          (pos i (List.mem_cons_of_mem _ hi)) before (best i hi)
    · refine ⟨j,List.mem_cons_of_mem _ hj,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · omega
      · exact best i hi

private theorem orient {n} {rs : List (Row n)} {S : List (Fin n)} (u : IVec n)
    (s : Supported S u) (h : Vanishes rs u) (nz : ∃ i, u i ≠ 0) :
    ∃ v, Supported S v ∧ Vanishes rs v ∧ ∃ i, 0 < v i := by
  by_cases yes : ∃ i, 0 < u i
  · exact ⟨u,s,h,yes⟩
  obtain ⟨k,hk⟩ := nz
  refine ⟨fun i => -u i,fun i hi => by simp [s i hi],?_,k,?_⟩
  · intro r hr
    simpa [h r hr] using rowValue_linear r u u 0 1
  · have nonpos : ¬0 < u k := fun e => yes ⟨k,e⟩
    change 0 < -u k
    omega

private theorem shrink {n} {rs : List (Row n)} (S : List (Fin n))
    (d : Nat) (hd : 0 < d) (z : Vec n) (cert : Correction rs d z)
    (support : ∀ i, i ∉ S → z i = 0) {u : IVec n}
    (su : Supported S u) (kernel : Vanishes rs u) (live : ∃ i, 0 < u i) :
    ∃ j ∈ S, ∃ d' > 0, ∃ z', Correction rs d' z' ∧ ∀ i, i ∉ S.erase j → z' i = 0 := by
  let ks := S.filter fun i => decide (0 < u i)
  have pos {i} (mem : i ∈ ks) : 0 < u i := of_decide_eq_true (List.mem_filter.mp mem).2
  have present {i} (h : 0 < u i) : i ∈ ks := by
    have mem : i ∈ S := Classical.byContradiction fun no => by have := su i no; omega
    exact List.mem_filter.mpr ⟨mem,decide_eq_true h⟩
  obtain ⟨i,hi⟩ := live
  obtain ⟨j,hj,best⟩ := smallest z u ks (fun _ => pos) (List.ne_nil_of_mem (present hi))
  have jp := pos hj
  let q := (u j).toNat
  have qeq : (q : Int) = u j := Int.toNat_of_nonneg (Int.le_of_lt jp)
  let raw (i : Fin n) := (q : Int) * (z i : Int) - (z j : Int) * u i
  have nonneg (i) : 0 ≤ raw i := by
    unfold raw
    by_cases yes : 0 < u i
    · have b := best i (present yes); rw [qeq,Int.mul_comm (u j) _]; omega
    · have a := Int.mul_nonneg (Int.natCast_nonneg q) (Int.natCast_nonneg (z i))
      have b := Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg (z j)) (show u i ≤ 0 by omega)
      omega
  let z' (i : Fin n) := (raw i).toNat
  have z'eq (i) : (z' i : Int) = raw i := Int.toNat_of_nonneg (nonneg i)
  refine ⟨j,(List.mem_filter.mp hj).1,q*d,Nat.mul_pos (by omega) hd,z',?_,?_⟩
  · apply (correction_iff ..).mpr
    apply vanishes_nat.mp
    have old := vanishes_nat.mpr ((correction_iff ..).mp cert)
    have same : (fun i => ((q*d + z' i : Nat) : Int)) =
        (fun i => (q : Int) * ((d + z i : Nat) : Int) - (z j : Int) * u i) := by
      funext i; rw [Int.natCast_add,Int.natCast_mul,z'eq,Int.natCast_add]; unfold raw; grind
    rw [same]
    intro r hr
    rw [rowValue_linear,old r hr,kernel r hr]; simp
  · intro i absent
    by_cases same : i = j
    · subst i; simp [z',raw,qeq,Int.mul_comm]
    · have out : i ∉ S := fun mem => absent ((List.mem_erase_of_ne same).mpr mem)
      simp [z',raw,support i out,su i out]

/-- Every feasible system has a shifted certificate supported on independent
columns. Descending the support multiplies its common denominator while
eliminating at least one nonzero direction. -/
theorem sparse_correction {n} (rs : List (Row n)) (S : List (Fin n)) (unique : S.Nodup)
    (d : Nat) (positive : 0 < d) (z : Vec n) (cert : Correction rs d z)
    (support : ∀ i, i ∉ S → z i = 0) :
    ∃ T : List (Fin n), T.Nodup ∧ T ⊆ S ∧ Independent rs T ∧
      ∃ scale > 0, ∃ coeffs, Correction rs scale coeffs ∧ ∀ i, i ∉ T → coeffs i = 0 := by
  by_cases ind : Independent rs S
  · exact ⟨S,unique,fun _ h => h,ind,d,positive,z,cert,support⟩
  simp only [Independent,Classical.not_forall] at ind
  obtain ⟨u,su,closed,live⟩ := ind
  obtain ⟨v,sv,kv,pos⟩ := orient u su closed live
  obtain ⟨j,hj,d',hd',z',cert',support'⟩ := shrink S d positive z cert support sv kv pos
  obtain ⟨T,hT,sub,h,rest⟩ := sparse_correction rs (S.erase j) (unique.erase j) d' hd' z' cert' support'
  exact ⟨T,hT,fun i hi => List.mem_of_mem_erase (sub hi),h,rest⟩
termination_by S.length
decreasing_by
  rw [List.length_erase_of_mem hj]
  have := List.length_pos_iff_exists_mem.mpr ⟨j,hj⟩
  omega

theorem feasible_iff_independent_correction {n} (rs : List (Row n)) :
    Feasible rs ↔ ∃ S : List (Fin n), S.Nodup ∧ S.length ≤ rs.length ∧ Independent rs S ∧
      ∃ scale > 0, ∃ coeffs, Correction rs scale coeffs ∧ ∀ i, i ∉ S → coeffs i = 0 := by
  constructor
  · intro h
    obtain ⟨d,hd,z,cert⟩ := (feasible_iff_correction rs).mp h
    obtain ⟨T,uniq,_,ind,rest⟩ := sparse_correction rs (List.finRange n) (List.nodup_finRange n)
      d hd z cert (by simp)
    exact ⟨T,uniq,independent_length_le rs T uniq ind,ind,rest⟩
  · rintro ⟨_,_,_,_,d,hd,z,cert,_⟩
    exact (feasible_iff_correction rs).mpr ⟨d,hd,z,cert⟩
end Tamarin.ACFeasibility.ColumnCone
