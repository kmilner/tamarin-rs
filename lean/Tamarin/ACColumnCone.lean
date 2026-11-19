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
end Tamarin.ACFeasibility.ColumnCone
