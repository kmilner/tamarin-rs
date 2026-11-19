import TamarinRuntime.ACRayPacket
import Tamarin.HomogeneousContract

namespace Tamarin.Homogeneous.RayPacket
open ACBasis

def Sound (ray : @Candidate) : Prop :=
  ∀ {n} {rs : List (Row n)} {v}, ray rs = some v →
    generate rs = [coordinates v] ∧ ∀ i : Fin n, 0 < v[i]

/-- A small positive solution bounds the primitive generator even when it
is a proper multiple. Both this bound and the candidate's domain describe
the input equations themselves. -/
def Admitted (domain : {n : Nat} → List (Row n) → Prop) (width : UInt64) (m : Matrix) : Prop :=
  0 < width ∧ width ≤ maxWidth ∧ m.size ≤ 128 ∧ ∃ rows,
    readRows width.toNat m.toList = some rows ∧ domain rows ∧
    ∃ x, SystemHolds rows x ∧ (∀ i, 0 < x i) ∧ 1 + 2 * width.toNat + total x ≤ 65536

private theorem total_mono {n} (x y : Vec n) (le : ∀ i, x i ≤ y i) : total x ≤ total y := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simpa [total,List.ofFn_succ] using Nat.add_le_add (le 0) (ih (fun i => x i.succ)
      (fun i => y i.succ) (fun i => le i.succ))

private theorem primitive_le {n} (g x : Vec n) (h : Generates [g] x)
    (live : ∀ i, 0 < x i) : total g ≤ total x := by
  obtain ⟨c,eq⟩ := h
  apply total_mono
  intro i
  have value : x i = g i * c 0 := by
    have e := congrFun eq i
    simpa [mix,dot,total,List.ofFn_succ] using e.symm
  have nz : 0 < c 0 := by
    have := live i
    by_cases z : c 0 = 0
    · simp [value,z] at this
    · omega
  rw [value]
  exact Nat.le_mul_of_pos_right _ nz

/-- All coordinates in the sole returned arm use the same slot, including
repeated copies when the primitive coefficient is greater than one. -/
theorem emit_single {n} (g : Vec n) (width : 0 < n) (live : ∀ i, 0 < g i) :
    emit [g] = #[Array.ofFn (fun i : Fin n => Array.replicate (g i) (0 : UInt64))] := by
  have no : covers [g] [] = false := by
    have i : Fin n := ⟨0,width⟩
    simp [covers]; exact ⟨i,by simp⟩
  have yes : covers [g] [0] = true := by simp [covers,live]
  rw [emit,Coverage.coveringSelections_eq]
  have selected : selections [g] = [[0]] := by
    change List.filter (covers [g]) [[],[0]] = [[0]]
    simp [no,yes]
  rw [selected]
  simp [arm]

theorem returned {ray : @Candidate} {width m out} (h : fallback ray width m = some out) :
    ∃ rows v, (0 < width ∧ width ≤ maxWidth ∧ m.size ≤ 128) ∧
      readRows width.toNat m.toList = some rows ∧ ray rows = some v ∧
      1 + 2*width.toNat + total (coordinates v) ≤ 65536 ∧ emit [coordinates v] = out := by
  simp only [fallback,Option.bind_eq_bind,Option.bind_eq_some_iff,guard,pure,Option.some.injEq] at h
  split at h
  · rename_i limits
    obtain ⟨_,_,rows,read,v,got,_,budget,eq⟩ := h
    exact ⟨rows,v,limits,read,got,by simpa [guard] using budget,eq⟩
  · simp_all

theorem completes {ray : @Candidate} (good : Sound ray)
    {domain : {n : Nat} → List (Row n) → Prop}
    (totalRay : ∀ {n} (rs : List (Row n)), domain rs → (ray rs).isSome)
    (w m) (admitted : Admitted @domain w m) : (solve ray w m).isSome := by
  obtain ⟨wp,small,len,rs,read,inside,x,holds,live,budget⟩ := admitted
  obtain ⟨v,got⟩ := Option.isSome_iff_exists.mp (totalRay rs inside)
  have basis := generate_correct rs
  rw [(good got).1] at basis
  have bound := primitive_le _ x ((basis x).mp holds) live
  have fits : 1 + 2*w.toNat + total (coordinates v) ≤ 65536 := by omega
  cases old : Homogeneous.solve w m <;> simp [solve,old,fallback,wp,small,len,read,got,fits,guard]

theorem correct {ray : @Candidate} (good : Sound ray) : Homogeneous.Correct (solve ray) where
  malformed := by
    intro w m bad
    simp [solve,Homogeneous.solve_correct.malformed w m bad,fallback,bad,guard]
  completes := by
    intro w m admitted
    obtain ⟨answer,got⟩ := Option.isSome_iff_exists.mp (Homogeneous.solve_correct.completes w m admitted)
    simp [solve,got]
  semantic := by
    intro s f rows avoid n fr m input out solved w inj typed fresh
    cases old : Homogeneous.solve n m with
    | some answer =>
      have eq : answer = out := by simpa [solve,old] using solved
      exact Homogeneous.solve_correct.semantic f rows avoid n fr m input out (eq ▸ old) w inj typed fresh
    | none =>
      obtain ⟨rs,v,_,read,got,_,rfl⟩ := returned (by simpa [solve,old] using solved)
      rw [input] at read
      cases read
      have basis := generate_correct (rows.map (encode fr.names))
      rw [(good got).1] at basis
      exact emit_correct f rows avoid fr _ basis (by simp) w inj typed fresh

end Tamarin.Homogeneous.RayPacket
