import TamarinRuntime.ACRowReduction
import Tamarin.ACBasis
import Tamarin.ACPrimitiveRow

namespace Tamarin.ACBasis.RowReduction
variable {n : Nat}

theorem orient_iff (r : Row n) (j : Fin n) (x : Vec n) : (orient r j).Holds x ↔ r.Holds x := by
  unfold orient
  split
  · rfl
  · exact eq_comm

private theorem dot_combination (u v : Nat) (a b x : Vec n) :
    dot (fun i => u*a i + v*b i) x = u * dot a x + v * dot b x := by
  induction n with
  | zero => simp [dot,total]
  | succ n ih =>
    have tail := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => x i.succ)
    simp only [dot,total,List.ofFn_succ,List.sum_cons,Nat.mul_add] at tail ⊢
    rw [tail,Nat.add_mul,Nat.mul_assoc,Nat.mul_assoc]
    omega

theorem cancel_iff (p t : Row n) (j : Fin n) (x : Vec n) (hp : p.Holds x) :
    (cancel p t j).Holds x ↔ t.Holds x := by
  unfold cancel
  dsimp only
  split
  · rfl
  · rename_i nz
    have h := (orient_iff p j x).mpr hp
    unfold Row.Holds at h
    rw [Row.ofWeights_holds,dot_combination,dot_combination,h,Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by omega : (orient p j).pos j ≠ 0)]
    exact orient_iff t j x

private theorem stored_eq (r : Row n) : stored r = r := by
  cases r; simp [stored]

theorem reduceAt_iff (p t o : Row n) (j : Fin n) (got : reduceAt p j t = some o)
    (x : Vec n) (hp : p.Holds x) : o.Holds x ↔ t.Holds x := by
  unfold reduceAt at got
  split at got
  · cases Option.some.inj got; rfl
  · simp only [stored_eq] at got
    by_cases small : (cancel p t j).primitive.cap < 2^128
    · obtain rfl : (cancel p t j).primitive = o := by simpa [guard,small] using got
      exact ((cancel p t j).primitive_holds x).trans (cancel_iff p t j x hp)
    · simp [guard,small,failure] at got

private theorem tail_iff (p : Row n) (j : Fin n) (ts os : List (Row n))
    (got : ts.mapM (reduceAt p j) = some os) (x : Vec n) (hp : p.Holds x) :
    SystemHolds os x ↔ SystemHolds ts x := by
  induction ts generalizing os with
  | nil => cases Option.some.inj got; rfl
  | cons t ts ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at got
    obtain ⟨o,h,rest,hr,rfl⟩ := got
    simp [SystemHolds] at ih ⊢
    exact and_congr (reduceAt_iff p t o j h x hp) (ih _ hr)

theorem echelon_iff (steps : Nat) (rs out : List (Row n)) (got : echelon steps rs = some out)
    (x : Vec n) : SystemHolds out x ↔ SystemHolds rs x := by
  induction steps generalizing rs out with
  | zero => cases Option.some.inj got; rfl
  | succ k ih =>
    cases rs with
    | nil => cases Option.some.inj got; rfl
    | cons p ts =>
      cases pick : (List.finRange n).find? (fun i => 0 < p.pos i || 0 < p.neg i) with
      | none =>
        simp only [echelon,pick,Option.bind_eq_bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at got
        obtain ⟨t,h,rfl⟩ := got
        simpa [SystemHolds] using and_congr_right (a := p.Holds x) (fun _ => ih _ _ h)
      | some j =>
        simp only [echelon,pick,Option.bind_eq_bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at got
        obtain ⟨os,red,tail,h,rfl⟩ := got
        simpa [SystemHolds] using and_congr_right (a := p.Holds x) (fun hp =>
          (ih _ _ h).trans (tail_iff p j ts os red x hp))

end Tamarin.ACBasis.RowReduction
