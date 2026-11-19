import Tamarin.ACColumnCone
import Tamarin.ACRationalProjection
import TamarinRuntime.ACColumnSupport

namespace Tamarin.ACFeasibility.ColumnSupport
open ACBasis ColumnCone

def On {n} (rs : List (Row n)) (S : List (Fin n)) : Prop :=
  ∃ d > 0, ∃ z, Correction rs d z ∧ ∀ i, i ∉ S → z i = 0

private def frame {n} (S : List (Fin n)) : Fin (S.length+1) → Vec n :=
  Fin.cases (fun _ => 1) (fun i => spike (S.get i) 1)

private theorem restrict_eq {n} (r : Row n) (S : List (Fin n)) :
    restrictRow S (prepare r) = r.pullback (frame S) := by
  dsimp only [restrictRow,prepare,Row.pullback]
  congr 1 <;> funext i <;> cases i using Fin.cases <;>
    simp [prepend,frame,dot_spike,List.get_eq_getElem] <;> simp [dot]

private def spread {n} : (S : List (Fin n)) → Vec S.length → Vec n
  | [], _ => fun _ => 0
  | k :: S, v => fun i => spike k (v 0) i + spread S (fun j => v j.succ) i

private theorem mix_spread {n} (S : List (Fin n)) (c : Vec (S.length+1)) (i) :
    mix (frame S) c i = c 0 + spread S (fun j => c j.succ) i := by
  have expand (T : List (Fin n)) (v : Vec T.length) :
      total (fun j => spike (T.get j) 1 i * v j) = spread T v i := by
    induction T with
    | nil => simp [spread,total]
    | cons k T ih =>
      simp only [total,List.ofFn_succ,List.sum_cons,List.get_cons_zero,spread] at *
      change spike k 1 i * v 0 + (List.ofFn fun j => spike (T.get j) 1 i * v j.succ).sum = _
      rw [ih (fun j => v j.succ)]
      by_cases eq : i = k <;> simp [spike,eq]
  simpa [mix,dot,total,List.ofFn_succ,frame,prepend] using congrArg (c 0 + ·) (expand S (fun j => c j.succ))

private theorem spread_off {n} (S : List (Fin n)) (v : Vec S.length) (i) (out : i ∉ S) :
    spread S v i = 0 := by
  induction S with
  | nil => rfl
  | cons k S ih =>
    simp only [List.mem_cons, not_or] at out
    simp [spread,spike,out.1,ih _ out.2]

private theorem spread_get {n} (S : List (Fin n)) (uniq : S.Nodup) (z : Vec n) (i) :
    spread S (fun j => z (S.get j)) i = if i ∈ S then z i else 0 := by
  induction S with
  | nil => simp [spread]
  | cons k S ih =>
    obtain ⟨hk,hu⟩ := List.nodup_cons.mp uniq
    change spike k (z k) i + spread S (fun j => z (S.get j)) i = _
    rw [ih hu]
    simp only [List.mem_cons]
    by_cases e : i = k
    · subst i; simp [spike,hk]
    · simp [spike,e]

private theorem restricted_iff {n} (rs : List (Row n)) (S : List (Fin n)) (uniq : S.Nodup) :
    (∃ c, SystemHolds ((rs.map prepare).map (restrictRow S)) c ∧ 0 < c 0) ↔ On rs S := by
  have solution c : SystemHolds ((rs.map prepare).map (restrictRow S)) c ↔
      SystemHolds rs (fun i => c 0 + spread S (fun j => c j.succ) i) := by
    simp only [SystemHolds,List.mem_map,forall_exists_index,and_imp]
    constructor
    · intro h r hr
      have e := h (restrictRow S (prepare r)) (prepare r) r hr rfl rfl
      rw [restrict_eq,Row.pullback_iff] at e
      simpa only [funext (mix_spread S c)] using e
    · intro h r p r' hr' ep er
      subst p; subst r; rw [restrict_eq,Row.pullback_iff]
      simpa only [funext (mix_spread S c)] using h r' hr'
  constructor
  · rintro ⟨c,h,hd⟩
    exact ⟨c 0,hd,_,(correction_iff ..).mpr ((solution c).mp h),spread_off S _⟩
  · rintro ⟨d,hd,z,h,hz⟩
    let c := prepend d (fun j => z (S.get j))
    refine ⟨c,(solution c).mpr ?_,hd⟩
    have same (i) : c 0 + spread S (fun j => c j.succ) i = d + z i := by
      change d + spread S (fun j => z (S.get j)) i = d + z i
      rw [spread_get S uniq]
      split <;> simp_all
    simpa only [funext same] using (correction_iff ..).mp h

private theorem ray_iff {k} (rs : List (Row (k+1))) (gs : List (Vec (k+1)))
    (basis : Cone.ScaleCorrect rs gs) :
    (gs.any fun g => decide (0 < g 0)) = true ↔ ∃ c, SystemHolds rs c ∧ 0 < c 0 := by
  simp only [List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨g,hg,gt⟩
    exact ⟨g,basis.sound g (Cone.gen_member hg),gt⟩
  · rintro ⟨c,sol,pos⟩
    obtain ⟨d,hd,w,eq⟩ := basis.complete c sol
    have sum : 0 < mix gs.get w 0 := by rw [eq]; exact Nat.mul_pos hd pos
    obtain ⟨t,ht,gt⟩ := List.sum_pos_iff_exists_pos_nat.mp sum
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨gs.get j,List.get_mem _ j,Nat.pos_of_mul_pos_right gt⟩

theorem checkSupport_correct {n} (rs : List (Row n)) (S : List (Fin n)) (uniq : S.Nodup)
    {b} (got : checkSupport (rs.map prepare) S = some b) : b = true ↔ On rs S := by
  let input := rs.map prepare
  change checkSupport input S = some b at got
  by_cases fits : (S.length+1) * max input.length RationalProjection.maxRays ≤ cells
  · simp only [checkSupport,guard,fits,↓reduceIte,pure] at got
    cases h : RationalProjection.basis (input.map (restrictRow S)) with
    | none => simp [h] at got
    | some gs =>
      obtain rfl := (show (gs.any fun g => decide (0 < g 0)) = b by simpa [h] using got)
      exact (ray_iff _ gs (RationalProjection.basis_correct _ _ h)).trans (restricted_iff rs S uniq)
  · simp [checkSupport,fits,guard,failure] at got

private def May {α} (P : List α → Prop) (xs : List α) (room : Nat) (seen : List α) : Prop :=
  ∃ a : List α, a.Sublist xs ∧ a.length ≤ room ∧ P (a.reverse ++ seen)

private theorem may_nil {α} (P : List α → Prop) (r : Nat) (s : List α) : May P [] r s ↔ P s := by
  simp [May]

private theorem may_zero {α} (P : List α → Prop) (xs s : List α) : May P xs 0 s ↔ P s := by
  constructor
  · rintro ⟨a,_,zero,hit⟩; obtain rfl := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero zero)
    simpa using hit
  · exact fun h => ⟨[],List.nil_sublist _,by simp,by simpa using h⟩

private theorem may_cons {α} (P : List α → Prop) (x : α) (xs : List α) (k : Nat) (s : List α) :
    May P (x::xs) (k+1) s ↔ May P xs (k+1) s ∨ May P xs k (x::s) := by
  constructor
  · rintro ⟨q,sub,len,hit⟩
    rcases List.sublist_cons_iff.mp sub with skip|⟨t,rfl,ts⟩
    · exact .inl ⟨_,skip,len,hit⟩
    · exact .inr ⟨_,ts,by simpa using len,by simpa using hit⟩
  · rintro (⟨q,sub,len,hit⟩|⟨q,sub,len,hit⟩)
    · exact ⟨q,sub.cons x,len,hit⟩
    · exact ⟨x::q,sub.cons_cons x,by simpa using len,by simpa using hit⟩

private def Every {α} (P : List α → Prop) (xs : List α) (room : Nat) (seen : List α) : Prop :=
  ∀ a : List α, a.Sublist xs → a.length ≤ room → P (a.reverse ++ seen)

private theorem Every.here {α P xs k s} (ok : @Every α P xs k s) : P s := by
  simpa using ok [] (List.nil_sublist _) (Nat.zero_le _)

private theorem Every.skip {α P x xs k s} (ok : @Every α P (x::xs) (k+1) s) : Every P xs (k+1) s :=
  fun a sub len => ok a (sub.cons x) len

private theorem Every.take {α P x xs k s} (ok : @Every α P (x::xs) (k+1) s) : Every P xs k (x::s) :=
  fun a sub len => by simpa using ok (x::a) (sub.cons_cons x) (Nat.succ_le_succ len)

private theorem explore_correct {α} (test : List α → Option Bool) (P : List α → Prop)
    (xs : List α) (room : Nat) (seen : List α) (fuel : Nat) {b f}
    (ok : Every (fun S => ∀ b, test S = some b → (b = true ↔ P S)) xs room seen)
    (ran : explore test xs room seen fuel = some (b,f)) : b = true ↔ May P xs room seen := by
  have has : 0 < fuel := by
    apply Classical.byContradiction; intro h
    cases xs <;> cases room <;> simp [explore,h,guard,failure] at ran
  induction xs generalizing room seen fuel b f with
  | nil =>
    rw [may_nil]
    simp only [explore,has,guard,↓reduceIte,pure] at ran
    change (test seen).bind (fun hit => some (hit,fuel-1)) = some (b,f) at ran
    obtain ⟨v,t,h⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj h)
    exact ok.here v t
  | cons x xs ih =>
    cases room with
    | zero =>
      rw [may_zero]
      simp only [explore,has,guard,↓reduceIte,pure] at ran
      change (test seen).bind (fun hit => some (hit,fuel-1)) = some (b,f) at ran
      obtain ⟨v,t,h⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj h)
      exact ok.here v t
    | succ k =>
      rw [may_cons]
      simp only [explore,guard,has,↓reduceIte,pure] at ran
      change (explore test xs (k+1) seen fuel).bind (fun pair =>
        if pair.1 then some (true,pair.2) else explore test xs k (x::seen) pair.2) = some (b,f) at ran
      obtain ⟨⟨yes,left⟩,first,rest⟩ := Option.bind_eq_some_iff.mp ran
      have one := ih (k+1) seen fuel ok.skip first has
      cases yes with
      | true =>
        obtain ⟨rfl,rfl⟩ := (show true = b ∧ left = f by simpa using rest)
        simp [(one.mp rfl)]
      | false =>
        have second : explore test xs k (x::seen) left = some (b,f) := by simpa using rest
        have fresh : 0 < left := by
          apply Classical.byContradiction; intro h
          cases xs <;> cases k <;> simp [explore,h,guard,failure] at second
        simpa [show ¬ May P xs (k + 1) seen by simpa using one.symm] using
          ih k (x::seen) left ok.take second fresh

private theorem may_iff {n} (rs : List (Row n)) : May (On rs) (List.finRange n) rs.length [] ↔ Feasible rs := by
  constructor
  · rintro ⟨_,_,_,d,hd,z,cert,_⟩
    exact (feasible_iff_correction rs).mpr ⟨d,hd,z,cert⟩
  · intro h
    obtain ⟨S,_,len,_,d,hd,z,cert,off⟩ := (feasible_iff_independent_correction rs).mp h
    let chosen := (List.finRange n).filter fun i => i ∈ S
    have mem (i) : i ∈ chosen ↔ i ∈ S := by simp [chosen]
    have nodup : chosen.Nodup := (List.nodup_finRange n).filter _
    have shorter := nodup.length_le_of_subset (fun {i} hi => (mem i).mp hi)
    refine ⟨chosen,List.filter_sublist,by omega,d,hd,z,cert,?_⟩
    intro i absent; apply off; simpa [chosen] using absent


theorem run_correct {n} (rs : List (Row n)) (budget : Nat) {b}
    (ran : run rs budget = some b) : b = true ↔ Feasible rs := by
  simp only [run,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.map_eq_some_iff] at ran
  obtain ⟨_,_,_,_,⟨out,result,rfl⟩⟩ := ran
  apply Iff.trans _ (may_iff rs)
  apply explore_correct _ _ _ _ _ _ _ result
  intro a sub len bit got
  have uniq := (List.nodup_finRange n).sublist sub
  exact checkSupport_correct rs _ (by simpa using (List.reverse_perm a).symm.nodup uniq) got

/-- Number of supports visited by an exhaustive search, including the empty
support. For m equations and n variables this is the sum of binomial(n,j)
for j up to min(m,n). The runtime never materializes these supports. -/
def visits : Nat → Nat → Nat
  | 0, _ | _, 0 => 1
  | n+1,k+1 => visits n (k+1) + visits n k

private theorem visits_pos (n k) : 0 < visits n k := by
  induction n generalizing k with
  | zero => simp [visits]
  | succ n ih => cases k with
    | zero => simp [visits]
    | succ k => exact Nat.add_pos_left (ih (k+1)) _

private theorem explore_total {α} (test : List α → Option Bool) (xs : List α)
    (room : Nat) (seen : List α) (fuel : Nat) (enough : visits xs.length room ≤ fuel)
    (ok : Every (fun S => (test S).isSome) xs room seen) :
    ∃ b f, explore test xs room seen fuel = some (b,f) ∧ fuel ≤ f + visits xs.length room := by
  have pos : 0 < fuel := Nat.lt_of_lt_of_le (visits_pos ..) enough
  induction xs generalizing room seen fuel with
  | nil =>
    obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp ok.here
    exact ⟨b,fuel-1,by simp [explore,pos,guard,hb],by simp [visits]; omega⟩
  | cons x xs ih =>
    cases room with
    | zero =>
      obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp ok.here
      exact ⟨b,fuel-1,by simp [explore,pos,guard,hb],by simp [visits]; omega⟩
    | succ k =>
      simp only [List.length_cons,visits] at enough ⊢
      have first := ih (k+1) seen fuel (by omega) ok.skip pos
      obtain ⟨yes,f,ran,left⟩ := first
      cases yes with
      | true => exact ⟨true,f,by simp [explore,pos,guard,ran],by omega⟩
      | false =>
        have room' : visits xs.length k ≤ f := by omega
        obtain ⟨bit,g,out,bound⟩ := ih k (x::seen) f room' ok.take
          (Nat.lt_of_lt_of_le (visits_pos ..) room')
        exact ⟨bit,g,by simp [explore,pos,guard,ran,out],by omega⟩

/-- The cost and complete cone-projection domains depend only on the input
rows and support widths, without an assumption on any verdict or witness. -/
def Within {n} (rs : List (Row n)) (budget : Nat) : Prop :=
  n ≤ 4096 ∧ rs.length ≤ 64 ∧
  (∀ r ∈ rs, total r.pos ≤ RationalProjection.maxCoeff ∧ total r.neg ≤ RationalProjection.maxCoeff) ∧
  visits n rs.length ≤ budget ∧
  ∀ (S : List (Fin n)), S.Nodup → S.length ≤ rs.length →
    (S.length+1) * max rs.length RationalProjection.maxRays ≤ cells ∧
    RationalProjection.Within ((rs.map prepare).map (restrictRow S))

theorem run_total {n} (rs : List (Row n)) (budget : Nat) (domain : Within rs budget) :
    (run rs budget).isSome := by
  obtain ⟨width,rows,coeff,fuel,supports⟩ := domain
  have total : Every (fun S => (checkSupport (rs.map prepare) S).isSome) (List.finRange n) rs.length [] := by
    intro a sub len
    have uniq := (List.reverse_perm a).symm.nodup ((List.nodup_finRange n).sublist sub)
    obtain ⟨fits,ok⟩ := supports (a.reverse++[]) (by simpa using uniq) (by simpa using len)
    obtain ⟨gs,done,_,_⟩ := RationalProjection.basis_within _ ok
    have allowed : (a.reverse.length+1) * max rs.length RationalProjection.maxRays ≤ cells := by simpa using fits
    simp only [checkSupport,List.length_map,List.append_nil] at done ⊢
    simp only [guard,allowed,↓reduceIte,pure,done]; rfl
  obtain ⟨b,f,h,_⟩ := explore_total _ (List.finRange n) rs.length [] budget (by simpa using fuel) total
  have small : ((rs.map prepare).all fun p => decide (p.left ≤ RationalProjection.maxCoeff) &&
      decide (p.right ≤ RationalProjection.maxCoeff)) = true := by
    apply List.all_eq_true.mpr
    intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (coeff r hr).1,decide_eq_true (coeff r hr).2⟩
  simp [run,guard,width,rows,small,h]

private theorem coeff_le_total {n} (v : Vec n) (i : Fin n) : v i ≤ ACBasis.total v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [ACBasis.total,List.ofFn_succ,List.sum_cons]
    exact Fin.cases (by omega) (fun j => Nat.le_trans (ih (fun k => v k.succ) j) (Nat.le_add_left ..)) i

private theorem restrict_cap {n} (S : List (Fin n)) (r : Row n)
    (weights : total r.pos ≤ 65536 ∧ total r.neg ≤ 65536) :
    (restrictRow S (prepare r)).cap ≤ 65536 := by
  apply (List.max_le_iff _).mpr
  intro b mem
  simp only [List.mem_cons,List.mem_append,List.mem_ofFn] at mem
  rcases mem with rfl|⟨i,rfl⟩|⟨i,rfl⟩
  · decide
  · apply Nat.le_trans (Nat.sub_le ..)
    cases i using Fin.cases with
    | zero => exact weights.1
    | succ j => exact Nat.le_trans (coeff_le_total r.pos (S.get j)) weights.1
  · apply Nat.le_trans (Nat.sub_le ..)
    cases i using Fin.cases with
    | zero => exact weights.2
    | succ j => exact Nat.le_trans (coeff_le_total r.neg (S.get j)) weights.2

private theorem grow {n K M} (r : Row n) (rs : List (Row n)) (width : n ≤ 3) (cap : r.cap ≤ 65536)
    (k : (RationalProjection.sizes rs).1 ≤ K) (m : (RationalProjection.sizes rs).2 ≤ M) :
    (RationalProjection.sizes (r::rs)).1 ≤ K + K*K ∧
    n * (r.cap * (RationalProjection.sizes rs).2) ≤ 3 * (65536*M) ∧
    (RationalProjection.sizes (r::rs)).2 ≤ max M (2 * (3*(65536*M)*M)) := by
  have w := Nat.mul_le_mul width (Nat.mul_le_mul cap m)
  exact ⟨Nat.add_le_add k (Nat.mul_le_mul k k),w,Nat.max_le.mpr
    ⟨Nat.le_trans m (Nat.le_max_left ..),
    Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul w m)) (Nat.le_max_right ..)⟩⟩

private theorem tiny_within {n} (rs : List (Row n)) (w : n ≤ 3) (few : rs.length ≤ 2)
    (bounds : ∀ r ∈ rs, r.cap ≤ 65536) : RationalProjection.Within rs := by
  have base : RationalProjection.Within ([] : List (Row n)) := Nat.le_trans w (by decide)
  have one (r : Row n) (cap : r.cap ≤ 65536) :
      RationalProjection.Within [r] ∧ (RationalProjection.sizes [r]).1 ≤ 12 ∧
        (RationalProjection.sizes [r]).2 ≤ 393216 := by
    obtain ⟨k,a,b⟩ := grow r [] w cap (K := 3) (M := 1) w (by simp [RationalProjection.sizes])
    exact ⟨⟨base,Nat.le_trans k (by decide),Nat.lt_of_le_of_lt a (by decide),
      Nat.lt_of_le_of_lt b (by decide)⟩,k,b⟩
  cases rs with
  | nil => exact base
  | cons r rs =>
    have cap := bounds r List.mem_cons_self
    cases rs with
    | nil => exact (one r cap).1
    | cons s tail =>
      obtain rfl : tail = [] := by simpa [Nat.le_zero] using few
      obtain ⟨ok,k,m⟩ := one s (bounds s (by simp))
      obtain ⟨l,a,b⟩ := grow r [s] w cap k m
      exact ⟨ok,Nat.le_trans l (by decide),Nat.lt_of_le_of_lt a (by decide),
        Nat.lt_of_le_of_lt b (by decide)⟩

/-- At most two equations, at most 4096 variables, and at most 65536
occurrences on either side of any row. With enough support credits the
checker always decides, even if all permitted supports must be examined. -/
theorem two_rows_total {n} (rs : List (Row n)) (budget : Nat)
    (width : n ≤ 4096) (few : rs.length ≤ 2)
    (coeff : ∀ r ∈ rs, total r.pos ≤ 65536 ∧ total r.neg ≤ 65536)
    (fuel : visits n rs.length ≤ budget) : (run rs budget).isSome := by
  apply run_total; refine ⟨width,by omega,?_,fuel,?_⟩
  · intro r hr
    have lim : 65536 ≤ RationalProjection.maxCoeff := by decide
    exact ⟨Nat.le_trans (coeff r hr).1 lim,Nat.le_trans (coeff r hr).2 lim⟩
  · intro S _ size
    have small : S.length+1 ≤ 3 := by omega
    refine ⟨?_,tiny_within _ small (by simpa using few) ?_⟩
    · have d : max rs.length RationalProjection.maxRays ≤ 256 := Nat.max_le.mpr ⟨by omega,by decide⟩
      exact Nat.le_trans (Nat.mul_le_mul small d) (by decide)
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      obtain ⟨raw,rawMem,rfl⟩ := List.mem_map.mp hp
      exact restrict_cap S raw (coeff raw rawMem)

private theorem visits_one (n : Nat) : visits n 1 = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change visits n 1 + visits n 0 = n+1+1
    rw [ih, show visits n 0 = 1 by cases n <;> rfl]

private theorem visits_two (n : Nat) : 2 * visits n 2 = n*n + n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2*(visits n 2 + visits n 1) = (n+1)*(n+1)+(n+1)+2
    rw [Nat.mul_add,ih,visits_one]
    grind

/-- The completion floor uses only the original rows and fixed arithmetic.
For two rows the budget covers exactly 1+n+binomial(n,2) supports. -/
theorem two_rows_floor {n} (rs : List (Row n)) (budget : Nat)
    (width : n ≤ 4096) (few : rs.length ≤ 2)
    (coeff : ∀ r ∈ rs, total r.pos ≤ 65536 ∧ total r.neg ≤ 65536)
    (fuel : n*n+n+2 ≤ 2*budget) : (run rs budget).isSome := by
  apply two_rows_total rs budget width few coeff
  have two := visits_two n
  have small := Nat.le_mul_self n
  rcases (show rs.length = 0 ∨ rs.length = 1 ∨ rs.length = 2 by omega) with h|h|h
  · rw [h]; cases n <;> change 1 ≤ budget <;> omega
  · rw [h,visits_one]; omega
  · rw [h]; omega

end Tamarin.ACFeasibility.ColumnSupport
