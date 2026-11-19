import TamarinRuntime.MixedSizeGraph
import Tamarin.ACBagSearch
import Tamarin.ACFeasibility

namespace Tamarin.MixedSizeGraph
open Whole ACBasis ACFeasibility

/-- Replay one physical row against the earlier rows. Each shared edge
contributes its child's full size again, including repeated edges. -/
def Charged (prior : Array Cost) (r : Array UInt64) (c : Cost) : Prop :=
  ∃ k, r[0]? = some k ∧
    if k ≤ 1 then c = ⟨1,1⟩ else
      ∃ cs : List Cost, (r.toList.drop 2).map (fun id => prior[id.toNat]?) = cs.map some ∧
        c = ⟨1 + (cs.map Cost.size).sum, 1 + cs.foldl (fun h v => max h v.height) 0⟩

inductive Table : Array Cost → List (Array UInt64) → Array Cost → Prop where
  | nil (prior) : Table prior [] prior
  | cons {prior r c rs out} : Charged prior r c → c.size ≤ 4096 → c.height ≤ 129 →
      Table (prior.push c) rs out → Table prior (r :: rs) out

/-- Physical work envelope, specified by the edge equations rather than by a
particular implementation of the preflight pass. -/
def GraphWithin (ns : Array (Array UInt64)) (roots : Array UInt64) : Prop :=
  ns.size ≤ 4096 ∧ roots.size ≤ 128 ∧ (ns.toList.map Array.size).sum ≤ 16384 ∧
    ∃ (costs : Array Cost) (cs : List Cost), Table #[] ns.toList costs ∧
      roots.toList.map (fun i => costs[i.toNat]?) = cs.map some ∧
      (cs.map Cost.size).sum ≤ 4096

private theorem reads {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ xs.map f = ys.map some := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
    cases ys with
    | nil => cases h : f x <;> cases g : xs.mapM f <;> simp [List.mapM_cons,h,g]
    | cons y ys =>
      cases h : f x <;> cases g : xs.mapM f <;> simp [List.mapM_cons,h,g,← ih]

private theorem charged (prior r c) : nodeCost prior r = some c ↔ Charged prior r c := by
  cases h : r[0]? with
  | none => simp [nodeCost,Charged,h]
  | some k =>
    by_cases leaf : k ≤ 1
    · simp [nodeCost,Charged,h,leaf,eq_comm]
    · simp [nodeCost,Charged,h,leaf,-List.map_drop,Option.bind_eq_some_iff,← reads]
      apply exists_congr
      intro cs
      exact and_congr_right fun _ => eq_comm

private theorem table_correct (rs : List (Array UInt64)) (before after : Array Cost) :
    rs.foldlM pushCost before = some after ↔ Table before rs after := by
  induction rs generalizing before with
  | nil =>
    constructor
    · rintro h; cases h; exact .nil _
    · rintro h; cases h; rfl
  | cons r rs ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind,Option.bind_eq_some_iff]
    constructor
    · rintro ⟨next,step,done⟩
      simp only [pushCost,Option.bind_eq_bind,Option.bind_eq_some_iff] at step
      obtain ⟨c,read,u,small,eq⟩ := step
      have bounds : c.size ≤ 4096 ∧ c.height ≤ 129 := by simpa [guard] using small
      cases eq
      exact .cons ((charged ..).mp read) bounds.1 bounds.2 ((ih _).mp done)
    · intro tab
      cases tab with
      | cons one small shallow tail =>
        have read := (charged ..).mpr one
        exact ⟨_,by simp [pushCost,read,small,shallow,guard],(ih _).mpr tail⟩

theorem withinGraph_iff (ns roots) : withinGraph ns roots = true ↔ GraphWithin ns roots := by
  simp only [withinGraph,GraphWithin,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨sn,sr,sw⟩,h⟩
    generalize he : ns.toList.foldlM pushCost #[] = table at h
    cases table with
    | none => simp at h
    | some table =>
      generalize hr : roots.toList.mapM (fun id => table[id.toNat]?) = cs at h
      cases cs with
      | none => simp [hr] at h
      | some cs =>
        exact ⟨sn,sr,sw,table,cs,(table_correct ..).mp he,(reads ..).mp hr,by simpa [hr] using h⟩
  · rintro ⟨sn,sr,sw,table,cs,hc,hr,total⟩
    exact ⟨⟨sn,sr,sw⟩,by simp [(table_correct ..).mpr hc,(reads ..).mpr hr,total]⟩

theorem count_weight (ks xs : List UInt64) (f : UInt64 → Nat) (distinct : ks.Nodup) (live : xs ⊆ ks) :
    dot (fun i : Fin ks.length => xs.count (ks.get i)) (fun i => f (ks.get i)) = (xs.map f).sum := by
  induction xs with
  | nil => simp [dot,total,List.sum_eq_zero_iff_forall_eq_nat]
  | cons a xs ih =>
    obtain ⟨j,hj⟩ := List.get_of_mem (live List.mem_cons_self)
    have incr : (fun i : Fin ks.length => (a::xs).count (ks.get i)) =
        fun i => spike j 1 i + xs.count (ks.get i) := by
      funext i
      by_cases eq : i = j
      · subst i; rw [hj,List.count_cons_self]; simp [spike,Nat.add_comm]
      · have ne : a ≠ ks.get i := by
          intro same
          apply eq
          exact Fin.ext (distinct.eq_of_getElem_eq i.isLt j.isLt (same.symm.trans hj.symm))
        rw [List.count_cons_of_ne ne]
        simp [spike,eq]
    let values := fun i => f (ks.get i)
    have one : dot (spike j 1) values = f a := by
      change total (fun i => spike j 1 i * values i) = _
      simp only [Nat.mul_comm (spike j 1 _) _,←show dot values (spike j 1) = total (fun i => values i * spike j 1 i) from rfl,
        dot_spike,Nat.mul_one,values,hj]
    rw [incr]
    have tail := ih (fun _ hv => live (List.mem_cons_of_mem _ hv))
    simpa only [dot,Nat.add_mul,total_add,List.map_cons,List.sum_cons,values] using
      congr (congrArg (fun a b : Nat => a + b) one) tail

private theorem balanced_feasible (s : List (Profile × Profile)) (ok : balanced s = true) :
    Feasible (s.map (row (keys s))) := by
  let ks := keys s
  let x : Vec (ks.length+1) := prepend 1 (fun _ => 1)
  have dist : ks.Nodup := Matching.ACBagSearch.dedup_distinct _
  have size (p : Profile) (live : p.vars ⊆ ks) : dot (weights ks p) x = p.fixed + p.vars.length := by
    have v := count_weight ks p.vars (fun _ => 1) dist live
    have ones (xs : List UInt64) : (xs.map (fun _ => 1)).sum = xs.length := by
      induction xs with
      | nil => rfl
      | cons _ _ ih => simp [ih,Nat.add_comm]
    calc
      _ = p.fixed + dot (fun i : Fin ks.length => p.vars.count (ks.get i)) (fun _ => 1) := by
        simp [weights,x,dot,total,List.ofFn_succ,prepend]
      _ = _ := congrArg (p.fixed + ·) (v.trans (ones _))
  refine ⟨x,?_,Fin.cases (show 0 < 1 by decide) (fun _ => (show 0 < 1 by decide))⟩
  intro r hr
  obtain ⟨⟨l,r⟩,mem,rfl⟩ := List.mem_map.mp hr
  have live : l.vars ++ r.vars ⊆ ks := fun _ h =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨(l,r),mem,h⟩)
  rw [row,Row.ofWeights_holds,size l (fun _ h => live (List.mem_append_left _ h)),
    size r (fun _ h => live (List.mem_append_right _ h))]
  exact beq_iff_eq.mp ((List.all_eq_true.mp ok) (l,r) mem)

theorem refutesDecoded_iff (ns roots p) :
    refutesDecoded ns roots p = true ↔ GraphWithin ns roots ∧
      (system p).length ≤ 64 ∧ (keys (system p)).length + 1 ≤ 4096 ∧
      (system p).length * ((keys (system p)).length + 1) ≤ 8192 ∧
      ACFeasibility.checkRows ((system p).map (row (keys (system p)))) = some false := by
  by_cases ok : balanced (system p) = true
  · have possible := balanced_feasible _ ok
    have never : checkRows ((system p).map (row (keys (system p)))) ≠ some false :=
      fun h => Bool.noConfusion ((checkedRows _ _ h).mpr possible)
    simp [refutesDecoded,ok,never]
  · simp [refutesDecoded,ok,numericWithin,withinGraph_iff,and_assoc]

theorem refutes_iff (ds ns roots) :
    refutes ds ns roots = true ↔ ds.size ≤ 32768 ∧
      ∃ p, Wire.decodeProblem ds ns roots = some p ∧ refutesDecoded ns roots p = true := by
  cases h : Wire.decodeProblem ds ns roots with
  | none => simp [refutes,h]
  | some p =>
    simp only [refutes,Bool.and_eq_true,decide_eq_true_eq,h,Option.any_some,Option.some.injEq,exists_eq_left']
    constructor
    · exact fun ⟨⟨bound,_⟩,rest⟩ => ⟨bound,rest⟩
    · rintro ⟨bound,done⟩
      obtain ⟨g,_⟩ := (refutesDecoded_iff ..).mp done
      exact ⟨⟨bound,g.1,g.2.1,g.2.2.1⟩,done⟩

end Tamarin.MixedSizeGraph
