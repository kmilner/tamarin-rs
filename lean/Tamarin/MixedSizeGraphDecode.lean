import TamarinRuntime.MixedSizeGraph

namespace Tamarin.MixedSizeGraph
open Whole

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

theorem refutesDecoded_iff (ns roots p) :
    refutesDecoded ns roots p = true ↔ GraphWithin ns roots ∧
      (system p).length ≤ 64 ∧ (keys (system p)).length + 1 ≤ 4096 ∧
      (system p).length * ((keys (system p)).length + 1) ≤ 8192 ∧
      ACFeasibility.checkRows ((system p).map (row (keys (system p)))) = some false := by
  simp only [refutesDecoded,numericWithin,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,withinGraph_iff]
  simp only [and_assoc]

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
