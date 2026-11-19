import Tamarin.VariantJoinFamily
import TamarinRuntime.VariantJoin

namespace Tamarin.Rewriting.VariantJoin.Select
abbrev Kernel := Array (Array UInt64) → Option (Array UInt64)

/-- A rejection must have a reducible component. Acceptance needs positive
evidence for every original-variable image and every observed normal value. -/
def Flag (row : Array UInt64) (flag : UInt64) : Prop :=
  (flag = 0 ∧ 0 ∈ row.toList) ∨ (flag = 1 ∧ ∀ w ∈ row.toList, w = 1)

def Correct (f : Kernel) : Prop :=
  ∀ rows mask, f rows = some mask ↔ Aligned Flag rows.toList mask.toList

private theorem keep (row : Array UInt64) (flag : UInt64) :
    VariantJoinCandidate.keep row = some flag ↔ Flag row flag := by
  have mem : row.contains 0 = true ↔ 0 ∈ row.toList := by simp
  have all : row.toList.all (· == 1) = true ↔ ∀ w ∈ row.toList, w = 1 := by simp only [List.all_eq_true,beq_iff_eq]
  unfold VariantJoinCandidate.keep Flag
  split
  · next h =>
    have red := mem.mp h
    have bad : ¬ (∀ w ∈ row.toList, w = 1) := fun hh => by have := hh _ red; contradiction
    simp only [Option.some.injEq]; grind
  · next h =>
    have no := mt mem.mpr h
    split
    · next ha => have := all.mp ha; simp only [Option.some.injEq]; grind
    · next ha => have := mt all.mpr ha; simp only [reduceCtorEq]; grind


private theorem masks (rows : List (Array UInt64)) (mask : List UInt64) :
    rows.mapM VariantJoinCandidate.keep = some mask ↔ Aligned Flag rows mask := by
  induction rows generalizing mask with
  | nil => cases mask <;> simp [Aligned,List.mapM_nil]
  | cons row rest ih =>
    rw [List.mapM_cons]
    cases hx : VariantJoinCandidate.keep row with
    | none =>
      have bad (w) : ¬Flag row w := fun h => by have := (keep row w).mpr h; simp_all
      cases mask <;> simp [Aligned,bad]
    | some w =>
      cases hy : rest.mapM VariantJoinCandidate.keep with
      | none =>
        have bad (vs) : ¬Aligned Flag rest vs := fun h => by have := (ih vs).mpr h; simp_all
        cases mask <;> simp [Aligned,bad]
      | some vs =>
        cases mask with
        | nil => simp [Aligned]
        | cons a as =>
          simp only [Aligned,List.cons.injEq,Option.bind_some, pure,Option.some.injEq,bind]
          rw [← keep,← ih,hx,hy]; simp

theorem correct : Correct VariantJoinCandidate.run := by
  intro rows mask
  rw [← masks]
  simp only [VariantJoinCandidate.run]
  cases mask; cases rows.toList.mapM VariantJoinCandidate.keep <;> simp

/-- Ordinary normalization supplies either definite flag by comparing its
result with the original component modulo the declared B axioms. -/
theorem normal_iff_same {sig : Signature} {R : Root sig} {t n : Term sig}
    (nf : NormalForm R t n) : Normal R t ↔ EquivB t n :=
  ⟨normal_reduces_equiv nf.1, fun eq => (normal_equiv R eq).mpr nf.2.1⟩

/-- The term checker may produce unknown for any component. It must justify
each definite answer against the active rewrite table. -/
def Evidence {sig : Signature} (R : Root sig) (ts : List (Term sig)) (row : Array UInt64) : Prop :=
  Aligned (fun t w => (w = 0 → ¬ Normal R t) ∧ (w = 1 → Normal R t)) ts row.toList

private theorem flags {sig : Signature} {R : Root sig} {ts : List (Term sig)} {ws : List UInt64}
    (e : Aligned (fun t w => (w = 0 → ¬ Normal R t) ∧ (w = 1 → Normal R t)) ts ws) :
    (0 ∈ ws → ¬(∀ t ∈ ts, Normal R t)) ∧ ((∀ w ∈ ws, w = 1) → ∀ t ∈ ts, Normal R t) := by
  induction ts generalizing ws with
  | nil => cases ws <;> simp_all [Aligned]
  | cons t ts ih =>
    cases ws with
    | nil => contradiction
    | cons w ws =>
      have tail := ih e.2
      simp only [List.forall_mem_cons]
      rw [List.mem_cons]
      exact ⟨fun h hn => h.elim (fun eq => e.1.1 eq.symm hn.1) (fun hr => tail.1 hr hn.2),
        fun h => ⟨e.1.2 h.1,tail.2 h.2⟩⟩

/-- The emitted mask includes exactly the normal joined rows, even when some
individual reducibility checks were inconclusive. -/
theorem semantic {f : Kernel} (hc : Correct f) {sig : Signature} {R : Root sig}
    (terms : List (List (Term sig))) {rows : Array (Array UInt64)} {mask : Array UInt64}
    (e : Aligned (Evidence R) terms rows.toList) (ran : f rows = some mask) :
    Aligned (fun ts w => (w = 1 ↔ ∀ t ∈ ts, Normal R t)) terms mask.toList := by
  have valid := (hc _ _).mp ran
  generalize hr : rows.toList = rs at e valid
  generalize hm : mask.toList = ms at valid ⊢
  clear hr hm ran
  induction terms generalizing rs ms with
  | nil => cases rs <;> cases ms <;> simp_all [Aligned]
  | cons t rest ih =>
    cases rs with
    | nil => contradiction
    | cons r rs =>
      cases ms with
      | nil => contradiction
      | cons m ms =>
        refine ⟨?_,ih _ e.2 _ valid.2⟩
        have proof := flags e.1
        rcases valid.1 with ⟨rfl,red⟩ | ⟨rfl,normal⟩
        · constructor
          · intro impossible; contradiction
          · intro hn; exact False.elim (proof.1 red hn)
        · exact ⟨fun _ => proof.2 normal,fun _ => rfl⟩


/-- Rust zips the checked mask with exactly the candidates it submitted. -/
def emit {α : Type} (candidates : List α) (mask : List UInt64) : List α :=
  (candidates.zip mask).filterMap fun (t, flag) => if flag = 1 then some t else none

private theorem emit_iff {α : Type} (P : α → Prop) {candidates : List α} {ms : List UInt64}
    (h : Aligned (fun t w => w = 1 ↔ P t) candidates ms) (v : α) :
    v ∈ emit candidates ms ↔ v ∈ candidates ∧ P v := by
  induction candidates generalizing ms with
  | nil => cases ms <;> simp [emit]
  | cons t rest ih =>
    cases ms with
    | nil => contradiction
    | cons w ms =>
      have tail := ih h.2
      have head := h.1
      by_cases ok : w = 1
      · simp only [emit,List.zip_cons_cons,List.filterMap_cons,ok,↓reduceIte,List.mem_cons]
        change (v = t ∨ v ∈ emit rest ms) ↔ _
        rw [tail]; grind
      · simp only [emit,List.zip_cons_cons,List.filterMap_cons,ok,↓reduceIte,List.mem_cons]
        change v ∈ emit rest ms ↔ _
        rw [tail]; grind

/-- Term-level contract on the surviving rows of one completed unification
call. The two local answers can share arbitrary original variables. -/
def Semantic (f : Kernel) : Prop :=
  ∀ {sig : Signature} {I A B : Type} {rules : List (Equation sig)}
    (_ : Normalized (ruleRoot rules) Substitution.identity)
    (q : Row sig I A) (r : Row sig I B) (_ : ∀ v, q.Uses v → ¬r.Uses v)
    (keys : List I) (_ : ∀ i, i ∈ keys) (anchors : List (Term sig))
    (_ : ∀ v, q.Uses v ∨ r.Uses v → (problem q r keys anchors).Occurs v)
    (sols : List (Substitution sig)) (_ : CompleteSet (problem q r keys anchors) sols)
    (ts : Row sig I (Sum A B) → List (Term sig))
    (_ : ∀ j, j.IsNormal (ruleRoot rules) ↔ ∀ t ∈ ts j, Normal (ruleRoot rules) t)
    (statuses : Array (Array UInt64)) (mask : Array UInt64) (_ : f statuses = some mask)
    (_ : Aligned (Evidence (ruleRoot rules)) ((sols.map (join q r)).map ts) statuses.toList)
    (x : I → Term sig) (y : A → Term sig) (z : B → Term sig)
    (_ : ∀ i, Normal (ruleRoot rules) (x i))
    (_ : ∀ a, Normal (ruleRoot rules) (y a)) (_ : ∀ b, Normal (ruleRoot rules) (z b)),
    Denotes (ruleRoot rules) q x y ∧ Denotes (ruleRoot rules) r x z ↔
      ∃ j ∈ emit (sols.map (join q r)) mask.toList, Denotes (ruleRoot rules) j x (Sum.elim y z)

theorem exact_call {f : Kernel} (hc : Correct f) : Semantic f := by
  intro sig I A B rules vars q r apart keys allKeys anchors tracked sols csu ts inventory statuses mask ran evidence x y z nx ny nz
  rw [exact_join vars q r apart keys allKeys anchors tracked sols csu x y z nx ny nz]
  have flags := semantic hc _ evidence ran
  have mapFlags {js : List (Row sig I (Sum A B))} {ws : List UInt64}
      (h : Aligned (fun terms w => w = 1 ↔ ∀ t ∈ terms, Normal (ruleRoot rules) t) (js.map ts) ws) :
      Aligned (fun j w => w = 1 ↔ j.IsNormal (ruleRoot rules)) js ws := by
    induction js generalizing ws with
    | nil => cases ws <;> exact h
    | cons j rest ih => cases ws with
      | nil => contradiction
      | cons _ _ => exact ⟨h.1.trans (inventory j).symm,ih h.2⟩
  have keep := emit_iff _ (mapFlags flags)
  constructor
  · rintro ⟨μ,hm,hn,hit⟩; exact ⟨_,(keep _).mpr ⟨List.mem_map_of_mem hm,hn⟩,hit⟩
  · rintro ⟨j,hj,hit⟩
    obtain ⟨mem,norm⟩ := (keep j).mp hj
    obtain ⟨μ,hm,rfl⟩ := List.mem_map.mp mem
    exact ⟨μ,hm,norm,hit⟩

end Tamarin.Rewriting.VariantJoin.Select
