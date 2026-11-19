import Tamarin.OneOpenPivot
import Tamarin.ResidualSearch

/-! An indivisible AC occurrence has one owner in the opposite product. The
owner can equal that occurrence or supply a nonempty remainder. Each child
keeps the rest of the conjunction and all accumulated observable bindings. -/
namespace Tamarin.ACOwnerPivot
open AtomicACPair Cancellation
variable {sig : Signature}

abbrev Query := OneOpenPivot.Query

/-- A pivot can occur anywhere among the selected side's factors. The
remaining factors form one nonempty fringe; its representation may reorder them. -/
theorem presentedOfFactors [DecidableEq sig.ACSym] (q : Query sig) (caller : Problem sig)
    (e : Equation sig) (layout : caller.Perm (e :: q.tail)) (u : Term sig) (us : List (Term sig))
    (fringe : EquivB (ACRepresentation.fold q.f u us) q.loose)
    (sides : ((ACRepresentation.flatten q.f e.lhs).Perm (q.rigid :: u :: us) ∧
              (ACRepresentation.flatten q.f e.rhs).Perm q.operands) ∨
             ((ACRepresentation.flatten q.f e.rhs).Perm (q.rigid :: u :: us) ∧
              (ACRepresentation.flatten q.f e.lhs).Perm q.operands)) : q.Presented caller := by
  have left (t : Term sig) (h : (ACRepresentation.flatten q.f t).Perm (q.rigid :: u :: us)) :
      EquivB t q.lhs :=
    (OneOpenPivot.Query.fromSlots q.f h rfl).trans (EquivB.ac_congr q.f (.refl _) fringe)
  have right (t : Term sig) (h : (ACRepresentation.flatten q.f t).Perm q.operands) :
      EquivB t q.rhs := OneOpenPivot.Query.fromSlots q.f h rfl
  exact ⟨e,layout,sides.imp (fun h => ⟨left _ h.1,right _ h.2⟩) (fun h => ⟨left _ h.1,right _ h.2⟩)⟩

/-- An arm names an occurrence in the opposite product, its complementary
product, and the equations passed to the continuation. A sharing arm can
allocate its own witness. -/
structure Arm (sig : Signature) where
  index : Nat
  rem : Term sig
  share : Bool
  witness : Variable
  work : Problem sig

namespace Arm
variable (q : Query sig) (a : Arm sig)

def equations : Problem sig :=
  if a.share then
    ⟨q.operand a.index,.ac q.f q.rigid (.var a.witness)⟩ ::
    ⟨q.loose,.ac q.f (.var a.witness) a.rem⟩ :: q.tail
  else ⟨q.rigid,q.operand a.index⟩ :: ⟨q.loose,a.rem⟩ :: q.tail

/-- Smart constructors may reorder or regroup either side of any equation. -/
inductive Aligned : Problem sig → Problem sig → Prop where
  | nil : Aligned [] []
  | cons {e t : Equation sig} {xs ys : Problem sig} :
    EquivB e.lhs t.lhs → EquivB e.rhs t.rhs → Aligned xs ys → Aligned (e :: xs) (t :: ys)

structure Reads (packet : OpenMatchSelect.Packet) : Prop where
  grouping : ∃ j js, a.index :: j :: js ∈ OpenMatchSelect.decoded packet ∧
    EquivB a.rem (ACRepresentation.fold q.f (q.operand j) (js.map q.operand))
  layout : ∃ actual, a.work.Perm actual ∧ Aligned actual (a.equations q)

private theorem grouped {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel)
    {n packet} (size : n.toNat = q.operands.length) (ran : kernel 1 n = some packet)
    (read : a.Reads q packet) : EquivB q.rhs (.ac q.f (q.operand a.index) a.rem) := by
  obtain ⟨j,js,mem,group⟩ := read.grouping
  exact (q.regroup (size ▸ ok.perm ran mem)).trans (.ac_congr _ (.refl _) group.symm)

private theorem placed {packet} (read : a.Reads q packet) (σ : Substitution sig) :
    a.work.Solves σ ↔ (a.equations q).Solves σ := by
  obtain ⟨actual,perm,eqs⟩ := read.layout
  have aligned {xs ys : Problem sig} (h : Aligned xs ys) :
      xs.Solves σ ↔ ys.Solves σ := by
    induction h with
    | nil => rfl
    | cons l r _ ih =>
      rw [ACPivot.Query.solves_cons,ACPivot.Query.solves_cons,ih]
      exact and_congr_left fun _ => ⟨fun eq => (l.subst σ.image).symm.trans (eq.trans (r.subst σ.image)),
        fun eq => (l.subst σ.image).trans (eq.trans (r.subst σ.image).symm)⟩
  rw [← aligned eqs]
  simp only [Problem.Solves,perm.mem_iff]

private def Owner (σ : Substitution sig) :=
  if a.share then EquivB (σ.apply (q.operand a.index)) (.ac q.f (σ.apply q.rigid) (σ.image a.witness))
  else EquivB (σ.apply q.rigid) (σ.apply (q.operand a.index))

private theorem solves {packet} (read : a.Reads q packet)
    (grouped : EquivB q.rhs (.ac q.f (q.operand a.index) a.rem)) (σ : Substitution sig) :
    a.work.Solves σ ↔ q.problem.Solves σ ∧ a.Owner q σ := by
  have group := grouped.subst σ.image
  rw [a.placed q read,OneOpenPivot.Query.problem,ACPivot.Query.solves_cons]
  cases hs : a.share <;> simp only [equations,Owner,hs,ite_false,ite_true,Bool.false_eq_true,
    ACPivot.Query.solves_cons]
  · constructor
    · rintro ⟨owner,rest,tail⟩
      exact ⟨⟨(EquivB.ac_congr q.f owner rest).trans group.symm,tail⟩,owner⟩
    · rintro ⟨⟨eq,tail⟩,owner⟩
      exact ⟨owner,EquivB.ac_cancel_left q.f ((eq.trans group).trans (.ac_congr _ owner.symm (.refl _))),tail⟩
  · constructor
    · rintro ⟨owner,rest,tail⟩
      exact ⟨⟨(EquivB.ac_congr q.f (.refl _) rest).trans
        ((EquivB.ac_assoc q.f _ _ _).symm.trans ((EquivB.ac_congr _ owner.symm (.refl _)).trans group.symm)),tail⟩,owner⟩
    · rintro ⟨⟨eq,tail⟩,owner⟩
      exact ⟨owner,EquivB.ac_cancel_left q.f ((eq.trans group).trans
        ((EquivB.ac_congr _ owner (.refl _)).trans (.ac_assoc _ _ _ _))),tail⟩

end Arm

/-- Valid continuations interpret a selector row. Every position has an
equality arm, and every position that can expand has a proper-sharing arm.
Equal owner terms may reuse the same arm. A common occurrence allows direct
cancellation using a single equality arm. -/
structure Decoding (q : Query sig) (packet : OpenMatchSelect.Packet) (arms : List (Arm sig))
    (expands : Nat → Prop) : Prop where
  reads : ∀ a ∈ arms, a.Reads q packet
  covers : (∀ i rest, i :: rest ∈ OpenMatchSelect.decoded packet → ∀ share : Bool,
    (share = true → expands i) → ∃ a ∈ arms, a.share = share ∧ EquivB (q.operand i) (q.operand a.index)) ∨
    ∃ a ∈ arms, a.share = false ∧ EquivB q.rigid (q.operand a.index)

private theorem alignedRefl (p : Problem sig) : Arm.Aligned p p := by
  induction p with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (.refl _) (.refl _) ih

private def canonicalArm (q : Query sig) (i j : Nat) (js : List Nat) (w : Variable) (share : Bool) : Arm sig :=
  let a : Arm sig := ⟨i,ACRepresentation.fold q.f (q.operand j) (js.map q.operand),share,w,[]⟩
  {a with work := a.equations q}

/-- Canonical interpretation without branch deduplication. The user of the
selector can instead prove its own decoding against the same contract. -/
def interpret (q : Query sig) (canShare : Nat → Bool) (w : Nat → Variable) : List Nat → List (Arm sig)
  | i :: j :: js =>
    (if canShare i then [false,true] else [false]).map (canonicalArm q i j js (w i))
  | _ => []

theorem canonical {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel)
    (q : Query sig) {n packet} (size : n.toNat = q.operands.length) (ran : kernel 1 n = some packet)
    (canShare : Nat → Bool) (w : Nat → Variable) :
    Decoding q packet ((OpenMatchSelect.decoded packet).flatMap (interpret q canShare w))
      (fun i => canShare i = true) := by
  constructor
  · intro a ha
    obtain ⟨row,hr,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨_,proof⟩ := q.readable ok size ran _ hr
    cases proof with
    | row i j js rem branch grouping placement =>
      obtain ⟨share,_,rfl⟩ := List.mem_map.mp ha
      exact ⟨⟨j,js,hr,.refl _⟩,_,.refl _,alignedRefl _⟩
  · left
    intro i rest hr share allowed
    obtain ⟨_,proof⟩ := q.readable ok size ran _ hr
    cases proof with
    | row i j js rem branch grouping placement =>
      refine ⟨canonicalArm q i j js (w i) share,List.mem_flatMap.mpr ⟨_,hr,List.mem_map.mpr ⟨share,?_,rfl⟩⟩,rfl,.refl _⟩
      cases share <;> cases h : canShare i <;> simp_all

private theorem findOwner (q : Query sig) (σ : Substitution sig) (atom : Atomic q.f q.rigid)
    (typed : ∀ b ∈ q.operands, HasSort b (sig.acSort q.f)) {expands : Nat → Prop}
    (eligible : ∀ i < q.operands.length, Atomic q.f (q.operand i) ∨ expands i)
    (sol : q.problem.Solves σ) :
    ∃ i < q.operands.length, EquivB (σ.apply q.rigid) (σ.apply (q.operand i)) ∨
      expands i ∧ ∃ t, HasSort t (sig.acSort q.f) ∧
        EquivB (σ.apply (q.operand i)) (.ac q.f (σ.apply q.rigid) t) := by
  have flat := flatten_equiv q.f (sol _ List.mem_cons_self)
  change (flatten q.f (.ac q.f (σ.apply q.rigid) (σ.apply q.loose))).Perm
    (flatten q.f (σ.apply (ACRepresentation.fold q.f q.first (q.second :: q.rest)))) at flat
  rw [flatten_ac,ACPivot.fold_factors] at flat
  have inv := ACPivot.locate q.f σ q.rigid [q.loose] q.operands atom typed (by simpa [ACPivot.factors,OneOpenPivot.Query.operands] using flat)
  obtain ⟨b,hb,mem,split⟩ := inv
  obtain ⟨i,hi,atIndex⟩ := List.getElem_of_mem (l := q.operands) hb
  have atI : q.operand i = b := by simp [OneOpenPivot.Query.operand,hi,atIndex]
  refine ⟨i,hi,?_⟩
  rcases eligible i hi with fixed | openSlot
  · exact .inl (ACPivot.fixed_owner fixed σ (atI ▸ mem))
  · rw [atI]
    exact split.imp EquivB.symm fun proper => ⟨openSlot,proper⟩

/-- The caller chooses each witness outside the pending equations and the
images of all accumulated bindings that it still observes. -/
def Fresh (q : Query sig) (a : Arm sig) (observed : Variable → Prop) (θ : Substitution sig) : Prop :=
  a.share = true → a.witness.sort = sig.acSort q.f ∧ ¬ q.problem.Occurs a.witness ∧
    ∀ v, observed v → ¬ (θ.image v).Occurs a.witness

private theorem extend (q : Query sig) (a : Arm sig) (share : a.share = true)
    (observed : Variable → Prop) (θ σ : Substitution sig) (fresh : Fresh q a observed θ)
    (sol : q.problem.Solves σ) (group : EquivB q.rhs (.ac q.f (q.operand a.index) a.rem))
    (t : Term sig) (ht : HasSort t (sig.acSort q.f))
    (owner : EquivB (σ.apply (q.operand a.index)) (.ac q.f (σ.apply q.rigid) t)) :
    ∃ δ, q.problem.Solves δ ∧ a.Owner q δ ∧ ∀ v, observed v → δ.apply (θ.image v) = σ.apply (θ.image v) := by
  obtain ⟨sort,absent,retained⟩ := fresh share
  let δ := RigidAllocation.Query.override σ a.witness t (sort ▸ ht)
  have same (v : Variable) (ne : v ≠ a.witness) : δ.image v = σ.image v := by
    simp [δ,RigidAllocation.Query.override,ne]
  have agree (u : Term sig) (h : ¬ u.Occurs a.witness) : δ.apply u = σ.apply u :=
    Term.subst_eq_of_agree _ _ _ fun v hv => same v (fun eq => h (eq ▸ hv))
  have solved : q.problem.Solves δ := by
    intro e he
    rw [agree e.lhs (fun h => absent ⟨e,he,.inl h⟩), agree e.rhs (fun h => absent ⟨e,he,.inr h⟩)]
    exact sol e he
  refine ⟨δ,solved,?_,fun v hv => agree _ (retained v hv)⟩
  simp only [Arm.Owner,share,ite_true]
  rw [agree (q.operand a.index) (fun h => absent ⟨_,List.mem_cons_self,.inr ((group.occurs_iff _).mpr (.inl h))⟩),
      agree q.rigid (fun h => absent ⟨_,List.mem_cons_self,.inl (.inl h)⟩)]
  simpa [δ,RigidAllocation.Query.override] using owner

/-- A completed split preserves the denotation of the entire caller state.
This includes callers with multiple open factors on either side, prior
bindings, or variables occurring on both sides and in other equations. -/
def Semantic (kernel : OpenMatchSelect.Kernel) : Prop :=
  ∀ {s : Signature} (q : Query s) {n packet}, n.toNat = q.operands.length → kernel 1 n = some packet →
    (∀ (canShare : Nat → Bool) (w : Nat → Variable),
      Decoding q packet ((OpenMatchSelect.decoded packet).flatMap (interpret q canShare w))
        (fun i => canShare i = true)) ∧
    ∀ (caller : Problem s), q.Presented caller → Atomic q.f q.rigid →
    (∀ b ∈ q.operands, HasSort b (s.acSort q.f)) →
    ∀ expands, (∀ i < q.operands.length, Atomic q.f (q.operand i) ∨ expands i) →
    ∀ arms, Decoding q packet arms expands →
    ∀ observed θ, (∀ a ∈ arms, Fresh q a observed θ) → ∀ ρ,
      Residual.Denotes observed caller θ ρ ↔ ∃ a ∈ arms, Residual.Denotes observed a.work θ ρ

theorem semantic {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel) : Semantic kernel := by
  intro s q n packet size ran
  refine ⟨canonical ok q size ran,?_⟩
  intro caller placed atom typed expands eligible arms rows observed θ fresh ρ
  have group a ha := Arm.grouped q a ok size ran (rows.reads a ha)
  have solves a ha := Arm.solves q a (rows.reads a ha) (group a ha)
  constructor
  · rintro ⟨σ,hσ,agree⟩
    have sol := (placed.solves q σ).mp hσ
    rcases rows.covers with covers | ⟨a,ha,kind,eq⟩
    · obtain ⟨i,hi,alt⟩ := findOwner q σ atom typed eligible sol
      obtain ⟨rest,mem⟩ := ok.prefixes [i] ran rfl (by simp) (by simpa [size] using hi)
      rcases alt with exactOwner | ⟨exp, t,ht,proper⟩
      · obtain ⟨a,ha,kind,same⟩ := covers i rest mem false (by simp)
        refine ⟨a,ha,σ,(solves a ha σ).mpr ⟨sol,?_⟩,agree⟩
        simpa only [Arm.Owner,kind,Bool.false_eq_true,ite_false,Substitution.apply] using exactOwner.trans (same.subst σ.image)
      · obtain ⟨a,ha,kind,same⟩ := covers i rest mem true (fun _ => exp)
        obtain ⟨δ,hd,own,kept⟩ := extend q a kind observed θ σ (fresh a ha) sol (group a ha) t ht
          ((same.subst σ.image).symm.trans proper)
        exact ⟨a,ha,δ,(solves a ha δ).mpr ⟨hd,own⟩,fun v hv => kept v hv ▸ agree v hv⟩
    · refine ⟨a,ha,σ,(solves a ha σ).mpr ⟨sol,?_⟩,agree⟩
      simpa only [Arm.Owner,kind,Bool.false_eq_true,ite_false,Substitution.apply] using eq.subst σ.image
  · rintro ⟨a,ha,σ,sol,agree⟩
    exact ⟨σ,(placed.solves q σ).mpr (((solves a ha σ).mp sol).1),agree⟩

end Tamarin.ACOwnerPivot
