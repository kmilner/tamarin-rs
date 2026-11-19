import Tamarin.OperandBatch
import Tamarin.ProjectedBindings

/-! Decode the tagged packet into actual residual equations. The first word
looks up a full operand; only subsequent words are local witness ordinals. -/
namespace Tamarin.ProjectedOperands
open ACSystem Homogeneous OperandBatch ProjectedBindings
variable {sig : Signature} {n : Nat}

def readRow (term : Fin n → Term sig) (f : sig.ACSym) (name : UInt64 → Variable)
    (order : Order) (row : Array UInt64) : Option (Equation sig) := do
  let tag :: rest := row.toList | none
  let operand ← (List.ofFn term)[tag.toNat]?
  let image ← ACRepresentation.decode f ((order.arrange (rest.map name)).map Term.var)
  return ⟨image, operand⟩

def readArm (term : Fin n → Term sig) (f : sig.ACSym) (name : UInt64 → Variable)
    (order : Order) (a : Arm) : Option (Problem sig) := a.toList.mapM (readRow term f name order)

private theorem mapM_related {α} (is : List α) (u v : α → Option (Equation sig))
    (h : ∀ i ∈ is, ∃ e d, u i = some e ∧ v i = some d ∧
      ∀ δ : Substitution sig, EquivB (δ.apply e.lhs) (δ.apply e.rhs) ↔
        EquivB (δ.apply d.lhs) (δ.apply d.rhs)) :
    ∃ p q : Problem sig, is.mapM u = some p ∧ is.mapM v = some q ∧ ∀ δ, p.Solves δ ↔ q.Solves δ := by
  induction is with
  | nil => exact ⟨[],[],rfl,rfl,fun _ => Iff.rfl⟩
  | cons i is ih =>
    obtain ⟨e,d,heu,hdv,eq⟩ := h i (by simp)
    obtain ⟨p,q,hp,hq,tail⟩ := ih (fun i hmem => h i (List.mem_cons_of_mem _ hmem))
    refine ⟨e::p,d::q,by simp [heu,hp],by simp [hdv,hq],fun δ => ?_⟩
    change (∀ e ∈ _::_, _) ↔ (∀ e ∈ _::_, _)
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_congr (eq δ) (tail δ)

private theorem arm_related (f : sig.ACSym) {a : Arm} {n : Nat} (width : a.size = n) (fits : n < UInt64.size)
    (term : Fin n → Term sig) (name w : UInt64 → Variable) (rank : UInt64 → UInt64) (order : Order)
    (shape : ∀ row ∈ a.toList, row ≠ #[])
    (agree : ∀ row ∈ a.toList, ∀ j ∈ row.toList, name (rank j) = w j)
    (typed : ∀ row ∈ a.toList, ∀ j ∈ row.toList, (w j).sort = sig.acSort f) :
    let raw := (List.finRange n).mapM (fun i : Fin n => do
      return (⟨← OperandAbstraction.decodeImage f w a i.val, term i⟩ : Equation sig))
    ∃ p q : Problem sig, readArm term f name order (AnswerProjection.tagArm rank a) = some p ∧
      raw = some q ∧ ∀ δ, p.Solves δ ↔ q.Solves δ := by
  subst n
  let src (i : Fin a.size) := #[i.val.toUInt64] ++ a[i].map rank
  have rows : (AnswerProjection.tagArm rank a).toList = (List.finRange a.size).map src := by
    simp only [AnswerProjection.tagArm, Array.toList_ofFn, List.finRange, List.map_ofFn, Function.comp_def, src]
  simp only [readArm, rows, List.mapM_map]
  apply mapM_related
  intro i _
  have hm : a[i] ∈ a.toList := by simp
  have same : (a[i].toList.map (fun j => name (rank j))) = a[i].toList.map w :=
    List.map_congr_left (agree _ hm)
  have hi : i.val.toUInt64.toNat = i.val := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt fits)
  cases split : (a[i].toList.map w) with
  | nil => exact False.elim (shape _ hm (by simpa using split))
  | cons x xs =>
    obtain ⟨t,ht,_,he⟩ := ProjectedBindings.decode_order f order x xs (by
      intro v hv; rw [← split] at hv
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      exact typed _ hm j hj)
    simp only [Fin.getElem_fin] at same split
    refine ⟨⟨t,term i⟩,⟨(ACSystem.Side.mk x xs).term f,term i⟩,?_,?_,?_⟩
    · simp [src, readRow, hi, same, split, ht, List.map_map, Function.comp_def]
    · simp [OperandAbstraction.decodeImage, i.isLt, split]
    · intro δ
      exact ⟨fun h => (he.subst δ.image).symm.trans h, fun h => (he.subst δ.image).trans h⟩

/-- Exactly the variables the local name allocator has to avoid. This
includes variables that now occur only in an accumulated image. -/
def occupied (term : Fin n → Term sig) (pending : Problem sig)
    (observed : List Variable) (bindings : Substitution sig) : List Variable :=
  (List.ofFn term).flatMap Term.variables ++ pending.variables ++
    observed.flatMap (fun v => (bindings.image v).variables)

/-- Decoding every completed arm preserves precisely the original worklist solutions.
The caller supplies term identities and unused names for live ordinals. No virtual
column names, raw-slot assignment, or comparison with an abstract matrix is a premise. -/
def Correct (run : OperandUnification.Kernel) (project : AnswerProjection.Kernel) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (f : s.ACSym) (width : UInt64)
    (rows : List (OperandBatch.Row width.toNat)), (∀ i, i ∈ used rows) →
    ∀ (term : Fin width.toNat → Term s), (∀ i, HasSort (term i) (s.acSort f)) →
    ∀ {selected : Problem s}, OperandBatch.Represents f term rows selected →
    ∀ (pending original : Problem s), original.Perm (selected ++ pending) →
    ∀ raw, run width (sides rows) = some raw → ∀ out, project width raw = some out →
    ∀ (observed : List Variable) (bindings : Substitution s) (name : UInt64 → Variable) (order : Order),
    (∀ i ∈ ordinals out, ∀ j ∈ ordinals out, name i = name j → i = j) →
    (∀ j ∈ ordinals out, (name j).sort = s.acSort f) →
    (∀ j ∈ ordinals out, name j ∉ occupied term pending observed bindings) →
    (∀ a ∈ out.toList, (readArm term f name order a).isSome) ∧
    ∀ ρ, Residual.Denotes (· ∈ observed) original bindings ρ ↔
      ∃ a ∈ out.toList, ∃ q, readArm term f name order a = some q ∧
        Residual.Denotes (· ∈ observed) (q ++ pending) bindings ρ

theorem correct {run solve project} (bridge : OperandUnification.Refines run solve)
    (kernel : OperandAbstraction.NestedLifting solve) (proj : AnswerProjection.Correct project) :
    Correct run project := by
  intro sig _ f width rows allUsed term typed selected layout pending original partition raw ran
    out hp observed bindings name order inj sorts fresh
  obtain ⟨adm,rfl⟩ := (proj ..).mp hp
  let rank := AnswerProjection.rank raw
  let concrete (j) := name (rank j)
  let names := (FactoredAC.slots raw).map concrete
  let base := VariablePermutation.freshBound names
  let avoid := occupied term pending observed bindings
  let cols := variables (abstractRows base f rows)
  let fr := frame base f rows allUsed
  have live {j} (hj : j ∈ FactoredAC.slots raw) := ProjectedBindings.live_rank (rank := rank) hj
  have ghost {j} (hj : j ∈ FactoredAC.slots raw) : concrete j ∉ cols := by
    intro hv
    obtain ⟨i, hi⟩ := fr.live _ hv
    have lt := VariablePermutation.lt_freshBound names _ (List.mem_map_of_mem (f := concrete) hj)
    change (concrete j).id < base at lt
    have eq : base + i.val = (concrete j).id := congrArg Variable.id hi
    omega
  obtain ⟨w,eq,wi,ws,wf⟩ := FactoredAC.extend_slots (FactoredAC.slots raw) (cols ++ avoid) _
    concrete (fun i hi j hj e => AnswerProjection.rank_injective adm hi hj (inj _ (live hi) _ (live hj) e))
    (fun j hj => sorts _ (live hj))
    (by intro j hj; exact fun h => (List.mem_append.mp h).elim (ghost hj) (fresh _ (live hj)))
  have apart (j) : w j ∉ occupied term pending observed bindings :=
    fun h => wf j (List.mem_append_right _ h)
  have split := OperandBatch.nested base bridge kernel f rows allUsed term typed layout pending original
    partition ran (· ∈ observed) bindings w wi ws (fun j h => wf j (List.mem_append_left _ h))
    (by intro j i h; apply apart j; simp only [occupied, List.mem_append, List.mem_flatMap,
          Term.mem_variables]; exact .inl (.inl ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,h⟩))
    (by intro j h; apply apart j; simp only [occupied, List.mem_append, Problem.mem_variables];
        exact .inl (.inr h))
    (by intro j v hv h; apply apart j; simp only [occupied,List.mem_append,List.mem_flatMap,Term.mem_variables];
        exact .inr ⟨v,hv,h⟩)
  let decode := OperandAbstraction.decodeResidual fr (operands base f term typed) w
  have related (a) (ha : a ∈ raw.toList) : ∃ p q : Problem sig,
      readArm term f name order (AnswerProjection.tagArm rank a) = some p ∧
      decode a = some q ∧ ∀ δ, p.Solves δ ↔ q.Solves δ := by
    have member {r : Array UInt64} (hr : r ∈ a.toList) {j} (hj : j ∈ r.toList) :
        j ∈ FactoredAC.slots raw :=
      List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨r,hr,hj⟩⟩
    have h := arm_related f (adm.1.2.2 a ha).1 width.toNat_lt_size term name w rank order
      (adm.1.2.2 a ha).2 (fun r hr j hj => (eq j (member hr hj)).symm) (fun _ _ j _ => ws j)
    simpa only [decode, fr, OperandAbstraction.decodeResidual, frame, OperandBatch.operand_at] using h
  simp only [Array.toList_map, List.mem_map] at *
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨_,_,hp,_,_⟩ := related a ha
    change (readArm term f name order (AnswerProjection.tagArm rank a)).isSome
    rw [hp]; rfl
  · intro ρ
    rw [split.2]
    constructor
    · rintro ⟨a,ha,q,hq,hd⟩
      obtain ⟨p,q',hp,hq',holds⟩ := related a ha
      obtain rfl := Option.some.inj (hq.symm.trans hq')
      refine ⟨_,⟨a,ha,rfl⟩,p,hp,?_⟩
      apply (Residual.equivalent _ (θ := bindings) (ρ := ρ) (p := p ++ pending) (q := q ++ pending) ?_).mpr hd
      intro δ
      simp only [Problem.Solves, List.mem_append, or_imp, forall_and]
      exact and_congr (holds δ) Iff.rfl
    · rintro ⟨_,⟨a,ha,rfl⟩,p,hp,hd⟩
      obtain ⟨p',q,hp',hq,holds⟩ := related a ha
      obtain rfl := Option.some.inj (hp.symm.trans hp')
      refine ⟨a,ha,q,hq,?_⟩
      apply (Residual.equivalent _ (θ := bindings) (ρ := ρ) (p := p ++ pending) (q := q ++ pending) ?_).mp hd
      intro δ
      simp only [Problem.Solves, List.mem_append, or_imp, forall_and]
      exact and_congr (holds δ) Iff.rfl

/-- Specialization to the allocator used while materializing nested residual equations. -/
theorem allocated {run project} (verified : Correct run project) (projection : AnswerProjection.Correct project)
    [DecidableEq sig.ACSym] (f : sig.ACSym) (width : UInt64) (rows : List (OperandBatch.Row width.toNat))
    (used : ∀ i, i ∈ OperandBatch.used rows) (term : Fin width.toNat → Term sig)
    (typed : ∀ i, HasSort (term i) (sig.acSort f)) {selected : Problem sig}
    (layout : OperandBatch.Represents f term rows selected) (pending original : Problem sig)
    (partition : original.Perm (selected ++ pending)) {raw out} (ran : run width (sides rows) = some raw)
    (projected : project width raw = some out) (observed : List Variable) (bs : Substitution sig)
    (reserved : UInt64 → Bool) {ws}
    (alloc : OrdinalAllocation.allocate reserved (AnswerProjection.keys raw).length = some ws)
    (make : UInt64 → Variable) (inj : Function.Injective make) (sort : ∀ i, (make i).sort = sig.acSort f)
    (fresh : ∀ i, make i ∈ occupied term pending observed bs → reserved i = true) (order : Order) :
    let read := readArm term f (OrdinalAllocation.nameAt make ws) order
    (∀ a ∈ out.toList, (read a).isSome) ∧
    ∀ ρ, Residual.Denotes (· ∈ observed) original bs ρ ↔
      ∃ a ∈ out.toList, ∃ q, read a = some q ∧ Residual.Denotes (· ∈ observed) (q ++ pending) bs ρ := by
  obtain ⟨distinct, sorts, disjoint⟩ := allocated_names projection projected reserved alloc make inj _ sort _ fresh
  exact verified f width rows used term typed layout pending original partition raw ran out projected
    observed bs _ order distinct sorts disjoint

end Tamarin.ProjectedOperands
