import Tamarin.VariableElimination
import Tamarin.HomogeneousContract
import Tamarin.ResidualSearch

/-! Lift a solver for abstract equations through arbitrary sorted term operands.
A matrix column denotes a whole operand. A branch equates each column image
with that operand, keeping a single residual conjunction for the entire query. -/
namespace Tamarin.OperandAbstraction

variable {sig : Signature}

def residual (columns : List Variable) (operands branch : Substitution sig) : Problem sig :=
  columns.map fun v => ⟨branch.image v, operands.image v⟩

private theorem residual_iff (cols : List Variable) (θ σ δ : Substitution sig) :
    (residual cols θ σ).Solves δ ↔
      ∀ v ∈ cols, EquivB (δ.apply (σ.image v)) (δ.apply (θ.image v)) := by
  constructor
  · intro h v hv
    exact h _ (List.mem_map_of_mem hv)
  · intro h e he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact h v hv

def InOperand (cols : List Variable) (θ : Substitution sig) (w : Variable) : Prop :=
  ∃ v ∈ cols, (θ.image v).Occurs w

private theorem occurs_in_operand (q : Problem sig) (cols : List Variable) (θ : Substitution sig)
    (live : ∀ v, q.Occurs v → v ∈ cols) {w} (hw : (q.substitute θ).Occurs w) :
    InOperand cols θ w := by
  obtain ⟨e, he, hw⟩ := hw
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp he
  rcases hw with hl | hr
  · obtain ⟨v, hv, hw⟩ := θ.occurs_in_image original.lhs w hl
    exact ⟨v, live v ⟨original, member, .inl hv⟩, hw⟩
  · obtain ⟨v, hv, hw⟩ := θ.occurs_in_image original.rhs w hr
    exact ⟨v, live v ⟨original, member, .inr hv⟩, hw⟩

/-- Branch witnesses must have names disjoint from variables inside *all*
operands, including variables absent from the surface AC equation. -/
def Observed (cols : List Variable) (θ : Substitution sig) (pending : Problem sig) (w : Variable) :=
  InOperand cols θ w ∨ pending.Occurs w

def Separated (cols : List Variable) (θ σ : Substitution sig) (pending : Problem sig) : Prop :=
  ∀ v ∈ cols, ∀ w, (σ.image v).Occurs w → ¬ Observed cols θ pending w

private theorem solves_append (a b : Problem sig) (ρ : Substitution sig) :
    (a ++ b).Solves ρ ↔ a.Solves ρ ∧ b.Solves ρ := by
  simp [Problem.Solves, or_imp, forall_and]

private theorem occurs_append (a b : Problem sig) (w : Variable) :
    (a ++ b).Occurs w ↔ a.Occurs w ∨ b.Occurs w := by
  simp [Problem.Occurs, or_and_right, exists_or]

private noncomputable def combine (useLeft : Variable → Prop) (a b : Substitution sig) :
    Substitution sig := by
  classical
  exact {
    image := fun v => if useLeft v then a.image v else b.image v
    support := a.support ++ b.support
    sorted := by intro v; split <;> first | exact a.sorted v | exact b.sorted v
    outside := by
      intro v hv
      simp only [List.mem_append, not_or] at hv
      simp [a.outside v hv.1, b.outside v hv.2] }

private theorem branch_sound (q pending : Problem sig) (cols : List Variable) (θ σ δ : Substitution sig)
    (live : ∀ v, v ∈ cols ↔ q.Occurs v) (solution : q.Solves σ)
    (hδ : (residual cols θ σ ++ pending).Solves δ) : (q.substitute θ ++ pending).Solves δ := by
  obtain ⟨constraints, rest⟩ := (solves_append ..).mp hδ
  apply (solves_append ..).mpr
  refine ⟨?_, rest⟩
  have h := (residual_iff ..).mp constraints
  apply (q.solves_substitute_iff θ δ).mpr
  exact q.solves_instance solution ⟨δ, fun v hv => (h v ((live v).mpr hv)).symm⟩

/-- Extend a particular solution while preserving any kept range variables.
Only slots used in the current branch need to be separate from these variables. -/
private theorem extend_solution (q pending : Problem sig) (cols : List Variable) (θ : Substitution sig)
    (live : ∀ v, v ∈ cols ↔ q.Occurs v) (branches : List (Substitution sig))
    (outer : CompleteSet q branches) (kept : Variable → Prop)
    (includes : ∀ w, Observed cols θ pending w → kept w)
    (apart : ∀ σ ∈ branches, ∀ v ∈ cols, ∀ w, (σ.image v).Occurs w → ¬ kept w)
    (ρ : Substitution sig) (hρ : (q.substitute θ ++ pending).Solves ρ) :
    ∃ σ ∈ branches, ∃ δ, (residual cols θ σ ++ pending).Solves δ ∧
      ∀ w, kept w → δ.image w = ρ.image w := by
  obtain ⟨hρ, rest⟩ := (solves_append ..).mp hρ
  obtain ⟨σ, hσ, ε, he⟩ := outer.covers _ ((q.solves_substitute_iff θ ρ).mp hρ)
  classical
  let δ := combine kept ρ ε
  have keep (w) (hw : kept w) : δ.image w = ρ.image w := by
    simp [δ, combine, hw]
  have agree (v) (hv : v ∈ cols) : δ.apply (θ.image v) = ρ.apply (θ.image v) := by
    apply Term.subst_eq_of_agree
    intro w hw
    exact keep _ (includes _ (.inl ⟨v, hv, hw⟩))
  have hr : (residual cols θ σ).Solves δ := by
    apply (residual_iff ..).mpr
    intro v hv
    have witness : δ.apply (σ.image v) = ε.apply (σ.image v) := by
      apply Term.subst_eq_of_agree
      intro w hw
      simp [δ, combine, apart σ hσ v hv w hw]
    rw [witness, agree v hv]
    exact (he v ((live v).mp hv)).symm
  have hp : pending.Solves δ := by
    apply pending.solves_instance rest
    refine ⟨Substitution.identity, fun w hw => ?_⟩
    change EquivB (δ.image w) (Substitution.identity.apply (ρ.image w))
    rw [keep w (includes w (.inr hw)), Substitution.apply_identity]
    exact .refl _
  exact ⟨σ, hσ, δ, (solves_append ..).mpr ⟨hr, hp⟩, keep⟩

/-- The residual solver can use any search order or algorithm. Each branch
gets its own witnesses. One factorization must cover all original variables,
even when several operands contain the same variable. Output restriction and
range renaming can then use FreshAnswer.reify_complete. -/
theorem complete (q pending : Problem sig) (cols : List Variable) (θ : Substitution sig)
    (live : ∀ v, v ∈ cols ↔ q.Occurs v) (branches : List (Substitution sig))
    (outer : CompleteSet q branches)
    (apart : ∀ σ ∈ branches, Separated cols θ σ pending)
    (answers : Substitution sig → List (Substitution sig))
    (inner : ∀ σ ∈ branches, CompleteSet (residual cols θ σ ++ pending) (answers σ)) :
    CompleteSet (q.substitute θ ++ pending) (branches.flatMap answers) := by
  constructor
  · intro δ hδ
    obtain ⟨σ, hσ, hm⟩ := List.mem_flatMap.mp hδ
    exact branch_sound q pending cols θ σ δ live (outer.sound σ hσ) ((inner σ hσ).sound δ hm)
  · intro ρ hρ
    obtain ⟨σ, hσ, δ, hd, keep⟩ := extend_solution q pending cols θ live branches outer
      (Observed cols θ pending) (fun _ h => h) apart ρ hρ
    obtain ⟨τ, hτ, η, hi⟩ := (inner σ hσ).covers _ hd
    refine ⟨τ, List.mem_flatMap.mpr ⟨σ, hσ, hτ⟩, η, ?_⟩
    intro w hw
    have obs := ((occurs_append ..).mp hw).imp
      (occurs_in_operand q cols θ (fun v => (live v).mpr)) id
    rw [← keep w obs]
    apply hi
    apply (occurs_append ..).mpr
    apply obs.imp _ id
    rintro ⟨v, hv, hwv⟩
    exact ⟨_, List.mem_map_of_mem hv, Or.inr hwv⟩

/-! Interpret the actual numeric arm. Malformed or empty rows cannot supply
residual equations. The list of column names is only a semantic decoding. -/
open ACSystem Homogeneous

def decodeImage (f : sig.ACSym) (w : UInt64 → Variable) (arm : Arm) (i : Nat) :
    Option (Term sig) := do
  let row ← arm[i]?
  let x :: xs := row.toList.map w | none
  return (Side.mk x xs).term f

def decodeResidual {f : sig.ACSym} {rows : List ACSystem.Row} {n}
    (fr : Frame f rows n) (θ : Substitution sig) (w : UInt64 → Variable) (arm : Arm) :
    Option (Problem sig) :=
  (List.finRange n).mapM fun (i : Fin n) => do return ⟨← decodeImage f w arm i, θ.image (fr.names i)⟩

private theorem image_spec {f : sig.ACSym} {rows : List ACSystem.Row} {n}
    {fr : Frame f rows n} {w : UInt64 → Variable} {arm σ}
    (rep : Represents fr w arm σ) (i : Fin n) :
    decodeImage f w arm i = some (σ.image (fr.names i)) ∧
    ∀ z, (σ.image (fr.names i)).Occurs z → ∃ j, w j = z := by
  obtain ⟨x, xs, entry, val⟩ := rep.2 i
  cases h : arm[i.val]? with
  | none => simp [h] at entry
  | some row =>
    simp [h] at entry
    constructor
    · simp [decodeImage, h, entry, val]
    · intro z hz
      rw [val] at hz
      have mem := (Side.occurs_iff ⟨x, xs⟩ f z).mp hz
      change z ∈ x :: xs at mem
      rw [← entry] at mem
      obtain ⟨j, _, hj⟩ := List.mem_map.mp mem
      exact ⟨j, hj⟩

/-- The numeric backend's existing contract already suffices for compounds.
Every emitted arm must have a complete residual solution set before the
concatenation can be published. This statement quantifies over decoders and
residual solvers and uses only the actual packet to construct the residuals. -/
def PacketLifting (run : UInt64 → Matrix → Option Answers) : Prop :=
  ∀ {sig : Signature} (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64) (fr : Frame f rows n.toNat)
    (m : Matrix) (_input : readRows n.toNat m.toList = some (rows.map (ACBasis.encode fr.names)))
    (out : Answers) (_result : run n m = some out)
    (θ : Substitution sig) (pending : Problem sig) (w : UInt64 → Variable) (_inj : Function.Injective w)
    (_typed : ∀ j, (w j).sort = sig.acSort f)
    (_fresh : ∀ j, w j ∉ variables rows)
    (_separate : ∀ j, ¬ Observed ((List.finRange n.toNat).map fr.names) θ pending (w j))
    (solve : Problem sig → List (Substitution sig))
    (_checked : ∀ arm ∈ out.toList, ∀ p, decodeResidual fr θ w arm = some p → CompleteSet (p ++ pending) (solve (p ++ pending))),
    (∀ arm ∈ out.toList, (decodeResidual fr θ w arm).isSome) ∧
    CompleteSet ((problem f rows).substitute θ ++ pending)
      (out.toList.flatMap fun arm => ((decodeResidual fr θ w arm).toList.flatMap (fun p => solve (p ++ pending))))

private theorem packet_branches {run} (correct : Homogeneous.Correct run) (f : sig.ACSym)
    (rows : List ACSystem.Row) (n : UInt64) (fr : Frame f rows n.toNat) (m : Matrix)
    (input : readRows n.toNat m.toList = some (rows.map (ACBasis.encode fr.names)))
    (out : Answers) (result : run n m = some out) (θ : Substitution sig) (w : UInt64 → Variable)
    (inj : Function.Injective w) (typed : ∀ j, (w j).sort = sig.acSort f)
    (fresh : ∀ j, w j ∉ variables rows) :
    let cols := (List.finRange n.toNat).map fr.names
    ∃ pairs : List (Arm × Substitution sig), out = (pairs.map Prod.fst).toArray ∧
      CompleteSet (problem f rows) (pairs.map Prod.snd) ∧
      (∀ p ∈ pairs, decodeResidual fr θ w p.1 = some (residual cols θ p.2)) ∧
      ∀ p ∈ pairs, ∀ v ∈ cols, ∀ z, (p.2.image v).Occurs z → ∃ j, w j = z := by
  let cols := (List.finRange n.toNat).map fr.names
  obtain ⟨pairs, hout, reps, hc⟩ := correct.semantic f rows [] n fr m input out result
    w inj typed (by simpa using fresh)
  have decoded (p) (hp : p ∈ pairs) :
      decodeResidual fr θ w p.1 = some (residual cols θ p.2) := by
    have row := fun i => (image_spec (reps p hp) i).1
    unfold decodeResidual
    simp [row, residual, cols, List.map_map, Function.comp_def]
    apply List.mapM_pure (m := Option)
  refine ⟨pairs, hout, hc.mathematical, decoded, ?_⟩
  intro p hp v hv z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  exact (image_spec (reps p hp) i).2 z hz

theorem packet_complete {run} (correct : Homogeneous.Correct run) : PacketLifting run := by
  intro sig f rows n fr m input out result θ pending w inj typed fresh separate solve checked
  let cols := (List.finRange n.toNat).map fr.names
  have live (v) : v ∈ cols ↔ (problem f rows).Occurs v := by
    simpa [cols, occurs_iff_mem] using
      (show (∃ i, fr.names i = v) ↔ v ∈ variables rows from
        ⟨fun ⟨i, h⟩ => h ▸ fr.used i, fr.live v⟩)
  obtain ⟨pairs, hout, hc, decoded, slots⟩ :=
    packet_branches correct f rows n fr m input out result θ w inj typed fresh
  rw [hout, List.toList_toArray] at checked ⊢
  have cores := complete (problem f rows) pending cols θ live (pairs.map Prod.snd) hc
  have lift := cores (by
    intro σ hs v hv z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    obtain ⟨j, rfl⟩ := slots p hp v hv z hz
    exact separate j) (fun σ => solve (residual cols θ σ ++ pending)) (by
      intro σ hs
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      exact checked _ (List.mem_map_of_mem hp) _ (decoded p hp))
  constructor
  · intro arm ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    simp [decoded p hp]
  · simp only [List.flatMap_map] at lift ⊢
    have same : pairs.flatMap (fun p => (decodeResidual fr θ w p.1).toList.flatMap (fun p => solve (p ++ pending))) =
        pairs.flatMap (fun p => solve (residual cols θ p.2 ++ pending)) := by
      simp only [List.flatMap_def]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro p hp
      simp [decoded p hp, cols]
    rwa [same]

/-- Re-enter the numeric kernel from a worklist state. Old bindings survive
the split, even if an observed variable or its image has disappeared from
the pending equations. Freshness is local to the interpretation of slots. -/
def NestedLifting (run : UInt64 → Matrix → Option Answers) : Prop :=
  ∀ {s : Signature} (f : s.ACSym) (rows : List ACSystem.Row) (n : UInt64) (fr : Frame f rows n.toNat)
    (m : Matrix) (_input : readRows n.toNat m.toList = some (rows.map (ACBasis.encode fr.names)))
    (out : Answers) (_result : run n m = some out) (θ : Substitution s) (pending : Problem s)
    (observe : Variable → Prop) (bindings : Substitution s) (w : UInt64 → Variable)
    (_inj : Function.Injective w) (_typed : ∀ j, (w j).sort = s.acSort f)
    (_fresh : ∀ j, w j ∉ variables rows)
    (_separate : ∀ j, ¬ Observed ((List.finRange n.toNat).map fr.names) θ pending (w j))
    (_retained : ∀ j x, observe x → ¬ (bindings.image x).Occurs (w j)),
    (∀ arm ∈ out.toList, (decodeResidual fr θ w arm).isSome) ∧
    ∀ ρ, Residual.Denotes observe ((problem f rows).substitute θ ++ pending) bindings ρ ↔
      ∃ arm ∈ out.toList, ∃ p, decodeResidual fr θ w arm = some p ∧
        Residual.Denotes observe (p ++ pending) bindings ρ

theorem nested_lifting {run} (correct : Homogeneous.Correct run) : NestedLifting run := by
  intro s f rows n fr m input out result θ pending observe bindings w inj typed fresh separate retained
  obtain ⟨pairs, hout, hc, decoded, slots⟩ :=
    packet_branches correct f rows n fr m input out result θ w inj typed fresh
  let cols := (List.finRange n.toNat).map fr.names
  have live (v) : v ∈ cols ↔ (problem f rows).Occurs v := by
    simpa [cols, occurs_iff_mem] using
      (show (∃ i, fr.names i = v) ↔ v ∈ variables rows from
        ⟨fun ⟨i, h⟩ => h ▸ fr.used i, fr.live v⟩)
  rw [hout, List.toList_toArray]
  constructor
  · rintro arm ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    simp [decoded p hp]
  · intro ρ
    constructor
    · rintro ⟨δ, hd, agree⟩
      let kept := fun v => Observed cols θ pending v ∨ ∃ x, observe x ∧ (bindings.image x).Occurs v
      obtain ⟨σ, hσ, ε, he, keep⟩ := extend_solution (problem f rows) pending cols θ live
        (pairs.map Prod.snd) hc kept (fun _ h => .inl h) (by
          rintro σ hm v hv z hz keep
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
          obtain ⟨j, rfl⟩ := slots p hp v hv z hz
          rcases keep with h | ⟨x, hx, h⟩
          · exact separate j h
          · exact retained j x hx h) δ hd
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσ
      refine ⟨p.1, List.mem_map_of_mem hp, _, decoded p hp, ε, he, ?_⟩
      intro x hx
      have same : ε.apply (bindings.image x) = δ.apply (bindings.image x) := by
        apply Term.subst_eq_of_agree
        exact fun v hv => keep v (.inr ⟨x, hx, hv⟩)
      rw [same]
      exact agree x hx
    · rintro ⟨arm, ha, q, hq, δ, hd, agree⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain rfl := Option.some.inj ((decoded p hp).symm.trans hq)
      exact ⟨δ, branch_sound _ _ _ _ _ _ live (hc.sound p.2 (List.mem_map_of_mem hp)) hd, agree⟩

end Tamarin.OperandAbstraction
