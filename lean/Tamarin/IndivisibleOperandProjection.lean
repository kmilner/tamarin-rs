import Tamarin.IndivisibleOperands

namespace Tamarin.IndivisibleOperands
open ACSystem ACBasis Homogeneous OperandBatch ProjectedBindings
variable {sig : Signature}

/-- Bit i always denotes the original column i, irrespective of solver ordering. -/
def wordMask (width bits : UInt64) (i : Fin width.toNat) : Bool := bits.toNat.testBit i.val

/-- Numeric certificate for an independently budgeted masked search. The
complete unfiltered family serves only as a mathematical reference. -/
def Emitted (width bits : UInt64) (m : Matrix) (raw : Answers) : Prop :=
  ∃ rs, readRows width.toNat m.toList = some rs ∧ (generate rs).length ≤ 64 ∧
    raw = (emit (generate rs)).filter (keeps (wordMask width bits))

private def specSolve (width : UInt64) (m : Matrix) : Option Answers := do
  let rs ← readRows width.toNat m.toList
  let gs := generate rs
  guard (gs.length ≤ 64)
  return emit gs

private theorem spec_correct : Homogeneous.Correct specSolve where
  malformed _ _ bad := by simp [specSolve,bad]
  completes width m admitted := by
    obtain ⟨_,_,_,rs,read,_,size⟩ := admitted
    have small : (generate rs).length ≤ 64 := size.elim
      (fun h => Nat.le_trans h.1 (by decide : 12 ≤ 64)) And.left
    simp [specSolve,read,small,guard]
  semantic f rows avoid n fr m input out result w inj typed fresh := by
    let rs := rows.map (encode fr.names)
    by_cases size : (generate (rows.map (encode fr.names))).length ≤ 64
    · have e : emit (generate rs) = out := by simpa [specSolve,input,guard,rs,size] using result
      rw [←e]
      exact emit_correct f rows avoid fr _ (generate_correct _) size w inj typed fresh
    · simp [specSolve,input,guard,size,failure] at result

/-- Raw operand reconciliation remains complete before any ordinal names
are allocated, including searches whose full mathematical packet exceeds
the unmasked kernel's budget. -/
theorem interprets
    [DecidableEq sig.ACSym] (f : sig.ACSym) (width bits : UInt64)
    (rows : List (OperandBatch.Row width.toNat)) (used : ∀ i, i ∈ OperandBatch.used rows)
    (term : Fin width.toNat → Term sig) (typed : ∀ i, HasSort (term i) (sig.acSort f))
    (sound : SoundMask f term (wordMask width bits))
    {selected : Problem sig} (layout : Represents f term rows selected)
    (pending original : Problem sig) (partition : original.Perm (selected ++ pending))
    (sidesOK : OperandCounts.Admitted width (sides rows))
    (nontrivial : GraphUnification.Nontrivial (OperandUnification.matrix width (sides rows)).toList)
    {raw : Answers} (emitted : Emitted width bits (OperandUnification.matrix width (sides rows)) raw)
    (observe : Variable → Prop) (bindings : Substitution sig) :
    ProjectedOperands.Interprets f rows used term typed pending original raw observe bindings := by
  obtain ⟨numeric,readMatrix,small,filtered⟩ := emitted
  let full := emit (generate numeric)
  have source : specSolve width (OperandUnification.matrix width (sides rows)) = some full := by
    simp [specSolve,readMatrix,small,guard,full]
  let bridge := OperandUnification.run_refines OperandCounts.run_correct specSolve
  have ran := (bridge width (sides rows) full).mpr ⟨sidesOK,nontrivial,source⟩
  intro base w wi ws wf ap af retained
  let fr := frame base f rows used
  let decode := OperandAbstraction.decodeResidual fr (operands base f term typed) w
  have split := OperandBatch.nested base bridge (OperandAbstraction.nested_lifting spec_correct)
    f rows used term typed layout pending original partition ran observe bindings w wi ws wf ap af retained
  have kept (a : Arm) (_ : a ∈ full.toList) (q) (h : decode a = some q) (δ) (sol : q.Solves δ) :
      keeps (wordMask width bits) a = true := by
    apply keeps_of_reconciled fr _ w _ _ h sol
    intro i marked
    simpa only [fr,frame,operand_at] using sound i marked
  have stream : raw.toList = full.toList.filter (keeps (wordMask width bits)) := by
    rw [filtered]; simp [full]
  rw [stream]
  constructor
  · intro a ha
    exact split.1 a (List.mem_filter.mp ha).1
  · intro ρ
    exact (split.2 ρ).trans (filter_denotes full.toList decode _ kept pending observe bindings ρ).symm

/-- How a masked success is read after compaction. The caller supplies fresh
names only for ordinals in the filtered packet. Sparse, permuted or repeated
original witness identifiers need no separate allocation. -/
theorem projected {project : AnswerProjection.Kernel} (proj : AnswerProjection.Correct project)
    [DecidableEq sig.ACSym] (f : sig.ACSym) (width bits : UInt64)
    (rows : List (OperandBatch.Row width.toNat)) (used : ∀ i, i ∈ OperandBatch.used rows)
    (term : Fin width.toNat → Term sig) (typed : ∀ i, HasSort (term i) (sig.acSort f))
    (sound : SoundMask f term (wordMask width bits))
    {selected : Problem sig} (layout : Represents f term rows selected)
    (pending original : Problem sig) (partition : original.Perm (selected ++ pending))
    (sidesOK : OperandCounts.Admitted width (sides rows))
    (nontrivial : GraphUnification.Nontrivial (OperandUnification.matrix width (sides rows)).toList)
    {raw out : Answers} (emitted : Emitted width bits (OperandUnification.matrix width (sides rows)) raw)
    (projected : project width raw = some out)
    (observed : List Variable) (bindings : Substitution sig) (name : UInt64 → Variable) (order : Order)
    (inj : ∀ i ∈ ordinals out, ∀ j ∈ ordinals out, name i = name j → i = j)
    (sorts : ∀ j ∈ ordinals out, (name j).sort = sig.acSort f)
    (fresh : ∀ j ∈ ordinals out, name j ∉ ProjectedOperands.occupied term pending observed bindings) :
    let read := ProjectedOperands.readArm term f name order
    (∀ a ∈ out.toList, (read a).isSome) ∧
    ∀ ρ, Residual.Denotes (· ∈ observed) original bindings ρ ↔
      ∃ a ∈ out.toList, ∃ q, read a = some q ∧ Residual.Denotes (· ∈ observed) (q ++ pending) bindings ρ := by
  exact ProjectedOperands.project_family proj f width rows used term typed pending original projected
    observed bindings (interprets f width bits rows used term typed sound layout pending original partition
      sidesOK nontrivial emitted (· ∈ observed) bindings) name order inj sorts fresh

end Tamarin.IndivisibleOperands
