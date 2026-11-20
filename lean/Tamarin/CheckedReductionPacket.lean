import Tamarin.GeneralReductionWire
import Tamarin.ReductionSignatureExtension
import Tamarin.TotalInputBounds
import Tamarin.TablePositions

namespace Tamarin.CheckedReductionWire
open TotalUnifyWire TotalUnifyWire.Packet MaudeOperations Rewriting

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → UInt64 → UInt64 → Array (Array UInt64)

def Decodes (d : Dictionary) (reply : Array (Array UInt64)) (u : Term d.sig) : Prop :=
  ∃ words tokens, reply = #[#[1],words] ∧ tokenize words.toList = some tokens ∧ execute d tokens [] = some [u]

private theorem fits_iff {d : Dictionary} (widths : ∀ f, d.sig.arity f < UInt64.size) (t : Term d.sig) :
    FieldsFit t ↔ ∀ v, t.Occurs v → v.id < UInt64.size := by
  induction t with
  | var v => simp [FieldsFit,Term.Occurs]
  | atom a => simp [FieldsFit,Term.Occurs]
  | free f xs ih => simp [FieldsFit,widths f,Term.Occurs,ih]; grind
  | comm f l r il ir | ac f l r il ir => simp [FieldsFit,Term.Occurs,il,ir]; grind

theorem decodes_emit {d : Dictionary} {rs : Problem d.sig} {t u : Term d.sig}
    {ds ns es root} (h : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩)
    (bound : ReferenceReduction.Bound rs) (reply : ReductionReply (ruleRoot rs) t u) :
    Decodes d (emit u) u := by
  obtain ⟨widths,observed⟩ := TableWire.input_fits h
  have source := observed t List.mem_cons_self
  have safe := (fits_iff widths u).mpr (fun v hv => (fits_iff widths t).mp source v
    (TableNarrowing.reducesUses bound reply.normalForm.1 v hv))
  obtain ⟨ts,hw⟩ := fits_write _ safe
  exact ⟨(ts.flatMap Token.words).toArray,ts,by simp [emit,hw],by simp [tokenize_words],write_executes u ts hw []⟩

/-- Every success decodes to a unique reachable normal form. A valid request
may defer only outside the certified class, when the bounded reference also
stops. Other algorithms may complete more requests. -/
structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es root n, TableWire.input ds ns es #[root] = none → kernel ds ns es root n = #[#[0]]
  valid : ∀ ds ns es root n d t rs, TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩ →
    (∃ u, Decodes d (kernel ds ns es root n) u ∧ ReductionReply (ruleRoot rs) t u) ∨
    (kernel ds ns es root n = #[#[2]] ∧ definitions rs = false ∧ destructors rs = false ∧ (admitted rs t n = false ∨
      CheckedReduction.run rs (fuel rs t n) t = none))

theorem correct : Correct run where
  malformed := fun _ _ _ _ _ h => by simp [run,h]
  valid := by
    intro ds ns es root n d t rs h
    cases cert : definitions rs with
    | true =>
      obtain ⟨cls,sorts⟩ := Bool.and_eq_true_iff.mp cert
      have reply := ConstantDefinitions.reductionReply cls sorts t
      exact .inl ⟨_,by simpa [run,h,cert] using decodes_emit h (ConstantDefinitions.bound cls) reply,reply⟩
    | false =>
      cases proj : destructors rs with
      | true =>
        obtain ⟨ok,sorts⟩ := Bool.and_eq_true_iff.mp proj
        have cls := (DestructorTable.accepts_iff rs).mp ok
        have reply := DestructorTable.reductionReply cls cls.decreasing sorts t
        exact .inl ⟨_,by simpa [run,h,cert,proj] using decodes_emit h (TableDecrease.bound cls.decreasing) reply,reply⟩
      | false =>
        cases hb : admitted rs t n with
        | false => exact .inr ⟨by simp [run,h,cert,proj,hb],rfl,rfl,.inl rfl⟩
        | true =>
          have valid : (CheckedReduction.rangeBound rs ∧ TableDecrease.sorted rs) ∧ CheckedReduction.affordable rs (fuel rs t n) 100000 t := by
            simpa only [admitted,Bool.and_eq_true] using hb
          have bound := (CheckedReduction.rangeBound_iff _).mp valid.1.1
          cases hc : CheckedReduction.run rs (fuel rs t n) t with
          | none => exact .inr ⟨by simp [run,h,cert,proj,hb,hc],rfl,rfl,.inr rfl⟩
          | some u =>
            have reply := CheckedReduction.correct bound hc
            exact .inl ⟨u,by simpa [run,h,cert,proj,hb,hc] using decodes_emit h bound reply,reply⟩


/-- On node-decreasing canonical presentations the runtime fuel is already
sufficient regardless of the fallback budget. -/
theorem measured_completes {s : Signature} (rs : Problem s) [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] (ok : TableDecrease.decreasing rs)
    (canonical : CanonicalPresentation (ruleRoot rs)) (t : Term s) (n : UInt64) :
    ∃ u, CheckedReduction.run rs (fuel rs t n) t = some u :=
  CheckedReduction.completes (TableDecrease.bound ok) canonical FiniteOccurs.nodes
    (TableDecrease.step_lt ok) _ _ (by simp [fuel,TableDecrease.budget,ok])

end Tamarin.CheckedReductionWire

namespace Tamarin.GeneralReductionWire
open Rewriting MaudeOperations TotalUnifyWire

def Answer (d : Dictionary) (rs : Problem d.sig) (t : Term d.sig) (wire : Array (Array UInt64)) : Prop :=
  ∃ u, CheckedReductionWire.Decodes d wire u ∧ ReductionReply (ruleRoot rs) t u ∧
    ∀ extra : Signature, ReductionReply (ruleRoot (SignatureExtension.query extra rs))
      (SignatureExtension.embed extra t) (SignatureExtension.embed extra u)

/-- Every range-restricted, settled query must return its unique endpoint or
report a genuine conflict. The semantic rewrite tree determines when this is
mandatory, independently of the kernel and its traversal order. -/
structure Correct (kernel : CheckedReductionWire.Kernel) : Prop where
  malformed : ∀ ds ns es root n, TableWire.input ds ns es #[root] = none → kernel ds ns es root n = #[#[0]]
  valid : ∀ ds ns es root n d t rs, TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩ →
    let wire := kernel ds ns es root n
    Answer d rs t wire ∨
      (wire = #[#[2]] ∧ (¬ ReferenceReduction.Bound rs ∨ CheckedReduction.Conflicting rs t)) ∨
      (wire = #[#[3]] ∧ ReferenceReduction.Bound rs ∧ ¬ CheckedReduction.Settled rs n.toNat t)

theorem correct : Correct run where
  malformed := fun _ _ _ _ _ h => by simp [run,h]
  valid := by
    intro ds ns es root n d t rs decoded
    cases ranged : CheckedReduction.rangeBound rs with
    | false => exact .inr (.inl ⟨by simp [run,decoded,ranged],
        .inl fun h => by simp [(CheckedReduction.rangeBound_iff _).mpr h] at ranged⟩)
    | true =>
      have bound := (CheckedReduction.rangeBound_iff _).mp ranged
      cases done : CheckedReduction.run rs n.toNat t with
      | some u =>
        have reply := CheckedReduction.correct bound done
        exact .inl ⟨u,by simpa [run,decoded,ranged,done] using CheckedReductionWire.decodes_emit decoded bound reply,
          reply,fun extra => SignatureExtension.reduction extra rs bound t u reply⟩
      | none =>
        cases conflict : CheckedReduction.ambiguous rs n.toNat t with
        | false =>
          refine .inr (.inr ⟨by simp [run,decoded,ranged,done,conflict],bound,fun settled => ?_⟩)
          rcases CheckedReduction.decides_settled bound settled with ⟨u,ok⟩ | clash
          · simp [done] at ok
          · simp [conflict] at clash
        | true => exact .inr (.inl ⟨by simp [run,decoded,ranged,done,conflict],
            .inr (CheckedReduction.ambiguous_sound bound _ _ conflict)⟩)

/-- Any two inequivalent normal forms force permanent rejection once the
stage covers the entire locally sort-preserving tree, regardless of which
branches a replacement algorithm visits first. -/
theorem Correct.rejects_conflict {kernel : CheckedReductionWire.Kernel} (ok : Correct kernel) {ds ns es root d t rs}
    (decoded : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (n : UInt64)
    (settled : CheckedReduction.Settled rs n.toNat t) (conflict : CheckedReduction.Conflicting rs t) :
    kernel ds ns es root n = #[#[2]] := by
  rcases ok.valid _ _ _ _ _ _ _ _ decoded with ⟨u,_,answer,_⟩ | ⟨stopped,_⟩ | ⟨_,_,pending⟩
  · obtain ⟨a,b,na,nb,ne⟩ := conflict
    exact (ne ((answer.unique a na).trans (answer.unique b nb).symm)).elim
  · exact stopped
  · exact (pending settled).elim

/-- Every sufficiently funded stage returns a unique reachable normal form,
including under arbitrary extension of the caller's signature. The sufficient
depth is the height of the actual rewrite relation, independent of the kernel. -/
theorem Correct.completes {kernel : CheckedReductionWire.Kernel} (ok : Correct kernel) {ds ns es root d t rs}
    (decoded : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (bound : ReferenceReduction.Bound rs)
    (canonical : CanonicalPresentation (ruleRoot rs)) (n : UInt64)
    (enough : ReductionHeight.height bound canonical.terminating t < n.toNat) :
    Answer d rs t (kernel ds ns es root n) := by
  rcases ok.valid _ _ _ _ _ _ _ _ decoded with answer | ⟨_,invalid | conflict⟩ | ⟨_,_,pending⟩
  · exact answer
  · exact (invalid bound).elim
  · obtain ⟨a,b,na,nb,ne⟩ := conflict
    obtain ⟨_,la,lb⟩ := canonical.confluent na.1 nb.1
    exact (ne ((normal_reduces_equiv la na.2.1).trans (normal_reduces_equiv lb nb.2.1).symm)).elim
  · exact (pending (CheckedReduction.settled_of_height bound canonical _ _ enough)).elim

end Tamarin.GeneralReductionWire
