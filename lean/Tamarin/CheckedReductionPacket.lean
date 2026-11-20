import Tamarin.CheckedReductionWire
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

private theorem decodes_emit {d : Dictionary} {rs : Problem d.sig} {t u : Term d.sig}
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
    (kernel ds ns es root n = #[#[2]] ∧ definitions rs = false ∧ (admitted rs t n = false ∨
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
      cases hb : admitted rs t n with
      | false => exact .inr ⟨by simp [run,h,cert,hb],rfl,.inl rfl⟩
      | true =>
        have valid : (CheckedReduction.rangeBound rs ∧ TableDecrease.sorted rs) ∧ CheckedReduction.affordable rs (fuel rs t n) 100000 t := by
          simpa only [admitted,Bool.and_eq_true] using hb
        have bound := (CheckedReduction.rangeBound_iff _).mp valid.1.1
        cases hc : CheckedReduction.run rs (fuel rs t n) t with
        | none => exact .inr ⟨by simp [run,h,cert,hb,hc],rfl,.inr rfl⟩
        | some u =>
          have reply := CheckedReduction.correct bound hc
          exact .inl ⟨u,by simpa [run,h,cert,hb,hc] using decodes_emit h bound reply,reply⟩

/-- On node-decreasing canonical presentations the runtime fuel is already
sufficient regardless of the fallback budget. -/
theorem measured_completes {s : Signature} (rs : Problem s) [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] (ok : TableDecrease.decreasing rs)
    (canonical : CanonicalPresentation (ruleRoot rs)) (t : Term s) (n : UInt64) :
    ∃ u, CheckedReduction.run rs (fuel rs t n) t = some u :=
  CheckedReduction.completes (TableDecrease.bound ok) canonical FiniteOccurs.nodes
    (TableDecrease.step_lt ok) _ _ (by simp [fuel,TableDecrease.budget,ok])

end Tamarin.CheckedReductionWire
