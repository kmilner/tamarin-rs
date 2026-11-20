import Tamarin.CheckedReductionWire
import Tamarin.TotalInputBounds
import Tamarin.UniformReduction

namespace Tamarin.CheckedReductionWire
open TotalUnifyWire TotalUnifyWire.Packet MaudeOperations Rewriting

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → UInt64 → UInt64 → Array (Array UInt64)

def Decodes (d : Dictionary) (reply : Array (Array UInt64)) (u : Term d.sig) : Prop :=
  ∃ words tokens, reply = #[#[1],words] ∧ tokenize words.toList = some tokens ∧ execute d tokens [] = some [u]

private theorem step_scope {s : Signature} {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    {a b : Term s} (v : Variable) (st : Step (ruleRoot rs) a b) : b.Occurs v → a.Occurs v := by
  induction st with
  | root red =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := red
    intro live
    obtain ⟨w,fromRule,contains⟩ := (UniformReduction.occurs_apply ..).mp live
    exact (UniformReduction.occurs_apply ..).mpr ⟨w,bound r hr _ fromRule,contains⟩
  | free f xs i _ ih =>
    rintro ⟨j,hj⟩
    by_cases eq : j = i
    · subst j; exact ⟨_,ih (by simpa using hj)⟩
    · exact ⟨_,by simpa [eq] using hj⟩
  | ac_left _ _ _ ih | comm_left _ _ _ ih => exact fun h => h.imp ih id
  | ac_right _ _ _ ih | comm_right _ _ _ ih => exact fun h => h.imp id ih

theorem reduces_scope {s : Signature} {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    {a b : Term s} (path : Reduces (ruleRoot rs) a b) (v : Variable) : b.Occurs v → a.Occurs v := by
  apply RootNarrowing.reduction_invariant (fun z => z.Occurs v → a.Occurs v) _ _ path id
  · intro t u ih eq hit
    exact ih ((eq.occurs_iff v).mpr hit)
  · rintro t u ih ⟨_,_,before,st,after⟩ hit
    exact ih ((before.occurs_iff v).mpr (step_scope bound v st ((after.occurs_iff v).mpr hit)))

private theorem fits_iff {d : Dictionary} (widths : ∀ f, d.sig.arity f < UInt64.size) (t : Term d.sig) :
    FieldsFit t ↔ ∀ v, t.Occurs v → v.id < UInt64.size := by
  induction t with
  | var v => simp [FieldsFit,Term.Occurs]
  | atom a => simp [FieldsFit,Term.Occurs]
  | free f xs ih => simp [FieldsFit,widths f,Term.Occurs,ih]; grind
  | comm f l r il ir | ac f l r il ir => simp [FieldsFit,Term.Occurs,il,ir]; grind

private theorem input_fits {ds ns es root d rs t} (decoded : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) :
    (∀ f, d.sig.arity f < UInt64.size) ∧ FieldsFit t := by
  simp only [TableWire.input,Option.bind_eq_bind,Option.bind_eq_some_iff] at decoded
  obtain ⟨⟨_,ts⟩,dg,_,_,obs,ho,eq⟩ := decoded
  cases eq
  have h : ts[root.toNat]? = some t := by
    cases hx : ts[root.toNat]? with
    | none => simp [hx] at ho
    | some u => simpa [hx] using ho
  exact ⟨graph_widths dg,graph_fieldsFit dg _ (Array.mem_of_getElem? h)⟩

/-- A success must both decode and meet the public reduction contract.
An alternative implementation may complete more searches. CI requires
completion on all packets covered by the reference fuel and term format. -/
structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es root n, TableWire.input ds ns es #[root] = none → kernel ds ns es root n = #[#[0]]
  valid : ∀ ds ns es root n d t rs, TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩ →
    (∃ u, Decodes d (kernel ds ns es root n) u ∧ ReductionReply (ruleRoot rs) t u) ∨
    (kernel ds ns es root n = #[#[2]] ∧ (admitted rs t n = false ∨
      CheckedReduction.run rs (fuel rs t n) t = none))

theorem correct : Correct run where
  malformed := fun _ _ _ _ _ h => by simp [run,h]
  valid := by
    intro ds ns es root n d t rs h
    cases hb : admitted rs t n with
    | false =>
      exact .inr ⟨by simp [run,h,hb],.inl rfl⟩
    | true =>
      have valid : (CheckedReduction.rangeBound rs ∧ TableDecrease.sorted rs) ∧ CheckedReduction.affordable rs (fuel rs t n) 100000 t := by
        simpa only [admitted,Bool.and_eq_true] using hb
      have bound := (CheckedReduction.rangeBound_iff _).mp valid.1.1
      cases hc : CheckedReduction.run rs (fuel rs t n) t with
      | none => exact .inr ⟨by simp [run,h,hb,hc],.inr rfl⟩
      | some u =>
        have reply := CheckedReduction.correct bound hc
        obtain ⟨widths,source⟩ := input_fits h
        have safe := (fits_iff widths u).mpr (fun v hv => (fits_iff widths t).mp source v
          (reduces_scope bound reply.normalForm.1 v hv))
        obtain ⟨ts,hw⟩ := fits_write _ safe
        exact .inl ⟨u,⟨(ts.flatMap Token.words).toArray,ts,by simp [run,h,hb,hc,hw],
          by simp [tokenize_words],write_executes u ts hw []⟩,reply⟩

/-- On node-decreasing canonical presentations the runtime fuel is already
sufficient regardless of the fallback budget. -/
theorem measured_completes {s : Signature} (rs : Problem s) [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] (ok : TableDecrease.decreasing rs)
    (canonical : CanonicalPresentation (ruleRoot rs)) (t : Term s) (n : UInt64) :
    ∃ u, CheckedReduction.run rs (fuel rs t n) t = some u :=
  CheckedReduction.completes (TableDecrease.bound ok) canonical FiniteOccurs.nodes
    (TableDecrease.step_lt ok) _ _ (by simp [fuel,TableDecrease.budget,ok])

end Tamarin.CheckedReductionWire
