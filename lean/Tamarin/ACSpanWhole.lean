import Tamarin.ACSpanOverlap

namespace Tamarin.ACSpanWhole
open Whole ACBasis VariantOverlapGraph

/-- A nonzero integer multiple of the desired incidence row belongs to the
integer span of the observed rows. The arithmetic envelope is specified on
the input and the coefficients can have either sign. -/
def Linear (f : UInt64) (obs : Observations) (a b : Tree) : Prop :=
  let rs := obs.map (ACSpanGraph.profile f)
  let q := ACSpanGraph.profile f (a,b)
  let ks := ACSpanGraph.keys rs q
  let premises := rs.map (ACSpanGraph.row ks)
  let target := ACSpanGraph.row ks q
  SpanCertificate.Within premises target ∧ ∃ c, SpanCertificate.Valid premises target c

private theorem linear_completes {f obs a b} (floor : Linear f obs a b) :
    ACSpanGraph.linear f obs a b = true := (SpanCertificate.isSome_iff _ _ floor.1).mpr floor.2

/-- A linear consequence may determine the whole value directly, or all
the holes in the common constructor context around the two outputs. -/
def Admitted (raw : Observations) (x y : Tree) : Prop :=
  let obs := ACSpanOverlap.canonicalPairs raw
  let a := canonical x
  let b := canonical y
  let heads := ACSpanGraph.heads obs
  heads.length ≤ 8 ∧ ((∃ f ∈ heads, Linear f obs a b) ∨
    (let goals := (ACSpanOverlap.obligations a b).eraseDups
     goals.length ≤ 8 ∧ ∀ e ∈ goals, ∃ f ∈ heads, Linear f obs e.1 e.2))

private theorem admitted {obs a b} (h : Admitted obs a b) : ACSpanOverlap.extra obs a b = true := by
  obtain ⟨room,h⟩ := h
  simp only [ACSpanOverlap.extra,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,
    Bool.or_eq_true,List.all_eq_true]
  refine ⟨room,?_⟩
  rcases h with direct | parts
  · obtain ⟨f,hf,span⟩ := direct
    exact .inl ⟨f,hf,linear_completes span⟩
  · refine .inr ⟨parts.1,?_⟩
    intro e he
    obtain ⟨f,hf,span⟩ := parts.2 e he
    exact ⟨f,hf,linear_completes span⟩

def Required (candidate : Kernel) : Prop :=
  ∀ ds ns es obs a b, ds.size ≤ 32768 → MixedSizeGraph.GraphWithin ns es →
    Wire.decodeProblem ds ns es = some (obs ++ [(a,b)]) → Admitted obs a b → candidate ds ns es = true

theorem required : Required ACSpanOverlap.run := by
  intro ds ns es obs a b size graph dec h
  exact (runWith_iff ..).mpr ⟨size,graph,obs,a,b,dec,.inr (admitted h)⟩

theorem correct : Correct ACSpanOverlap.run where
  malformed := by
    intro ds ns es bad
    cases h : ACSpanOverlap.run ds ns es with
    | false => rfl
    | true => obtain ⟨_,_,_,_,_,read,_⟩ := (runWith_iff ..).mp h; simp [bad] at read
  semantic := by
    intro s I c ids left right a b ds ns es raw decoded rep yes
    obtain ⟨size,graph,obs,x,y,read,kind⟩ := (runWith_iff ..).mp yes
    cases decoded.symm.trans read
    rcases kind with simple | span
    · exact run_correct.semantic c ids left right a b ds ns es _ decoded rep
        ((run_structural ..).mpr ⟨size,graph,obs,x,y,read,simple⟩)
    · exact ACSpanOverlap.extra_agrees c ids left right a b rep span
  completes := fun _ _ _ obs a b sz g dec h => (runWith_iff ..).mpr ⟨sz,g,obs,a,b,dec,.inl h⟩

end Tamarin.ACSpanWhole
