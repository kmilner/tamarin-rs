import Tamarin.TotalMatchWire
import Tamarin.TotalInputBounds

namespace Tamarin.TotalMatchWire
open TotalUnifyWire Packet
variable {d : Dictionary}

/-- Regrouping and permuting a term preserves the field widths of its symbol
occurrences. -/
private theorem fit_equiv {a b : Term d.sig} (h : EquivB a b) : FieldsFit a ↔ FieldsFit b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b _ ih => exact and_congr_right fun _ => forall_congr' ih
  | ac_congr _ _ _ ih ik | comm_congr _ _ _ ih ik => exact and_congr ih ik
  | ac_swap | comm_swap => exact and_comm
  | ac_assoc => exact and_assoc

private theorem image_fits (t : Term d.sig) (σ : Substitution d.sig) (v : Variable) (h : t.Occurs v)
    (bounded : FieldsFit (σ.apply t)) : FieldsFit (σ.image v) := by
  induction t with
  | var w => exact h ▸ bounded
  | atom => contradiction
  | free _ _ ih => obtain ⟨i,hi⟩ := h; exact ih i hi (bounded.2 i)
  | ac _ _ _ ih ik | comm _ _ _ ih ik =>
    exact h.elim (fun hl => ih hl bounded.1) (fun hr => ik hr bounded.2)

/-- Every matching family fits when the input fits. Each observed image is a
subterm of the instantiated pattern, which is equal modulo B to the subject.
A subject-only key retains its original value. -/
theorem representable {p : Problem d.sig} {allowed} {answers : List (Substitution d.sig)}
    (hs : ∀ e ∈ p, FieldsFit e.lhs ∧ FieldsFit e.rhs) (ok : Matching.Complete p allowed answers) :
    Representable p answers := by
  intro σ hσ v hv
  obtain ⟨e,he,occ⟩ := (Problem.mem_variables ..).mp hv
  have bounded : v.id < UInt64.size := occ.elim
    (fun h => var_fits _ _ h (hs e he).1) (fun h => var_fits _ _ h (hs e he).2)
  refine ⟨bounded,?_⟩
  obtain ⟨sol,inScope⟩ := ok.sound _ hσ
  by_cases live : Matching.Observed p v
  · obtain ⟨a,ha,hit⟩ := live
    exact image_fits _ σ v hit ((fit_equiv (sol a ha)).mpr (hs a ha).2)
  · rw [inScope v (fun h => live h.1)]
    exact bounded

/-- The spec reads a caller's list of bindable numeric IDs directly. Only
pattern occurrences can be assigned, independently of the implementation's
choice of worklist. -/
def Bindable (ids : Array UInt64) (v : Variable) : Prop := ∃ i ∈ ids, i.toNat = v.id

private theorem correct_scope (p : Problem d.sig) (ids : Array UInt64) (v : Variable)
    (obs : Matching.Observed p v) : v ∈ domain p ids ↔ Bindable ids v := by
  obtain ⟨e,he,occ⟩ := obs
  have hv := (Problem.mem_variables p v).mpr ⟨e,he,.inl occ⟩
  simp [domain,hv,Bindable,Array.any_eq_true,Array.mem_iff_getElem]
  exact ⟨fun ⟨i,h,e⟩ => ⟨_,⟨i,h,rfl⟩,e⟩, fun ⟨_,⟨i,h,rfl⟩,e⟩ => ⟨i,h,e⟩⟩

private theorem complete (p : Problem d.sig) (ids : Array UInt64) :
    Matching.Complete p (Bindable ids) ((ReferenceMatching.matcher d.sig).run p trivial (domain p ids)) := by
  have ok := (ReferenceMatching.matcher d.sig).correct p trivial (domain p ids)
  have scope (σ : Substitution d.sig) : Matching.Scoped p (fun v => v ∈ domain p ids) σ ↔
      Matching.Scoped p (Bindable ids) σ := by
    have on (v) : Matching.Observed p v ∧ v ∈ domain p ids ↔ Matching.Observed p v ∧ Bindable ids v :=
      and_congr_right (correct_scope p ids v)
    simp only [Matching.Scoped,on]
  exact ⟨fun σ h => ⟨(ok.sound σ h).1,(scope σ).mp (ok.sound σ h).2⟩,
    fun σ h hsc => ok.covers σ h ((scope σ).mpr hsc)⟩

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array UInt64 → Array (Array UInt64)

/-- Every valid query completes, including kind-level terms. Answer rows
preserve the original variable identities in substitution images. -/
structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es ids, input ds ns es = none → kernel ds ns es ids = #[#[0]]
  valid : ∀ ds ns es ids d p, input ds ns es = some ⟨d,p⟩ →
    ∃ answers, Decodes p (kernel ds ns es ids) answers ∧ Matching.Complete p (Bindable ids) answers

theorem correct : Correct run where
  malformed := fun ds ns es _ h => by simp [run,h]
  valid := by
    intro ds ns es ids d p hi
    have ok := complete p ids
    obtain ⟨wire,hw⟩ := pack_exists p _ (representable (input_fieldsFit hi) ok)
    have eq : run ds ns es ids = wire := by
      simp [run,hi,hw]
    exact ⟨_,eq ▸ pack_decodes _ _ _ hw,ok⟩

end Tamarin.TotalMatchWire
