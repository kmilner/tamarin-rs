import Tamarin.FreshSubstitution

/-! Caller-chosen finite range renamings for ordinary unification answers. -/
namespace Tamarin.CallerFreshening
variable {sig : Signature}

/-- Only names actually read from this branch need distinct, same-sort images.
Source names may equal other target names because substitution is simultaneous. -/
structure Allocation (sources : List Variable) where
  assign : Variable → Variable
  sorted : ∀ w ∈ sources, (assign w).sort = w.sort
  injective : ∀ u ∈ sources, ∀ v ∈ sources, assign u = assign v → u = v

namespace Allocation
variable {sources : List Variable}

private def forward (a : Allocation sources) (sig : Signature) : Substitution sig where
  image := fun v => if v ∈ sources then .var (a.assign v) else .var v
  support := sources
  outside := fun _ h => ite_eq_right h
  sorted := by
    intro v
    split
    · next h => rw [← a.sorted v h]; exact .var _
    · exact .var _

private def findSource (a : Allocation sources) (v : Variable) :=
  sources.find? (fun u => a.assign u == v)

private theorem findSource_eq (a : Allocation sources) {v u : Variable}
    (h : a.findSource v = some u) : a.assign u = v :=
  beq_iff_eq.mp (List.find?_some (p := fun w => a.assign w == v) h)

private def backward (a : Allocation sources) (sig : Signature) : Substitution sig where
  image := fun v => .var ((a.findSource v).getD v)
  support := sources.map a.assign
  outside := by
    intro v hv
    cases h : a.findSource v with
    | none => rfl
    | some u =>
      exact False.elim (hv (List.mem_map.mpr ⟨u, List.mem_of_find?_eq_some h,
        a.findSource_eq h⟩))
  sorted := by
    intro v
    cases h : a.findSource v with
    | none => exact .var _
    | some u =>
      have he : a.assign u = v := a.findSource_eq h
      have hs := a.sorted u (List.mem_of_find?_eq_some h)
      rw [← he, hs]
      exact .var _

private theorem backward_at (a : Allocation sources) (w : Variable) (hw : w ∈ sources) :
    (a.backward sig).image (a.assign w) = .var w := by
  change Term.var ((a.findSource _).getD _) = _
  cases h : a.findSource (a.assign w) with
  | none => exact False.elim (List.find?_eq_none.mp h w hw (by simp))
  | some u =>
    apply congrArg Term.var
    exact a.injective u (List.mem_of_find?_eq_some h) w hw (a.findSource_eq h)

end Allocation

abbrev sources (p : Problem sig) (σ : Substitution sig) :=
  FreshAnswer.rangeVariables p.variables σ

private theorem source_mem {p : Problem sig} {σ : Substitution sig} {v w : Variable}
    (hv : p.Occurs v) (hw : (σ.image v).Occurs w) : w ∈ sources p σ :=
  List.mem_flatMap.mpr ⟨v, (p.mem_variables v).mpr hv, ((σ.image v).mem_variables w).mpr hw⟩

/-- The observable behavior of the caller's ordinary substitution after fresh-range
decoding. One map covers every occurrence in every image, including identity entries. -/
def Represents (p : Problem sig) (σ out : Substitution sig) (a : Allocation (sources p σ)) : Prop :=
  ∀ v, out.image v = if v ∈ p.variables then (σ.image v).subst (fun w => .var (a.assign w))
    else .var v

/-- Smart constructors can reorder C/AC children and regroup AC products after
a nonmonotone allocation. The same allocation still applies to every observed
image, and variables outside the input retain their exact identity. -/
structure RepresentsMod (p : Problem sig) (σ out : Substitution sig)
    (a : Allocation (sources p σ)) : Prop where
  observed : ∀ v, p.Occurs v → EquivB (out.image v) ((σ.image v).subst (fun w => .var (a.assign w)))
  outside : DomainRestricted p out

theorem Represents.modulo {p : Problem sig} {σ out : Substitution sig} {a : Allocation (sources p σ)}
    (rep : Represents p σ out a) : RepresentsMod p σ out a := by
  constructor
  · intro v hv
    rw [rep v, ite_eq_left ((p.mem_variables _).mpr hv)]
    exact .refl _
  · intro v hv
    exact (rep v).trans (ite_eq_right (fun h => hv ((p.mem_variables _).mp h)))

theorem RepresentsMod.instance_iff {p : Problem sig} {σ out : Substitution sig} {a : Allocation (sources p σ)}
    (rep : RepresentsMod p σ out a) (ρ : Substitution sig) :
    Substitution.InstanceOn p.Occurs ρ σ ↔ Substitution.InstanceOn p.Occurs ρ out := by
  constructor
  · intro hi
    apply Substitution.instanceOn_trans p.Occurs hi
    refine ⟨a.backward sig, ?_⟩
    intro v hv
    change EquivB _ ((out.image v).subst _)
    apply EquivB.trans _ (((rep.observed v hv).subst (a.backward sig).image).symm)
    rw [Term.subst_comp]
    have he := (σ.image v).subst_eq_of_agree
      (fun w => (a.backward sig).image (a.assign w)) Term.var
      (fun w hw => a.backward_at w (source_mem hv hw))
    change EquivB _ ((σ.image v).subst (fun w => (a.backward sig).image (a.assign w)))
    rw [he, Term.subst_id]
    exact .refl _
  · intro hi
    apply Substitution.instanceOn_trans p.Occurs hi
    refine ⟨a.forward sig, ?_⟩
    intro v hv
    change EquivB (out.image v) ((σ.image v).subst _)
    apply (rep.observed v hv).trans
    have he := (σ.image v).subst_eq_of_agree (fun w => .var (a.assign w))
      (a.forward sig).image (fun w hw => (ite_eq_left (source_mem hv hw)).symm)
    rw [he]
    exact .refl _

theorem instance_iff {p : Problem sig} {σ out : Substitution sig} {a : Allocation (sources p σ)}
    (rep : Represents p σ out a) (ρ : Substitution sig) :
    Substitution.InstanceOn p.Occurs ρ σ ↔ Substitution.InstanceOn p.Occurs ρ out :=
  rep.modulo.instance_iff ρ

/-- Observed variable identities may be retained. Only external witnesses need to
avoid caller names, as in the contract for ordinary substitutions. -/
def Avoids (r : Request sig) (σ : Substitution sig) (a : Allocation (sources r.problem σ)) : Prop :=
  ∀ w ∈ sources r.problem σ, ¬ r.problem.Occurs (a.assign w) → a.assign w ∉ r.avoid

theorem refinement_mod {ι : Type} (r : Request sig) (arms : List ι)
    (raw out : ι → Substitution sig) (a : (i : ι) → Allocation (sources r.problem (raw i)))
    (rep : ∀ i ∈ arms, RepresentsMod r.problem (raw i) (out i) (a i))
    (fresh : ∀ i ∈ arms, Avoids r (raw i) (a i)) :
    OutputRefinement r (arms.map raw) (arms.map out) := by
  constructor
  · intro ρ
    constructor
    · rintro ⟨_, hm, hi⟩
      obtain ⟨i, hiMem, rfl⟩ := List.mem_map.mp hm
      exact ⟨_, List.mem_map_of_mem hiMem, ((rep i hiMem).instance_iff ρ).mp hi⟩
    · rintro ⟨_, hm, hi⟩
      obtain ⟨i, hiMem, rfl⟩ := List.mem_map.mp hm
      exact ⟨_, List.mem_map_of_mem hiMem, ((rep i hiMem).instance_iff ρ).mpr hi⟩
  · intro τ hm v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact (rep i hi).outside v hv
  · intro τ hm v hv w hw external hin
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have renamed := (((rep i hi).observed v hv).occurs_iff w).mp hw
    obtain ⟨u, hu, rfl⟩ := (Term.occurs_rename ..).mp renamed
    exact fresh i hi u (source_mem hv hu) external hin

theorem refinement {ι : Type} (r : Request sig) (arms : List ι)
    (raw out : ι → Substitution sig) (a : (i : ι) → Allocation (sources r.problem (raw i)))
    (rep : ∀ i ∈ arms, Represents r.problem (raw i) (out i) (a i))
    (fresh : ∀ i ∈ arms, Avoids r (raw i) (a i)) :
    OutputRefinement r (arms.map raw) (arms.map out) :=
  refinement_mod r arms raw out a (fun i hi => (rep i hi).modulo) fresh

end Tamarin.CallerFreshening
