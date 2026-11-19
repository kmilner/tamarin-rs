import Tamarin.SortClash
import Tamarin.VariablePermutation

/-! Maude solves the underlying component problem before assigning sorts to
the free variables of a solved form. A schematic image here is raw syntax.
Only the final arm is a sort-respecting substitution. -/
namespace Tamarin.UnifierSorts
variable {s : Signature}

abbrev Template (s : Signature) := Variable → Term s

/-- Raw component solutions may have unsorted parameters. One instantiation
must account for every variable observed in the input. -/
structure CompleteTemplates (p : Problem s) (rows : List (Template s)) : Prop where
  sound : ∀ θ ∈ rows, ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)
  covers : ∀ ρ : Substitution s, p.Solves ρ →
    ∃ θ ∈ rows, ∃ μ : Variable → Term s,
      ∀ v, p.Occurs v → EquivB (ρ.image v) ((θ v).subst μ)

private def sorts := [SortId.pub,.fresh,.msg,.node,.nat]

private def assignments : List Variable → List (Variable → SortId)
  | [] => [fun _ => .msg]
  | v :: vs => (assignments vs).flatMap fun tail =>
      sorts.map fun k w => if w = v then k else tail w

private theorem assignment_covers (vs : List Variable) (k : Variable → SortId) :
    ∃ g ∈ assignments vs, ∀ v ∈ vs, g v = k v := by
  induction vs with
  | nil => exact ⟨_,List.mem_singleton_self _,by simp⟩
  | cons v vs ih =>
    obtain ⟨tail,ht,agree⟩ := ih
    have mem : k v ∈ sorts := by cases k v <;> simp [sorts]
    refine ⟨_,List.mem_flatMap.mpr ⟨tail,ht,List.mem_map.mpr ⟨k v,mem,rfl⟩⟩,?_⟩
    intro w hw
    by_cases eq : w = v
    · simp [eq]
    · exact (ite_eq_right eq).trans (agree w ((List.mem_cons.mp hw).resolve_left eq))

private def slots (p : Problem s) (θ : Template s) :=
  (p.variables.flatMap (fun v => (θ v).variables)).eraseDups

private theorem slot_mem {p : Problem s} {θ : Template s} {v w}
    (live : p.Occurs v) (seen : (θ v).Occurs w) : w ∈ slots p θ := by
  exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨v,(p.mem_variables _).mpr live,
    (Term.mem_variables ..).mpr seen⟩)

private def name (vs : List Variable) (base : Nat) (g : Variable → SortId) (w : Variable) : Variable :=
  ⟨base + vs.idxOf w, g w⟩

private theorem name_injective {vs : List Variable} {base g} {v w : Variable} (hv : v ∈ vs)
    (hw : w ∈ vs) (h : name vs base g v = name vs base g w) : v = w := by
  have e := Nat.add_left_cancel (congrArg Variable.id h)
  have left := List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)
  have right := List.getElem_idxOf (List.idxOf_lt_length_of_mem hw)
  grind

private def images (θ : Template s) (label : Variable → Variable) (v : Variable) :=
  (θ v).subst (fun w => .var (label w))

private def read (p : Problem s) (img : Variable → Term s)
    (sorted : ∀ v ∈ p.variables, (img v).checkSort v.sort = true) : Substitution s where
  image v := if v ∈ p.variables then img v else .var v
  support := p.variables
  outside v hv := ite_eq_right hv
  sorted v := by
    split
    · next h => exact Term.checkSort_sound _ _ (sorted v h)
    · exact .var _

private def arm (p : Problem s) (θ : Template s) (base : Nat) (g : Variable → SortId) :
    Option (Substitution s) :=
  let img := images θ (name (slots p θ) base g)
  if ok : p.variables.all (fun v => (img v).checkSort v.sort) then
    some (read p img (List.all_eq_true.mp ok))
  else none

private def perTemplate (p : Problem s) (θ : Template s) (avoid : List Variable) :=
  (assignments (slots p θ)).filterMap (arm p θ (VariablePermutation.freshBound (p.variables ++ avoid)))

def solve (p : Problem s) (rows : List (Template s)) (avoid : List Variable) :=
  rows.flatMap (fun θ => perTemplate p θ avoid)

private theorem read_apply (p : Problem s) (θ : Template s) (label : Variable → Variable)
    {ok} (t : Term s) (live : ∀ v, t.Occurs v → p.Occurs v) :
    (read p (images θ label) ok).apply t = (t.subst θ).subst (fun w => .var (label w)) := by
  rw [Term.subst_comp]
  apply Term.subst_eq_of_agree
  intro v hv
  exact ite_eq_left ((p.mem_variables _).mpr (live _ hv))

private theorem sort_at_root {t : Term s} {k} (ht : HasSort t k) : HasSort t t.rootSort := by
  induction ht with
  | widen _ _ ih => exact ih
  | var => exact .var _
  | atom => exact .atom _
  | free _ _ h _ => exact .free _ _ h
  | ac _ _ _ ha hb _ _ => exact .ac _ _ _ ha hb
  | comm _ _ _ ha hb _ _ => exact .comm _ _ _ ha hb

/-- Replacing each actual parameter by a variable of its actual least sort
preserves every sort check. Each occurring parameter has that least sort. -/
private theorem generalizeSorts (t : Term s) (μ : Variable → Term s) (label : Variable → Variable)
    (names : ∀ w, t.Occurs w → (label w).sort = (μ w).rootSort) (k : SortId)
    (typed : (t.subst μ).checkSort k = true) :
    (t.subst (fun w => .var (label w))).checkSort k = true ∧
      ∀ w, t.Occurs w → HasSort (μ w) (label w).sort := by
  induction t generalizing k with
  | var v =>
    have ht := Term.checkSort_sound _ _ typed
    have e := names v rfl
    refine ⟨(Subsort.check_iff ..).mpr (e ▸ Term.rootSort_le ht),?_⟩
    intro w hw
    obtain rfl := hw
    exact e ▸ sort_at_root ht
  | atom => exact ⟨typed, nofun⟩
  | free f xs ih =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true, List.all_eq_true] at typed ⊢
    have child i := ih i (fun w hw => names w ⟨i,hw⟩) _ (typed.2 i (List.mem_finRange i))
    exact ⟨⟨typed.1, fun i _ => (child i).1⟩, fun w ⟨i,hw⟩ => (child i).2 w hw⟩
  | ac f a b ia ib | comm f a b ia ib =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true] at typed ⊢
    have left := ia (fun w hw => names w (.inl hw)) _ typed.1.2
    have right := ib (fun w hw => names w (.inr hw)) _ typed.2
    exact ⟨⟨⟨typed.1.1,left.1⟩,right.1⟩,fun w hw => hw.elim (left.2 w) (right.2 w)⟩

private theorem realize (vs : List Variable) (label : Variable → Variable) (μ : Variable → Term s)
    (inj : ∀ v ∈ vs, ∀ w ∈ vs, label v = label w → v = w)
    (typed : ∀ v ∈ vs, HasSort (μ v) (label v).sort) :
    ∃ δ : Substitution s, ∀ v ∈ vs, δ.image (label v) = μ v := by
  classical
  let δ : Substitution s := {
    image := fun w => if h : ∃ v ∈ vs, label v = w then μ h.choose else .var w
    support := vs.map label
    outside := by
      intro w hw
      exact dite_eq_right (fun h => hw (List.mem_map.mpr h))
    sorted := by
      intro w
      split
      · next h =>
        have ok := typed h.choose h.choose_spec.1
        rwa [h.choose_spec.2] at ok
      · exact .var w }
  refine ⟨δ,fun v hv => ?_⟩
  have h : ∃ w ∈ vs, label w = label v := ⟨v,hv,rfl⟩
  simp only [δ,dite_eq_left h]
  exact congrArg μ (inj h.choose h.choose_spec.1 v hv h.choose_spec.2)

private theorem perTemplate_sound {p : Problem s} {θ : Template s} {avoid σ}
    (mem : σ ∈ perTemplate p θ avoid)
    (solves : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    p.Solves σ ∧ DomainRestricted p σ ∧ FreshFor p avoid σ := by
  obtain ⟨g,_,hit⟩ := List.mem_filterMap.mp mem
  simp only [arm] at hit
  split at hit
  · next ok =>
    obtain rfl := Option.some.inj hit
    constructor
    · intro e he
      rw [read_apply p θ _ e.lhs (fun _ hv => ⟨e,he,.inl hv⟩),
        read_apply p θ _ e.rhs (fun _ hv => ⟨e,he,.inr hv⟩)]
      exact (solves e he).subst _
    · constructor
      · intro v off
        exact ite_eq_right (fun mem => off ((p.mem_variables _).mp mem))
      · intro v live w occurs _ clash
        simp only [read, ite_eq_left ((p.mem_variables _).mpr live), images, Term.occurs_rename] at occurs
        obtain ⟨k,_,rfl⟩ := occurs
        have h := VariablePermutation.lt_freshBound (p.variables ++ avoid) _
          (List.mem_append_right _ clash)
        simp only [name] at h
        omega
  · contradiction

private theorem perTemplate_covers {p : Problem s} (θ : Template s) (avoid : List Variable)
    (ρ : Substitution s) (μ : Variable → Term s)
    (agree : ∀ v, p.Occurs v → EquivB (ρ.image v) ((θ v).subst μ)) :
    ∃ σ ∈ perTemplate p θ avoid, Substitution.InstanceOn p.Occurs ρ σ := by
  let vs := slots p θ
  let base := VariablePermutation.freshBound (p.variables ++ avoid)
  obtain ⟨g,hg,hgSort⟩ := assignment_covers vs (fun w => (μ w).rootSort)
  let label := name vs base g
  have checked (v) (hv : p.Occurs v) := generalizeSorts (θ v) μ label
    (fun w hw => hgSort w (slot_mem hv hw)) v.sort
    (SortClash.check_equiv (agree v hv) v.sort ▸ Term.checkSort_complete (ρ.sorted v))
  have ok : ∀ v ∈ p.variables, ((images θ label v).checkSort v.sort) = true :=
    fun v hv => (checked v ((p.mem_variables v).mp hv)).1
  have typed : ∀ w ∈ vs, HasSort (μ w) (label w).sort := by
    intro w hw
    obtain ⟨v,hv,occ⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hw)
    exact (checked v ((p.mem_variables v).mp hv)).2 w ((Term.mem_variables ..).mp occ)
  obtain ⟨δ,hδ⟩ := realize vs label μ (fun _ hv _ hw => name_injective hv hw) typed
  refine ⟨read p (images θ label) ok, List.mem_filterMap.mpr ⟨g,hg,?_⟩, δ, ?_⟩
  · exact dite_eq_left (List.all_eq_true.mpr ok)
  · intro v hv
    apply (agree v hv).trans
    change EquivB _ (δ.apply (if v ∈ p.variables then images θ label v else .var v))
    rw [ite_eq_left ((p.mem_variables _).mpr hv)]
    unfold Substitution.apply images
    rw [Term.subst_comp]
    have eq := Term.subst_eq_of_agree μ (fun w => δ.image (label w)) (θ v)
      (fun w hw => (hδ w (slot_mem hv hw)).symm)
    exact eq ▸ EquivB.refl _

theorem correct (p : Problem s) (rows : List (Template s)) (h : CompleteTemplates p rows)
    (avoid : List Variable) : (Outcome.complete (solve p rows avoid)).CorrectIn p avoid := by
  have sound (σ) (mem : σ ∈ solve p rows avoid) : p.Solves σ ∧ DomainRestricted p σ ∧ FreshFor p avoid σ := by
    obtain ⟨θ,hθ,hm⟩ := List.mem_flatMap.mp mem
    exact perTemplate_sound hm (h.sound θ hθ)
  refine ⟨⟨fun σ hm => (sound σ hm).1,?_⟩,fun σ hm => (sound σ hm).2.1,fun σ hm => (sound σ hm).2.2⟩
  intro ρ hs
  obtain ⟨θ,ht,μ,agree⟩ := h.covers ρ hs
  obtain ⟨σ,hm,instanceOf⟩ := perTemplate_covers θ avoid ρ μ agree
  exact ⟨σ,List.mem_flatMap.mpr ⟨θ,ht,hm⟩,instanceOf⟩

/-- One raw component solver valid for every input suffices for sorted and
kind-level Tamarin queries. Sort refinement and caller freshness are discharged here. -/
def unifier (raw : Problem s → List (Template s)) (hc : ∀ p, CompleteTemplates p (raw p)) :
    VerifiedUnifier s (fun _ => True) where
  solve p _ avoid := solve p (raw p) avoid
  correct p _ avoid := (correct p _ (hc p) avoid).mathematical
  domain p _ avoid := (correct p _ (hc p) avoid).domain
  fresh p _ avoid := (correct p _ (hc p) avoid).fresh

end Tamarin.UnifierSorts
