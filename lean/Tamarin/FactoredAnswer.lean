import Tamarin.CallerFreshening

/-! A residual answer is used under every image of the earlier free factor.
These lemmas specify which alias removals and witness allocations preserve
the answers to the original equations. They apply to ordinary, decoded
substitutions: distinct packet-local names and input names must first be put
in their proper scopes. -/
namespace Tamarin.FactoredAnswer
variable {sig : Signature}

/-- The factor can read a variable that no longer occurs in a residual
equation (for example, one side of an eliminated free pair). -/
def live (p : Problem sig) (m : Substitution sig) (w : Variable) : Prop :=
  ∃ v, p.Occurs v ∧ (m.image v).Occurs w

/-- Lists may contain repeated occurrences and need no canonical ordering. -/
def liveKeys (p : Problem sig) (m : Substitution sig) : List Variable :=
  FreshAnswer.rangeVariables p.variables m

theorem mem_liveKeys {p : Problem sig} {m : Substitution sig} {v : Variable} :
    v ∈ liveKeys p m ↔ live p m v := by
  simp [liveKeys, FreshAnswer.rangeVariables, live]

def ArmEquivalent (seen : Variable → Prop) (a b : Substitution sig) : Prop :=
  Substitution.InstanceOn seen a b ∧ Substitution.InstanceOn seen b a

theorem ArmEquivalent.refl (seen : Variable → Prop) (a : Substitution sig) :
    ArmEquivalent seen a a :=
  ⟨Substitution.instanceOn_refl .., Substitution.instanceOn_refl ..⟩

theorem ArmEquivalent.trans {seen : Variable → Prop} {a b c : Substitution sig}
    (ab : ArmEquivalent seen a b) (bc : ArmEquivalent seen b c) : ArmEquivalent seen a c :=
  ⟨Substitution.instanceOn_trans _ ab.1 bc.1, Substitution.instanceOn_trans _ bc.2 ab.2⟩

/-- One residual instantiator explains every original variable, including
several factored variables that mention the same residual parameter. -/
theorem compose_instance {p : Problem sig} {m a b : Substitution sig}
    (h : Substitution.InstanceOn (live p m) a b) :
    Substitution.InstanceOn p.Occurs (a.compose m) (b.compose m) := by
  obtain ⟨δ, hd⟩ := h
  refine ⟨δ, ?_⟩
  intro v hv
  change EquivB (a.apply (m.image v)) (δ.apply (b.apply (m.image v)))
  rw [← Substitution.apply_compose]
  exact (m.image v).subst_equiv _ _ (fun w hw => hd w ⟨v, hv, hw⟩)

/-- Omitting a binding makes its key denote itself. -/
def eraseBinding (σ : Substitution sig) (x : Variable) : Substitution sig where
  image := fun v => if v = x then .var v else σ.image v
  support := σ.support
  outside := by intro v hv; simp [σ.outside v hv]
  sorted := by intro v; split <;> first | exact .var v | exact σ.sorted v

/-- A singleton, same-sort variable image may be omitted when neither the
disappearing witness nor the newly implicit key is shared with another image.
The second condition matters for *ordinary* substitutions. Rust's fresh-range
representation provides that separation by opening ranges in a fresh scope.
The reverse direction justifies extending an omitted key with a fresh alias. -/
theorem omit_alias {seen : Variable → Prop} (σ : Substitution sig) (x w : Variable)
    (bare : σ.image x = .var w) (sort : w.sort = x.sort)
    (alone : ∀ v, seen v → v ≠ x → ¬ (σ.image v).Occurs w ∧ ¬ (σ.image v).Occurs x) :
    ArmEquivalent seen σ (eraseBinding σ x) := by
  have hw : HasSort (Term.var (sig := sig) w) x.sort := sort ▸ HasSort.var w
  have hx : HasSort (Term.var (sig := sig) x) w.sort := sort.symm ▸ HasSort.var x
  constructor
  · refine ⟨Substitution.binding x (.var w) hw, ?_⟩
    intro v hv
    change EquivB (σ.image v) ((Substitution.binding x (.var w) hw).apply ((eraseBinding σ x).image v))
    by_cases he : v = x
    · subst v; rw [bare]; simp [eraseBinding, Substitution.apply, Term.subst]; exact .refl _
    · simp only [eraseBinding, ite_eq_right he]
      rw [Substitution.binding_apply_of_not_occurs _ _ _ _ (alone v hv he).2]
      exact .refl _
  · refine ⟨Substitution.binding w (.var x) hx, ?_⟩
    intro v hv
    change EquivB ((eraseBinding σ x).image v) ((Substitution.binding w (.var x) hx).apply (σ.image v))
    by_cases he : v = x
    · subst v; rw [bare]; simp [eraseBinding, Substitution.apply, Term.subst]; exact .refl _
    · simp only [eraseBinding, ite_eq_right he]
      rw [Substitution.binding_apply_of_not_occurs _ _ _ _ (alone v hv he).1]
      exact .refl _

/-- A checked reference operation on decoded bindings. Keeping a binding is
always legal, so a producer need not maximize compression. -/
def omitIfIsolated (keys : List Variable) (σ : Substitution sig) (x : Variable) : Substitution sig :=
  match σ.image x with
  | .var w =>
    if w.sort == x.sort && keys.all (fun v => v == x ||
      (!((σ.image v).variables.contains w) && !((σ.image v).variables.contains x)))
    then eraseBinding σ x else σ
  | _ => σ

theorem omitIfIsolated_equivalent (keys : List Variable) (σ : Substitution sig) (x : Variable) :
    ArmEquivalent (· ∈ keys) σ (omitIfIsolated keys σ x) := by
  unfold omitIfIsolated
  split
  next w bare =>
    split
    next h =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      apply omit_alias σ x w bare h.1
      intro v hv ne
      simpa [ne] using h.2 v hv
    next => exact .refl _ _
  all_goals exact .refl _ _

/-- Applying the check in any order preserves the represented residual arm.
A removed alias may have many occurrences under its *own* free factor. -/
theorem omit_many (keys order : List Variable) (σ : Substitution sig) :
    ArmEquivalent (· ∈ keys) σ (order.foldl (omitIfIsolated keys) σ) := by
  induction order generalizing σ with
  | nil => exact .refl _ _
  | cons x rest ih => exact (omitIfIsolated_equivalent keys σ x).trans (ih _)

theorem composed_set_equivalent {ι : Type} (p : Problem sig) (m : Substitution sig)
    (arms : List ι) (raw prepared : ι → Substitution sig)
    (changes : ∀ i ∈ arms, ArmEquivalent (live p m) (raw i) (prepared i)) :
    AnswerSetEquivalent p (arms.map fun i => (raw i).compose m)
      (arms.map fun i => (prepared i).compose m) := by
  intro ρ
  constructor <;> rintro ⟨_, ha, hi⟩ <;> obtain ⟨i, hmem, rfl⟩ := List.mem_map.mp ha
  · exact ⟨_, List.mem_map_of_mem hmem,
      Substitution.instanceOn_trans _ hi (compose_instance (changes i hmem).1)⟩
  · exact ⟨_, List.mem_map_of_mem hmem,
      Substitution.instanceOn_trans _ hi (compose_instance (changes i hmem).2)⟩

/-- End of the composition pipeline with reference freshening. The proof
also covers empty answer lists and aliases appearing only inside the factor. -/
theorem lift_complete {ι : Type} (r : Request sig) (m : Substitution sig)
    (arms : List ι) (raw prepared : ι → Substitution sig)
    (changes : ∀ i ∈ arms, ArmEquivalent (live r.problem m) (raw i) (prepared i))
    (complete : CompleteSet r.problem (arms.map fun i => (raw i).compose m)) :
    (Outcome.complete (arms.map fun i =>
      FreshAnswer.freshen r.problem r.avoid ((prepared i).compose m))).CorrectIn r.problem r.avoid := by
  simpa only [List.map_map, Function.comp_def] using
    FreshAnswer.freshen_correct r _ ((composed_set_equivalent r.problem m arms raw prepared changes).preserves_complete complete)

/-- Only the fresh names that occur on this arm need assigned sorts. -/
private def allocated (p : Problem sig) (σ : Substitution sig)
    (a : CallerFreshening.Allocation (CallerFreshening.sources p σ)) : Substitution sig where
  image := fun v => if v ∈ p.variables then (σ.image v).subst (fun w =>
    if w ∈ CallerFreshening.sources p σ then .var (a.assign w) else .var w) else .var v
  support := p.variables
  outside := fun _ h => ite_eq_right h
  sorted := by
    intro v
    split
    · apply (σ.sorted v).subst
      intro w
      split
      · next hw => rw [← a.sorted w hw]; exact .var _
      · exact .var _
    · exact .var _

private theorem allocated_rep (p : Problem sig) (σ : Substitution sig)
    (a : CallerFreshening.Allocation (CallerFreshening.sources p σ)) :
    CallerFreshening.Represents p σ (allocated p σ a) a := by
  intro v
  simp only [allocated]
  split
  · next hv =>
      apply Term.subst_eq_of_agree
      intro w hw
      exact ite_eq_left (List.mem_flatMap.mpr ⟨v, hv, ((σ.image v).mem_variables w).mpr hw⟩)
  · rfl

/-- A finite list of ordinary caller-visible bindings after the packet's range
names have been opened. Lookup of an omitted key returns that key. -/
def readBindings (b : FreshAnswer sig) := Substitution.fromBindings b.bindings b.sorted

/-- Entry-level obligations for a materializer. Every stored row may reorder
C or AC arguments. Every omitted observable row must denote its own key.
The same allocation is used throughout the arm, including omitted entries. -/
structure Stores (p : Problem sig) (σ : Substitution sig) (packet : FreshAnswer sig)
    (a : CallerFreshening.Allocation (CallerFreshening.sources p σ)) : Prop where
  domain : ∀ v t, (v, t) ∈ packet.bindings → p.Occurs v
  written : ∀ v t, (v, t) ∈ packet.bindings →
    EquivB t ((σ.image v).subst (fun w => .var (a.assign w)))
  omitted : ∀ v, p.Occurs v → v ∉ packet.bindings.map Prod.fst →
    EquivB (.var v) ((σ.image v).subst (fun w => .var (a.assign w)))

private theorem Stores.agrees {p : Problem sig} {σ : Substitution sig} {b : FreshAnswer sig}
    {a : CallerFreshening.Allocation (CallerFreshening.sources p σ)} (s : Stores p σ b a) :
    Substitution.AgreesOn p.Occurs (readBindings b) (allocated p σ a) := by
  intro v hv
  rw [allocated_rep p σ a v, ite_eq_left ((p.mem_variables v).mpr hv)]
  change EquivB (Substitution.lookupBinding b.bindings v) _
  by_cases hm : v ∈ b.bindings.map Prod.fst
  · obtain ⟨⟨u, t⟩, h, rfl⟩ := List.mem_map.mp hm
    rw [Substitution.lookupBinding_eq_of_mem _ b.consistent _ t h]
    exact s.written _ t h
  · rw [Substitution.lookupBinding_outside _ _ hm]
    exact s.omitted v hv hm

private theorem instance_of_agrees {seen : Variable → Prop} {α β : Substitution sig}
    (h : Substitution.AgreesOn seen α β) : Substitution.InstanceOn seen α β := by
  refine ⟨Substitution.identity, ?_⟩
  intro v hv
  change EquivB _ (Substitution.identity.apply _)
  rw [Substitution.apply_identity]
  exact h v hv

/-- Caller-allocated finite output rows refine the represented branch, including
sorts, fresh range names, sparse identities, and C/AC smart constructors. -/
theorem packet_refinement {ι : Type} (r : Request sig) (arms : List ι) (raw : ι → Substitution sig)
    (packets : ι → FreshAnswer sig)
    (a : (i : ι) → CallerFreshening.Allocation (CallerFreshening.sources r.problem (raw i)))
    (rows : ∀ i ∈ arms, Stores r.problem (raw i) (packets i) (a i))
    (fresh : ∀ i ∈ arms, CallerFreshening.Avoids r (raw i) (a i)) :
    OutputRefinement r (arms.map raw) (arms.map fun i => readBindings (packets i)) := by
  have ideal := CallerFreshening.refinement r arms raw
    (fun i => allocated r.problem (raw i) (a i)) a (fun i _ => allocated_rep r.problem (raw i) (a i)) fresh
  constructor
  · intro ρ
    rw [ideal.equivalent ρ]
    constructor <;> rintro ⟨_, h, hi⟩ <;> obtain ⟨i, hm, rfl⟩ := List.mem_map.mp h
    · exact ⟨_, List.mem_map_of_mem hm, Substitution.instanceOn_trans _ hi
        (instance_of_agrees (fun v hv => ((rows i hm).agrees v hv).symm))⟩
    · exact ⟨_, List.mem_map_of_mem hm, Substitution.instanceOn_trans _ hi
        (instance_of_agrees (rows i hm).agrees)⟩
  · intro _ h v hv
    obtain ⟨i, hm, rfl⟩ := List.mem_map.mp h
    apply Substitution.lookupBinding_outside
    rintro he
    obtain ⟨⟨u, t⟩, ht, rfl⟩ := List.mem_map.mp he
    exact hv ((rows i hm).domain _ t ht)
  · intro _ h v hv w hw
    obtain ⟨i, hm, rfl⟩ := List.mem_map.mp h
    exact ideal.fresh _ (List.mem_map_of_mem hm) v hv w
      ((((rows i hm).agrees v hv).occurs_iff w).mp hw)

/-- A complete semantic factorization yields a correct caller-visible answer
list from local checks on edited arms and their actual finite decoded rows. -/
theorem materialized_complete {ι : Type} (r : Request sig) (m : Substitution sig)
    (arms : List ι) (raw prepared : ι → Substitution sig) (packets : ι → FreshAnswer sig)
    (a : (i : ι) → CallerFreshening.Allocation
      (CallerFreshening.sources r.problem ((prepared i).compose m)))
    (changes : ∀ i ∈ arms, ArmEquivalent (live r.problem m) (raw i) (prepared i))
    (rows : ∀ i ∈ arms, Stores r.problem ((prepared i).compose m) (packets i) (a i))
    (fresh : ∀ i ∈ arms, CallerFreshening.Avoids r ((prepared i).compose m) (a i))
    (complete : CompleteSet r.problem (arms.map fun i => (raw i).compose m)) :
    (Outcome.complete (arms.map fun i => readBindings (packets i))).CorrectIn r.problem r.avoid :=
  (packet_refinement r arms _ packets a rows fresh).preserves_correct
    ((composed_set_equivalent r.problem m arms raw prepared changes).preserves_complete complete)

end Tamarin.FactoredAnswer
