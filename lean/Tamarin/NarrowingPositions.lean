import Tamarin.ContextualReduction
import Tamarin.StableVariants

/-! Positions at which a symbolic narrowing search must look after an
assignment. Reassociation can put a redex across the two source operands.
A step inside one exposed factor still belongs to its original operand,
even when a variable supplied an entire product. -/
namespace Tamarin.Rewriting.NarrowingPositions
open ConstructorVariants ACSubproductReduction ContextualReduction
variable {s : Signature} {R : Root s}

/-- Split out one chosen occurrence, retaining every other occurrence,
including duplicates equivalent to the selected factor. -/
private theorem expose [DecidableEq s.ACSym] (f : s.ACSym) {a p : Term s}
    (mem : p ∈ ACRepresentation.flatten f a) : ∃ k, EquivB a (plug f k p) := by
  have sub : DHProduct.Subbag f p a := by
    have haveClass : Cancellation.classOf p ∈ Cancellation.flatten f a := by
      rw [DHProduct.classes]
      exact List.mem_map_of_mem mem
    classical
    exact ⟨_,by rw [DHProduct.atom_factors f a p mem]; exact List.perm_cons_erase haveClass⟩
  rcases sub.context with eq|⟨k,eq⟩
  · exact ⟨none,eq⟩
  · exact ⟨some k,eq⟩

private theorem plug_left (f : s.ACSym) (k : Option (Term s)) (other : Term s) :
    ∃ rest, ∀ t : Term s, EquivB (.ac f (plug f k t) other) (plug f rest t) := by
  cases k with
  | none => exact ⟨some other,fun _ => .refl _⟩
  | some r => exact ⟨some (.ac f r other),fun t => .ac_assoc f t r other⟩

private theorem step_left [DecidableEq s.ACSym] (f : s.ACSym) (a b p q : Term s)
    (mem : p ∈ ACRepresentation.flatten f a) (st : StepModulo R p q) (k : Option (Term s))
    (original : EquivB (.ac f a b) (plug f k p)) :
    ∃ v, StepModulo R a v ∧ EquivB (.ac f v b) (plug f k q) := by
  obtain ⟨j,selected⟩ := expose f mem
  obtain ⟨rest,shape⟩ := plug_left f j b
  have before := (EquivB.ac_congr f selected (.refl b)).trans (shape p)
  refine ⟨plug f j q,?_,(shape q).trans (same_context f before original (.refl p) q)⟩
  exact (all_steps_iff f a _).mpr (.inr ⟨p,mem,q,j,st,selected,.refl _⟩)

/-- Every specialized step of a binary source product either selects a
top-level subbag or acts within one of its original operands. The target
keeps the same complement, including when a rewritten operand becomes
another product. Overlap between these alternatives is harmless. -/
theorem ac_children_iff [DecidableEq s.ACSym] (f : s.ACSym) (a b u : Term s) :
    StepModulo R (.ac f a b) u ↔ Occurrence R f (.ac f a b) u ∨
      (∃ v, StepModulo R a v ∧ EquivB (.ac f v b) u) ∨
      (∃ v, StepModulo R b v ∧ EquivB (.ac f a v) u) := by
  constructor
  · intro step
    rcases (all_steps_iff f _ _).mp step with root|⟨p,mem,q,k,st,original,after⟩
    · exact .inl root
    · rcases List.mem_append.mp (by simpa [ACRepresentation.flatten] using mem) with left|right
      · obtain ⟨v,hv,e⟩ := step_left f a b p q left st k original
        exact .inr (.inl ⟨v,hv,e.trans after⟩)
      · obtain ⟨v,hv,e⟩ := step_left f b a p q right st k ((EquivB.ac_swap f b a).trans original)
        exact .inr (.inr ⟨v,hv,(EquivB.ac_swap f a v).trans (e.trans after)⟩)
  · rintro (root|⟨_,⟨p,q,pre,st,post⟩,e⟩|⟨_,⟨p,q,pre,st,post⟩,e⟩)
    · exact (all_steps_iff f _ _).mpr (.inl root)
    · exact ⟨_,_,.ac_congr f pre (.refl b),.ac_left f b st,(EquivB.ac_congr f post (.refl b)).trans e⟩
    · exact ⟨_,_,.ac_congr f (.refl a) pre,.ac_right f a st,(EquivB.ac_congr f (.refl a) post).trans e⟩

private theorem nested_plug (f : s.ACSym) (outer inner : Option (Term s)) :
    ∃ rest, ∀ t, EquivB (plug f outer (plug f inner t)) (plug f rest t) := by
  cases outer with
  | none => exact ⟨inner,fun _ => .refl _⟩
  | some b => exact plug_left f inner b

private theorem apply_plug (f : s.ACSym) (ρ : Substitution s) (k : Option (Term s)) (p : Term s) :
    ρ.apply (plug f k p) = plug f (k.map ρ.apply) (ρ.apply p) := by cases k <;> rfl

private theorem specialize {f : s.ACSym} (ρ : Substitution s) {q p k} (e : EquivB q (plug f k p)) :
    EquivB (ρ.apply q) (plug f (k.map ρ.apply) (ρ.apply p)) :=
  apply_plug f ρ k p ▸ e.subst ρ.image

private theorem replay {f : s.ACSym} {a p v u : Term s} {k}
    (source : EquivB a (plug f k p)) (step : StepModulo R p v)
    (out : EquivB (plug f k v) u) : StepModulo R a u := by
  obtain ⟨x,y,before,fire,after⟩ := lift_step f k step
  exact ⟨x,y,source.trans before,fire,after.trans out⟩

/-- Every specialized step at a flat source array either fires at an AC
subbag, or changes one of the original source entries in its original
context. The complement is chosen before specialization. A variable can
expand to a product, and the successor can itself introduce new factors. -/
theorem ac_positions_iff [DecidableEq s.ACSym] (f : s.ACSym) (q : Term s) (ρ : Substitution s)
    (u : Term s) :
    StepModulo R (ρ.apply q) u ↔ Occurrence R f (ρ.apply q) u ∨
      ∃ p ∈ ACRepresentation.flatten f q, ∃ k v, EquivB q (plug f k p) ∧
        StepModulo R (ρ.apply p) v ∧ EquivB (plug f (k.map ρ.apply) v) u := by
  constructor
  · intro step
    rcases (all_steps_iff f _ _).mp step with root|⟨t,ht,w,context,fire,whole,out⟩
    · exact .inl root
    · rw [StableVariants.flatten_apply] at ht
      obtain ⟨p,hp,htp⟩ := List.mem_flatMap.mp ht
      obtain ⟨outer,source⟩ := expose f hp
      obtain ⟨inner,within⟩ := expose f htp
      obtain ⟨combined,layout⟩ := nested_plug f (outer.map ρ.apply) inner
      have start := (specialize ρ source).trans ((plug_congr f _ within).trans (layout t))
      have child := (all_steps_iff f (ρ.apply p) _).mpr
        (Or.inr ⟨t,htp,w,inner,fire,within,EquivB.refl _⟩)
      exact .inr ⟨p,hp,outer,_,source,child,(layout w).trans
        ((same_context f start whole (.refl t) w).trans out)⟩
  · rintro (root|⟨p,_,k,v,source,child,out⟩)
    · exact (all_steps_iff f _ _).mpr (.inl root)
    · exact replay (specialize ρ source) child out

/-- A driver can precompute a specific complement for each source slot.
Equivalent factors at different indices may share narrowing results. The
chosen slot's own complement reconstructs the same specialized successor. -/
theorem ac_slots_iff [DecidableEq s.ACSym] {I : Type} (f : s.ACSym) (q : Term s)
    (entry : I → Term s) (rest : I → Option (Term s))
    (allSlots : ∀ p ∈ ACRepresentation.flatten f q, ∃ i, EquivB (entry i) p)
    (whole : ∀ i, EquivB q (plug f (rest i) (entry i))) (ρ : Substitution s) (u : Term s) :
    StepModulo R (ρ.apply q) u ↔ Occurrence R f (ρ.apply q) u ∨
      ∃ i v, StepModulo R (ρ.apply (entry i)) v ∧ EquivB (plug f ((rest i).map ρ.apply) v) u := by
  constructor
  · intro step
    rcases (ac_positions_iff f q ρ u).mp step with root|⟨p,hp,k,v,source,⟨a,b,l,fire,r⟩,out⟩
    · exact .inl root
    · obtain ⟨i,e⟩ := allSlots p hp
      have ep : EquivB (ρ.apply (entry i)) (ρ.apply p) := e.subst ρ.image
      exact .inr ⟨i,v,⟨a,b,ep.trans l,fire,r⟩,
        (same_context f (specialize ρ (whole i)) (specialize ρ source) ep v).trans out⟩
  · rintro (root|⟨i,v,child,out⟩)
    · exact (all_steps_iff f _ _).mpr (.inl root)
    · exact replay (specialize ρ (whole i)) child out

/-- Normality of the images of the source factors suffices. A source
variable may contribute arbitrarily many factors at the same AC head. -/
theorem ac_iff [DecidableEq s.ACSym] (f : s.ACSym) (q : Term s) (ρ : Substitution s)
    (normal : ∀ t ∈ ACRepresentation.flatten f q, Normal R (ρ.apply t)) (u : Term s) :
    StepModulo R (ρ.apply q) u ↔ Occurrence R f (ρ.apply q) u := by
  apply step_iff f
  rw [StableVariants.flatten_apply]
  intro t ht
  obtain ⟨p,hp,mem⟩ := List.mem_flatMap.mp ht
  exact ((DHProduct.subgroup_normal_iff f _).mp (normal p hp)).1 t mem

theorem free_iff (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (ρ : Substitution s)
    (normal : ∀ i, Normal R (ρ.apply (xs i))) (u : Term s) :
    StepModulo R (ρ.apply (.free f xs)) u ↔ AtRoot R (ρ.apply (.free f xs)) u := by
  change StepModulo R (.free f (fun i => ρ.apply (xs i))) u ↔ _
  rw [ContextualReduction.free_iff]
  exact ⟨fun h => h.elim id (fun ⟨i,v,st,_⟩ => (normal i v st).elim),Or.inl⟩

theorem comm_iff (f : s.CSym) (a b : Term s) (ρ : Substitution s)
    (left : Normal R (ρ.apply a)) (right : Normal R (ρ.apply b)) (u : Term s) :
    StepModulo R (ρ.apply (.comm f a b)) u ↔ AtRoot R (ρ.apply (.comm f a b)) u := by
  change StepModulo R (.comm f (ρ.apply a) (ρ.apply b)) u ↔ _
  rw [ContextualReduction.comm_iff]
  exact ⟨fun h => h.elim id (fun cs => cs.elim
    (fun ⟨v,st,_⟩ => (left v st).elim) (fun ⟨v,st,_⟩ => (right v st).elim)),Or.inl⟩

/-- Stable operands can be arbitrary open terms. Their images under any
normalized assignment are sufficient for the flat AC narrowing guard. -/
theorem ac_stable_iff [DecidableEq s.ACSym] (f : s.ACSym) (q : Term s)
    (stable : ∀ t ∈ ACRepresentation.flatten f q, StableVariants.Stable R t)
    (ρ : Substitution s) (hn : Normalized R ρ) (u : Term s) :
    StepModulo R (ρ.apply q) u ↔ Occurrence R f (ρ.apply q) u :=
  ac_iff f q ρ (fun t ht => stable t ht ρ hn) u

/-- A free or C root occurrence gives a rule assignment with precisely
the original subject and successor, including the orientation modulo B. -/
theorem root_iff_instances (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (a b : Term s) :
    AtRoot (ruleRoot rules) a b ↔ ∃ r ∈ rules, head r.lhs = head a ∧ ∃ τ : Substitution s,
      EquivB a (τ.apply r.lhs) ∧ EquivB (τ.apply r.rhs) b := by
  constructor
  · rintro ⟨_,_,e,⟨r,hr,τ,rfl,rfl⟩,out⟩
    exact ⟨r,hr,(instance_head r (apps r hr) τ).symm.trans e.head_eq.symm,τ,e,out⟩
  · rintro ⟨r,hr,_,τ,e,out⟩
    exact ⟨_,_,e,⟨r,hr,τ,rfl,rfl⟩,out⟩

end Tamarin.Rewriting.NarrowingPositions
