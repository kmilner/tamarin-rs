import Tamarin.NarrowingPositions
import Tamarin.VariantFrontier

/-! Complete one-step narrowing assembled from ordinary unifiers. Each branch
keeps a substitution on all visible variables and a replacement term. When
the replacement is put back under a parent, the same substitution is applied
to every untouched sibling. -/
namespace Tamarin.Rewriting.RootNarrowing
open VariantJoin ACSubproductReduction
variable {s : Signature} {I : Type}

structure Branch (s : Signature) where
  subst : Substitution s
  value : Term s

/-- Any specialized semantic transition has a branch covering the visible
variables and the result with a single witness. The admissibility predicate
can, for example, require every instantiated input image to be normal. -/
def CoversStep (scope : Variable → Prop) (admit : Substitution s → Prop)
    (step : Substitution s → Term s → Prop) (branches : Branch s → Prop) : Prop :=
  ∀ ρ, admit ρ → ∀ u, step ρ u → ∃ b, branches b ∧ FitsOn scope ρ u b.subst b.value

theorem CoversStep.of_schemas {R : Root s} (redex : Term s) (anchors : List (Term s))
    (admit : Substitution s → Prop) (step : Substitution s → Term s → Prop)
    (schemas : List (Schema R))
    (instances : ∀ ρ, admit ρ → ∀ u, step ρ u → ∃ p ∈ schemas, ∃ τ : Substitution s,
      EquivB (ρ.apply redex) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs))
    (apart : ∀ p ∈ schemas, ∀ v, p.lhs.Occurs v → ¬(redex.Occurs v ∨ Observed anchors v))
    (answers : Schema R → List (Substitution s))
    (checked : ∀ p ∈ schemas, CompleteSet (p.problem redex) (answers p))
    (reserved : ∀ p ∈ schemas, ∀ μ ∈ answers p, Reserves (p.problem redex) anchors μ) :
    CoversStep (Observed anchors) admit step (fun b => ∃ p ∈ schemas, ∃ μ ∈ answers p,
      b = ⟨μ,μ.apply p.rhs⟩) := by
  intro ρ hρ u st
  obtain ⟨p,hp,τ,l,r⟩ := instances ρ hρ u st
  obtain ⟨μ,hm,δ,agr,value⟩ := (p.lift_in_context redex anchors (apart p hp) (checked p hp)
    (reserved p hp) ρ u).mp ⟨τ,l,r⟩
  exact ⟨_,⟨p,hp,μ,hm,rfl⟩,δ,fun v hv => agr v (.inr hv),value⟩

/-- Standardizing a rule apart preserves both sides under a single
assignment. For an AC extension the remainder variable is renamed as well. -/
def Schema.Presents {R : Root s} (p : Schema R) (r : Equation s) : Prop :=
  ∃ π : VariablePermutation, p.lhs = (π.subst s).apply r.lhs ∧ p.rhs = (π.subst s).apply r.rhs

theorem Schema.Presents.instance {R : Root s} {p : Schema R} {r : Equation s}
    (hp : p.Presents r) (τ : Substitution s) :
    ∃ η : Substitution s, η.apply p.lhs = τ.apply r.lhs ∧ η.apply p.rhs = τ.apply r.rhs := by
  obtain ⟨π,l,h⟩ := hp
  exact ⟨τ.compose (π.inverse.subst s),by rw [l,Substitution.apply_compose,π.inverse_apply],
    by rw [h,Substitution.apply_compose,π.inverse_apply]⟩

def HasInstance {R : Root s} (schemas : List (Schema R)) (a u : Term s) : Prop :=
  ∃ p ∈ schemas, ∃ τ : Substitution s, EquivB a (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs)

/-- A single complete head bucket supplies the root hypothesis of
`CoversStep.of_schemas` for free or commutative applications. -/
theorem instances_at_root (rules : List (Equation s)) (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (a u : Term s) (schemas : List (Schema (ruleRoot rules)))
    (bucket : ∀ r ∈ rules, ConstructorVariants.head r.lhs = ConstructorVariants.head a →
      ∃ p ∈ schemas, p.Presents r) (step : ContextualReduction.AtRoot (ruleRoot rules) a u) :
    HasInstance schemas a u := by
  obtain ⟨r,hr,hd,τ,l,h⟩ := (NarrowingPositions.root_iff_instances rules apps a u).mp step
  obtain ⟨p,hp,opening⟩ := bucket r hr hd
  obtain ⟨η,el,er⟩ := opening.instance τ
  exact ⟨p,hp,η,el ▸ l,er ▸ h.symm⟩

/-- Bare and one-remainder schemas suffice for the AC root hypothesis,
even when a caller variable specializes to several factors at that head. -/
theorem instances_at_ac (rules : List (Equation s)) (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (f : s.ACSym) (a u : Term s) (typed : HasSort a (s.acSort f))
    (bound : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .ac f → ∀ v, r.rhs.Occurs v → r.lhs.Occurs v)
    (z : Equation s → Variable) (sort : ∀ r ∈ rules, (z r).sort = s.acSort f)
    (fresh : ∀ r ∈ rules, ¬r.lhs.Occurs (z r)) (schemas : List (Schema (ruleRoot rules)))
    (bucket : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .ac f →
      ∀ ext, ∃ p ∈ schemas, p.Presents (pattern f (z r) r ext))
    (step : Occurrence (ruleRoot rules) f a u) : HasInstance schemas a u := by
  obtain ⟨r,hr,hd,ext,τ,l,h⟩ :=
    (occurrence_iff_instances f rules apps bound a u typed z sort fresh).mp step
  obtain ⟨p,hp,opening⟩ := bucket r hr hd ext
  obtain ⟨η,el,er⟩ := opening.instance τ
  exact ⟨p,hp,η,el ▸ l,er ▸ h.symm⟩

inductive Frame (s : Signature) where
  | free (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (i : Fin (s.arity f))
  | comm (f : s.CSym) (sibling : Term s)
  | ac (f : s.ACSym) (rest : Option (Term s))

def Frame.fill : Frame s → Substitution s → Term s → Term s
  | .free f xs i, ρ, v => .free f (fun j => if j = i then v else ρ.apply (xs j))
  | .comm f t, ρ, v => .comm f v (ρ.apply t)
  | .ac f rest, ρ, v => plug f (rest.map ρ.apply) v

def Frame.Uses (frame : Frame s) (w : Variable) : Prop :=
  match frame with
  | .free _ xs i => ∃ j, j ≠ i ∧ (xs j).Occurs w
  | .comm _ t => t.Occurs w
  | .ac _ rest => ∃ t ∈ rest, t.Occurs w

/-- A proper AC complement may contain repeated variables and may grow a
different number of factors under the specialization. -/
theorem Frame.fits {scope : Variable → Prop} {ρ : Substitution s} {u : Term s} {b : Branch s}
    (frame : Frame s) (tracked : ∀ w, frame.Uses w → scope w)
    (fit : FitsOn scope ρ u b.subst b.value) :
    FitsOn scope ρ (frame.fill ρ u) b.subst (frame.fill b.subst b.value) := by
  obtain ⟨η,agree,value⟩ := fit
  refine ⟨η,agree,?_⟩
  have sibling (t : Term s) (mem : ∀ w, t.Occurs w → frame.Uses w) :
      EquivB (ρ.apply t) (η.apply (b.subst.apply t)) := by
    rw [← Substitution.apply_compose]
    exact t.subst_equiv _ _ (fun w h => agree w (tracked w (mem w h)))
  cases frame with
  | free f xs i =>
    apply EquivB.free
    intro j
    by_cases e : j = i
    · simpa [Frame.fill,e,Substitution.apply] using value
    · simpa [Frame.fill,e,Substitution.apply] using sibling (xs j) (fun _ hv => ⟨j,e,hv⟩)
  | comm f t => exact .comm_congr f value (sibling t (fun _ h => h))
  | ac f rest =>
    cases rest with
    | none => exact value
    | some t => exact .ac_congr f value (sibling t (fun _ h => ⟨t,rfl,h⟩))

/-- Combine a complete search at the root with complete recursive searches
on the exposed operands. An indexed frame supplies the original complement.
At an AC head the root alternatives include matches against subproducts. -/
theorem CoversStep.contexts {J : Type} {scope : Variable → Prop} {admit : Substitution s → Prop}
    {whole root : Substitution s → Term s → Prop} {child : J → Substitution s → Term s → Prop}
    {roots : Branch s → Prop} {children : J → Branch s → Prop} (frame : J → Frame s)
    (tracked : ∀ j v, (frame j).Uses v → scope v)
    (positions : ∀ ρ, admit ρ → ∀ u, whole ρ u → root ρ u ∨
      ∃ j v, child j ρ v ∧ EquivB ((frame j).fill ρ v) u)
    (atRoot : CoversStep scope admit root roots)
    (below : ∀ j, CoversStep scope admit (child j) (children j)) :
    CoversStep scope admit whole (fun b => roots b ∨ ∃ j a, children j a ∧
      b = ⟨a.subst,(frame j).fill a.subst a.value⟩) := by
  intro ρ ok u st
  rcases positions ρ ok u st with r | ⟨j,v,hv,after⟩
  · obtain ⟨b,hb,fit⟩ := atRoot ρ ok u r
    exact ⟨b,.inl hb,fit⟩
  · obtain ⟨a,ha,fit⟩ := below j ρ ok v hv
    obtain ⟨η,agr,value⟩ := (frame j).fits (tracked j) fit
    exact ⟨_,.inr ⟨j,a,ha,rfl⟩,η,agr,after.symm.trans value⟩

/-- Completeness at a source position, including all rewrites that become
possible only after specializing that position. -/
abbrev Search (R : Root s) (scope : Variable → Prop) (admit : Substitution s → Prop)
    (t : Term s) := CoversStep scope admit (fun ρ u => StepModulo R (ρ.apply t) u)

def framed {J : Type} (frame : J → Frame s) (roots : Branch s → Prop)
    (children : J → Branch s → Prop) (b : Branch s) : Prop :=
  roots b ∨ ∃ j a, children j a ∧ b = ⟨a.subst,(frame j).fill a.subst a.value⟩

variable {R : Root s} {scope : Variable → Prop} {admit : Substitution s → Prop}
    {roots : Branch s → Prop}

theorem search_free (f : s.FreeSym) (xs : Fin (s.arity f) → Term s)
    (children : Fin (s.arity f) → Branch s → Prop)
    (tracked : ∀ i v, (Frame.free f xs i).Uses v → scope v)
    (root : CoversStep scope admit (fun ρ u => ContextualReduction.AtRoot R (ρ.apply (.free f xs)) u) roots)
    (below : ∀ i, Search R scope admit (xs i) (children i)) :
    Search R scope admit (.free f xs) (framed (Frame.free f xs) roots children) :=
  CoversStep.contexts (Frame.free f xs) tracked
    (fun ρ _ u => (ContextualReduction.free_iff f (fun i => ρ.apply (xs i)) u).mp) root below

theorem search_comm (f : s.CSym) (xs : Bool → Term s) (children : Bool → Branch s → Prop)
    (tracked : ∀ i v, (xs (!i)).Occurs v → scope v)
    (root : CoversStep scope admit
      (fun ρ u => ContextualReduction.AtRoot R (ρ.apply (.comm f (xs false) (xs true))) u) roots)
    (below : ∀ i, Search R scope admit (xs i) (children i)) :
    Search R scope admit (.comm f (xs false) (xs true))
      (framed (fun i => Frame.comm f (xs (!i))) roots children) := by
  apply CoversStep.contexts (fun i => Frame.comm f (xs (!i))) tracked _ root below
  intro ρ _ u st
  rcases (ContextualReduction.comm_iff f _ _ u).mp st with atRoot|⟨v,fire,out⟩|⟨v,fire,out⟩
  · exact .inl atRoot
  · exact .inr ⟨false,v,fire,out⟩
  · exact .inr ⟨true,v,fire,(EquivB.comm_swap ..).trans out⟩

theorem search_ac [DecidableEq s.ACSym] {J : Type} (f : s.ACSym) (q : Term s)
    (entry : J → Term s) (rest : J → Option (Term s)) (children : J → Branch s → Prop)
    (allSlots : ∀ p ∈ ACRepresentation.flatten f q, ∃ i, EquivB (entry i) p)
    (whole : ∀ i, EquivB q (plug f (rest i) (entry i)))
    (tracked : ∀ i v, (Frame.ac f (rest i)).Uses v → scope v)
    (root : CoversStep scope admit (fun ρ u => Occurrence R f (ρ.apply q) u) roots)
    (below : ∀ i, Search R scope admit (entry i) (children i)) :
    Search R scope admit q (framed (fun i => Frame.ac f (rest i)) roots children) :=
  CoversStep.contexts (fun i => Frame.ac f (rest i)) tracked
    (fun ρ _ u => (NarrowingPositions.ac_slots_iff f q entry rest allSlots whole ρ u).mp) root below

/-- A subtree of a normalized caller image is normal, including after the
substitution that specializes all siblings. Iterate this lemma down the path
from an observable input to an occurrence skipped by the search. -/
theorem Frame.child_normal (frame : Frame s) (ρ : Substitution s) (t : Term s)
    (hn : Normal R (frame.fill ρ t)) : Normal R t := by
  cases frame with
  | free f xs i =>
    simpa [Frame.fill] using normal_free_child f _ hn i
  | comm f sibling => exact (normal_comm_children f hn).1
  | ac f rest =>
    cases rest with
    | none => exact hn
    | some r => exact (normal_ac_children f hn).1

theorem search_protected (t : Term s) (normal : ∀ ρ, admit ρ → Normal R (ρ.apply t)) :
    Search R scope admit t (fun _ => False) :=
  fun ρ h u st => (normal ρ h u st).elim

def Branch.state (b : Branch s) (q : State s I) : State s I :=
  ⟨fun i => b.subst.apply (q.input i),fun _ => b.value⟩

/-- Encoded rows may be renamed, reordered or folded immediately. Their
whole inputs and intermediate value must have a common instance witness. -/
theorem successors_of_branches {rules : List (Equation s)} (q : State s I) (out : List (State s I))
    (scope : Variable → Prop) (visible : ∀ i v, (q.input i).Occurs v → scope v)
    (branches : Branch s → Prop)
    (traversed : CoversStep scope (fun ρ => ∀ i, Normal (ruleRoot rules) (ρ.apply (q.input i)))
      (fun ρ u => StepModulo (ruleRoot rules) (ρ.apply (q.value ())) u) branches)
    (read : ∀ b, branches b → ∃ r ∈ out, r.Subsumes (b.state q)) :
    Successors rules q out := by
  intro ρ hn u step
  obtain ⟨b,hb,η,agr,value⟩ := traversed ρ hn u step
  obtain ⟨r,mem,δ,fit⟩ := read b hb
  have h : VariantJoin.Fits (b.state q) (fun i => ρ.apply (q.input i)) (fun _ => u) η := by
    refine ⟨fun i => ?_,fun _ => value⟩
    change EquivB (ρ.apply (q.input i)) (η.apply (b.subst.apply (q.input i)))
    rw [← Substitution.apply_compose]
    exact (q.input i).subst_equiv _ _ (fun v hv => agr v (visible i v hv))
  exact ⟨r,mem,η.compose δ,fit.compose h⟩

end Tamarin.Rewriting.RootNarrowing
