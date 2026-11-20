import Tamarin.MaudeOperations
import Tamarin.Cancellation
import Tamarin.ConstructorVariants
import Tamarin.NarrowingFrontier
import Tamarin.SortClash

/-! A termination and confluence criterion for finite oriented rule tables
modulo C/AC. A normalized instance of each root rule must have a unique
normal form. For each AC head, the reachable product of normal classes must
be associative and commutative. Inert AC constructors satisfy this directly. -/
namespace Tamarin.Rewriting.NormalAlgebra
open Cancellation ConstructorVariants
variable {sig : Signature} {R : Root sig} {rs : Problem sig}

private theorem exists_rep (q : Class sig) : ∃ t, classOf t = q := by
  induction q using Quotient.inductionOn with
  | h t => exact ⟨t,rfl⟩

noncomputable def representative (q : Class sig) : Term sig := (exists_rep q).choose

theorem representative_class (q : Class sig) : classOf (representative q) = q := (exists_rep q).choose_spec

abbrev Value (R : Root sig) := {q : Class sig // Normal R (representative q)}

noncomputable abbrev Value.rep (x : Value R) : Term sig := representative x.val

theorem Value.normal (x : Value R) : Normal R x.rep := x.property

theorem Value.class_rep (x : Value R) : classOf x.rep = x.val := representative_class _

theorem Value.eq_of_rep {x y : Value R} (e : EquivB x.rep y.rep) : x = y :=
  Subtype.ext (x.class_rep.symm.trans ((Quotient.sound e).trans y.class_rep))

noncomputable def value (t : Term sig) (h : Normal R t) : Value R :=
  ⟨classOf t,(normal_equiv R (Quotient.exact (representative_class (classOf t))).symm).mp h⟩

theorem value_rep (t : Term sig) (h : Normal R t) : EquivB t (value t h).rep :=
  (Quotient.exact (representative_class (classOf t))).symm

/-- A simultaneous choice of reachable normal forms for a binary AC head.
The carrier already identifies structurally equivalent representatives. -/
structure Product (f : sig.ACSym) (R : Root sig) where
  mul : Value R → Value R → Value R
  reaches : ∀ a b, Reduces R (Term.ac f a.rep b.rep) (mul a b).rep
  comm : ∀ a b, mul a b = mul b a
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

/-- A single row needs this property only after its variable images are normal. -/
def Unique (R : Root sig) (t : Term sig) :=
  ∀ {a b}, NormalForm R t a → NormalForm R t b → EquivB a b

def UniqueRow (rules : Problem sig) (r : Equation sig) :=
  ∀ σ, Normalized (ruleRoot rules) σ → Unique (ruleRoot rules) (σ.apply r.lhs)

structure Presentation (rs : Problem sig) : Prop where
  apps : ∀ r ∈ rs, Application r.lhs
  terminating : WellFounded fun b a => StepModulo (ruleRoot rs) a b
  sortPreserving : ∀ {a b}, StepModulo (ruleRoot rs) a b → ∀ k, HasSort a k → HasSort b k

private theorem exists_normal {R : Root sig} (wf : WellFounded fun b a => StepModulo R a b)
    (t : Term sig) : ∃ u, Reduces R t u ∧ Normal R u := by
  induction t using wf.induction with
  | h t ih =>
    by_cases h : ∃ u, StepModulo R t u
    · obtain ⟨u,step⟩ := h
      obtain ⟨v,path,norm⟩ := ih u step
      exact ⟨v,(Reduces.step step).trans path,norm⟩
    · exact ⟨t,.basis (.refl _),fun u st => h ⟨u,st⟩⟩

private noncomputable def chosen (tab : Presentation rs) (t : Term sig) : Value (ruleRoot rs) :=
  let h := exists_normal tab.terminating t
  value h.choose h.choose_spec.2

private theorem chosen_reaches (tab : Presentation rs) (t : Term sig) :
    Reduces (ruleRoot rs) t (chosen tab t).rep :=
  (exists_normal tab.terminating t).choose_spec.1.trans (.basis (value_rep _ (exists_normal tab.terminating t).choose_spec.2))

private theorem sorted (tab : Presentation rs) {a b : Term sig} (path : Reduces (ruleRoot rs) a b)
    (k) : HasSort a k → HasSort b k :=
  RootNarrowing.reduction_invariant (fun t => HasSort t k)
    (fun h eq => Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete h))
    (fun h st => tab.sortPreserving st k h) path

/-- The free AC constructor descends directly to a product on normal classes. -/
noncomputable def inertProduct (tab : Presentation rs) (f : sig.ACSym) (unused : Head.ac f ∉ ruleHeads rs) :
    Product f (ruleRoot rs) := by
  let nf (a b : Value (ruleRoot rs)) : Normal (ruleRoot rs) (.ac f a.rep b.rep) :=
    constructor_node_normal _ tab.apps _ unused ⟨a.normal,b.normal⟩
  exact {
    mul := fun a b => value _ (nf a b)
    reaches := fun a b => .basis (value_rep _ _)
    comm := fun a b => Subtype.ext (Quotient.sound (EquivB.ac_swap f a.rep b.rep))
    assoc := fun a b c => Subtype.ext (Quotient.sound
      (((EquivB.ac_congr f (value_rep _ _).symm (.refl c.rep)).trans
        (.ac_assoc f a.rep b.rep c.rep)).trans (.ac_congr _ (.refl a.rep) (value_rep _ _)))) }

/-- Pick the normal result of a C application once per structural class,
so exchanging its two arguments always makes the same choice. -/
private noncomputable def commValue (tab : Presentation rs) (f : sig.CSym) (a b : Value (ruleRoot rs)) :=
  chosen tab (representative (classOf (.comm f a.rep b.rep)))

private noncomputable def model (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs)) :
    Model sig where
  Carrier := Value (ruleRoot rs)
  atom a := chosen tab (.atom a)
  free f xs := chosen tab (.free f (fun i => (xs i).rep))
  comm := commValue tab
  ac f := (p f).mul
  comm_swap f a b := congrArg (fun q => chosen tab (representative q)) (Quotient.sound (EquivB.comm_swap f a.rep b.rep))
  ac_swap f := (p f).comm
  ac_assoc f := (p f).assoc

private noncomputable abbrev interp (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs))
    (t : Term sig) := (model tab p).eval (fun v => chosen tab (.var v)) t

private theorem reaches (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs)) (t : Term sig) :
    Reduces (ruleRoot rs) t (interp tab p t).rep := by
  induction t with
  | var v => exact chosen_reaches tab _
  | atom a => exact chosen_reaches tab _
  | free f xs ih => exact (Reduces.free f _ _ ih).trans (chosen_reaches tab _)
  | comm f a b l r =>
    apply (Reduces.comm f l r).trans
    exact (Reduces.basis (Quotient.exact (representative_class _)).symm).trans (chosen_reaches tab _)
  | ac f a b l r => exact (Reduces.ac f l r).trans ((p f).reaches (interp tab p a) (interp tab p b))

private theorem subst_congr (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs))
    (σ τ : Substitution sig) (agree : ∀ v, interp tab p (σ.image v) = interp tab p (τ.image v))
    (t : Term sig) : interp tab p (σ.apply t) = interp tab p (τ.apply t) := by
  induction t with
  | var => apply agree
  | atom => rfl
  | free f _ ih => exact congrArg ((model tab p).free f) (funext ih)
  | comm f _ _ l r => exact (congrArg (fun x => (model tab p).comm f x _) l).trans (congrArg ((model tab p).comm f _) r)
  | ac f _ _ l r => exact (congrArg (fun x => (model tab p).ac f x _) l).trans (congrArg ((model tab p).ac f _) r)

private theorem root_equal (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs))
    (rows : ∀ r ∈ rs, UniqueRow rs r)
    {a b : Term sig} (step : ruleRoot rs a b) : interp tab p a = interp tab p b := by
  classical
  obtain ⟨row,mem,σ,rfl,rfl⟩ := step
  let τ : Substitution sig := {
    image := fun v => if v ∈ σ.support then (interp tab p (σ.image v)).rep else .var v
    support := σ.support
    outside := fun v h => ite_eq_right h
    sorted := fun v => by split <;> first | exact sorted tab (reaches tab p _) _ (σ.sorted v) | exact HasSort.var _ }
  have norm : Normalized (ruleRoot rs) τ := by
    intro v
    dsimp [τ]; split
    · exact Value.normal _
    · exact (constructor_normal rs tab.apps).1 v
  have equal v : interp tab p (σ.image v) = interp tab p (τ.image v) := by
    dsimp [τ]; split
    · exact Value.eq_of_rep (normal_reduces_equiv (reaches tab p _) (Value.normal _))
    · rw [σ.outside _ (by assumption)]
  have unique : Unique (ruleRoot rs) (τ.apply row.lhs) := rows row mem τ norm
  apply (subst_congr tab p σ τ equal row.lhs).trans
  apply Eq.trans _ (subst_congr tab p σ τ equal row.rhs).symm
  apply Value.eq_of_rep
  let l := reaches tab p (τ.apply row.lhs)
  let fire : Reduces (ruleRoot rs) (τ.apply row.lhs) (τ.apply row.rhs) :=
    .step ⟨_,_,.refl _,.root ⟨row,mem,τ,rfl,rfl⟩,.refl _⟩
  let r := fire.trans (reaches tab p (τ.apply row.rhs))
  exact unique ⟨l,(interp tab p _).normal,sorted tab l⟩ ⟨r,(interp tab p _).normal,sorted tab r⟩

private theorem step_equal (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs))
    (rows : ∀ r ∈ rs, UniqueRow rs r)
    {a b : Term sig} (step : Step (ruleRoot rs) a b) : interp tab p a = interp tab p b := by
  induction step with
  | root h => exact root_equal tab p rows h
  | free f xs i _ ih =>
    apply congrArg ((model tab p).free f); funext j
    by_cases h : j = i
    · simpa [h] using ih
    · simp [h]
  | comm_left f c _ h => exact congrArg (fun x => (model tab p).comm f x _) h
  | comm_right f c _ h => exact congrArg ((model tab p).comm f _) h
  | ac_left f c _ h => exact congrArg (fun x => (model tab p).ac f x _) h
  | ac_right f c _ h => exact congrArg ((model tab p).ac f _) h

private theorem invariant (tab : Presentation rs) (p : ∀ f, Product f (ruleRoot rs))
    (rows : ∀ r ∈ rs, UniqueRow rs r)
    {a b : Term sig} (red : Reduces (ruleRoot rs) a b) : interp tab p a = interp tab p b := by
  induction red with
  | basis e => exact e.eval_eq _ _
  | step st =>
    obtain ⟨_,_,l,st,r⟩ := st
    exact (l.eval_eq _ _).trans ((step_equal tab p rows st).trans (r.eval_eq _ _))
  | trans _ _ l r => exact l.trans r
  | free f _ _ _ h => exact congrArg ((model tab p).free f) (funext h)
  | comm f _ _ l r =>
    exact (congrArg (fun x => (model tab p).comm f x _) l).trans (congrArg ((model tab p).comm f _) r)
  | ac f _ _ l r =>
    exact (congrArg (fun x => (model tab p).ac f x _) l).trans (congrArg ((model tab p).ac f _) r)

/-- The per-head and normalized-instance obligations imply confluence of
every rewrite, including overlaps below variables and at AC subproducts. -/
theorem Presentation.canonical (tab : Presentation rs)
    (p : ∀ f, Product f (ruleRoot rs))
    (rows : ∀ r ∈ rs, UniqueRow rs r) : MaudeOperations.CanonicalPresentation (ruleRoot rs) where
  terminating := tab.terminating
  sortPreserving := tab.sortPreserving
  confluent := by
    intro t a b left right
    have eq := (invariant tab p rows left).symm.trans (invariant tab p rows right)
    exact ⟨_,(reaches tab p a).trans (.basis (eq ▸ EquivB.refl _)),reaches tab p b⟩

/-- Standalone presentations with user-defined free/C rules and inert AC
constructors only need the normalized row checks. -/
theorem Presentation.canonical_of_inert_ac (tab : Presentation rs)
    (inert : ∀ f, Head.ac f ∉ ruleHeads rs) (rows : ∀ r ∈ rs, UniqueRow rs r) :
    MaudeOperations.CanonicalPresentation (ruleRoot rs) :=
  tab.canonical (fun f => inertProduct tab f (inert f)) rows

end Tamarin.Rewriting.NormalAlgebra
