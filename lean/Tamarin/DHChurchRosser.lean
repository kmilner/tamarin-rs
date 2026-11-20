import Tamarin.DHChurchRosserAlgebra
import Tamarin.DHStaging

/-! Semantic confluence for the exact DH rules. Variables in a root rewrite
may denote reducible terms. Interpret them first in the normal-form algebra,
then validate the complete schema on these shared normal message values. -/
namespace Tamarin.Rewriting.DHPeer.ChurchRosser
open Cancellation ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem exists_normal {R : Root sig} (wf : WellFounded fun b a => StepModulo R a b)
    (t : Term sig) : ∃ u, Reduces R t u ∧ Normal R u := by
  induction t using wf.induction with
  | h t ih =>
    by_cases h : ∃ u, StepModulo R t u
    · obtain ⟨u,step⟩ := h
      obtain ⟨v,path,norm⟩ := ih u step
      exact ⟨v,(Reduces.step step).trans path,norm⟩
    · exact ⟨t,.basis (.refl _),fun u st => h ⟨u,st⟩⟩

private noncomputable def chosen (tab : ExactTable E) (t : Term sig) : Value (ruleRoot T.rules) :=
  let h := exists_normal tab.terminating t
  value h.choose h.choose_spec.2

private theorem chosen_reaches (tab : ExactTable E) (t : Term sig) :
    Reduces (ruleRoot T.rules) t (chosen tab t).rep :=
  (exists_normal tab.terminating t).choose_spec.1.trans (.basis (value_rep _ (exists_normal tab.terminating t).choose_spec.2))

private theorem sorted (tab : ExactTable E) {a b : Term sig} (path : Reduces (ruleRoot T.rules) a b)
    (k) : HasSort a k → HasSort b k :=
  RootNarrowing.reduction_invariant (fun t => HasSort t k)
    (fun h eq => Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete h))
    (fun h st => tab.sortPreserving st k h) path

private theorem comm_normal (tab : ExactTable E) (f : sig.CSym) (a b : Value (ruleRoot T.rules)) :
    Normal (ruleRoot T.rules) (.comm f a.rep b.rep) :=
  constructor_node_normal _ tab.apps _ (tab.absent (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h)) ⟨a.normal,b.normal⟩

private theorem inert_ac (tab : ExactTable E) (f : sig.ACSym) (h : f ≠ s.mul) (a b : Value (ruleRoot T.rules)) :
    Normal (ruleRoot T.rules) (.ac f a.rep b.rep) :=
  constructor_node_normal _ tab.apps _ (tab.absent (fun eq => h (Head.ac.inj eq)) (by intro e; cases e)
    (by intro e; cases e)) ⟨a.normal,b.normal⟩

private noncomputable def commValue (tab : ExactTable E) (f : sig.CSym) (a b : Value (ruleRoot T.rules)) :=
  value _ (comm_normal tab f a b)

private noncomputable def acValue [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    (f : sig.ACSym) (a b : Value (ruleRoot T.rules)) :=
  if h : f = s.mul then p.mul a b else value _ (inert_ac tab f h a b)

private noncomputable def model [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules)) :
    Model sig where
  Carrier := Value (ruleRoot T.rules)
  atom a := chosen tab (.atom a)
  free f xs := chosen tab (.free f (fun i => (xs i).rep))
  comm := commValue tab
  ac := acValue tab p
  comm_swap f a b := Subtype.ext (Quotient.sound (EquivB.comm_swap f a.rep b.rep))
  ac_swap f a b := by
    by_cases h : f = s.mul
    · simpa [acValue,h] using p.comm a b
    · simpa only [acValue,dite_eq_right h] using
        (show value _ (inert_ac tab f h a b) = value _ (inert_ac tab f h b a) from
          Subtype.ext (Quotient.sound (EquivB.ac_swap f a.rep b.rep)))
  ac_assoc f a b c := by
    by_cases h : f = s.mul
    · simpa [acValue,h] using p.assoc a b c
    · simp only [acValue,dite_eq_right h]
      apply Subtype.ext
      apply Quotient.sound
      exact ((EquivB.ac_congr f (value_rep _ _).symm (.refl c.rep)).trans
        (.ac_assoc f a.rep b.rep c.rep)).trans (.ac_congr _ (.refl a.rep) (value_rep _ _))

private noncomputable abbrev interp [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    (t : Term sig) := (model tab p).eval (fun v => chosen tab (.var v)) t

private theorem reaches [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules)) (t : Term sig) :
    Reduces (ruleRoot T.rules) t (interp tab p t).rep := by
  induction t with
  | var v => exact chosen_reaches tab _
  | atom a => exact chosen_reaches tab _
  | free f xs ih => exact (Reduces.free f _ _ ih).trans (chosen_reaches tab _)
  | comm f a b l r => exact (Reduces.comm f l r).trans (.basis (value_rep _ (comm_normal tab f _ _)))
  | ac f a b l r =>
    apply (Reduces.ac f l r).trans
    change Reduces _ _ (acValue tab p f _ _).rep
    by_cases h : f = s.mul
    · subst f; simp only [acValue,dite_true]; exact p.reaches (interp tab p a) (interp tab p b)
    · simp only [acValue,dite_eq_right h]; exact .basis (value_rep _ _)

private theorem expr_congr [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    (e : Expr (Fin 3)) (a b : Fin 3 → Term sig) (h : ∀ i, interp tab p (a i) = interp tab p (b i)) :
    interp tab p (e.eval s a) = interp tab p (e.eval s b) := by
  induction e with
  | var => apply h
  | one | neutral => rfl
  | inv e ih => exact congrArg (fun x => (model tab p).free s.inv (fun _ => x)) ih
  | mul _ _ l r => exact (congrArg (fun x => (model tab p).ac s.mul x _) l).trans (congrArg ((model tab p).ac s.mul _) r)
  | pow _ _ l r =>
    apply congrArg ((model tab p).free s.pow); funext i
    change interp tab p (if _ then _ else _) = interp tab p (if _ then _ else _)
    split <;> assumption

private def Unique (R : Root sig) (t : Term sig) :=
  ∀ {a b}, NormalForm R t a → NormalForm R t b → EquivB a b

private theorem signed_unique [DecidableEq sig.ACSym] (tab : ExactTable E) {t : Term sig}
    (ht : HasSort t .msg) (h : Staging.Signed s (ruleRoot T.rules) t) : Unique (ruleRoot T.rules) t := by
  intro a b l r
  exact Balance.normal_unique tab.inventory E.presentation (fun _ => Balance.plain_of_inverse E) h
    (l.2.2 _ ht) (r.2.2 _ ht) l.2.1 r.2.1 l.1 r.1

private theorem neutral_normal (tab : ExactTable E) : Normal (ruleRoot T.rules) s.neutralTerm := by
  refine constructor_node_normal _ tab.apps _ ?_ ?_
  · apply tab.absent
    · intro h; cases h
    · intro h; have eq := congrArg sig.arity (Head.free.inj h); simp [s.neutralArity,s.invArity] at eq
    · intro h; have eq := congrArg sig.arity (Head.free.inj h); simp [s.neutralArity,s.powArity] at eq
  · intro i; exact Fin.elim0 (s.neutralArity ▸ i)

private theorem schema_unique [DecidableEq sig.ACSym] (tab : ExactTable E) (r : Rule)
    (a : Fin 3 → Term sig) (ty : ∀ i, HasSort (a i) .msg) (nf : ∀ i, Normal (ruleRoot T.rules) (a i)) :
    Unique (ruleRoot T.rules) (r.instantiate s a).lhs := by
  have typ := r.equation.1.sorted s a ty
  have signed i : Staging.Signed s (ruleRoot T.rules) (a i) := fun k => Balance.defined s _ k (nf i)
  have unit : Staging.Signed s (ruleRoot T.rules) s.product.one := fun k => ⟨0,Balance.read_one ..⟩
  cases r
  case expOne =>
    intro u v
    exact DHTower.Spine.unique tab.power tab.inventory tab.unit typ
      (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ (nf 0)) unit)
  case tower =>
    intro u v
    exact DHTower.Spine.unique tab.power tab.inventory tab.unit typ
      (DHTower.Spine.defined_power (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ (nf 0))
        (signed 1)) (signed 2))
  case neutral =>
    intro u v
    exact DHTower.Spine.unique tab.power tab.inventory tab.unit typ
      (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ (neutral_normal tab)) (signed 0))
  all_goals
    apply signed_unique tab typ
    solve_by_elim (maxDepth := 12) only [Staging.signed_mul,Staging.signed_inv,signed,unit]

private theorem extra_unique [DecidableEq sig.ACSym] (tab : ExactTable E) (r : ExtraRule)
    (a : Fin 3 → Term sig) (ty : ∀ i, HasSort (a i) .msg) (nf : ∀ i, Normal (ruleRoot T.rules) (a i)) :
    Unique (ruleRoot T.rules) (r.instantiate s a).lhs := by
  have typ := r.equation.1.sorted s a ty
  have signed i : Staging.Signed s (ruleRoot T.rules) (a i) := fun k => Balance.defined s _ k (nf i)
  have unit : Staging.Signed s (ruleRoot T.rules) s.product.one := fun k => ⟨0,Balance.read_one ..⟩
  cases r <;> apply signed_unique tab typ <;>
    solve_by_elim (maxDepth := 12) only [Staging.signed_mul,Staging.signed_inv,signed,unit]

/-- Equalizing an instantiated row only requires uniqueness at its normalized
schema instance. The actual substitution can contain arbitrary reducible terms. -/
private theorem equation [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    (lhs rhs : Expr (Fin 3)) (args : Fin 3 → Term sig) (typed : ∀ i, HasSort (args i) .msg)
    (use : ∀ ys : Fin 3 → Term sig, (∀ i, HasSort (ys i) .msg) → (∀ i, Normal (ruleRoot T.rules) (ys i)) →
      Unique (ruleRoot T.rules) (lhs.eval s ys) ∧ Reduces (ruleRoot T.rules) (lhs.eval s ys) (rhs.eval s ys)) :
    interp tab p (lhs.eval s args) = interp tab p (rhs.eval s args) := by
  let ys i := (interp tab p (args i)).rep
  have ty i : HasSort (ys i) .msg := sorted tab (reaches tab p _) _ (typed i)
  have norm i : Normal (ruleRoot T.rules) (ys i) := (interp tab p (args i)).normal
  have eq i : interp tab p (args i) = interp tab p (ys i) :=
    Value.eq_of_rep (normal_reduces_equiv (reaches tab p _) (norm i))
  obtain ⟨unique,step⟩ := use ys ty norm
  apply (expr_congr tab p lhs args ys eq).trans
  apply Eq.trans _ (expr_congr tab p rhs args ys eq).symm
  apply Value.eq_of_rep
  let a := reaches tab p (lhs.eval s ys)
  let b := step.trans (reaches tab p (rhs.eval s ys))
  exact unique ⟨a,(interp tab p _).normal,sorted tab a⟩ ⟨b,(interp tab p _).normal,sorted tab b⟩

private theorem root_equal [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    {a b : Term sig} (step : ruleRoot T.rules a b) : interp tab p a = interp tab p b := by
  obtain ⟨row,mem,σ,rfl,rfl⟩ := step
  rcases tab row mem with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · simp only [Rule.instantiate,Expr.subst_eval]
    apply equation tab p _ _ _
    · intro i; exact T.actualSort r i ▸ σ.sorted (T.actual r i)
    · intro ys ty nf
      exact ⟨schema_unique tab r ys ty nf,T.fire r ys ty⟩
  · simp only [ExtraRule.instantiate,Expr.subst_eval]
    apply equation tab p _ _ _
    · intro i; exact E.sorted r i ▸ σ.sorted (E.actual r i)
    · intro ys ty nf
      exact ⟨extra_unique tab r ys ty nf,.step ⟨_,_,.refl _,.root (E.fireRoot r ys ty),.refl _⟩⟩

private theorem step_equal [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    {a b : Term sig} (step : Step (ruleRoot T.rules) a b) : interp tab p a = interp tab p b := by
  induction step with
  | root h => exact root_equal tab p h
  | free f xs i _ ih =>
    apply congrArg ((model tab p).free f); funext j
    by_cases h : j = i
    · simpa [h] using ih
    · simp [h]
  | comm_left f c _ h => exact congrArg (fun x => (model tab p).comm f x _) h
  | comm_right f c _ h => exact congrArg ((model tab p).comm f _) h
  | ac_left f c _ h => exact congrArg (fun x => (model tab p).ac f x _) h
  | ac_right f c _ h => exact congrArg ((model tab p).ac f _) h

private theorem invariant [DecidableEq sig.ACSym] (tab : ExactTable E) (p : Product s (ruleRoot T.rules))
    {a b : Term sig} (red : Reduces (ruleRoot T.rules) a b) : interp tab p a = interp tab p b := by
  induction red with
  | basis e => exact e.eval_eq _ _
  | step st =>
    obtain ⟨_,_,l,st,r⟩ := st
    exact (l.eval_eq _ _).trans ((step_equal tab p st).trans (r.eval_eq _ _))
  | trans _ _ l r => exact l.trans r
  | free f _ _ _ h => exact congrArg ((model tab p).free f) (funext h)
  | comm f _ _ l r =>
    exact (congrArg (fun x => (model tab p).comm f x _) l).trans (congrArg ((model tab p).comm f _) r)
  | ac f _ _ l r =>
    exact (congrArg (fun x => (model tab p).ac f x _) l).trans (congrArg ((model tab p).ac f _) r)

/-- All thirteen rewrite equations and all their contextual and substitution
instances preserve the normal-form interpretation. Only multiplication requires
a deliberate choice on the quotient. Free-head normalization may pick *any*
reachable normal representative. -/
theorem canonical_of_product [DecidableEq sig.ACSym] (tab : ExactTable E)
    (p : Product s (ruleRoot T.rules)) : MaudeOperations.CanonicalPresentation (ruleRoot T.rules) where
  terminating := tab.terminating
  sortPreserving := tab.sortPreserving
  confluent := by
    intro t a b left right
    have eq := (invariant tab p left).symm.trans (invariant tab p right)
    exact ⟨_,(reaches tab p a).trans (.basis (eq ▸ EquivB.refl _)),reaches tab p b⟩

end Tamarin.Rewriting.DHPeer.ChurchRosser
