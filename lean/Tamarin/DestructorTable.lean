import Tamarin.ConstantDefinitions
import Tamarin.RootNormalForms
import Tamarin.CheckedReduction

/-! Constructor-pattern destructor tables. Each defined free head returns a
subterm at a common position reached through free heads. Proper patterns
may contain repeated variables and constructor C/AC symbols. -/
namespace Tamarin.DestructorTable
open Rewriting
variable {s : Signature}

def atPath (t : Term s) : List Nat → Option (Term s)
  | [] => some t
  | i :: p => match t with
    | .free f xs => if h : i < s.arity f then atPath (xs ⟨i,h⟩) p else none
    | _ => none

def paths : Term s → List (List Nat)
  | .free f xs => [] :: (List.finRange (s.arity f)).flatMap fun i => (paths (xs i)).map (i.val :: ·)
  | _ => [[]]

theorem path_mem {p : List Nat} {a b : Term s} (h : atPath a p = some b) : p ∈ paths a := by
  induction p generalizing a with
  | nil => cases a <;> simp [paths]
  | cons i p ih =>
    cases a <;> simp only [atPath] at h <;> try contradiction
    split at h <;> try contradiction
    next hi =>
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨⟨i,hi⟩,List.mem_finRange _,List.mem_map.mpr ⟨p,ih h,rfl⟩⟩)

private theorem path_size {p} {t u : Term s} (h : atPath t p = some u) :
    u.variables.Sublist t.variables ∧ FiniteOccurs.nodes u ≤ FiniteOccurs.nodes t ∧
    (p ≠ [] → FiniteOccurs.nodes u < FiniteOccurs.nodes t) := by
  induction p generalizing t with
  | nil => simp only [atPath,Option.some.injEq] at h; subst u; simp
  | cons i p ih =>
    cases t <;> simp only [atPath] at h <;> try contradiction
    split at h <;> try contradiction
    next f xs hi =>
      obtain ⟨vars,size,_⟩ := ih h
      have child := FiniteOccurs.le_sum _ (List.ofFn fun j => FiniteOccurs.nodes (xs j))
        (List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩)
      have strict := Nat.lt_succ_of_le (Nat.le_trans size child)
      exact ⟨vars.trans (List.sublist_flatten_of_mem (List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩)),Nat.le_of_lt strict,fun _ => strict⟩

theorem apply_path (σ : Substitution s) {a b : Term s} {p}
    (h : atPath a p = some b) : atPath (σ.apply a) p = some (σ.apply b) := by
  induction p generalizing a with
  | nil => simpa [atPath] using congrArg (Option.map σ.apply) h
  | cons i p ih =>
    cases a <;> simp only [atPath] at h <;> try contradiction
    split at h <;> try contradiction
    next hi => simpa [Substitution.apply,Term.subst,atPath,hi] using ih h

private theorem path_congr {a b x y : Term s} {p} (h : EquivB a b)
    (l : atPath a p = some x) (r : atPath b p = some y) : EquivB x y := by
  induction p generalizing a b with
  | nil => simp_all [atPath]
  | cons i p ih =>
    cases a <;> simp only [atPath] at l <;> try contradiction
    obtain ⟨ys,rfl,kids⟩ := free_equiv_view h
    split at l <;> try contradiction
    next hi => exact ih (kids ⟨i,hi⟩) l (by simpa [atPath,hi] using r)

/-- An open constructor pattern can inspect variables and constructor terms.
A free head occurring anywhere in the pattern must have no active rewrite row. -/
def Pattern (rs : Problem s) : Term s → Prop
  | .var _ | .atom _ => True
  | .free f xs => (∀ r ∈ rs, ∀ args, r.lhs ≠ .free f args) ∧ ∀ i, Pattern rs (xs i)
  | .ac _ a b | .comm _ a b => Pattern rs a ∧ Pattern rs b

variable [DecidableEq s.FreeSym]

def inert (rs : Problem s) : Term s → Bool
  | .free f xs => (ConstantDefinitions.entry rs f).isNone && (List.finRange _).all fun i => inert rs (xs i)
  | .ac _ a b | .comm _ a b => inert rs a && inert rs b
  | _ => true

theorem inert_iff (rs : Problem s) (t : Term s) : inert rs t ↔ Pattern rs t := by
  induction t with
  | var _ | atom _ => simp [inert,Pattern]
  | free f xs ih => simp [inert,Pattern,Option.isNone_iff_eq_none,ConstantDefinitions.undefined_iff,ih]
  | comm f a b l r | ac f a b l r => simp [inert,Pattern,l,r]

/-- All rules for a destructor agree on which coordinate they return wherever
their guards match. Different destructors can project different coordinates. -/
structure Presentation (rs : Problem s) : Prop where
  patterns : ∀ r ∈ rs, ∃ f xs, r.lhs = .free f xs ∧ ∀ i, Pattern rs (xs i)
  positions : ∀ r ∈ rs, ∃ p : List Nat, p ≠ [] ∧ ∀ q ∈ rs,
    ConstantDefinitions.freeHead q.lhs = ConstantDefinitions.freeHead r.lhs →
    atPath q.lhs p = some q.rhs

omit [DecidableEq s.FreeSym] in
theorem Presentation.decreasing {rs : Problem s} (cls : Presentation rs) : TableDecrease.decreasing rs := by
  apply List.all_eq_true.mpr
  intro r hr
  obtain ⟨p,ne,pos⟩ := cls.positions r hr
  obtain ⟨vars,_,size⟩ := path_size (pos r hr rfl)
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (size ne),List.all_eq_true.mpr
    (fun v _ => decide_eq_true (vars.count_le v))⟩

omit [DecidableEq s.FreeSym] in
theorem Presentation.sorted_iff {rs : Problem s} (cls : Presentation rs) :
    TableDecrease.sorted rs ↔ ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort := by
  have row (r) (hr : r ∈ rs) : TableDecrease.sortRule r ↔ HasSort r.rhs r.lhs.rootSort := by
    obtain ⟨_,_,shape,_⟩ := cls.patterns r hr
    simp only [TableDecrease.sortRule,shape,Term.checkSort_iff]
  exact ⟨fun ok r hr => (row r hr).mp (List.all_eq_true.mp ok r hr),
    fun typed => List.all_eq_true.mpr (fun r hr => (row r hr).mpr (typed r hr))⟩

variable [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def accepts (rs : Problem s) : Bool := rs.all fun r =>
  (match r.lhs with
   | .free _ xs => (List.finRange _).all fun i => inert rs (xs i)
   | _ => false) &&
  (paths r.lhs).any fun p => !p.isEmpty && rs.all fun q =>
    ConstantDefinitions.freeHead q.lhs != ConstantDefinitions.freeHead r.lhs || atPath q.lhs p == some q.rhs

theorem accepts_iff (rs : Problem s) : accepts rs ↔ Presentation rs := by
  simp only [accepts,List.all_eq_true,Bool.and_eq_true,List.any_eq_true,Bool.not_eq_true',
    List.isEmpty_eq_false_iff,Bool.or_eq_true,bne_iff_ne,beq_iff_eq]
  constructor
  · intro h
    refine ⟨fun r hr => ?_,fun r hr => ?_⟩
    · have pat := (h r hr).1
      cases src : r.lhs <;> simp [src] at pat
      next f xs => exact ⟨f,xs,rfl,fun i => (inert_iff ..).mp (pat i)⟩
    · obtain ⟨p,_,ne,ok⟩ := (h r hr).2; exact ⟨p,ne,fun q hq e => (ok q hq).resolve_left (not_not_intro e)⟩
  · intro h r hr
    obtain ⟨f,xs,src,kids⟩ := h.patterns r hr
    obtain ⟨p,ne,ok⟩ := h.positions r hr
    exact ⟨by simp [src,inert_iff,kids],p,path_mem (ok r hr rfl),ne,fun q hq => if eq : _ = _ then Or.inr (ok q hq eq) else Or.inl eq⟩


variable {rs : Problem s}

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem root_unique (cls : Presentation rs) {a b u v : Term s}
    (eq : EquivB a b) (l : ruleRoot rs a u) (r : ruleRoot rs b v) : EquivB u v := by
  obtain ⟨row,hr,σ,rfl,rfl⟩ := l
  obtain ⟨other,ho,τ,rfl,rfl⟩ := r
  obtain ⟨f,xs,src,_⟩ := cls.patterns row hr
  obtain ⟨g,ys,dst,_⟩ := cls.patterns other ho
  obtain ⟨p,_,all⟩ := cls.positions row hr
  have same : f = g := Head.free.inj (by simpa [src,dst,Substitution.apply,Term.subst,ConstructorVariants.head,headModel,Model.eval] using eq.head_eq)
  exact path_congr eq (apply_path σ (all row hr rfl))
    (apply_path τ (all other ho (by simp [src,dst,ConstantDefinitions.freeHead,same])))

def contract (rs : Problem s) (t : Term s) : Term s :=
  (ReferenceReduction.roots rs t).head?.getD t

private theorem selected (bound : ReferenceReduction.Bound rs) (t : Term s) :
    (contract rs t = t ∧ ∀ u, ¬ ContextualReduction.AtRoot (ruleRoot rs) t u) ∨
      ContextualReduction.AtRoot (ruleRoot rs) t (contract rs t) := by
  cases h : ReferenceReduction.roots rs t with
  | nil =>
    refine .inl ⟨by simp [contract,h],fun u hu => ?_⟩
    obtain ⟨_,mem,_⟩ := (ReferenceReduction.roots_iff rs bound ..).mpr hu
    simp [h] at mem
  | cons u us =>
    exact .inr ((ReferenceReduction.roots_iff rs bound ..).mp
      ⟨u,by simp [h],by simp [contract,h,EquivB.refl]⟩)

private theorem contracts (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    {a b u : Term s} (eq : EquivB a b) (fire : ruleRoot rs b u) : EquivB (contract rs a) u := by
  rcases selected bound a with ⟨_,none⟩ | ⟨p,q,l,hit,r⟩
  · exact (none u ⟨b,u,eq,fire,.refl _⟩).elim
  · exact r.symm.trans (root_unique cls (l.symm.trans eq) hit fire)

private theorem contract_congr (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    {a b : Term s} (eq : EquivB a b) : EquivB (contract rs a) (contract rs b) := by
  rcases selected bound b with ⟨eb,none⟩ | ⟨p,q,l,hit,r⟩
  · rcases selected bound a with ⟨ea,_⟩ | ⟨p,q,l,hit,r⟩
    · rwa [ea,eb]
    · exact (none _ ⟨p,q,eq.symm.trans l,hit,r⟩).elim
  · exact (contracts cls bound (eq.trans l) hit).trans r

def fold (rs : Problem s) : Term s → Term s
  | .var v => .var v
  | .atom a => .atom a
  | .free f xs => contract rs (.free f (fun i => fold rs (xs i)))
  | .comm f a b => .comm f (fold rs a) (fold rs b)
  | .ac f a b => .ac f (fold rs a) (fold rs b)

private theorem reachable (bound : ReferenceReduction.Bound rs) (t : Term s) :
    Reduces (ruleRoot rs) t (fold rs t) := by
  induction t with
  | var _ | atom _ => exact .basis (.refl _)
  | free f xs ih =>
    apply (Reduces.free f _ _ ih).trans
    change Reduces _ _ (contract rs _)
    rcases selected bound (.free f (fun i => fold rs (xs i))) with ⟨e,_⟩ | ⟨p,q,l,hit,r⟩
    · rw [e]; exact .basis (.refl _)
    · exact .step ⟨p,q,l,.root hit,r⟩
  | ac f a b l r => exact .ac f l r
  | comm f a b l r => exact .comm f l r

private theorem fold_basis (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    {a b : Term s} (e : EquivB a b) : EquivB (fold rs a) (fold rs b) := by
  induction e with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ l r => exact l.trans r
  | free f xs ys _ ih => exact contract_congr cls bound (.free f _ _ ih)
  | comm_congr f _ _ l r => exact .comm_congr f l r
  | ac_congr f _ _ l r => exact .ac_congr f l r
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

private theorem contract_inert (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    {f : s.FreeSym} (off : ConstantDefinitions.entry rs f = none) (xs) :
    contract rs (.free f xs) = .free f xs := by
  rcases selected bound (.free f xs) with ⟨e,_⟩ | ⟨_,_,eq,⟨r,hr,σ,rfl,rfl⟩,_⟩
  · exact e
  · obtain ⟨g,ys,src,_⟩ := cls.patterns r hr
    have same : f = g := Head.free.inj (by simpa [src,Substitution.apply,Term.subst,ConstructorVariants.head,headModel,Model.eval] using eq.head_eq)
    have miss := List.find?_eq_none.mp off r hr
    simp [src,ConstantDefinitions.freeHead,same] at miss

private def folded (bound : ReferenceReduction.Bound rs) (sorted : TableDecrease.sorted rs)
    (σ : Substitution s) : Substitution s where
  image v := fold rs (σ.image v)
  support := σ.support
  outside v hv := by rw [σ.outside v hv]; rfl
  sorted v := RootNarrowing.reduction_invariant (fun t => HasSort t v.sort)
    (fun ht eq => Term.checkSort_sound _ _ ((SortClash.check_equiv eq _ ) ▸ Term.checkSort_complete ht))
    (fun ht st => TableDecrease.sortPreserving sorted st _ ht) (reachable bound _) (σ.sorted v)

private theorem fold_pattern (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    (sorts : TableDecrease.sorted rs) (σ : Substitution s) {p : Term s} (clean : inert rs p) :
    fold rs (σ.apply p) = (folded bound sorts σ).apply p := by
  induction p with
  | var _ | atom _ => rfl
  | free f xs ih =>
    obtain ⟨off,kids⟩ := Bool.and_eq_true_iff.mp clean
    change contract rs (.free f _) = .free f _
    rw [contract_inert cls bound (Option.isNone_iff_eq_none.mp off)]
    exact congrArg (Term.free f) (funext fun i => ih i (List.all_eq_true.mp kids i (List.mem_finRange i)))
  | comm f a b l r | ac f a b l r =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp clean
    simp [Substitution.apply,Term.subst,fold] at *
    exact ⟨l ha,r hb⟩

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem clean_path {p} {t u : Term s} (clean : inert rs t) (h : atPath t p = some u) :
    inert rs u := by
  induction p generalizing t with
  | nil => simp_all only [atPath,Option.some.injEq]
  | cons i p ih =>
    cases t <;> simp only [atPath] at h <;> try contradiction
    split at h <;> try contradiction
    exact ih (List.all_eq_true.mp (Bool.and_eq_true_iff.mp clean).2 _ (List.mem_finRange _)) h

private theorem fold_root (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    (sorts : TableDecrease.sorted rs) {a b : Term s} (fire : ruleRoot rs a b) :
    EquivB (fold rs a) (fold rs b) := by
  obtain ⟨r,hr,σ,rfl,rfl⟩ := fire
  obtain ⟨f,xs,src,kids⟩ := cls.patterns r hr
  obtain ⟨p,ne,all⟩ := cls.positions r hr
  have pos := all r hr rfl
  rw [src] at pos
  have clean : inert rs r.rhs := by
    cases p with
    | nil => contradiction
    | cons i p =>
      simp only [atPath] at pos
      split at pos <;> try contradiction
      exact clean_path ((inert_iff ..).mpr (kids _)) pos
  let τ := folded bound sorts σ
  rw [fold_pattern cls bound sorts σ clean,src]
  change EquivB (contract rs (.free f (fun i => fold rs (σ.apply (xs i))))) (τ.apply r.rhs)
  rw [show (fun i => fold rs (σ.apply (xs i))) = (fun i => τ.apply (xs i)) from
    funext fun i => fold_pattern cls bound sorts σ ((inert_iff ..).mpr (kids i))]
  exact contracts cls bound (.refl _) ⟨r,hr,τ,by rw [src]; rfl,rfl⟩

private theorem fold_step (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    (sorts : TableDecrease.sorted rs) {a b : Term s} (st : Step (ruleRoot rs) a b) :
    EquivB (fold rs a) (fold rs b) := by
  induction st with
  | root fire => exact fold_root cls bound sorts fire
  | free f xs i _ ih =>
    apply contract_congr cls bound
    apply EquivB.free
    intro j
    by_cases e : j = i
    · simpa [e] using ih
    · simp [e,EquivB.refl]
  | comm_left f _ _ ih => exact .comm_congr f ih (.refl _)
  | comm_right f _ _ ih => exact .comm_congr f (.refl _) ih
  | ac_left f _ _ ih => exact .ac_congr f ih (.refl _)
  | ac_right f _ _ ih => exact .ac_congr f (.refl _) ih

private theorem invariant (cls : Presentation rs) (bound : ReferenceReduction.Bound rs)
    (sorts : TableDecrease.sorted rs) {a b : Term s} (steps : Reduces (ruleRoot rs) a b) :
    EquivB (fold rs a) (fold rs b) := by
  induction steps with
  | basis h => exact fold_basis cls bound h
  | step h =>
    obtain ⟨_,_,pre,st,post⟩ := h
    exact (fold_basis cls bound pre).trans ((fold_step cls bound sorts st).trans (fold_basis cls bound post))
  | trans _ _ l r => exact l.trans r
  | free f xs ys _ ih => exact contract_congr cls bound (.free f _ _ ih)
  | comm f _ _ l r => exact .comm_congr f l r
  | ac f _ _ l r => exact .ac_congr f l r

theorem canonical (cls : Presentation rs) (dec : TableDecrease.decreasing rs)
    (sorts : TableDecrease.sorted rs) : MaudeOperations.CanonicalPresentation (ruleRoot rs) where
  terminating := TableDecrease.terminating dec
  sortPreserving := TableDecrease.sortPreserving sorts
  confluent l r :=
    let bound := TableDecrease.bound dec
    ⟨_,(reachable bound _).trans (.basis ((invariant cls bound sorts l).symm.trans (invariant cls bound sorts r))),
      reachable bound _⟩

theorem reductionReply (cls : Presentation rs) (dec : TableDecrease.decreasing rs)
    (sorts : TableDecrease.sorted rs) (t : Term s) :
    MaudeOperations.ReductionReply (ruleRoot rs) t (fold rs t) := by
  let bound := TableDecrease.bound dec
  let theory := canonical cls dec sorts
  let r := ReferenceReduction.reducer rs bound theory
  have reply := r.correct t
  have path := reachable bound t
  have same := (invariant cls bound sorts reply.normalForm.1).trans
    (normal_reduces_equiv (reachable bound _) reply.normalForm.2.1).symm
  refine ⟨⟨path,(normal_equiv _ same).mpr reply.normalForm.2.1,?_⟩,fun u other => (reply.unique u other).trans same.symm⟩
  exact fun k ht => Term.checkSort_sound _ _ ((SortClash.check_equiv same k) ▸ Term.checkSort_complete (reply.normalForm.2.2 k ht))

end Tamarin.DestructorTable
