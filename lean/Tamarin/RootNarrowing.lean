import Tamarin.ACUnifierExclusion
import Tamarin.VariantJoinAmbient

/-! Soundness and lifting for root narrowing with an ordinary sorted CSU.
An AC extension introduces one independently bound operand for the entire
nonempty remainder. Without a termination or frontier argument these local
transitions do not by themselves make a complete family of variants. -/
namespace Tamarin.Rewriting.RootNarrowing
variable {sig : Signature} {R : Root sig}

/-- An oriented rule or a rule in an AC context. Every sorted instance is a
genuine rewrite, and all witnesses returned by the right side occur on the left. -/
structure Schema (R : Root sig) where
  lhs : Term sig
  rhs : Term sig
  step : ∀ τ : Substitution sig, StepModulo R (τ.apply lhs) (τ.apply rhs)
  bound : ∀ v, rhs.Occurs v → lhs.Occurs v

def Schema.openRule (rules : List (Equation sig)) (r : Equation sig) (mem : r ∈ rules)
    (bound : ∀ w, r.rhs.Occurs w → r.lhs.Occurs w) (π : VariablePermutation) :
    Schema (ruleRoot rules) where
  lhs := (π.subst sig).apply r.lhs
  rhs := (π.subst sig).apply r.rhs
  step τ := ⟨_,_,.refl _,.root ⟨r,mem,τ.compose (π.subst sig),
    (Substitution.apply_compose ..).symm,(Substitution.apply_compose ..).symm⟩,.refl _⟩
  bound v hv := by
    obtain ⟨w,hw,eq⟩ := (Term.occurs_rename r.rhs π.forward v).mp hv
    exact (Term.occurs_rename r.lhs π.forward v).mpr ⟨w,bound w hw,eq⟩

def Schema.extend (p : Schema R) (f : sig.ACSym) (z : Variable) : Schema R where
  lhs := .ac f p.lhs (.var z)
  rhs := .ac f p.rhs (.var z)
  step τ := by
    obtain ⟨a,b,eq,step,finish⟩ := p.step τ
    exact ⟨_,_,.ac_congr f eq (.refl _),.ac_left f (τ.image z) step,.ac_congr f finish (.refl _)⟩
  bound _ hv := hv.imp (p.bound _) id

/-- Branch images and result are instantiated by the *same* substitution.
At a nonterminal narrowing step the resulting value may still be reducible. -/
def FitsOn (observable : Variable → Prop) (ρ : Substitution sig) (u : Term sig) (μ : Substitution sig)
    (value : Term sig) : Prop :=
  ∃ δ : Substitution sig, (∀ v, observable v → EquivB (ρ.image v) (δ.apply (μ.image v))) ∧
    EquivB u (δ.apply value)

abbrev Fits (q : Term sig) := FitsOn (sig := sig) q.Occurs

def Schema.problem (p : Schema R) (query : Term sig) : Problem sig := [⟨p.lhs,query⟩]

/-- A successful narrowing arm replays an actual rule from the active table.
Ordinary B-unification may have chosen any representative of the left side. -/
theorem Schema.replay (p : Schema R) (q : Term sig) {answers} (csu : CompleteSet (p.problem q) answers)
    {μ : Substitution sig} (mem : μ ∈ answers) : StepModulo R (μ.apply q) (μ.apply p.rhs) := by
  have matched := csu.sound μ mem _ List.mem_cons_self
  obtain ⟨a,b,pre,step,post⟩ := p.step μ
  exact ⟨a,b,matched.symm.trans pre,step,post⟩

/-- A narrowed subterm may sit inside a larger query. Every input image and
untouched sibling is factored through the same witness as the rewritten value,
including variables that never occur in the unification problem itself. -/
private theorem Schema.lift_on (p : Schema R) (q : Term sig) (observable : Variable → Prop)
    (live : ∀ v, q.Occurs v → observable v) (apart : ∀ v, p.lhs.Occurs v → ¬observable v)
    {answers} (sound : Sound (p.problem q) answers)
    (coverage : ∀ ρ, (p.problem q).Solves ρ → ∃ μ ∈ answers,
      Substitution.InstanceOn (fun v => (p.problem q).Occurs v ∨ observable v) ρ μ)
    (ρ : Substitution sig) (u : Term sig) :
    (∃ τ : Substitution sig, EquivB (ρ.apply q) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs)) ↔
      ∃ μ ∈ answers, FitsOn observable ρ u μ (μ.apply p.rhs) := by
  constructor
  · rintro ⟨τ,matchEq,result⟩
    let joint := VariantJoin.choose observable ρ τ
    have left := (VariantJoin.choose_apply _ ρ τ p.lhs).2 apart
    have right := (VariantJoin.choose_apply _ ρ τ p.rhs).2 (fun v hv => apart v (p.bound v hv))
    have source := (VariantJoin.choose_apply observable ρ τ q).1 live
    have sol : (p.problem q).Solves joint := by
      intro e hm; obtain rfl := List.mem_singleton.mp hm
      exact left ▸ source ▸ matchEq.symm
    obtain ⟨μ,mem,δ,factor⟩ := coverage _ sol
    refine ⟨μ,mem,δ,?_,?_⟩
    · intro v hv
      have h := factor v (.inr hv)
      change EquivB (joint.image v) (δ.apply (μ.image v)) at h
      simpa only [joint,VariantJoin.choose,ite_eq_left hv] using h
    · have rhs := p.rhs.subst_equiv joint.image (δ.compose μ).image
        (fun v hv => factor v (.inl ⟨_,List.mem_cons_self,.inl (p.bound v hv)⟩))
      change EquivB (joint.apply p.rhs) ((δ.compose μ).apply p.rhs) at rhs
      rw [right,Substitution.apply_compose] at rhs
      exact result.trans rhs
  · rintro ⟨μ,mem,δ,input,result⟩
    have eq := q.subst_equiv ρ.image (δ.compose μ).image (fun v hv => input v (live v hv))
    refine ⟨δ.compose μ,eq.trans ?_,?_⟩
    · exact ((p.problem q).solves_compose (sound μ mem) δ _ List.mem_cons_self).symm
    · simpa only [Substitution.apply_compose] using result

/-- Exactly the independently matched root instances are represented,
including agreement on every query variable and on the instantiated RHS.
No normality hypothesis is imposed on these intermediate terms. -/
theorem Schema.lift_iff (p : Schema R) (q : Term sig)
    (apart : ∀ v, p.lhs.Occurs v → ¬q.Occurs v) {answers} (csu : CompleteSet (p.problem q) answers)
    (ρ : Substitution sig) (u : Term sig) :
    (∃ τ : Substitution sig, EquivB (ρ.apply q) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs)) ↔
      ∃ μ ∈ answers, Fits q ρ u μ (μ.apply p.rhs) := by
  apply p.lift_on q q.Occurs (fun _ h => h) apart csu.sound
  intro σ sol
  obtain ⟨μ,mem,δ,agree⟩ := csu.covers _ sol
  exact ⟨μ,mem,δ,fun v h => agree v (h.elim id (fun hv => ⟨_,List.mem_cons_self,.inr hv⟩))⟩

/-- Tracking terms outside the redex requires only reserving their extra
variables. They need not be sent as equations or examined by the ordinary
unifier. This applies verbatim to an AC schema extended by a remainder. -/
theorem Schema.lift_in_context (p : Schema R) (q : Term sig) (context : List (Term sig))
    (apart : ∀ v, p.lhs.Occurs v → ¬(q.Occurs v ∨ Observed context v))
    {answers} (csu : CompleteSet (p.problem q) answers)
    (reserved : ∀ μ ∈ answers, VariantJoin.Reserves (p.problem q) context μ)
    (ρ : Substitution sig) (u : Term sig) :
    (∃ τ : Substitution sig, EquivB (ρ.apply q) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs)) ↔
      ∃ μ ∈ answers, FitsOn (fun v => q.Occurs v ∨ Observed context v) ρ u μ (μ.apply p.rhs) := by
  apply p.lift_on q _ (fun _ h => .inl h) apart csu.sound
  intro σ sol
  obtain ⟨μ,mem,covered⟩ := csu.covers _ sol
  obtain ⟨δ,agree⟩ := (reserved μ mem).factor covered
  refine ⟨μ,mem,δ,fun v h => agree v ?_⟩
  exact h.elim Or.inl (fun hv => hv.elim (fun hq => .inl ⟨_,List.mem_cons_self,.inr hq⟩) Or.inr)

/-- A concrete AC remainder can be added to a rule assignment without
changing any of the rule's existing bindings, even when it contains caller
variables. Its fresh placeholder has the sort of the AC operator. -/
theorem extend_assignment (lhs rhs : Term sig) (bound : ∀ v, rhs.Occurs v → lhs.Occurs v)
    (f : sig.ACSym) (z : Variable) (fresh : ¬lhs.Occurs z)
    (τ : Substitution sig) (rest : Term sig) (typed : HasSort rest z.sort) :
    ∃ η : Substitution sig, η.apply (.ac f lhs (.var z)) = .ac f (τ.apply lhs) rest ∧
      η.apply (.ac f rhs (.var z)) = .ac f (τ.apply rhs) rest := by
  let image := Substitution.binding z rest typed
  let η := VariantJoin.choose (· = z) image τ
  have on (t : Term sig) (ht : ¬t.Occurs z) : η.apply t = τ.apply t :=
    (VariantJoin.choose_apply _ _ _ t).2 fun _ occ eq => ht (eq ▸ occ)
  have h : η.image z = rest := by simp [η,VariantJoin.choose,image,Substitution.binding]
  refine ⟨η,?_,?_⟩
  · change Term.ac f (η.apply lhs) (η.image z) = _
    rw [on lhs fresh,h]
  · change Term.ac f (η.apply rhs) (η.image z) = _
    rw [on rhs (fun hv => fresh (bound z hv)),h]

theorem Schema.extend_witness (p : Schema R) (f : sig.ACSym) (z : Variable)
    (fresh : ¬p.lhs.Occurs z) (τ : Substitution sig) (rest : Term sig) (typed : HasSort rest z.sort) :
    ∃ τ' : Substitution sig, τ'.apply (p.extend f z).lhs = .ac f (τ.apply p.lhs) rest ∧
      τ'.apply (p.extend f z).rhs = .ac f (τ.apply p.rhs) rest :=
  extend_assignment p.lhs p.rhs p.bound f z fresh τ rest typed

/-- Every actual application of this rule to an AC subbag after
specialization lifts to the whole-root or the fresh-remainder CSU. The
result has a genuine contextual rewrite and a matching caller assignment. -/
theorem Schema.subbag_lift [DecidableEq sig.ACSym] (p : Schema R) (q : Term sig)
    (f : sig.ACSym) (z : Variable) (sort : z.sort = sig.acSort f) (fresh : ¬p.lhs.Occurs z)
    (apart : ∀ v, (p.extend f z).lhs.Occurs v → ¬q.Occurs v) {bare extended}
    (bc : CompleteSet (p.problem q) bare) (ec : CompleteSet ((p.extend f z).problem q) extended)
    (ρ τ : Substitution sig) (typed : HasSort (ρ.apply q) (sig.acSort f))
    (hit : DHProduct.Subbag f (τ.apply p.lhs) (ρ.apply q)) :
    ∃ u, StepModulo R (ρ.apply q) u ∧
      ((EquivB (ρ.apply q) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs) ∧
        ∃ μ ∈ bare, Fits q ρ u μ (μ.apply p.rhs)) ∨
       ∃ rest, EquivB (ρ.apply q) (.ac f (τ.apply p.lhs) rest) ∧ EquivB u (.ac f (τ.apply p.rhs) rest) ∧
         ∃ μ ∈ extended, Fits q ρ u μ (μ.apply (p.extend f z).rhs)) := by
  have fire {s t} (eq : EquivB (ρ.apply q) s) (step : StepModulo R s t) : StepModulo R (ρ.apply q) t := by
    obtain ⟨a,b,pre,hs,post⟩ := step; exact ⟨a,b,eq.trans pre,hs,post⟩
  rcases hit.context with all|⟨rest,hasRest⟩
  · refine ⟨_,fire all (p.step τ),.inl ⟨all,.refl _,?_⟩⟩
    exact (p.lift_iff q (fun v h => apart v (.inl h)) bc _ _).mp ⟨τ,all,.refl _⟩
  · have shape := (SortClash.check_equiv hasRest _ ▸ Term.checkSort_complete typed :
        (Term.ac f (τ.apply p.lhs) rest).checkSort (sig.acSort f) = true)
    simp only [Term.checkSort,Bool.and_eq_true] at shape
    obtain ⟨η,l,r⟩ := p.extend_witness f z fresh τ rest (sort ▸ Term.checkSort_sound _ _ shape.2)
    have eq := l ▸ hasRest
    refine ⟨_,fire eq ((p.extend f z).step η),.inr ⟨rest,hasRest,r ▸ .refl _,?_⟩⟩
    exact ((p.extend f z).lift_iff q apart ec _ _).mp ⟨η,eq,.refl _⟩

end Tamarin.Rewriting.RootNarrowing
