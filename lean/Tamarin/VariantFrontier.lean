import Tamarin.NarrowingFrontier
import Tamarin.VariantJoinSubsumption
import Tamarin.VariantJoinPacked

/-! From complete symbolic one-step successors to exact variant families.
Search order and the number of folded states are immaterial. The inputs of
a folded state are just as observable as its still-changing result. -/
namespace Tamarin.Rewriting.RootNarrowing
open VariantJoin
variable {s : Signature} {I : Type} {rules : List (Equation s)}
abbrev State (s : Signature) (I : Type) := Row s I Unit

/-- The successor generator must explain each concrete step from the
specialized value while preserving all original input images together. -/
def Successors (rules : List (Equation s)) (q : State s I) (out : List (State s I)) : Prop :=
  ∀ δ : Substitution s, (∀ i, Normal (ruleRoot rules) (δ.apply (q.input i))) → ∀ u,
    StepModulo (ruleRoot rules) (δ.apply (q.value ())) u →
    ∃ r ∈ out, ∃ η : Substitution s, VariantJoin.Fits r (fun i => δ.apply (q.input i)) (fun _ => u) η

/-- It is safe to drop an impossible input or fold through a previously
retained state. A redex in the result alone does not justify dropping it. -/
theorem closed_of_successors (states : List (State s I)) (next : State s I → List (State s I))
    (steps : ∀ q ∈ states, Successors rules q (next q))
    (account : ∀ q ∈ states, ∀ r ∈ next q,
      (∃ i, ¬ Normal (ruleRoot rules) (r.input i)) ∨ ∃ p ∈ states, p.Subsumes r) :
    Closed (ruleRoot rules) states := by
  intro q hq δ hn u st
  obtain ⟨r,hr,η,fit⟩ := steps q hq δ hn u st
  rcases account q hq r hr with ⟨i,bad⟩ | ⟨p,hp,θ,cover⟩
  · exact False.elim (bad (normal_of_instance ((normal_equiv _ (fit.inputs i)).mp (hn i))))
  · have both := cover.compose fit
    exact ⟨p,hp,η.compose θ,both.inputs,both.values ()⟩

/-- A symbolic row that can denote a concrete normal result must itself be
normal. All retained normal rows must be represented in the emitted family.
Replaying a returned row is sufficient for soundness under specialization. -/
theorem exact_of_frontier (keys : List Variable) (t : Term s) (typed : HasSort t t.rootSort)
    (scope : ∀ v, t.Occurs v → v ∈ keys) (vars : Normalized (ruleRoot rules) Substitution.identity)
    (states kept : List (State s (Key keys))) (seed : (⟨fun i => .var i.val, fun _ => t⟩ : State s (Key keys)) ∈ states)
    (closed : Closed (ruleRoot rules) states)
    (terminal : ∀ q ∈ states, q.IsNormal (ruleRoot rules) → ∃ r ∈ kept, r.Subsumes q)
    (sorted : ∀ r ∈ kept, r.Sorted)
    (replay : ∀ r, ∀ h : r ∈ kept, NormalForm (ruleRoot rules) ((r.project (sorted r h)).apply t) (r.value ())) :
    Exact (ruleRoot rules) Subtype.val (fun _ : Unit => t) kept := by
  intro ρ hn y ny
  constructor
  · intro forms
    obtain ⟨r,hr,η,nh,fit⟩ := frontier_covers vars states kept closed terminal (fun i => ρ.image i.val)
      (fun i => hn i.val) _ _ (forms ()).1 (ny ())
      ⟨_,seed,ρ,fun _ => .refl _,.refl _⟩
    exact ⟨r,hr,η,nh,fit.inputs,fun i => by cases i; exact fit.values ()⟩
  · rintro ⟨r,hr,η,_,fit⟩ i
    cases i
    apply form_of_instance hn typed (σ := r.project (sorted r hr)) (δ := η) _ (replay r hr) (fit.values ()) (ny ())
    intro v hv
    have same := fit.inputs ⟨v,scope v hv⟩
    change EquivB (ρ.image v) (η.apply ((r.project _).image v))
    rwa [r.project_key _ ⟨v,scope v hv⟩]

/-- Agreement must hold on every normal overlap of two answer rows, also
when both are independently renamed copies of one row. A complete ordinary
CSU tests all overlaps at once. An already reducible joint image or value
eliminates that entire arm by substitution stability of rewriting. -/
def CompatibleValues (R : Root s) (p q : State s I) : Prop :=
  ∀ x a b, (∀ i, Normal R (x i)) → Normal R a → Normal R b →
    Denotes R p x (fun _ => a) → Denotes R q x (fun _ => b) → EquivB a b

theorem compatible_of_csu (vars : Normalized (ruleRoot rules) Substitution.identity)
    (p q fresh : State s I) (rename : q.Relabels fresh) (apart : ∀ v, p.Uses v → ¬fresh.Uses v)
    (keys : List I) (allKeys : ∀ i, i ∈ keys) (anchors : List (Term s))
    (tracked : ∀ v, p.Uses v ∨ fresh.Uses v → (problem p fresh keys anchors).Occurs v)
    (answers : List (Substitution s)) (checked : CompleteSet (problem p fresh keys anchors) answers)
    (agree : ∀ μ ∈ answers, (join p fresh μ).IsNormal (ruleRoot rules) →
      EquivB (μ.apply (p.value ())) (μ.apply (fresh.value ()))) :
    CompatibleValues (ruleRoot rules) p q := by
  intro x a b nx na nb lp rq
  have fr := (rename.denotes x _).mp rq
  obtain ⟨μ,hm,normal,δ,_,fit⟩ := (exact_join vars p fresh apart keys allKeys anchors tracked answers checked x
    (fun _ => a) (fun _ => b) nx (fun _ => na) (fun _ => nb)).mp ⟨lp,fr⟩
  exact (fit.values (.inl ())).trans (((agree μ hm normal).subst δ.image).trans (fit.values (.inr ())).symm)

/-- Complete, possibly overlapping symbolic rows with a single-valued
overlap relation guarantee unique reconstruction at all normalized inputs.
This can certify a query in an ambient nonconfluent theory. -/
theorem unique_of_compatible {R : Root s} (t : Term s) (ids : I → Variable)
    (rows : List (State s I)) (exactRows : Exact R ids (fun _ : Unit => t) rows)
    (agree : ∀ p ∈ rows, ∀ q ∈ rows, CompatibleValues R p q)
    (ρ : Substitution s) (hn : Normalized R ρ) {a b}
    (left : NormalForm R (ρ.apply t) a) (right : NormalForm R (ρ.apply t) b) : EquivB a b := by
  obtain ⟨p,hp,lp⟩ := (exactRows ρ hn (fun _ => a) (fun _ => left.2.1)).mp (fun _ => left)
  obtain ⟨q,hq,rq⟩ := (exactRows ρ hn (fun _ => b) (fun _ => right.2.1)).mp (fun _ => right)
  exact agree p hp q hq _ _ _ (fun i => hn (ids i)) left.2.1 right.2.1 lp rq

end Tamarin.Rewriting.RootNarrowing
