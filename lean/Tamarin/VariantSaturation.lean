import Tamarin.ReferenceVariantFrontier
import Tamarin.VariantFreshening
import Tamarin.VariantLayers

/-! Total breadth-first variant search under the finite variant property.
A local expansion must preserve sound variants and decrease a measure on the
concrete specialization when an observed value can still rewrite. No bound on
the number of layers, solutions or fresh variables enters the search. -/
namespace Tamarin.VariantSaturation
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier VariantLayers
variable {s : Signature} {n : Nat} {rules : List (Equation s)} {query : Fin n → Term s}

theorem atFn {α β : Type} {rel : α → β → Prop} (f : Fin n → α) (g : Fin n → β)
    (h : Aligned rel (List.ofFn f) (List.ofFn g)) : ∀ i, rel (f i) (g i) := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f := g)] at h
    exact Fin.cases h.1 (ih _ _ h.2)

abbrev Sound (rules : List (Equation s)) (query : Fin n → Term s) (p : Point s n) :=
  (p.answer (keysOf query)).Sound (ruleRoot rules) (List.ofFn query)

structure Expansion (rules : List (Equation s)) (query : Fin n → Term s) where
  seed : Point s n
  next : Point s n → List (Point s n)
  identity : ∀ v ∈ keysOf query, seed.assignment.image v = .var v
  initial : Sound rules query seed
  preserves : ∀ p, Sound rules query p → ∀ c ∈ next p, Sound rules query c
  measure : (Fin n → Term s) → Nat
  invariant : ∀ x y, (∀ i, EquivB (x i) (y i)) → measure x = measure y
  progress : ∀ p, Sound rules query p → ∀ δ : Substitution s,
    (∀ i : Key (keysOf query), Normal (ruleRoot rules) (δ.apply (p.assignment.image i.val))) →
    (∀ i, Normal (ruleRoot rules) (δ.apply (p.value i))) ∨
    ∃ c ∈ next p, ∃ η : Substitution s,
      (∀ i : Key (keysOf query), EquivB (δ.apply (p.assignment.image i.val)) (η.apply (c.assignment.image i.val))) ∧
      measure (fun i => η.apply (c.value i)) < measure (fun i => δ.apply (p.value i))

private theorem sound_reached (g : Expansion rules query) {p} (reached : Reachable g.seed g.next p) :
    Sound rules query p := by
  induction reached with
  | seed => exact g.initial
  | child _ q h ih => exact g.preserves _ ih q h

private theorem endpoint (canonical : CanonicalPresentation (ruleRoot rules)) (p : Point s n)
    (sound : Sound rules query p) (ρ δ : Substitution s) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i))
    (input : ∀ i : Key (keysOf query), EquivB (ρ.image i.val) (δ.apply (p.assignment.image i.val)))
    (normal : ∀ i, Normal (ruleRoot rules) (δ.apply (p.value i))) (i : Fin n) :
    EquivB (out i) (δ.apply (p.value i)) := by
  let a := p.answer (keysOf query)
  have agree (v) (hv : (query i).Occurs v) : EquivB (ρ.image v) ((δ.compose a.subst).image v) := by
    have mem := (observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
    change EquivB _ (δ.apply (((p.row _).project (fun j => p.assignment.sorted j.val)).image v))
    rw [(p.row _).project_key (fun j => p.assignment.sorted j.val) ⟨v,mem⟩]
    exact input ⟨v,mem⟩
  have source : EquivB (ρ.apply (query i)) (δ.apply (a.subst.apply (query i))) := by
    rw [← Substitution.apply_compose]
    exact (query i).subst_equiv _ _ agree
  have replay := atFn query p.value sound.2 i
  have red := (Reduces.basis source).trans (SpecializedFresh.reduces_subst rules δ replay.1)
  obtain ⟨w,l,r⟩ := canonical.confluent (forms i).1 red
  exact (normal_reduces_equiv l (forms i).2.1).trans (normal_reduces_equiv r (normal i)).symm

/-- Run the same descent either in the full search tree or inside a closed
finite prefix. Folding a successor changes its witness but preserves every
concrete input, result and measure. -/
private theorem covers (g : Expansion rules query) (canonical : CanonicalPresentation (ruleRoot rules))
    (live : Point s n → Prop) (initial : live g.seed) (valid : ∀ p, live p → Sound rules query p)
    (closed : ∀ p, live p → ∀ c ∈ g.next p, ∃ q, live q ∧ (q.row (keysOf query)).Subsumes (c.row (keysOf query)))
    (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i)) :
    ∃ p, live p ∧ ∃ δ, Fits (p.row (keysOf query)) (fun i => ρ.image i.val) out δ := by
  let keys := keysOf query
  have go (k : Nat) : ∀ p, live p → ∀ δ : Substitution s,
      (∀ i : Key keys, EquivB (ρ.image i.val) (δ.apply (p.assignment.image i.val))) →
      g.measure (fun i => δ.apply (p.value i)) = k →
      ∃ q, live q ∧ ∃ η, Fits (q.row keys) (fun i => ρ.image i.val) out η := by
    induction k using Nat.strongRecOn with
    | ind k smaller =>
      intro p hp δ inputs rank
      rcases g.progress p (valid p hp) δ (fun i => (normal_equiv _ (inputs i)).mp (norm i.val)) with
        normal | ⟨c,hc,η,same,less⟩
      · exact ⟨p,hp,δ,inputs,endpoint canonical p (valid p hp) ρ δ out forms inputs normal⟩
      · obtain ⟨q,hq,θ,fit⟩ := closed p hp c hc
        have values (i) : EquivB (η.apply (c.value i)) ((η.compose θ).apply (q.value i)) := by
          rw [Substitution.apply_compose]
          exact (fit.values i).subst η.image
        have eq := g.invariant _ _ values
        apply smaller _ (eq ▸ rank ▸ less) q hq (η.compose θ) _ rfl
        intro i
        rw [Substitution.apply_compose]
        exact (inputs i).trans ((same i).trans ((fit.inputs i).subst η.image))
  exact go _ g.seed initial ρ (fun i => by rw [g.identity _ i.property]; exact .refl _) rfl

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def subsumes (query : Fin n → Term s) (p c : Point s n) :=
  let keys := keysOf query
  ReferenceVariantFolding.subsumes keys.attach (List.finRange n) (p.row keys) (c.row keys)

private theorem subsumes_iff (p c : Point s n) : subsumes query p c = true ↔
    (p.row (keysOf query)).Subsumes (c.row (keysOf query)) :=
  ReferenceVariantFolding.subsumes_iff (List.mem_attach _) List.mem_finRange ..

private theorem basis (g : Expansion rules query) (canonical : CanonicalPresentation (ruleRoot rules))
    (family : ∃ answers, CompleteVariants (ruleRoot rules) (List.ofFn query) answers) :
    FiniteBasis g.seed g.next (subsumes query) := by
  classical
  let keys := keysOf query
  obtain ⟨answers,correct⟩ := family
  have rowFor (a : {v // v ∈ answers}) := read_aligned query a.val.values (correct.1 a.val a.property).2
  let values (a : {v // v ∈ answers}) := (rowFor a).choose
  have source (a : {v // v ∈ answers}) := (rowFor a).choose_spec
  have covered (a : {v // v ∈ answers}) := covers g canonical (Reachable g.seed g.next) .seed
    (fun _ => sound_reached g) (fun _ hp c hc => ⟨c,.child hp c hc,Row.Subsumes.refl _⟩)
    a.val.subst (correct.1 a.val a.property).1 (values a) (source a).2
  let pick (a : {v // v ∈ answers}) := (covered a).choose
  refine ⟨answers.attach.map pick,?_,?_⟩
  · intro p hp
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hp
    exact (covered a).choose_spec.1
  · intro p hp
    let own := p.answer keys
    have replay := sound_reached g hp
    obtain ⟨a,ha,η,_,input,output⟩ := correct.2 own.subst replay.1 own.values replay.2
    let slot := (⟨a,ha⟩ : {v // v ∈ answers})
    obtain ⟨δ,fit⟩ := (covered slot).choose_spec.2
    have tuple : Aligned (fun x y => EquivB x (η.apply y)) (List.ofFn p.value) (List.ofFn (values slot)) :=
      (source slot).1 ▸ output
    apply Exists.intro (pick slot)
    refine ⟨List.mem_map_of_mem (List.mem_attach answers slot),(subsumes_iff ..).mpr ⟨η.compose δ,?_,?_⟩⟩
    · intro i
      have eq := input i.val ((observed query _).mp i.property)
      change EquivB (((p.row keys).project (fun j => p.assignment.sorted j.val)).image i.val) _ at eq
      rw [(p.row keys).project_key (fun j => p.assignment.sorted j.val) i] at eq
      rw [Substitution.apply_compose]
      exact eq.trans ((fit.inputs i).subst η.image)
    · intro i
      rw [Substitution.apply_compose]
      exact (atFn _ _ tuple i).trans ((fit.values i).subst η.image)

def solve (g : Expansion rules query) (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (r : VerifiedReducer (ruleRoot rules))
    (family : ∃ answers, CompleteVariants (ruleRoot rules) (List.ofFn query) answers) (avoid : List Variable) :
    {answers // VariantReply (ruleRoot rules) (List.ofFn query) avoid answers} := by
  let keys := keysOf query
  let found := VariantLayers.search g.seed g.next (subsumes query)
    (fun p => (subsumes_iff ..).mpr (Row.Subsumes.refl (p.row keys))) (basis g canonical family)
  let rows := found.val.map (Point.answer · keys)
  refine ⟨VariantFreshening.freshen keys avoid rows,VariantFreshening.reply r vars _ keys avoid (observed query) rows ⟨?_,?_⟩⟩
  · intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact sound_reached g (found.property.reachable p hp)
  · intro ρ nρ vs forms
    obtain ⟨out,rfl,nf⟩ := read_aligned query vs forms
    obtain ⟨p,mem,δ,fit⟩ := covers g canonical (· ∈ found.val) found.property.seeded
      (fun q h => sound_reached g (found.property.reachable q h))
      (fun p hp c hc => by
        obtain ⟨q,hq,sub⟩ := found.property.closed p hp c hc
        exact ⟨q,hq,(subsumes_iff ..).mp sub⟩) ρ nρ out nf
    obtain ⟨η,nη,hit⟩ := (normal_witness vars (fun i : Key keys => nρ i.val) (fun i => (nf i).2.1) fit).2
    refine ⟨_,List.mem_map_of_mem mem,η,nη,?_,alignedFn out p.value hit.values⟩
    intro v hv
    let i : Key keys := ⟨v,(observed query v).mpr hv⟩
    change EquivB _ (η.apply (((p.row keys).project (fun j => p.assignment.sorted j.val)).image v))
    rw [(p.row keys).project_key (fun j => p.assignment.sorted j.val) i]
    exact hit.inputs i

end
end Tamarin.VariantSaturation
