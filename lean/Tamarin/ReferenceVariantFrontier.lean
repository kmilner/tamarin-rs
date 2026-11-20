import Tamarin.ReferenceReduction
import Tamarin.ReferenceVariantFolding
import Tamarin.TupleNarrowingFrontier
import Tamarin.SymbolicNarrowing

/-! Check a proposed finite narrowing frontier for an entire query tuple.
Every normal answer must replay, and every live successor must have a representative. -/
namespace Tamarin.ReferenceVariantFrontier
open Rewriting VariantJoin TupleNarrowingFrontier MaudeOperations
variable {s : Signature} {n : Nat}

structure Point (s : Signature) (n : Nat) where
  assignment : Substitution s
  value : Fin n → Term s

def Point.row (p : Point s n) (keys : List Variable) : Row s (Key keys) (Fin n) :=
  ⟨fun i => p.assignment.image i.val, p.value⟩

def Point.answer (p : Point s n) (keys : List Variable) : Variant s :=
  ⟨(p.row keys).project (fun i => p.assignment.sorted i.val), List.ofFn p.value⟩

def seed (query : Fin n → Term s) : Point s n := ⟨.identity,query⟩

def keysOf (query : Fin n → Term s) : List Variable := ((List.ofFn query).flatMap Term.variables).eraseDups

/-- Apply a narrowing branch to every input and every untouched observation.
Only the selected result slot is replaced. -/
def expand (p : Point s n) (branches : Fin n → List (RootNarrowing.Branch s)) : List (Point s n) :=
  (List.finRange n).flatMap fun j => (branches j).map fun b =>
    ⟨b.subst.compose p.assignment, replace (fun i => b.subst.apply (p.value i)) j b.value⟩

theorem expand_covers {rules : List (Equation s)} (keys : List Variable) (p : Point s n)
    (branches : Fin n → List (RootNarrowing.Branch s))
    (search : ∀ j, RootNarrowing.Search (ruleRoot rules) (p.row keys).Uses
      (fun δ => ∀ i, Normal (ruleRoot rules) (δ.apply ((p.row keys).input i)))
      (p.value j) (· ∈ branches j)) :
    Successors rules (p.row keys) ((expand p branches).map (Point.row · keys)) := by
  intro δ admissible j u step
  obtain ⟨b,hb,η,agree,value⟩ := search j δ admissible u step
  have sibling (t : Term s) (visible : ∀ v, t.Occurs v → (p.row keys).Uses v) :
      EquivB (δ.apply t) (η.apply (b.subst.apply t)) := by
    rw [← Substitution.apply_compose]
    exact t.subst_equiv _ _ fun v hv => agree v (visible v hv)
  refine ⟨_,List.mem_map_of_mem (List.mem_flatMap.mpr ⟨j,List.mem_finRange _,List.mem_map_of_mem hb⟩),η,?_,?_⟩
  · intro i
    exact sibling _ fun _ hv => .inl ⟨i,hv⟩
  · intro i
    by_cases same : i = j
    · simpa [Point.row,replace,same] using value
    · simpa [Point.row,replace,same] using sibling (p.value i) (fun _ hv => .inr ⟨i,hv⟩)

theorem observed (query : Fin n → Term s) (v : Variable) :
    v ∈ keysOf query ↔ Observed (List.ofFn query) v := by
  simp [keysOf,Observed,List.mem_flatMap]

theorem alignedFn {α β : Type} {rel : α → β → Prop} (f : Fin n → α) (g : Fin n → β)
    (h : ∀ i, rel (f i) (g i)) : Aligned rel (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp [Aligned]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f := g)]
    exact ⟨h 0,ih _ _ (fun i => h i.succ)⟩

theorem read_aligned {α β : Type} {rel : α → β → Prop} (f : Fin n → α)
    (ys : List β) (h : Aligned rel (List.ofFn f) ys) :
    ∃ g, ys = List.ofFn g ∧ ∀ i, rel (f i) (g i) := by
  induction n generalizing ys with
  | zero =>
    cases ys with
    | nil => exact ⟨Fin.elim0,rfl,fun i => i.elim0⟩
    | cons => contradiction
  | succ n ih =>
    rw [List.ofFn_succ] at h
    cases ys with
    | nil => contradiction
    | cons b bs =>
      obtain ⟨tail,rfl,ht⟩ := ih _ _ h.2
      refine ⟨Fin.cases b tail,?_,Fin.cases h.1 ht⟩
      simp [List.ofFn_succ]

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def normal (rules : List (Equation s)) (t : Term s) :=
  (ReferenceReduction.successors rules t).isEmpty

theorem normal_iff {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules) (t : Term s) :
    normal rules t = true ↔ Normal (ruleRoot rules) t := by
  constructor
  · intro empty u step
    obtain ⟨v,mem,_⟩ := (ReferenceReduction.exactSteps rules bound t u).mpr step
    rw [List.isEmpty_iff.mp empty] at mem
    exact List.not_mem_nil mem
  · intro h
    apply List.isEmpty_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    exact fun u hu => h u ((ReferenceReduction.exactSteps rules bound t u).mp ⟨u,hu,.refl _⟩)

private def inputsNormal (rules : List (Equation s)) (keys : List Variable) (p : Point s n) :=
  keys.all (fun v => normal rules (p.assignment.image v))

private theorem inputs_iff {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (keys : List Variable) (p : Point s n) :
    inputsNormal rules keys p = true ↔ ∀ i, Normal (ruleRoot rules) ((p.row keys).input i) := by
  simp only [inputsNormal,List.all_eq_true,normal_iff bound]
  exact ⟨fun h i => h i i.property,fun h v hv => h ⟨v,hv⟩⟩

def terminal (rules : List (Equation s)) (keys : List Variable) (p : Point s n) :=
  inputsNormal rules keys p && (List.finRange n).all (fun i => normal rules (p.value i))

theorem terminal_iff {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (keys : List Variable) (p : Point s n) :
    terminal rules keys p = true ↔ (p.row keys).IsNormal (ruleRoot rules) := by
  simp [terminal,inputs_iff bound,normal_iff bound,Row.IsNormal,Point.row]

def accounted (rules : List (Equation s)) (keys : List Variable) (states : List (Point s n))
    (next : Point s n → List (Point s n)) :=
  states.all fun p => (next p).all fun r => !inputsNormal rules keys r ||
    states.any fun q => ReferenceVariantFolding.subsumes keys.attach (List.finRange n) (q.row keys) (r.row keys)

private def valid (reduce : Term s → Term s) (query : Fin n → Term s) (avoid : List Variable) (p : Point s n) :=
  let keys := keysOf query
  let allowed := fun w => decide (w ∈ keys ∨ w ∉ avoid)
  (List.finRange n).all (fun i => ReferenceMatching.equal (reduce (p.assignment.apply (query i))) (p.value i)) &&
    (keys.all fun v => (p.assignment.image v).variables.all allowed) &&
    (List.finRange n).all (fun i => (p.value i).variables.all allowed)

/-- The seed is always included. A rejected certificate carries no negative information about the query. -/
private def check (rules : List (Equation s)) (reduce : Term s → Term s) (query : Fin n → Term s) (avoid : List Variable)
    (proposed : List (Point s n)) (next : Point s n → List (Point s n)) : Option (List (Variant s)) :=
  let keys := keysOf query
  let states := seed query :: proposed
  let answers := states.filter (terminal rules keys)
  if accounted rules keys states next && answers.all (valid reduce query avoid) then
    some (answers.map fun p => p.answer keys)
  else none

private theorem valid_answer {rules : List (Equation s)} (r : VerifiedReducer (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s) (avoid : List Variable)
    (p : Point s n) (hn : (p.row (keysOf query)).IsNormal (ruleRoot rules)) (ok : valid r.reduce query avoid p = true) :
    let a := p.answer (keysOf query)
    a.Sound (ruleRoot rules) (List.ofFn query) ∧ a.Safe (List.ofFn query) avoid := by
  simp [valid,ReferenceMatching.equal_iff,observed] at ok
  let keys := keysOf query
  let σ := (p.answer keys).subst
  have on (v) (hv : Observed (List.ofFn query) v) : σ.image v = p.assignment.image v :=
    (p.row keys).project_key (fun i => p.assignment.sorted i.val) ⟨v,(observed query v).mpr hv⟩
  have result (i) : NormalForm (ruleRoot rules) (σ.apply (query i)) (p.value i) := by
    have same : σ.apply (query i) = p.assignment.apply (query i) := Term.subst_eq_of_agree _ _ _
      fun v hv => on v ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
    rw [same]
    have source := (r.correct (p.assignment.apply (query i))).normalForm
    have eq := ok.1.1 i
    exact ⟨source.1.trans (.basis eq),hn.2 i,
      fun k hk => Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete (source.2.2 k hk))⟩
  refine ⟨⟨(p.row keys).project_normal (fun i => p.assignment.sorted i.val) vars hn,alignedFn query p.value result⟩,?_,?_,?_⟩
  · intro v hv
    apply Substitution.outside
    exact fun hm => hv ((observed query v).mp hm)
  · intro v hv w hw
    change (σ.image v).Occurs w at hw
    rw [on v hv] at hw
    exact ok.1.2 v hv w hw
  · intro u hu w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
    exact ok.2 i w hw

/-- Finite closure accounts for every normalized specialization of the
whole tuple. Soundness and unique reconstruction of terminal rows can be
checked separately, using only the reduction graphs of those rows. -/
theorem covered {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (states : List (Point s n)) (seeded : seed query ∈ states) (next : Point s n → List (Point s n))
    (steps : ∀ p ∈ states, Successors rules (p.row (keysOf query)) ((next p).map (Point.row · (keysOf query))))
    (account : accounted rules (keysOf query) states next = true) :
    let answers := (states.filter (terminal rules (keysOf query))).map (Point.answer · (keysOf query))
    ∀ ρ, Normalized (ruleRoot rules) ρ → ∀ values,
      Aligned (fun t u => NormalForm (ruleRoot rules) (ρ.apply t) u) (List.ofFn query) values →
      ∃ a ∈ answers, ∃ η, Normalized (ruleRoot rules) η ∧
        Substitution.AgreesOn (Observed (List.ofFn query)) ρ (η.compose a.subst) ∧
        Aligned (fun u v => EquivB u (η.apply v)) values a.values := by
  dsimp only
  let keys := keysOf query
  let rows := fun (ps : List (Point s n)) => ps.map (Point.row · keys)
  let kept := states.filter (terminal rules keys)
  have closed (q) (hq : q ∈ rows states) : Successors rules q (rows states) := by
    intro δ hn j u st
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    obtain ⟨_,hm,η,fit⟩ := steps p hp δ hn j u st
    obtain ⟨child,member,rfl⟩ := List.mem_map.mp hm
    have test := List.all_eq_true.mp (List.all_eq_true.mp account p hp) child member
    simp only [Bool.or_eq_true] at test
    rcases test with bad|sub
    · have ok := (inputs_iff bound keys child).mpr (fun i =>
        normal_of_instance ((normal_equiv _ (fit.inputs i)).mp (hn i)))
      change (!inputsNormal rules keys child) = true at bad
      simp [ok] at bad
    · obtain ⟨g,hg,sub⟩ := List.any_eq_true.mp sub
      obtain ⟨σ,fits⟩ := (ReferenceVariantFolding.subsumes_iff (List.mem_attach keys) (List.mem_finRange) ..).mp sub
      exact ⟨_,List.mem_map_of_mem hg,η.compose σ,fits.compose fit⟩
  intro ρ nρ values forms
  obtain ⟨out,rfl,nf⟩ := read_aligned query values forms
  obtain ⟨_,hm,normalRow,η,nη,fit⟩ := TupleNarrowingFrontier.covers vars (rows states) closed
    (fun i => ρ.image i.val) (fun i => nρ i.val) (fun i => ρ.apply (query i)) out nf
    ⟨(seed query).row keys,List.mem_map_of_mem seeded,ρ,fun _ => .refl _,fun _ => .refl _⟩
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have survives : p ∈ kept := List.mem_filter.mpr ⟨hp,(terminal_iff bound keys p).mpr normalRow⟩
  refine ⟨_,List.mem_map_of_mem survives,η,nη,?_,alignedFn out p.value fit.values⟩
  intro w live
  have mem : w ∈ keys := (observed query w).mpr live
  change EquivB _ (η.apply (((p.row keys).project (fun i => p.assignment.sorted i.val)).image w))
  rw [(p.row keys).project_key (fun i => p.assignment.sorted i.val) ⟨w,mem⟩]
  exact fit.inputs ⟨w,mem⟩

/-- The oracle must cover individual rewrites exposed by every specialization
of a proposed state. The checker establishes global coverage, soundness,
freshness and reconstruction, including on kind-level observations. -/
private theorem correct {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (r : VerifiedReducer (ruleRoot rules)) (vars : Normalized (ruleRoot rules) Substitution.identity)
    (query : Fin n → Term s) (avoid : List Variable) (proposed : List (Point s n)) (next : Point s n → List (Point s n))
    (steps : ∀ p ∈ seed query :: proposed,
      Successors rules (p.row (keysOf query)) ((next p).map (Point.row · (keysOf query))))
    {answers} (accepted : check rules r.reduce query avoid proposed next = some answers) :
    VariantReply (ruleRoot rules) (List.ofFn query) avoid answers := by
  let keys := keysOf query
  let states := seed query :: proposed
  let kept := states.filter (terminal rules keys)
  change (if accounted rules keys states next && kept.all (valid r.reduce query avoid) then
    some (kept.map (Point.answer · keys)) else none) = some answers at accepted
  split at accepted
  next passed =>
    obtain ⟨account,replayed⟩ := (by simpa only [Bool.and_eq_true] using passed : _ ∧ _)
    cases accepted
    have validRow (p) (hp : p ∈ kept) := valid_answer r vars query avoid p
      ((terminal_iff bound keys p).mp (List.mem_filter.mp hp).2) (List.all_eq_true.mp replayed p hp)
    apply VariantReply.ofCanonical r vars
    · constructor
      · rintro _ h
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
        exact (validRow p hp).1
      · exact covered bound vars query states List.mem_cons_self next steps account
    · rintro _ h
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      exact (validRow p hp).2
  next => contradiction

/-- Only a certified local generator and reducer may promote a successful
frontier check to a command reply. The caller may propose any finite frontier. -/
def certify {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (r : VerifiedReducer (ruleRoot rules)) (vars : Normalized (ruleRoot rules) Substitution.identity)
    (query : Fin n → Term s) (avoid : List Variable) (proposed : List (Point s n)) (next : Point s n → List (Point s n))
    (steps : ∀ p ∈ seed query :: proposed,
      Successors rules (p.row (keysOf query)) ((next p).map (Point.row · (keysOf query)))) :
    Option {answers // VariantReply (ruleRoot rules) (List.ofFn query) avoid answers} :=
  match h : check rules r.reduce query avoid proposed next with
  | none => none
  | some answers => some ⟨answers,correct bound r vars query avoid proposed next steps h⟩

end
end Tamarin.ReferenceVariantFrontier
