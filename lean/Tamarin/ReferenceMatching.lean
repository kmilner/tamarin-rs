import Tamarin.ACSplits
import Tamarin.MaudeOperations
import Tamarin.MatchingFree
import Tamarin.Commutative
import Tamarin.SortClash

/-! Finite structural reference for whole-term matching. A branch records an
image requirement at each pattern-variable occurrence. Distinct occurrences
may constrain the same variable, even across different equations. -/
namespace Tamarin.ReferenceMatching
open Matching
variable {s : Signature}
abbrev Requirements (s : Signature) := List (Variable × Term s)

private def holds (σ : Substitution s) (row : Requirements s) : Prop :=
  ∀ v t, (v,t) ∈ row → EquivB (σ.image v) t

private def combine (xs ys : List (Requirements s)) :=
  xs.flatMap fun a => ys.map (a ++ ·)

private def together : List (List (Requirements s)) → List (Requirements s)
  | [] => [[]]
  | xs :: rest => combine xs (together rest)

private def accepts (σ : Substitution s) (rows : List (Requirements s)) : Prop :=
  ∃ row ∈ rows, holds σ row

private theorem mem_combine {xs ys : List (Requirements s)} {row} :
    row ∈ combine xs ys ↔ ∃ a ∈ xs, ∃ b ∈ ys, a ++ b = row := by
  simp [combine]

private theorem combine_iff (σ : Substitution s) (xs ys : List (Requirements s)) :
    accepts σ (combine xs ys) ↔ accepts σ xs ∧ accepts σ ys := by
  constructor
  · rintro ⟨_, member, sat⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_combine.mp member
    exact ⟨⟨a,ha,fun v t h => sat v t (List.mem_append_left _ h)⟩,
      ⟨b,hb,fun v t h => sat v t (List.mem_append_right _ h)⟩⟩
  · rintro ⟨⟨a,ha,sa⟩,⟨b,hb,sb⟩⟩
    exact ⟨_, mem_combine.mpr ⟨a, ha, b, hb, rfl⟩,
      fun v t h => (List.mem_append.mp h).elim (sa v t) (sb v t)⟩

private theorem together_iff (σ : Substitution s) (xs : List (List (Requirements s))) :
    accepts σ (together xs) ↔ ∀ rows ∈ xs, accepts σ rows := by
  induction xs with
  | nil => simp [accepts, together, holds]
  | cons x xs ih => simp [together, combine_iff, ih]

private theorem mentions_combine {xs ys : List (Requirements s)} {row v}
    (member : row ∈ combine xs ys)
    (side : (∀ part ∈ xs, ∃ u, (v, u) ∈ part) ∨ (∀ part ∈ ys, ∃ u, (v, u) ∈ part)) :
    ∃ u, (v, u) ∈ row := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_combine.mp member
  rcases side with left | right
  · obtain ⟨u, hu⟩ := left a ha
    exact ⟨u, List.mem_append_left _ hu⟩
  · obtain ⟨u, hu⟩ := right b hb
    exact ⟨u, List.mem_append_right _ hu⟩

private theorem part_of_together (xs : List (List (Requirements s))) {row}
    (member : row ∈ together xs) {ys} (hy : ys ∈ xs) :
    ∃ part ∈ ys, part ⊆ row := by
  induction xs generalizing row with
  | nil => contradiction
  | cons y xs ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_combine.mp member
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨a, ha, List.subset_append_left ..⟩
    · obtain ⟨v,hv,sub⟩ := ih hb hm
      exact ⟨v, hv, sub.trans (List.subset_append_right ..)⟩

private theorem lookup_requirement (row : Requirements s) {v}
    (mentioned : ∃ t, (v, t) ∈ row) : ∃ u, row.lookup v = some u ∧ (v, u) ∈ row := by
  obtain ⟨t, member⟩ := mentioned
  have found : (row.lookup v).isSome := List.lookup_isSome_iff.mpr ⟨(v, t), member, by simp⟩
  obtain ⟨u, lookup⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨_, _, eq, _⟩ := List.lookup_eq_some_iff.mp lookup
  exact ⟨u, lookup, by simp [eq]⟩

private theorem mismatch {a b : Term s}
    (ne : (headModel s).eval Head.var a ≠ (headModel s).eval Head.var b) :
    ¬ EquivB a b := fun eq => ne eq.head_eq

private def isVariable (v : Variable) : Term s → Bool
  | .var w => v == w
  | _ => false

private theorem isVariable_iff (v : Variable) (t : Term s) :
    isVariable v t = true ↔ EquivB (.var v) t := by
  cases t with
  | var w =>
    simp only [isVariable, beq_iff_eq]
    exact ⟨fun h => h ▸ .refl _, fun h => Head.var.inj h.head_eq⟩
  | _ => exact ⟨nofun,fun h => nomatch h.head_eq⟩

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def branches : Term s → Term s → List (Requirements s)
  | .var v, t => [[(v,t)]]
  | .atom a, .atom b => if a = b then [[]] else []
  | .free f xs, .free g ys =>
    if h : f = g then together (List.ofFn fun i => branches (xs i) (ys (h ▸ i))) else []
  | .comm f a b, .comm g l r =>
    if f = g then
      combine (branches a l) (branches b r) ++ combine (branches a r) (branches b l)
    else []
  | .ac f a b, t =>
    (ACSplits.splits f t).flatMap fun (l,r) => combine (branches a l) (branches b r)
  | _, _ => []

private theorem branches_iff (σ : Substitution s) (pattern subject : Term s) :
    accepts σ (branches pattern subject) ↔ EquivB (σ.apply pattern) subject := by
  induction pattern generalizing subject with
  | var v => simp [branches, accepts, holds, Substitution.apply, Term.subst]
  | atom a =>
    cases subject with
    | atom b =>
      by_cases same : a = b
      · subst b; simp [branches, accepts, holds, Substitution.apply, Term.subst, EquivB.refl]
      · simp [branches, same, accepts]
        exact mismatch (fun h => same (Head.atom.inj h))
    | _ => simp [branches, accepts]; exact mismatch (fun h => nomatch h)
  | free f xs ih =>
    cases subject with
    | free g ys =>
      by_cases same : f = g
      · subst g
        simp only [branches, ↓reduceDIte, together_iff]
        change _ ↔ EquivB (.free f (fun i => σ.apply (xs i))) (.free f ys)
        rw [free_equiv_iff]
        constructor
        · exact fun hs i => (ih i (ys i)).mp (hs _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
        · rintro hs _ hm
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
          exact (ih i (ys i)).mpr (hs i)
      · simp [branches, same, accepts]
        exact mismatch (fun h => same (Head.free.inj h))
    | _ => simp [branches, accepts]; exact mismatch (fun h => nomatch h)
  | comm f a b ia ib =>
    cases subject with
    | comm g l r =>
      by_cases same : f = g
      · subst g
        have append (xs ys : List (Requirements s)) :
            accepts σ (xs ++ ys) ↔ accepts σ xs ∨ accepts σ ys := by
          simp [accepts, List.mem_append, or_and_right, exists_or]
        simp only [branches, ite_true, append, combine_iff, ia, ib]
        exact (Commutative.equiv_iff ..).symm
      · simp [branches, same, accepts]
        exact mismatch (fun h => same (Head.comm.inj h))
    | _ => simp [branches, accepts]; exact mismatch (fun h => nomatch h)
  | ac f a b ia ib =>
    constructor
    · rintro ⟨row,member,sat⟩
      obtain ⟨⟨l,r⟩,split,br⟩ := List.mem_flatMap.mp member
      obtain ⟨hl,hr⟩ := (combine_iff σ _ _).mp ⟨row,br,sat⟩
      exact (EquivB.ac_congr f ((ia l).mp hl) ((ib r).mp hr)).trans (ACSplits.sound f _ split).symm
    · intro eq
      obtain ⟨l,r,split,hl,hr⟩ := ACSplits.complete f eq.symm
      obtain ⟨row,member,sat⟩ := (combine_iff σ _ _).mpr ⟨(ia l).mpr hl,(ib r).mpr hr⟩
      exact ⟨row,List.mem_flatMap.mpr ⟨(l,r),split,member⟩,sat⟩

private theorem mentions (p t : Term s) {row} (hr : row ∈ branches p t)
    {v} (hv : p.Occurs v) : ∃ u, (v,u) ∈ row := by
  induction p generalizing t row with
  | var w =>
    obtain rfl := hv
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _⟩
  | atom => contradiction
  | free f xs ih =>
    cases t <;> simp only [branches, List.not_mem_nil] at hr
    split at hr
    · obtain ⟨i,occ⟩ := hv
      obtain ⟨part,hp,sub⟩ := part_of_together _ hr (List.mem_ofFn.mpr ⟨i,rfl⟩)
      obtain ⟨u,hu⟩ := ih i _ hp occ
      exact ⟨u,sub hu⟩
    · contradiction
  | comm f a b ia ib =>
    cases t <;> simp only [branches, List.not_mem_nil] at hr
    split at hr
    · rcases List.mem_append.mp hr with member | member <;>
        exact mentions_combine member (hv.imp (fun av _ hit => ia _ hit av) (fun bv _ hit => ib _ hit bv))
    · contradiction
  | ac f a b ia ib =>
    obtain ⟨⟨l, r⟩, _, member⟩ := List.mem_flatMap.mp hr
    exact mentions_combine member (hv.imp (fun av _ hit => ia l hit av) (fun bv _ hit => ib r hit bv))

/-- When the left-hand variables are rigid, their required images must be
the same variables. The same decomposition thus decides ordinary B-equality. -/
def equal (a b : Term s) : Bool :=
  (branches a b).any fun row => row.all fun (v,t) => isVariable v t

theorem equal_iff (a b : Term s) : equal a b = true ↔ EquivB a b := by
  apply Iff.trans _ (by simpa using branches_iff (Substitution.identity : Substitution s) a b)
  simp [equal, accepts, holds, isVariable_iff, Substitution.identity, Prod.forall]

private def queryBranches (p : Problem s) :=
  together (p.map fun e => branches e.lhs e.rhs)

private theorem query_iff (p : Problem s) (σ : Substitution s) :
    accepts σ (queryBranches p) ↔ Matches p σ := by
  simp [queryBranches, together_iff, branches_iff, Matches]

private theorem query_mentions (p : Problem s) {row} (member : row ∈ queryBranches p) {v}
    (obs : Observed p v) : ∃ t, (v,t) ∈ row := by
  obtain ⟨e,he,occ⟩ := obs
  obtain ⟨part,hp,sub⟩ := part_of_together _ member (List.mem_map_of_mem he)
  obtain ⟨t,ht⟩ := mentions e.lhs e.rhs hp occ
  exact ⟨t,sub ht⟩

private def keys (p : Problem s) (bindable : List Variable) : List Variable :=
  (MaudeOperations.patternVariables p).filter (fun v => bindable.contains v)

private def imageAt (row : Requirements s) (domain : List Variable) (v : Variable) : Term s :=
  let t := (row.lookup v).getD (.var v)
  if v ∈ domain ∧ t.checkSort v.sort = true then t else .var v

private def assignment (row : Requirements s) (domain : List Variable) : Substitution s where
  image := imageAt row domain
  support := domain
  outside v hv := by simp [imageAt,hv]
  sorted v := by
    simp only [imageAt]
    split
    · next h => exact Term.checkSort_sound _ _ h.2
    · exact .var v

private def valid (p : Problem s) (σ : Substitution s) : Bool :=
  p.all (fun e => equal (σ.apply e.lhs) e.rhs)

private theorem valid_iff (p : Problem s) (σ : Substitution s) :
    valid p σ = true ↔ Matches p σ := by simp [valid, Matches, equal_iff]

def solve (p : Problem s) (bindable : List Variable) : List (Substitution s) :=
  ((queryBranches p).map fun row => assignment row (keys p bindable)).filter (valid p)

end

/-- Full scoped matching, including rigid subject variables, requires equality
on symbol identities alone. There is no restriction on input sorts or size. -/
def matcher (s : Signature) [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] : VerifiedMatcher s (fun _ => True) where
  run p _ bindable := solve p bindable
  correct p _ bindable := by
    constructor
    · intro σ mem
      obtain ⟨h,ok⟩ := List.mem_filter.mp mem
      obtain ⟨row,_,rfl⟩ := List.mem_map.mp h
      refine ⟨(valid_iff ..).mp ok, fun v frozen => ?_⟩
      apply Substitution.outside
      simpa [assignment,keys] using frozen
    · intro ρ matched scope
      obtain ⟨row,member,sat⟩ := (query_iff p ρ).mpr matched
      let out := assignment row (keys p bindable)
      have agree : Substitution.AgreesOn (Observed p) ρ out := by
        intro v obs
        by_cases allowed : v ∈ bindable
        · have key : v ∈ keys p bindable := by simp [keys,obs,allowed]
          obtain ⟨u, lookup, hit⟩ := lookup_requirement row (query_mentions p member obs)
          have same := sat v u hit
          have sorted := SortClash.check_equiv same v.sort ▸ Term.checkSort_complete (ρ.sorted v)
          simpa [out, assignment, imageAt, lookup, key, sorted] using same
        · have off : v ∉ keys p bindable := by simp [keys,allowed]
          rw [scope v (fun h => allowed h.2), out.outside v off]
          exact .refl _
      have solved := matches_of_agrees matched (fun v hv => (agree v hv).symm)
      exact ⟨out,List.mem_filter.mpr ⟨List.mem_map.mpr ⟨row,member,rfl⟩,(valid_iff ..).mpr solved⟩,agree⟩

end Tamarin.ReferenceMatching
