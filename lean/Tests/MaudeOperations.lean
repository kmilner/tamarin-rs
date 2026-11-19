import Tamarin.MaudeOperationRefinements
import Tamarin.MatchViaUnification
import Tamarin.SortClash

/-! The Maude probe has the single equation h(a) = b [variant]. The tuple
for get variants observes both h(X) and X under the same substitution. -/
namespace Tamarin.MaudeOperations.Tests
open Rewriting
abbrev S := Pairing.signature
private def constTerm (n : Nat) : Term S := .free (.other n 0) Fin.elim0
private abbrev a := constTerm 0
private abbrev b := constTerm 1
private def h (t : Term S) : Term S := .free (.other 0 1) (fun _ => t)
private def rules : List (Equation S) := [⟨h a, b⟩]
private abbrev R := ruleRoot rules
private def x : Variable := ⟨0, .msg⟩
private def query : List (Term S) := [h (.var x), .var x]

private theorem apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  trivial

private theorem constSorted (n : Nat) : HasSort (constTerm n) .msg := .free _ _ (fun i => i.elim0)

private theorem constNormal (n : Nat) : Normal R (constTerm n) := by
  refine ConstructorVariants.constructor_node_normal rules apps (constTerm n) ?_ ?_
  · intro member
    have he := List.mem_singleton.mp member
    change (Head.free (.other n 0) : Head S) = (Head.free (.other 0 1) : Head S) at he
    cases he
  · exact fun i => i.elim0

private theorem haReduces : NormalForm R (h a) b := by
  refine ⟨.step ⟨_, _, .refl _, .root ?_, .refl _⟩, constNormal _, ?_⟩
  · exact ⟨⟨h a, b⟩, by simp [rules], .identity, by simp, by simp⟩
  · intro s hs
    exact .widen (constSorted 1) (Term.rootSort_le hs)

-- Plain match does not apply the active equation to the subject.
example : ¬ ∃ σ : Substitution S, Matching.Matches [⟨b, h a⟩] σ := by
  rintro ⟨σ, hm⟩
  exact nomatch (hm _ (List.mem_singleton_self _)).head_eq

-- The same term does reduce. An implementation cannot just return its input.
example : ¬ ReductionReply R (h a) (h a) := by
  intro reply
  exact nomatch (reply.unique _ haReduces).head_eq

-- Omitting the specialized variant loses the reachable observation (b,a).
example (avoid : List Variable) :
    ¬ VariantReply R query avoid [⟨.identity, query⟩] := by
  intro reply
  let σ := Substitution.binding x a (constSorted 0)
  have image : σ.image x = a := Substitution.binding_image_self ..
  have normalized : Normalized R σ := by
    intro v
    by_cases hv : v = x
    · subst v
      rw [image]
      exact constNormal _
    · change Normal R (if v = x then a else .var v)
      rw [ite_eq_right hv]
      exact (ConstructorVariants.constructor_normal rules apps).1 v
  have obs : Aligned (fun t u => NormalForm R (σ.apply t) u) query [b, a] := by
    refine ⟨?_, ?_, trivial⟩
    · change NormalForm R (h (σ.image x)) b
      rw [image]
      exact haReduces
    · change NormalForm R (σ.image x) a
      rw [image]
      exact ⟨.basis (.refl _), constNormal _, fun _ hs => hs⟩
  obtain ⟨row, hr, _, _, _, values⟩ := reply.complete.2 σ normalized [b,a] obs
  obtain rfl := List.mem_singleton.mp hr
  exact nomatch values.1.head_eq

-- Plain get variants on an empty tuple still has the identity specialization.
example (s : Signature) (avoid : List Variable) :
    ¬ VariantReply (ruleRoot (sig := s) []) [] avoid [] := by
  intro reply
  have vars := (ConstructorVariants.constructor_normal (sig := s) [] (by simp)).1
  obtain ⟨_, impossible, _⟩ := reply.complete.2 Substitution.identity vars [] trivial
  exact List.not_mem_nil impossible

-- An open subject may contain the very variable that binds in the pattern.
-- Freezing that pattern variable changes the result of the same query.
example (u : VerifiedUnifier (Matching.RigidSubject.frozenSig S) (fun _ => True)) :
    let m := kindMatcherOfUnifier u
    let p : Problem S := [⟨.var x, h (.var x)⟩]
    (m.run p trivial [x]).isEmpty = false ∧ m.run p trivial [] = [] := by
  intro m p
  constructor
  · apply (hasMatch_iff m p trivial [x]).mpr
    let σ := Substitution.binding x (h (.var x)) (HasSort.free _ _ (fun _ => HasSort.var x))
    refine ⟨σ, ?_, ?_⟩
    · intro e he
      obtain rfl := List.mem_singleton.mp he
      change EquivB (σ.image x) (h (.var x))
      rw [show σ.image x = h (.var x) from Substitution.binding_image_self ..]
      exact .refl _
    · intro v frozen
      apply Substitution.binding_image_other
      rintro rfl
      exact frozen ⟨⟨_, List.mem_singleton_self _, rfl⟩, List.mem_singleton_self _⟩
  · apply Classical.byContradiction
    intro nonempty
    obtain ⟨σ, hm, fixed⟩ := (m.correct p trivial []).nonempty_iff.mp nonempty
    have eq := hm _ (List.mem_singleton_self _)
    change EquivB (σ.image x) (h (.var x)) at eq
    rw [fixed x (by simp)] at eq
    exact nomatch eq.head_eq

-- Maude accepts a kind-level natural-number application in a rigid pattern.
-- A Msg pattern variable still cannot capture it as its substitution image.
private abbrev NatSig : Signature := { S with acSort := fun _ => .nat }
private def ill : Term NatSig := .ac 0 (.atom (0, .pub)) (.atom (1, .nat))

example (m : Matching.VerifiedMatcher NatSig (fun _ => True)) :
    (m.run [⟨ill, .ac 0 (.atom (1, .nat)) (.atom (0, .pub))⟩] trivial []).isEmpty = false ∧
    m.run [⟨.var x, ill⟩] trivial [x] = [] := by
  constructor
  · apply (hasMatch_iff ..).mpr
    refine ⟨.identity, ?_, fun _ _ => rfl⟩
    intro e he
    obtain rfl := List.mem_singleton.mp he
    simpa [ill] using (EquivB.ac_swap (sig := NatSig) 0 (.atom (0, .pub)) (.atom (1, .nat)))
  · apply Classical.byContradiction
    intro nonempty
    obtain ⟨σ, hm, _⟩ := (m.correct _ trivial [x]).nonempty_iff.mp nonempty
    have eq := hm _ (List.mem_singleton_self _)
    change EquivB (σ.image x) ill at eq
    have impossible : ill.checkSort .msg = true :=
      (SortClash.check_equiv eq .msg) ▸ Term.checkSort_complete (σ.sorted x)
    contradiction

end Tamarin.MaudeOperations.Tests
