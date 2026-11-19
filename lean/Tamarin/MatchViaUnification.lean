import Tamarin.MaudeOperations
import Tamarin.RigidSubject

/-! A total reference matcher from a total ordinary B-unifier. All subject
variables are replaced by rigid, sort-preserving atoms. After thawing each
answer, a scope filter handles callers which freeze some pattern variables. -/
namespace Tamarin.MaudeOperations
open Matching RigidSubject
variable {s : Signature}

private def fixes (σ : Substitution s) (v : Variable) : Bool :=
  match σ.image v with
  | .var w => w == v
  | _ => false

private theorem fixes_iff (σ : Substitution s) (v : Variable) :
    fixes σ v = true ↔ σ.image v = .var v := by
  cases h : σ.image v <;> simp [fixes, h]

private def inScope (p : Problem s) (bindable : List Variable) (σ : Substitution s) : Bool :=
  (patternVariables p).all fun v => bindable.contains v || fixes σ v

private theorem scope_test {p : Problem s} {bindable : List Variable} {σ : Substitution s}
    (outside : Scoped p (fun _ => True) σ) :
    inScope p bindable σ = true ↔ Scoped p (fun v => v ∈ bindable) σ := by
  simp only [inScope, List.all_eq_true, mem_patternVariables, Bool.or_eq_true, List.contains_iff_mem,
    fixes_iff]
  constructor
  · intro accepted v frozen
    by_cases observed : Matching.Observed p v
    · exact (accepted v observed).resolve_left (fun h => frozen ⟨observed, h⟩)
    · exact outside v (fun h => observed h.1)
  · intro valid v observed
    by_cases allowed : v ∈ bindable
    · exact .inl allowed
    · exact .inr (valid v (fun h => allowed h.2))

private theorem filter_complete (p : Problem s) (bindable : List Variable) {rows}
    (hc : Complete p (fun _ => True) rows) :
    Complete p (fun v => v ∈ bindable) (rows.filter (inScope p bindable)) := by
  constructor
  · intro σ member
    obtain ⟨hr, accept⟩ := List.mem_filter.mp member
    obtain ⟨hm, outside⟩ := hc.sound σ hr
    exact ⟨hm, (scope_test outside).mp accept⟩
  · intro ρ hm restricted
    obtain ⟨σ, member, agree⟩ := hc.covers ρ hm
      (fun v unseen => restricted v (fun h => unseen ⟨h.1, trivial⟩))
    have outside := (hc.sound σ member).2
    refine ⟨σ, List.mem_filter.mpr ⟨member, (scope_test outside).mpr ?_⟩, agree⟩
    intro v frozen
    by_cases observed : Matching.Observed p v
    · have same := agree v observed
      rw [restricted v frozen] at same
      cases img : σ.image v <;> rw [img] at same <;> cases same.head_eq
      rfl
    · exact outside v (fun h => observed h.1)

/-- The admissible input domain is inherited from the supplied unifier on
the translated conjunction. Its generality and termination are the only
search obligations. No matching-specific rank, width, or paging bound enters. -/
def matcherOfUnifier {inputs admitted} (u : VerifiedUnifier (frozenSig s) admitted)
    (accept : ∀ p : Problem s, inputs p → admitted (query s p)) : VerifiedMatcher s inputs where
  run p hp bindable :=
    ((u.solve (query s p) (accept p hp) []).map (decode s)).filter (inScope p bindable)
  correct p hp bindable := by
    apply filter_complete
    apply RigidSubject.complete
    apply of_ground_subjects
    · intro e he
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
      exact freeze_ground s r.rhs
    · exact u.correct _ _ _
    · exact u.domain _ _ _

def sortedMatcherOfUnifier (u : VerifiedUnifier (frozenSig s)) : VerifiedMatcher s :=
  matcherOfUnifier u (query_wellFormed s)

def kindMatcherOfUnifier (u : VerifiedUnifier (frozenSig s) (fun _ => True)) :
    VerifiedMatcher s (fun _ => True) :=
  matcherOfUnifier u (fun _ _ => trivial)

end Tamarin.MaudeOperations
