import Tamarin.ACMatchBagsRefinement
import Tamarin.MatchPrefilter

/-! The incidence test uses equality of the caller's factor identifiers.
Relate those identifiers to the structural congruence classes of the actual
equations, including subject factors that contain pattern variable names. -/
namespace Tamarin.OpenMatch.Profiles

variable {α : Type} [DecidableEq α] {sig : Signature}

def Possible (keys : List Variable) (atoms : List α) (rows : List (List Variable × List α)) : Prop :=
  (∀ row ∈ rows, row.2 ⊆ atoms) ∧
  (∀ b ∈ atoms, ∃ a ∈ keys, profile (rows.map Prod.fst) a = profile (rows.map Prod.snd) b) ∧
  ∀ group, (keys.filter (fun a => profile (rows.map Prod.fst) a == group)).length ≤
    (atoms.filter (fun b => profile (rows.map Prod.snd) b == group)).length

/-- A failed profile or capacity check rules out every simultaneous match.
The caller may use any factor identifiers that distinguish B classes on the
observed subjects. Their order and all identifiers outside these equations
are irrelevant. -/
theorem possible_of_matches [DecidableEq sig.ACSym] (f : sig.ACSym) (problem : Problem sig)
    (layout : Equation sig → List Variable × List α) (term : α → Term sig)
    (pivot : Equation sig) (used : pivot ∈ problem) (distinct : (layout pivot).2.Nodup)
    (covered : ∀ e ∈ problem, (layout e).1 ⊆ (layout pivot).1)
    (left : ∀ e ∈ problem, ((layout e).1.map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    (right : ∀ e ∈ problem, ((layout e).2.map term).Perm (ACRepresentation.flatten f e.rhs))
    (reflects : ∀ e ∈ problem, ∀ a ∈ (layout e).2, ∀ d ∈ problem, ∀ b ∈ (layout d).2,
      EquivB (term a) (term b) → a = b)
    (σ : Substitution sig) (matched : Matching.Matches problem σ) :
    Possible (layout pivot).1 (layout pivot).2 (problem.map layout) := by
  obtain ⟨im,⟨nonempty,all⟩,_⟩ := Matching.ACBags.of_matches f problem layout id term (fun _ => [])
    (by simp) (by simpa using left) (by simpa using right) reflects σ matched
  have atPivot := List.mem_map_of_mem (f := layout) used
  exact necessary _ _ _ im (nonempty _ atPivot) distinct (all _ atPivot)
    (fun row hr => by obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr; exact covered e he) all

/-- Rust can use the structural term itself as the factor key on canonical
C/AC representatives. Freezing the subject makes this criterion applicable
to open terms. Restricting substitutions by an existing seed can only
further restrict the set excluded by this refutation. -/
theorem refutes_canonical [DecidableEq sig.ACSym] [DecidableEq (Term sig)] (f : sig.ACSym)
    (problem : Problem sig) (keys : Equation sig → List Variable) (pivot : Equation sig)
    (used : pivot ∈ problem) (distinct : (ACRepresentation.flatten f pivot.rhs).Nodup)
    (covered : ∀ e ∈ problem, keys e ⊆ keys pivot)
    (left : ∀ e ∈ problem, ((keys e).map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    {le : Term (Matching.RigidSubject.frozenSig sig) → Term (Matching.RigidSubject.frozenSig sig) → Prop}
    (anti : ∀ a b, le a b → le b a → a = b)
    (canonical : ∀ e ∈ problem, ∀ t ∈ ACRepresentation.flatten f e.rhs,
      CanonicalTree.Canonical le (Matching.RigidSubject.freeze sig t))
    (failed : ¬ Possible (keys pivot) (ACRepresentation.flatten f pivot.rhs)
      (problem.map (fun e => (keys e, ACRepresentation.flatten f e.rhs)))) :
    ¬ ∃ σ, Matching.Matches problem σ := by
  rintro ⟨σ,sol⟩
  apply failed
  apply possible_of_matches f problem (fun e => (keys e, ACRepresentation.flatten f e.rhs))
    id pivot used distinct covered left _ _ σ sol
  · intro e _
    simp
  · intro e he a ha d hd b hb eq
    exact (Matching.Prefilter.canonical_eq_iff anti (canonical e he a ha) (canonical d hd b hb)).mp eq

end Tamarin.OpenMatch.Profiles
