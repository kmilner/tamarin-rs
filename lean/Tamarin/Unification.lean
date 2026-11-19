import Tamarin.Substitution

/-!
# Solver obligations

This module states contracts; it does not assume or implement a solver.
`CompleteSet` is the central contract. Soundness alone cannot justify closing
a proof-search branch. Results are finite lists but coverage ignores order,
duplicates, and redundant instances. Minimality is deliberately not required.
-/
namespace Tamarin

structure Equation (sig : Signature) where
  lhs : Term sig
  rhs : Term sig

abbrev Problem (sig : Signature) := List (Equation sig)

namespace Problem
variable {sig : Signature}

def Occurs (p : Problem sig) (v : Variable) : Prop :=
  ∃ e ∈ p, e.lhs.Occurs v ∨ e.rhs.Occurs v

/-- Both sides are well-sorted individually. Incomparable sorts are a valid
unsatisfiable query, not malformed input. No transport-level TOP is needed. -/
def WellFormed (p : Problem sig) : Prop :=
  ∀ e ∈ p, (∃ s, HasSort e.lhs s) ∧ (∃ s, HasSort e.rhs s)

def Solves (p : Problem sig) (σ : Substitution sig) : Prop :=
  ∀ e ∈ p, EquivB (σ.apply e.lhs) (σ.apply e.rhs)

def Satisfiable (p : Problem sig) : Prop := ∃ σ, p.Solves σ

theorem solves_compose (p : Problem sig) {σ : Substitution sig}
    (h : p.Solves σ) (δ : Substitution sig) : p.Solves (δ.compose σ) := by
  intro e he
  rw [Substitution.apply_compose, Substitution.apply_compose]
  exact (h e he).subst δ.image

/-- Coverage on input variables is strong enough to preserve solutions. -/
theorem solves_instance (p : Problem sig) {ρ σ : Substitution sig}
    (h : p.Solves σ) (instanceOf : Substitution.InstanceOn p.Occurs ρ σ) :
    p.Solves ρ := by
  obtain ⟨δ, hδ⟩ := instanceOf
  intro e he
  have hl := e.lhs.subst_equiv ρ.image (δ.compose σ).image
    (fun v hv => hδ v ⟨e, he, Or.inl hv⟩)
  have hr := e.rhs.subst_equiv ρ.image (δ.compose σ).image
    (fun v hv => hδ v ⟨e, he, Or.inr hv⟩)
  exact .trans hl (.trans (p.solves_compose h δ e he) hr.symm)

end Problem

/-- Every answer solves the whole conjunction with one substitution. -/
def Sound {sig : Signature} (p : Problem sig) (answers : List (Substitution sig)) : Prop :=
  ∀ σ ∈ answers, p.Solves σ

/-- Coverage includes nonground solutions, repeated variables, alien free
subterms, multiple AC/C symbols, and substitutions that narrow sorts.
The same δ must witness the factorization on ALL input variables. -/
def Covers {sig : Signature} (p : Problem sig) (answers : List (Substitution sig)) : Prop :=
  ∀ ρ : Substitution sig, p.Solves ρ →
    ∃ σ ∈ answers, Substitution.InstanceOn p.Occurs ρ σ

structure CompleteSet {sig : Signature} (p : Problem sig)
    (answers : List (Substitution sig)) : Prop where
  sound : Sound p answers
  covers : Covers p answers

/-- For any solution ρ, coverage by a complete set is an iff, not just a
one-way promise. This is the denotation an optimization must preserve. -/
theorem CompleteSet.solves_iff {sig : Signature} {p : Problem sig}
    {answers : List (Substitution sig)} (h : CompleteSet p answers)
    (ρ : Substitution sig) :
    p.Solves ρ ↔ ∃ σ ∈ answers, Substitution.InstanceOn p.Occurs ρ σ := by
  constructor
  · exact h.covers ρ
  · intro ⟨σ, hσ, hi⟩
    exact p.solves_instance (h.sound σ hσ) hi

/-- A complete empty result is exactly a proof of unsatisfiability. -/
theorem complete_empty_iff {sig : Signature} (p : Problem sig) :
    CompleteSet p [] ↔ ¬ p.Satisfiable := by
  constructor
  · intro h ⟨ρ, hρ⟩
    obtain ⟨σ, hσ, _⟩ := h.covers ρ hρ
    exact List.not_mem_nil hσ
  · intro h
    constructor
    · intro σ hσ; exact False.elim (List.not_mem_nil hσ)
    · intro ρ hρ; exact False.elim (h ⟨ρ, hρ⟩)

/-- The empty conjunction has a singleton identity solution set, not zero
solutions. This checks the most important empty-list convention. -/
theorem empty_problem_complete {sig : Signature} :
    CompleteSet ([] : Problem sig) [Substitution.identity] := by
  constructor
  · intro σ _ e he; exact False.elim (List.not_mem_nil he)
  · intro ρ _
    refine ⟨Substitution.identity, by simp, Substitution.identity, ?_⟩
    intro v ⟨e, he, _⟩
    exact False.elim (List.not_mem_nil he)

/-- Output substitutions leave variables outside the query untouched. -/
def DomainRestricted {sig : Signature} (p : Problem sig) (σ : Substitution sig) : Prop :=
  ∀ v, ¬ p.Occurs v → σ.image v = .var v

/-- Auxiliary variables avoid a finite caller-supplied context. Input variables
may remain in ranges. Witness identities in different answers are scoped
independently; callers must freshen each answer before applying it. -/
def FreshFor {sig : Signature} (p : Problem sig) (avoid : List Variable)
    (σ : Substitution sig) : Prop :=
  ∀ v, p.Occurs v → ∀ w, (σ.image v).Occurs w → ¬ p.Occurs w → w ∉ avoid

/-- The eventual pure reference solver must inhabit this structure using a
terminating Lean definition and proofs. No inhabitant is postulated here.
The semantic signature is generic; an implementation may require additional
decidable-equality/finite-signature data when constructing this structure.
This is not a Rust ABI or a specification of Maude's enumeration order. -/
structure VerifiedUnifier (sig : Signature) where
  solve : (p : Problem sig) → p.WellFormed → List Variable → List (Substitution sig)
  correct : ∀ p hp avoid, CompleteSet p (solve p hp avoid)
  domain : ∀ p hp avoid σ, σ ∈ solve p hp avoid → DomainRestricted p σ
  fresh : ∀ p hp avoid σ, σ ∈ solve p hp avoid → FreshFor p avoid σ

inductive StopReason where
  | cancelled | resourceLimit | unsupported | invalidInput | internalError
  deriving DecidableEq, Repr

/-- An interrupted enumeration is never encoded as a complete empty list.
Partial answers can be retained, but cannot establish absence of solutions. -/
inductive Outcome (sig : Signature) where
  | complete : List (Substitution sig) → Outcome sig
  | stopped : StopReason → List (Substitution sig) → Outcome sig

def Outcome.Correct {sig : Signature} (p : Problem sig) : Outcome sig → Prop
  | .complete answers => CompleteSet p answers
  | .stopped _ partialAnswers => Sound p partialAnswers

/-- Returned ordinary substitutions, including partial results. -/
def Outcome.answers {sig : Signature} : Outcome sig → List (Substitution sig)
  | .complete answers | .stopped _ answers => answers

/-- Runtime safety additionally requires noninterference with caller variables
outside the query and freshness of auxiliary variables. `Correct` alone does
not imply these: even the empty query admits mathematically complete answer
sets that bind arbitrary unrelated variables. These are ordinary substitution
semantics, not an implicit conversion to Rust's fresh-range substitutions. -/
structure Outcome.CorrectIn {sig : Signature} (p : Problem sig)
    (avoid : List Variable) (result : Outcome sig) : Prop where
  mathematical : result.Correct p
  domain : ∀ σ ∈ result.answers, DomainRestricted p σ
  fresh : ∀ σ ∈ result.answers, FreshFor p avoid σ

/-- The caller's finite variable context is part of the decoded request.
The adapter must include every live caller variable that auxiliaries must
avoid. Input variables need not be added: `FreshFor` already distinguishes
them from auxiliaries. -/
structure Request (sig : Signature) where
  problem : Problem sig
  avoid : List Variable

/-- Equality of answer-set denotations on all input variables using a shared
instantiation per answer. This is the obligation for a representation adapter,
including conversion to/from Rust's branch-local fresh-range representation.
The decoded substitutions must reflect actual caller-side witness freshening;
simply reinterpreting ordinary range variables as fresh does not suffice. -/
def AnswerSetEquivalent {sig : Signature} (p : Problem sig)
    (semantic represented : List (Substitution sig)) : Prop :=
  ∀ ρ, (∃ σ ∈ semantic, Substitution.InstanceOn p.Occurs ρ σ) ↔
    (∃ σ ∈ represented, Substitution.InstanceOn p.Occurs ρ σ)

theorem AnswerSetEquivalent.preserves_complete {sig : Signature} {p : Problem sig}
    {semantic represented : List (Substitution sig)}
    (equivalent : AnswerSetEquivalent p semantic represented)
    (complete : CompleteSet p semantic) : CompleteSet p represented := by
  constructor
  · intro σ hσ
    apply (complete.solves_iff σ).mpr
    exact (equivalent σ).mpr ⟨σ, hσ, Substitution.instanceOn_refl p.Occurs σ⟩
  · intro ρ hρ
    exact (equivalent ρ).mp (complete.covers ρ hρ)

/-- A representation boundary must preserve denotation, domain, and freshness.
No inhabitant for the Rust encoder/decoder is assumed. In particular ordinary
`{x ↦ f(y)}` may require explicit identity/renaming bindings for input `y`
when represented with fresh range variables. -/
structure OutputRefinement {sig : Signature} (request : Request sig)
    (semantic represented : List (Substitution sig)) : Prop where
  equivalent : AnswerSetEquivalent request.problem semantic represented
  domain : ∀ σ ∈ represented, DomainRestricted request.problem σ
  fresh : ∀ σ ∈ represented, FreshFor request.problem request.avoid σ

theorem OutputRefinement.preserves_correct {sig : Signature} {request : Request sig}
    {semantic represented : List (Substitution sig)}
    (refinement : OutputRefinement request semantic represented)
    (complete : CompleteSet request.problem semantic) :
    (Outcome.complete represented).CorrectIn request.problem request.avoid :=
  ⟨refinement.equivalent.preserves_complete complete, refinement.domain, refinement.fresh⟩

/-- Safety for a runtime wrapper with explicit interruption. This alone allows
an implementation that always stops; it is NOT a total-solver contract. -/
def SafeExecution {sig : Signature} {Input Output : Type}
    (decodeInput : Input → Option (Request sig))
    (decodeOutput : Output → Option (Outcome sig))
    (run : Input → Output) : Prop :=
  ∀ input request, decodeInput input = some request → request.problem.WellFormed →
    ∃ result, decodeOutput (run input) = some result ∧
      result.CorrectIn request.problem request.avoid

/-- A terminating implementation of the supported fragment must complete on
every valid input in the absence of cancellation/resource limits. This
separate obligation rules out vacuous "always stopped" implementations.
Decoder correctness and faithful Rust encoding are additional obligations. -/
def TotalRefinement {sig : Signature} {Input Output : Type}
    (decodeInput : Input → Option (Request sig))
    (decodeOutput : Output → Option (Outcome sig))
    (run : Input → Output) : Prop :=
  ∀ input request, decodeInput input = some request → request.problem.WellFormed →
    ∃ answers, decodeOutput (run input) = some (.complete answers) ∧
      (Outcome.complete answers).CorrectIn request.problem request.avoid

end Tamarin
