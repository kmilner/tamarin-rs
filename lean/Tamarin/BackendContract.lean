import TamarinRuntime.Interface
import Tamarin.FlatACVariable
import Tamarin.WordCodec

/-!
Fixed semantic obligations for the current executable fragment. This module
must not import candidate algorithms. The supported-input conditions, decoder
and theorem types belong to the specification, not to the optimization search.
-/
namespace Tamarin

namespace Executable
def decodeStatus {sig : Signature} (status : UInt8) : Outcome sig :=
  if status = 2 then .complete [Substitution.identity]
  else if status = 1 then .complete []
  else .stopped .unsupported []
end Executable

/-- Semantic contract for the two numeric kernels. Every valid nonempty input
must complete. Success AND complete failure need complete-set proofs, including
nonground solutions. Result packet validity is an explicit obligation too.
This fragment contract is not a general VerifiedUnifier or a Rust encoder proof. -/
structure FlatACBackend.Correct (backend : FlatACBackend) : Prop where
  equal_status : ∀ lhs rhs, backend.equal lhs rhs = 0 ∨
    backend.equal lhs rhs = 1 ∨ backend.equal lhs rhs = 2
  empty_inputs : ∀ lhs rhs : Array UInt64, lhs = #[] ∨ rhs = #[] →
    backend.equal lhs rhs = 0 ∧ backend.residual lhs rhs = #[0]
  equal_correct : ∀ {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64),
    ∀ (f : sig.ACSym) (lhs rhs : Array UInt64),
    (∀ a ∈ lhs.toList ++ rhs.toList, encode (decode a) = some a) →
    (Executable.decodeStatus (sig := sig) (backend.equal lhs rhs)).Correct
      (FlatAC.problem f (lhs.toList.map decode) (rhs.toList.map decode))
  equal_completes : ∀ lhs rhs : Array UInt64,
    lhs.toList ≠ [] → rhs.toList ≠ [] →
    backend.equal lhs rhs = 1 ∨ backend.equal lhs rhs = 2
  equal_words : ∀ lhs rhs : Array UInt64, lhs.toList ≠ [] → rhs.toList ≠ [] →
    (backend.equal lhs rhs = 2 ↔ lhs.toList.Perm rhs.toList)
  residual_admits : ∀ small big : Array UInt64, ∀ excess : List UInt64,
    small.toList ≠ [] → excess ≠ [] → big.toList.Perm (excess ++ small.toList) →
    ∃ rest : List UInt64, backend.residual small big = (2 :: rest).toArray
  residual_packet : ∀ tail rhs : Array UInt64,
    backend.residual tail rhs = #[0] ∨ backend.residual tail rhs = #[1] ∨
    ∃ rest : List UInt64, rest ≠ [] ∧ backend.residual tail rhs = (2 :: rest).toArray
  residual_difference : ∀ tail rhs : Array UInt64, ∀ rest : List UInt64,
    backend.residual tail rhs = (2 :: rest).toArray → rhs.toList.Perm (rest ++ tail.toList)
  residual_success : ∀ {sig : Signature}
    (decode : UInt64 → sig.Atom) (v : Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64),
    backend.residual tail rhs = (2 :: rest).toArray →
    ∀ hs : HasSort (FlatAC.term f (rest.map decode)) v.sort,
    CompleteSet
      (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode))
      [Substitution.binding v (FlatAC.term f (rest.map decode)) hs]
  residual_failure : ∀ {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64),
    ∀ (v : Variable) (f : sig.ACSym) (tail rhs : Array UInt64),
    (∀ a ∈ tail.toList ++ rhs.toList, encode (decode a) = some a) → backend.residual tail rhs = #[1] →
    CompleteSet
      (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode)) []
  residual_completes : ∀ tail rhs : Array UInt64,
    tail.toList ≠ [] → rhs.toList ≠ [] →
    backend.residual tail rhs = #[1] ∨
    ∃ rest : List UInt64, rest ≠ [] ∧ backend.residual tail rhs = (2 :: rest).toArray

namespace FlatACBackend.Correct

variable {backend : FlatACBackend}

/-- Packet validity excludes an empty successful product independently of
which algorithm produced it. -/
theorem residual_nonempty (correct : backend.Correct) (tail rhs : Array UInt64)
    (rest : List UInt64) (h : backend.residual tail rhs = (2 :: rest).toArray) :
    rest ≠ [] := by
  rcases correct.residual_packet tail rhs with hzero | hone | ⟨xs, hn, hx⟩
  · have bad := congrArg Array.toList (hzero.symm.trans h)
    simp at bad
  · have bad := congrArg Array.toList (hone.symm.trans h)
    simp at bad
  · have same := congrArg Array.toList (hx.symm.trans h)
    have he : xs = rest := by simpa using same
    exact he ▸ hn

/-- The fixed numeric-to-semantic binding constructor also preserves caller
scope. This theorem is reusable for every candidate satisfying the contract;
it does not assert that the Rust decoder has been formally verified. -/
theorem residual_correctIn (correct : backend.Correct) {sig : Signature}
    (decode : UInt64 → sig.Atom) (v : Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64)
    (h : backend.residual tail rhs = (2 :: rest).toArray)
    (hs : HasSort (FlatAC.term f (rest.map decode)) v.sort) (avoid : List Variable) :
    (Outcome.complete [Substitution.binding v (FlatAC.term f (rest.map decode)) hs]).CorrectIn
      (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode)) avoid := by
  refine ⟨correct.residual_success decode v f tail rhs rest h hs, ?_, ?_⟩
  · intro σ hσ
    have he : σ = Substitution.binding v (FlatAC.term f (rest.map decode)) hs := by
      simpa [Outcome.answers] using hσ
    subst σ
    exact FlatAC.variable_difference_domain v f _ _ _ hs
  · intro σ hσ
    have he : σ = Substitution.binding v (FlatAC.term f (rest.map decode)) hs := by
      simpa [Outcome.answers] using hσ
    subst σ
    exact FlatAC.variable_difference_fresh v f _ _ _
      (by simpa using correct.residual_nonempty tail rhs rest h) hs avoid

end FlatACBackend.Correct

end Tamarin
