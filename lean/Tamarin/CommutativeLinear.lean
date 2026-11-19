import Tamarin.Commutative
import Tamarin.FreshSubstitution

/-! A complete executable reference for C(x,y) = C(s,t) with independent
right operands. This includes the four distinct Msg variables in Tamarin's
bilinear-pairing derivation check. s and t can share arbitrary variables. -/
namespace Tamarin.Commutative

structure Linear (sig : Signature) where
  f : sig.CSym
  x : Variable
  y : Variable
  s : Term sig
  t : Term sig
  distinct : x ≠ y
  sx : x.sort = sig.cSort f
  sy : y.sort = sig.cSort f
  ss : HasSort s (sig.cSort f)
  st : HasSort t (sig.cSort f)
  independent : ∀ v, s.Occurs v ∨ t.Occurs v → v ≠ x ∧ v ≠ y

namespace Linear
variable {sig : Signature} (l : Linear sig)

def query : Query sig := ⟨l.f, .var l.x, .var l.y, l.s, l.t, []⟩
def first (cross : Bool) := if cross then l.t else l.s
def second (cross : Bool) := if cross then l.s else l.t

def answer (cross : Bool) : Substitution sig where
  image v := if v = l.x then l.first cross else if v = l.y then l.second cross else .var v
  support := [l.x, l.y]
  outside := by intro v hv; simp_all
  sorted := by
    intro v; split
    · next h => subst v; rw [l.sx]; cases cross <;> first | exact l.ss | exact l.st
    · split
      · next h => subst v; rw [l.sy]; cases cross <;> first | exact l.ss | exact l.st
      · exact .var _

private theorem fixes (b) (t : Term sig) (ht : ∀ v, t.Occurs v → v ≠ l.x ∧ v ≠ l.y) :
    (l.answer b).apply t = t := by
  refine (Term.subst_eq_of_agree _ Term.var _ ?_).trans t.subst_id
  intro v hv
  simp [answer, (ht v hv).1, (ht v hv).2]

private theorem branch_solves (b) (σ : Substitution sig) :
    (l.query.branch b).Solves σ ↔ EquivB (σ.image l.x) (σ.apply (l.first b)) ∧
      EquivB (σ.image l.y) (σ.apply (l.second b)) := by
  cases b <;> simp [Query.branch, query, Problem.Solves, first, second, Substitution.apply, Term.subst]

theorem complete_branch (b) : CompleteSet (l.query.branch b) [l.answer b] := by
  constructor
  · intro σ hm; obtain rfl := List.mem_singleton.mp hm
    apply (l.branch_solves b _).mpr
    have hs := l.fixes b l.s (fun v h => l.independent v (.inl h))
    have ht := l.fixes b l.t (fun v h => l.independent v (.inr h))
    cases b <;> simp_all [answer,first,second,l.distinct.symm,EquivB.refl]
  · intro ρ hρ
    obtain ⟨hx,hy⟩ := (l.branch_solves b ρ).mp hρ
    refine ⟨_, List.mem_singleton_self _, ρ, fun w _ => ?_⟩
    change EquivB (ρ.image w) (ρ.apply ((l.answer b).image w))
    by_cases h : w = l.x
    · subst w; simpa [answer] using hx
    · by_cases k : w = l.y
      · subst w; simpa [answer, h] using hy
      · simp only [answer, ite_eq_right h, ite_eq_right k]
        exact .refl _

/-- The reference fresh-range decoder returns complete, scope-safe answers
without assumptions on a continuation solver. -/
def solve (run : UInt64 → UInt64 → UInt64 → UInt64 → UInt8 → UInt8)
    (key : Head sig → UInt64) (priority : UInt8) (avoid : List Variable) : List (Substitution sig) :=
  let bs := orientations (run 0 0 (headCode key l.s) (headCode key l.t) priority)
  bs.map fun b => FreshAnswer.freshen l.query.problem avoid (l.answer b)

theorem correct {run} (hc : Correct run) (key : Head sig → UInt64) (priority : UInt8)
    (hp : Priority l.query priority) (avoid : List Variable) :
    (Outcome.complete (l.solve run key priority avoid)).CorrectIn l.query.problem avoid := by
  let bs := orientations (run 0 0 (headCode key l.s) (headCode key l.t) priority)
  have main (σ : Substitution sig) : l.query.problem.Solves σ ↔ ∃ b ∈ bs, (l.query.branch b).Solves σ :=
    run_solves hc l.query key priority hp σ
  have complete : CompleteSet l.query.problem (bs.map l.answer) := by
    constructor
    · intro σ hm
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
      exact (main _).mpr ⟨b,hb,(l.complete_branch b).sound _ (List.mem_singleton_self _)⟩
    · intro ρ hρ
      obtain ⟨b,hb,hs⟩ := (main _).mp hρ
      obtain ⟨σ,hσ,δ,hi⟩ := (l.complete_branch b).covers ρ hs
      obtain rfl := List.mem_singleton.mp hσ
      exact ⟨_,List.mem_map.mpr ⟨b,hb,rfl⟩,δ,fun v hv => hi v ((l.query.occurs_iff b v).mpr hv)⟩
  simpa [solve, bs, List.map_map, Function.comp_def] using
    FreshAnswer.freshen_correct ⟨l.query.problem, avoid⟩ _ complete

end Linear
end Tamarin.Commutative
