import TamarinRuntime.ACSortedBagPacket
import Tamarin.ACMatchSingletonSorts
import Tamarin.ACSortedBagSearch

namespace Tamarin.Matching.ACSortedBagPacket
open ACMatchPacket ACSortedBagSearch

def encodeLimits (limits : Limits) : Packet :=
  (limits.map fun (key,allowed) => (key :: allowed).toArray).toArray

theorem decode_encode_limits (ls : Limits) : decodeLimits (encodeLimits ls).toList = some ls := by
  simp only [encodeLimits,List.toList_toArray]
  induction ls with
  | nil => rfl
  | cons l ls ih => cases l; simp [decodeLimits,ih]

theorem empty_entry {xs : List (Array UInt64)} (h : #[] ∈ xs) : decodeLimits xs = none := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with eq | tail
    · subst x; rfl
    · cases e : x.toList <;> simp [decodeLimits,e,ih tail]

structure Correct (run : Packet → Packet → UInt8) : Prop where
  malformed : ∀ p ls, (decode p.toList = none ∨ decodeLimits ls.toList = none) → run p ls = 0
  valid : ∀ p ls rs limits, decode p.toList = some rs → decodeLimits ls.toList = some limits →
    run p ls = 0 ∨ (run p ls = 1 ∧ ¬ Feasible rs limits) ∨ (run p ls = 2 ∧ Feasible rs limits)
  required : ∀ p ls rs limits, decode p.toList = some rs → decodeLimits ls.toList = some limits →
    ACBagSearch.Within rs → run p ls ≠ 0

theorem runWith_correct (solve : List Row → Limits → Option Bool)
    (valid : ∀ rs ls b, solve rs ls = some b → (b = true ↔ Feasible rs ls))
    (required : ∀ rs ls, ACBagSearch.Within rs → (solve rs ls).isSome) : Correct (runWith solve) where
  malformed p ls h := by
    rcases h with a | b
    · simp [runWith,a]
    · cases a : decode p.toList <;> simp [runWith,a,b]
  valid p ls rs limits h read := by
    cases e : solve rs limits with
    | none => simp [runWith,h,read,e]
    | some b => have eq := valid rs limits b e; cases b <;> simp_all [runWith]
  required p ls rs limits h read covered := by
    obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (required rs limits covered)
    cases b <;> simp [runWith,h,read,hb]

private theorem feasible_perm {rs ss : List Row} (perm : rs.Perm ss) (limits : Limits) :
    Feasible rs limits ↔ Feasible ss limits := by
  simp only [Feasible,ACBags.Solution,perm.mem_iff]

/-- Both verdicts refer directly to the original conjunction in its active
signature. The subject terms can include names also bound by the patterns. -/
theorem Correct.term {run} (ok : Correct run) {p ls rs limits}
    (read : decode p.toList = some rs) (rules : decodeLimits ls.toList = some limits)
    {sig : Signature} [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → Row} {name term fixed} (layout : ACBags.Presentation f problem row name term fixed)
    (order : rs.Perm (problem.map row)) (sorts : ACBags.SortLists f (problem.map row) name term limits)
    (done : run p ls ≠ 0) :
    (run p ls = 1 ∧ ¬∃ σ, Matches problem σ) ∨ (run p ls = 2 ∧ ∃ σ, Matches problem σ) := by
  have truth : Feasible rs limits ↔ ∃ σ, Matches problem σ := by
    rw [feasible_perm order,← layout.sorted_exact]
    exact ⟨fun ⟨im,sol,h⟩ => ⟨im,sol,(layout.fits_iff sol sorts).2 h⟩,
      fun ⟨im,sol,h⟩ => ⟨im,sol,(layout.fits_iff sol sorts).1 h⟩⟩
  rw [← truth]
  exact (ok.valid _ _ _ _ read rules).resolve_left done

end Tamarin.Matching.ACSortedBagPacket
