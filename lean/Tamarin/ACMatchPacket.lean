import TamarinRuntime.ACMatchPacket
import Tamarin.ACMatchBagsRefinement

namespace Tamarin.Matching.ACMatchPacket

/-- Row and occurrence order may be chosen locally by the reader. IDs
from different rows share the two request-local alphabets. -/
def encode (rows : List Row) : Packet :=
  (rows.flatMap fun (pat,subj) => [pat.toArray,subj.toArray]).toArray

theorem decode_encode (rows : List Row) : decode (encode rows).toList = some rows := by
  simp only [encode,List.toList_toArray]
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [decode,ih]

/-- A complete negative or positive tag is a statement about every row of
the original problem. Resource exhaustion has its own tag. -/
structure Correct (floor : List Row → Prop) (run : Packet → UInt8) : Prop where
  malformed : ∀ p, decode p.toList = none → run p = 0
  valid : ∀ p rs, decode p.toList = some rs →
    run p = 0 ∨ (run p = 1 ∧ ¬ACBags.Feasible rs) ∨ (run p = 2 ∧ ACBags.Feasible rs)
  required : ∀ p rs, decode p.toList = some rs → floor rs → run p ≠ 0

theorem runWith_correct (floor : List Row → Prop) (solve : List Row → Option Bool)
    (valid : ∀ rs b, solve rs = some b → (b = true ↔ ACBags.Feasible rs))
    (required : ∀ rs, floor rs → (solve rs).isSome) : Correct floor (runWith solve) where
  malformed p h := by simp [runWith,h]
  valid p rs h := by
    cases r : solve rs with
    | none => simp [runWith,h,r]
    | some b => have eq := valid rs b r; cases b <;> simp_all [runWith]
  required p rs h ok := by
    obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (required rs ok)
    cases b <;> simp [runWith,h,hb]

/-- A future implementation can replace the numeric search entirely. Its
packet proof implies the verdict on the original equations and frozen
subjects, with no enumeration or chosen-substitution premise. -/
theorem Correct.term {floor run} (ok : Correct floor run)
    {sig : Signature} [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → Row} {name term fixed} (layout : ACBags.Layout f problem row name term fixed)
    (packet : Packet) {rs} (read : decode packet.toList = some rs) (order : rs.Perm (problem.map row))
    (done : run packet ≠ 0) :
    (run packet = 1 ∧ ¬∃ σ, Matches problem σ) ∨ (run packet = 2 ∧ ∃ σ, Matches problem σ) := by
  rw [← layout.exact,← ACBags.feasible_perm order]
  exact (ok.valid _ _ read).resolve_left done

theorem Correct.term_required {floor run} (ok : Correct floor run)
    {sig : Signature} [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → Row} {name term fixed} (layout : ACBags.Layout f problem row name term fixed)
    (packet : Packet) {rs} (read : decode packet.toList = some rs) (order : rs.Perm (problem.map row))
    (covered : floor rs) :
    (run packet = 1 ∧ ¬∃ σ, Matches problem σ) ∨ (run packet = 2 ∧ ∃ σ, Matches problem σ) :=
  ok.term layout packet read order (ok.required _ _ read covered)

end Tamarin.Matching.ACMatchPacket
