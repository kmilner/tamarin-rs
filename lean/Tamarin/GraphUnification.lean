import TamarinRuntime.GraphUnification
import Tamarin.ACPrincipalRay
import Tamarin.ACRayPacket
import Tamarin.GraphMatrixRefinement
import Tamarin.FactoredAC

namespace Tamarin.GraphUnification
open Homogeneous FactoredAC

/-- At least one equation has different multiplicities on its two sides. -/
inductive Nontrivial : List (Array UInt64) → Prop where
  | here {a b tail} : a ≠ b → Nontrivial (a :: b :: tail)
  | later {a b tail} : Nontrivial tail → Nontrivial (a :: b :: tail)

theorem hasConstraint_iff : ∀ rows, hasConstraint rows = true ↔ Nontrivial rows
  | [] | [_] => ⟨by intro h; contradiction, by intro h; cases h⟩
  | a :: b :: tail => by
    simp only [hasConstraint, Bool.or_eq_true, bne_iff_ne, hasConstraint_iff tail]
    exact ⟨fun h => h.elim Nontrivial.here Nontrivial.later,
      fun h => by cases h with | here h => exact Or.inl h | later h => exact Or.inr h⟩

def Required (width : UInt64) (m : Matrix) : Prop :=
  Homogeneous.Admitted width m ∨ RayPacket.Admitted @ACBasis.PrincipalRay.Within width m

abbrev RepresentsMatrix := GraphMatrix.RepresentsUpTo RayPacket.maxWidth

/-- Independent wire admission rules out both accepting malformed graph requests and
always deferring the matrix fragment. Within the fragment, answers may be reordered. -/
structure WireCorrect (run : Kernel) : Prop where
  valid : ∀ n sym s ds ns es out, run n sym s ds ns es = some out →
    ∃ m, RepresentsMatrix n sym s ds ns es m ∧ Nontrivial m.toList
  completes : ∀ n sym s ds ns es m, RepresentsMatrix n sym s ds ns es m →
    Nontrivial m.toList → Required n m → (run n sym s ds ns es).isSome

private theorem ran_with {build solve n sym s ds ns es out}
    (h : runWith build solve n sym s ds ns es = some out) :
    ∃ m, build n sym s ds ns es = some m ∧ Nontrivial m.toList ∧ solve n m = some out := by
  cases hm : build n sym s ds ns es with
  | none => simp [runWith, hm] at h
  | some m =>
    cases hc : hasConstraint m.toList with
    | false => simp [runWith, hm, hc, guard, failure] at h
    | true => exact ⟨m, rfl, (hasConstraint_iff _).mp hc, by simpa [runWith, hm, hc, guard] using h⟩

/-- An optimizer can implement the graph call directly. The semantic obligation mentions
only the input graph, its column identities and the returned slots. No count matrix is
supplied by its caller. Taking the identity factor specializes this to unfactored queries. -/
structure Correct (run : Kernel) : Prop where
  wire : WireCorrect run
  semantic : ∀ {sig : Signature} (r : Request sig) (θ : Substitution sig)
    (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64) (fr : ACSystem.Frame f rows n.toNat),
    FactoredUnification.Factoring r.problem (ACSystem.problem f rows) θ →
    ∀ (c : WholeProblem.Codec sig) ds ns roots raw,
    Whole.Wire.decodeProblem ds ns roots = some raw →
    CheckedFactoring.Rows c (ACSystem.problem f rows) raw →
    (∀ i, c.vars.put (fr.names i) = i.val.toUInt64) →
    ∀ out, run n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns roots = some out →
    ∀ w : UInt64 → Variable,
    (∀ i ∈ slots out, ∀ j ∈ slots out, w i = w j → i = j) →
    (∀ j ∈ slots out, (w j).sort = sig.acSort f) →
    (∀ j ∈ slots out, w j ∉ ACSystem.variables rows ++ FactoredAnswer.liveKeys r.problem θ) →
    Result r θ fr w out

theorem runWith_correct {build solve} (counts : GraphMatrix.CorrectUpTo RayPacket.maxWidth build)
    (solver : Homogeneous.Correct solve)
    (principal : ∀ n m, RayPacket.Admitted @ACBasis.PrincipalRay.Within n m → (solve n m).isSome) :
    Correct (runWith build solve) where
  wire.valid := by
    intro n sym s ds ns es out h
    obtain ⟨m, hm, active, _⟩ := ran_with h
    exact ⟨m, (counts ..).mp hm, active⟩
  wire.completes := by
    intro n sym s ds ns es m rep active admitted
    have done := admitted.elim (solver.completes n m) (principal n m)
    simpa [runWith, (counts ..).mpr rep, (hasConstraint_iff _).mpr active, guard] using done
  semantic := by
    intro sig r θ f rows n fr fact c ds ns roots raw decoded represented columns out ran w inj typed fresh
    obtain ⟨m, hm, _, solved⟩ := ran_with ran
    obtain ⟨matrix, fits⟩ := GraphMatrixRefinement.matrix_of_build counts c f rows n fr columns
      decoded represented.layout hm
    exact of_factoring_slots solver r f rows n fr θ fact m matrix fits out solved w inj typed fresh

theorem run_correct : Correct run := runWith_correct (GraphMatrix.buildUpTo_correct _)
  (RayPacket.correct ACBasis.PrincipalRay.run_sound)
  (RayPacket.completes ACBasis.PrincipalRay.run_sound ACBasis.PrincipalRay.run_complete)

/-- For an unfactored query the returned packet denotes precisely all sorted solutions.
A single instantiation explains every variable of a solution on the chosen arm. -/
theorem Correct.solves_iff {run} (h : Correct run) {sig : Signature}
    (c : WholeProblem.Codec sig) (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64)
    (fr : ACSystem.Frame f rows n.toNat) (cols : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {ds ns es raw} (dec : Whole.Wire.decodeProblem ds ns es = some raw)
    (rep : CheckedFactoring.Rows c (ACSystem.problem f rows) raw) {out}
    (ran : run n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns es = some out)
    (w : UInt64 → Variable) (inj : ∀ i ∈ slots out, ∀ j ∈ slots out, w i = w j → i = j)
    (sorted : ∀ j ∈ slots out, (w j).sort = sig.acSort f)
    (fresh : ∀ j ∈ slots out, w j ∉ ACSystem.variables rows) :
    ∃ pairs : List (Branch sig), out = (pairs.map Prod.fst).toArray ∧
      (∀ b ∈ pairs, Homogeneous.Represents fr w b.1 b.2 ∧ DomainRestricted (ACSystem.problem f rows) b.2) ∧
      ∀ ρ, (ACSystem.problem f rows).Solves ρ ↔
        ∃ b ∈ pairs, Substitution.InstanceOn (ACSystem.problem f rows).Occurs ρ b.2 := by
  let p := ACSystem.problem f rows
  have fact := (FactoredUnification.Trace.done p Substitution.identity).factoring
  have safe (j) (hj : j ∈ slots out) : w j ∉ ACSystem.variables rows ++ FactoredAnswer.liveKeys p .identity := by
    rw [List.mem_append, not_or]
    refine ⟨fresh j hj, fun hm => ?_⟩
    obtain ⟨v, hv, same⟩ := FactoredAnswer.mem_liveKeys.mp hm
    change w j = v at same
    exact fresh j hj (same ▸ (ACSystem.occurs_iff_mem f rows v).mp hv)
  obtain ⟨pairs, packet, arms, complete, _⟩ := h.semantic ⟨p, []⟩ .identity f rows n fr fact c
    _ _ _ raw dec rep cols _ ran w inj sorted safe
  refine ⟨pairs, packet, arms, fun ρ => ?_⟩
  rw [complete.solves_iff ρ]
  constructor
  · rintro ⟨_, hm, hi⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    exact ⟨b, hb, hi⟩
  · rintro ⟨b, hb, hi⟩
    exact ⟨_, List.mem_map_of_mem hb, hi⟩

/-- A faithfully encoded admitted system with unequal multiplicities must reach an
answer. The matrix in the admission bound is defined entirely by the mathematical rows. -/
theorem Correct.completes_on {run} (h : Correct run) {sig : Signature}
    (c : WholeProblem.Codec sig) (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64)
    (fr : ACSystem.Frame f rows n.toNat) (cols : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {ds ns es raw} (decoded : Whole.Wire.decodeProblem ds ns es = some raw)
    (layout : WholeProblem.RowLayout (WholeProblem.encodeRows c (ACSystem.problem f rows)) raw)
    (declared : GraphMatrix.Declared ds (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)))
    (roots : es.size ≤ 128) (small : GraphMatrixRefinement.Fits rows)
    (active : Nontrivial (matrixWords fr.names rows))
    (admitted : Required n (matrixWords fr.names rows).toArray) :
    (run n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns es).isSome := by
  have bounds : 0 < n ∧ n ≤ RayPacket.maxWidth := admitted.elim
    (fun h => ⟨h.1,UInt64.le_trans h.2.1 (by decide)⟩) (fun h => ⟨h.1,h.2.1⟩)
  have counts := GraphMatrix.buildUpTo_correct RayPacket.maxWidth
  have hm := GraphMatrixRefinement.build_of_matrix counts c f rows n fr cols
    decoded layout declared bounds.1 bounds.2 roots small
  exact h.wire.completes _ _ _ _ _ _ _ ((counts ..).mp hm)
    (by simpa only [List.toList_toArray] using active) admitted

/-- The actual factor-checker verdict supplies the semantic factoring premise of the graph solver. -/
def Checked (check : FactorCheck.Kernel) (solve : Kernel) : Prop :=
  ∀ {s : Signature} (r : Request s) (θ : Substitution s) (f : s.ACSym) (rows : List ACSystem.Row)
    (g : Input s), g.Represents r.problem θ (ACSystem.problem f rows) →
    check g.decls g.nodes g.original g.bindings g.residual = true →
    ∀ (n : UInt64) (fr : ACSystem.Frame f rows n.toNat),
    (∀ i, g.codec.vars.put (fr.names i) = i.val.toUInt64) →
    ∀ out, solve n (g.codec.acs.put f) (WholeProblem.sortWord (s.acSort f))
      g.decls g.nodes g.residual = some out →
    ∀ w : UInt64 → Variable,
    (∀ i ∈ slots out, ∀ j ∈ slots out, w i = w j → i = j) →
    (∀ j ∈ slots out, (w j).sort = s.acSort f) →
    (∀ j ∈ slots out, w j ∉ ACSystem.variables rows ++ FactoredAnswer.liveKeys r.problem θ) →
    Result r θ fr w out

theorem checked_correct {check solve} (validator : FactorCheck.Correct check) (solver : Correct solve) :
    Checked check solve := by
  intro sig r θ f rows g layout accepted n fr columns out ran w inj typed fresh
  obtain ⟨raw, dec, rs, fact⟩ := g.checked_factor validator layout accepted
  exact solver.semantic r θ f rows n fr fact g.codec _ _ _ raw dec rs columns out ran w inj typed fresh

end Tamarin.GraphUnification
