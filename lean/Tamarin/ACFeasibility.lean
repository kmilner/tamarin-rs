import TamarinRuntime.ACFeasibility
import Tamarin.ACRationalProjection
import Tamarin.GraphMatrixRefinement

namespace Tamarin.ACFeasibility
open ACBasis Homogeneous

abbrev Kernel := UInt64 → UInt64 → UInt64 → Array UInt64 → Array (Array UInt64) → Array UInt64 → UInt8

def Feasible {n} (rs : List (Row n)) : Prop := ∃ x, SystemHolds rs x ∧ ∀ i, 0 < x i

def Verdict (tag : UInt8) (satisfiable : Prop) : Prop :=
  (tag = 1 ∧ ¬ satisfiable) ∨ (tag = 2 ∧ satisfiable)

def TailWithin {n} : List (Row n) → Prop
  | [] => True
  | _ :: rs => Within rs

def ConeTailWithin {n} : List (Row n) → Prop
  | [] => True
  | _ :: rs => RationalProjection.Within rs

/-- Accepted inputs have a valid graph and every definitive verdict decides
strict positive feasibility. Either input-only resource domain suffices for
mandatory completion. -/
structure Correct (kernel : Kernel) : Prop where
  valid : ∀ n sym s ds ns es, let tag := kernel n sym s ds ns es
    tag ≠ 0 → ∃ m rs, GraphMatrix.Represents n sym s ds ns es m ∧
      readRows n.toNat m.toList = some rs ∧ Verdict tag (Feasible rs)
  completes : ∀ n sym s ds ns es m rs, GraphMatrix.Represents n sym s ds ns es m →
    readRows n.toNat m.toList = some rs → TailWithin rs → kernel n sym s ds ns es ≠ 0
  coneCompletes : ∀ n sym s ds ns es m rs, GraphMatrix.Represents n sym s ds ns es m →
    readRows n.toNat m.toList = some rs → ConeTailWithin rs → kernel n sym s ds ns es ≠ 0

private theorem rowFeasible_iff {n} (r : Row n) (rs : List (Row n)) (gs : List (Vec n))
    (basis : Cone.ScaleCorrect rs gs) : rowFeasible r gs = true ↔ Feasible (r :: rs) := by
  rw [Feasible,Cone.last_row_iff r rs gs basis]
  simp [rowFeasible,List.all_eq_true,List.any_eq_true,PositiveWitness.enabled,
    List.get_eq_getElem]
  have getEq : (fun j : Fin gs.length => gs[j.val]) = gs.get := by
    funext j; simp [List.get_eq_getElem]
  rw [getEq]
  exact forall_congr' fun _ => exists_congr fun _ => and_comm

private theorem rows_correct {n} (rs : List (Row n)) :
    (∀ b, feasibleRows rs = some b → (b = true ↔ Feasible rs)) ∧
    ((TailWithin rs ∨ ConeTailWithin rs) → (feasibleRows rs).isSome) := by
  cases rs with
  | nil =>
    have feasible : Feasible (n := n) [] := ⟨fun _ => 1,by simp [SystemHolds],by simp⟩
    simp [feasibleRows,feasible]
  | cons r rs =>
    constructor
    · intro b run
      obtain ⟨gs,hg,eq⟩ := Option.bind_eq_some_iff.mp run
      obtain rfl := Option.some.inj eq
      apply rowFeasible_iff
      cases cone : RationalProjection.basis rs with
      | some rays =>
        change (RationalProjection.basis rs <|> boundedBasis rs) = some gs at hg
        simp [cone] at hg
        exact hg ▸ RationalProjection.basis_correct rs rays cone
      | none =>
        change (RationalProjection.basis rs <|> boundedBasis rs) = some gs at hg
        simp [cone] at hg
        rw [(bounded_spec _).1 gs hg]
        exact Cone.of_exact _ _ (generate_correct _)
    · intro domain
      cases cone : RationalProjection.basis rs with
      | some gs => simp [feasibleRows,cone]
      | none =>
        rcases domain with old|new
        · simp [feasibleRows,cone,(bounded_spec rs).2 old]
        · obtain ⟨_,yes,_⟩ := RationalProjection.basis_within rs new
          simp [cone] at yes

private theorem total {n sym s ds ns es m rs} (mat : GraphMatrix.Represents n sym s ds ns es m)
    (read : readRows n.toNat m.toList = some rs) (domain : TailWithin rs ∨ ConeTailWithin rs) :
    run n sym s ds ns es ≠ 0 := by
  have g := (GraphMatrix.build_correct ..).mpr mat
  obtain ⟨b,h⟩ := Option.isSome_iff_exists.mp ((rows_correct rs).2 domain)
  cases b <;> simp [run,g,read,h]

theorem run_correct : Correct run where
  valid := by
    intro n sym s ds ns es
    dsimp only
    intro nonzero
    cases g : GraphMatrix.build n sym s ds ns es with
    | none => simp [run,g] at nonzero
    | some m =>
      cases h : readRows n.toNat m.toList with
      | none => simp [run,g,h] at nonzero
      | some rs =>
        refine ⟨m,rs,(GraphMatrix.build_correct ..).mp g,h,?_⟩
        cases b : feasibleRows rs with
        | none => simp [run,g,h,b] at nonzero
        | some ans =>
          have iff := (rows_correct rs).1 ans b
          cases ans <;> simp_all [run,Verdict]
  completes := fun _ _ _ _ _ _ _ _ mat read ok => total mat read (.inl ok)
  coneCompletes := fun _ _ _ _ _ _ _ _ mat read ok => total mat read (.inr ok)

/-- For the original sorted term problem the verdict means that a unifier
exists (or that no unifier exists), independent of the number of unifiers. -/
theorem Correct.term {kernel} (ok : Correct kernel) {sig : Signature}
    (c : WholeProblem.Codec sig) (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64)
    (fr : ACSystem.Frame f rows n.toNat) (columns : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {ds ns roots raw} (decoded : Whole.Wire.decodeProblem ds ns roots = some raw)
    (layout : WholeProblem.RowLayout (WholeProblem.encodeRows c (ACSystem.problem f rows)) raw)
    (used : kernel n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns roots ≠ 0) :
    Verdict (kernel n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns roots)
      (ACSystem.problem f rows).Satisfiable := by
  obtain ⟨m,rs,rep,read,verdict⟩ := ok.valid _ _ _ _ _ _ used
  obtain ⟨mat,counts⟩ := GraphMatrixRefinement.matrix_of_build GraphMatrix.build_correct c f rows n fr columns
    decoded layout ((GraphMatrix.build_correct ..).mpr rep)
  rw [mat,read_matrixWords _ _ fr.live counts] at read
  obtain rfl := Option.some.inj read
  have live v : v ∈ ACSystem.variables rows ↔ ∃ i, fr.names i = v :=
    ⟨fr.live v,fun ⟨i,e⟩ => e ▸ fr.used i⟩
  have sorts v (hv : v ∈ ACSystem.variables rows) : Subsort (sig.acSort f) v.sort := by
    obtain ⟨i,rfl⟩ := fr.live v hv
    rw [fr.sorts]; exact .refl _
  have basis := generate_correct (rows.map (encode fr.names))
  have eq := (satisfiable_iff_basis_support f fr.names fr.injective rows live sorts _ basis).trans
    (coversCoordinates_iff _ _ basis)
  rwa [Feasible,←eq] at verdict

end Tamarin.ACFeasibility
