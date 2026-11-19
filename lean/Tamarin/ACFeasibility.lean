import TamarinRuntime.ACFeasibility
import Tamarin.ACTwoRowFeasibility
import Tamarin.ACColumnQuotient
import Tamarin.ACColumnSupport
import Tamarin.ACAdjustmentCoverage
import Tamarin.ACRowReductionCoverage
import Tamarin.ACReducedFeasibility
import Tamarin.ACRationalProjection
import Tamarin.GraphMatrixRefinement

namespace Tamarin.ACFeasibility
open ACBasis Homogeneous

abbrev Kernel := UInt64 → UInt64 → UInt64 → Array UInt64 → Array (Array UInt64) → Array UInt64 → UInt8

def Verdict (tag : UInt8) (satisfiable : Prop) : Prop :=
  (tag = 1 ∧ ¬ satisfiable) ∨ (tag = 2 ∧ satisfiable)

def TailWithin {n} : List (Row n) → Prop
  | [] => True
  | _ :: rs => Within rs

def ConeTailWithin {n} : List (Row n) → Prop
  | [] => True
  | _ :: rs => RationalProjection.Within rs

/-- Any of these input domains requires a definitive answer. An
implementation may decide additional systems using any sound certificate. -/
inductive BaseRequired {n} (rs : List (Row n)) : Prop where
  | direct : DirectWithin rs → BaseRequired rs
  | basis : n ≤ 32 → (TailWithin rs ∨ ConeTailWithin rs) → BaseRequired rs
  | reduced : RowReduction.Within rs → BaseRequired rs
  | triangular : Adjustment.Within rs → BaseRequired rs
  | twoRows : rs.length ≤ 2 → BaseRequired rs

/-- Each established domain also applies to the canonical quotient of an
input containing repeated columns, independently of its original width. -/
inductive Required {n} (rs : List (Row n)) : Prop where
  | original : BaseRequired rs → Required rs
  | quotient : ColumnQuotient.Within (@BaseRequired) rs → Required rs

namespace Required
variable {n : Nat} {rs : List (Row n)}

theorem direct (h : DirectWithin rs) : Required rs := .original (.direct h)
theorem basis (width : n ≤ 32) (h : TailWithin rs ∨ ConeTailWithin rs) : Required rs :=
  .original (.basis width h)
theorem reduced (h : RowReduction.Within rs) : Required rs := .original (.reduced h)
theorem triangular (h : Adjustment.Within rs) : Required rs := .original (.triangular h)
theorem twoRows (few : rs.length ≤ 2) : Required rs := .original (.twoRows few)

end Required

structure Correct (kernel : Kernel) : Prop where
  valid : ∀ n sym s ds ns es, let tag := kernel n sym s ds ns es
    tag ≠ 0 → ∃ m rs, GraphMatrix.RepresentsUpTo 4096 n sym s ds ns es m ∧
      readRows n.toNat m.toList = some rs ∧ Verdict tag (Feasible rs)
  required : ∀ n sym s ds ns es m rs, GraphMatrix.RepresentsUpTo 4096 n sym s ds ns es m →
    readRows n.toNat m.toList = some rs → Required rs → kernel n sym s ds ns es ≠ 0

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

private theorem widen {w sym s ds ns es m} (rep : GraphMatrix.Represents w sym s ds ns es m) :
    GraphMatrix.RepresentsUpTo 4096 w sym s ds ns es m :=
  ⟨rep.1,UInt64.le_trans rep.2.1 (by decide),rep.2.2⟩

private theorem definitive {n sym s ds ns es m rs}
    (rep : GraphMatrix.RepresentsUpTo 4096 n sym s ds ns es m)
    (read : readRows n.toNat m.toList = some rs) (done : (checkRows rs).isSome) :
    run n sym s ds ns es ≠ 0 := by
  have g := (GraphMatrix.buildUpTo_correct graphWidth ..).mpr rep
  obtain ⟨b,h⟩ := Option.isSome_iff_exists.mp done
  cases b <;> simp [run,g,read,h]

theorem Correct.completes {kernel} (ok : Correct kernel) (n sym s ds ns es m rs)
    (rep : GraphMatrix.Represents n sym s ds ns es m)
    (read : readRows n.toNat m.toList = some rs) (within : TailWithin rs) : kernel n sym s ds ns es ≠ 0 :=
  ok.required _ _ _ _ _ _ _ _ (widen rep) read (.basis rep.2.1 (.inl within))

theorem Correct.coneCompletes {kernel} (ok : Correct kernel) (n sym s ds ns es m rs)
    (rep : GraphMatrix.Represents n sym s ds ns es m)
    (read : readRows n.toNat m.toList = some rs) (within : ConeTailWithin rs) : kernel n sym s ds ns es ≠ 0 :=
  ok.required _ _ _ _ _ _ _ _ (widen rep) read (.basis rep.2.1 (.inr within))

theorem Correct.directCompletes {kernel} (ok : Correct kernel) (n sym s ds ns es m rs)
    (rep : GraphMatrix.RepresentsUpTo 4096 n sym s ds ns es m)
    (read : readRows n.toNat m.toList = some rs) (within : DirectWithin rs) : kernel n sym s ds ns es ≠ 0 :=
  ok.required _ _ _ _ _ _ _ _ rep read (.direct within)

private def Decides (o : Option Bool) (p : Prop) := ∀ b, o = some b → (b = true ↔ p)

private theorem fallback {a b : Option Bool} {p : Prop} (ha : Decides a p) (hb : Decides b p) :
    Decides (a <|> b) p := by
  cases h : a with
  | none => simpa using hb
  | some value => simpa [h] using ha

private theorem initial_sound {n} (rs : List (Row n)) : Decides (initialRows rs) (Feasible rs) := by
  unfold initialRows
  split
  · rename_i p q
    intro b h
    cases Option.some.inj h
    exact TwoRow.decidePair_iff p q
  · exact direct_sound _

private theorem initial_direct {n} (rs : List (Row n)) (h : DirectWithin rs) : (initialRows rs).isSome := by
  unfold initialRows
  split
  · rfl
  · exact direct_complete _ h

private theorem initial_two {n} (rs : List (Row n)) (few : rs.length ≤ 2) : (initialRows rs).isSome := by
  match rs with
  | [] => exact initial_direct _ (.inl (by simp))
  | [_] => exact initial_direct _ (.inl (by simp))
  | [_,_] => rfl
  | _ :: _ :: _ :: _ => simp at few

private theorem fast_sound {n} (rs : List (Row n)) : Decides (fastRows rs) (Feasible rs) := by
  apply fallback (initial_sound rs)
  apply fallback _ (reducedFeasible_sound rs)
  by_cases small : n ≤ 32
  · simp only [small,↓reduceIte]
    exact (rows_correct rs).1
  · simp [small,Decides]

private theorem base_sound {n} (rs : List (Row n)) : Decides (baseRows rs) (Feasible rs) :=
  fallback (fast_sound rs) (fun _ h => ColumnSupport.run_correct rs 4096 h)

private theorem checkedRows {n} (rs : List (Row n)) : Decides (checkRows rs) (Feasible rs) :=
  fallback (fast_sound rs) (fallback (fun _ h => ColumnQuotient.run_sound (@baseRows) base_sound rs h)
    (fun _ h => ColumnSupport.run_correct rs 4096 h))

private theorem reduced_complete {n} (rs : List (Row n)) (within : RowReduction.Within rs) :
    (reducedFeasible rs).isSome := by
  obtain ⟨out,h,covered⟩ := RowReduction.echelon_complete rs within
  obtain ⟨b,yes⟩ := Option.isSome_iff_exists.mp (direct_complete out covered)
  simp [reducedFeasible,within.1,guard,h,yes]

private theorem base_complete {n} (rs : List (Row n)) (domain : BaseRequired rs) : (baseRows rs).isSome := by
  cases domain with
  | direct h =>
    obtain ⟨b,got⟩ := Option.isSome_iff_exists.mp (initial_direct rs h)
    simp [baseRows,fastRows,got]
  | basis small h =>
    obtain ⟨b,got⟩ := Option.isSome_iff_exists.mp ((rows_correct rs).2 h)
    cases d : initialRows rs <;> simp [baseRows,fastRows,d,small,got]
  | triangular h => simp [baseRows,fastRows,Adjustment.completes rs h]
  | twoRows few =>
    obtain ⟨b,got⟩ := Option.isSome_iff_exists.mp (initial_two rs few)
    simp [baseRows,fastRows,got]
  | reduced h =>
    obtain ⟨b,got⟩ := Option.isSome_iff_exists.mp (reduced_complete rs h)
    simp [baseRows,fastRows,got]

theorem run_correct : Correct run where
  valid := by
    intro n sym s ds ns es
    dsimp only
    intro nonzero
    cases g : GraphMatrix.buildUpTo graphWidth n sym s ds ns es with
    | none => simp [run,g] at nonzero
    | some m =>
      cases h : readRows n.toNat m.toList with
      | none => simp [run,g,h] at nonzero
      | some rs =>
        refine ⟨m,rs,(GraphMatrix.buildUpTo_correct graphWidth ..).mp g,h,?_⟩
        cases b : checkRows rs with
        | none => simp [run,g,h,b] at nonzero
        | some ans =>
          have iff := checkedRows rs ans b
          cases ans <;> simp_all [run,Verdict]
  required := by
    intro n sym s ds ns es m rs rep read domain
    apply definitive rep read
    cases domain with
    | original d =>
      obtain ⟨b,h⟩ := Option.isSome_iff_exists.mp (base_complete rs d)
      cases fast : fastRows rs <;> simp_all [baseRows,checkRows]
    | quotient d =>
      obtain ⟨b,h⟩ := Option.isSome_iff_exists.mp (ColumnQuotient.run_complete (@baseRows)
        (@BaseRequired) base_complete rs d)
      simp [checkRows,h]

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
  obtain ⟨mat,counts⟩ := GraphMatrixRefinement.matrix_of_build (GraphMatrix.buildUpTo_correct 4096) c f rows n fr columns
    decoded layout ((GraphMatrix.buildUpTo_correct 4096 ..).mpr rep)
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

/-- An admitted term problem receives the right verdict at its graph entry
point. The caller supplies column identity and graph layout; matrix
multiplicities, non-wrapping and the concrete decision follow from them. -/
theorem Correct.term_required {kernel} (ok : Correct kernel) {sig : Signature}
    (c : WholeProblem.Codec sig) (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64)
    (fr : ACSystem.Frame f rows n.toNat) (columns : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {ds ns roots raw} (decoded : Whole.Wire.decodeProblem ds ns roots = some raw)
    (layout : WholeProblem.RowLayout (WholeProblem.encodeRows c (ACSystem.problem f rows)) raw)
    (declared : GraphMatrix.Declared ds (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)))
    (width : 0 < n ∧ n ≤ 4096) (rootBound : roots.size ≤ 128) (fits : GraphMatrixRefinement.Fits rows)
    (domain : Required (rows.map (encode fr.names))) :
    Verdict (kernel n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns roots)
      (ACSystem.problem f rows).Satisfiable := by
  have graph := GraphMatrixRefinement.build_of_matrix (GraphMatrix.buildUpTo_correct 4096) c f rows n
    fr columns decoded layout declared width.1 width.2 rootBound fits
  obtain ⟨mat,counts⟩ := GraphMatrixRefinement.matrix_of_build (GraphMatrix.buildUpTo_correct 4096)
    c f rows n fr columns decoded layout graph
  have read := read_matrixWords fr.names rows fr.live counts
  rw [←mat] at read
  exact ok.term c f rows n fr columns decoded layout
    (ok.required _ _ _ _ _ _ _ _ ((GraphMatrix.buildUpTo_correct 4096 ..).mp graph) read domain)

/-- Every admitted homogeneous term conjunction with at most two equations
gets a verdict, at every graph width and without a coefficient-side bound. -/
theorem two_term_rows {sig : Signature} {f : sig.ACSym} {rows : List ACSystem.Row} {n : Nat}
    (fr : ACSystem.Frame f rows n) (few : rows.length ≤ 2) : Required (rows.map (encode fr.names)) :=
  Required.twoRows (by simpa using few)

end Tamarin.ACFeasibility
