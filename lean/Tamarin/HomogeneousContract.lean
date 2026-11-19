import Tamarin.ACBasisComplete
import Tamarin.ACDistributedBasisEnumeration
import Tamarin.ACCompactPlane
import Tamarin.ACPrimitiveRow
import Tamarin.ACGridBudget
import Tamarin.ACBalanceBound
import Tamarin.ACWeightedBudget
import Tamarin.ACUnitBalance
import Tamarin.ACNeutralBasis
import Tamarin.ACSparsePlane
import Tamarin.ACOutputBudget
import TamarinRuntime.Homogeneous

namespace Tamarin.Homogeneous
open ACBasis ACSystem
variable {sig : Signature}

/-- The budget counts assignments to free coordinates. A nonzero coefficient
determines the remaining coordinate uniquely, including when its value is zero. -/
def GridFits {n} (r : Row n) (budget : Nat) : Prop :=
  r.boxSize ≤ budget ∨ ∃ i, (0 < r.pos i ∨ 0 < r.neg i) ∧ r.boxSize ≤ budget * (r.limits i + 1)

private theorem fitsPlane_iff {n} (r : Row n) (b : Nat) : r.fitsPlane b ↔ GridFits r b := by
  simp [Row.fitsPlane, GridFits, List.any_eq_true]

/-- An implementation may use any enumeration order internally. The
mandatory envelope uses the fixed original box, cut off at the specified
coefficient magnitude. -/
private def refLimits {n} (r : Row n) (cap : Nat) : Vec n := fun i => min (r.limits i) cap

private def keptCoefficients {n} (r : Row n) (cap : Nat) :=
  r.generators.filter fun v => decide (∀ i, v i ≤ cap)

private theorem cappedFits_iff {n} (r : Row n) (cap budget : Nat) :
    r.cappedFits cap budget ↔ GridBudget r (refLimits r cap) budget := by
  let limits := r.cappedLimits cap
  let size := gridSize limits
  change (decide (size ≤ budget) || (List.finRange n).any fun i =>
    (decide (0 < r.pos i) || decide (0 < r.neg i)) && decide (size ≤ budget * (limits i + 1))) = true ↔
    size ≤ budget ∨ ∃ i, (0 < r.pos i ∨ 0 < r.neg i) ∧ size ≤ budget * (limits i + 1)
  simp [List.any_eq_true]

private theorem kept_mono {n} (p : Row n) {lo hi : Nat} (le : lo ≤ hi) :
    (keptCoefficients p lo).length ≤ (keptCoefficients p hi).length := by
  have subset (xs : List (Vec n)) :
      (xs.filter fun v => decide (∀ i, v i ≤ lo)).Sublist (xs.filter fun v => decide (∀ i, v i ≤ hi)) := by
    induction xs with
    | nil => exact .slnil
    | cons x xs ih =>
      by_cases l : ∀ i, x i ≤ lo
      · have h i := Nat.le_trans (l i) le
        simpa [l,h] using ih.cons_cons x
      · by_cases h : ∀ i, x i ≤ hi
        · simpa [l,h] using ih.cons x
        · simpa [l,h] using ih
  exact (subset _).length_le

private def DenseWithin {n} (p : Row n) : Prop :=
  (GridFits p 16384 ∧ p.generators.length ≤ 2048) ∨
    ∃ cap, p.primitive.cap ≤ cap ∧ GridBudget p (refLimits p cap) 16384 ∧
      (keptCoefficients p cap).length ≤ 2048

/-- The sparse grid fixes neutral coordinates to zero. Their singleton
generators enter the count separately, at their reference positions. -/
private def SparseWithin {n} (p : Row n) : Prop :=
  let cap := p.primitive.cap
  GridBudget p (p.sparseLimits cap) 16384 ∧
    ((keptCoefficients p cap).filter (SparsePlane.keep p)).length ≤ 2048

/-- Every nonzero entry in the cancelled row equals its greatest weight.
The floor is stated directly on the coefficient table. -/
def CommonWeight {n} (r : Row n) : Prop :=
  let largest := (1 :: (List.ofFn r.pos ++ List.ofFn r.neg)).max (by simp)
  ∀ i, (r.pos i = 0 ∨ r.pos i = largest) ∧ (r.neg i = 0 ∨ r.neg i = largest)

private theorem commonWeight_iff {n} (r : Row n) : CommonWeight r ↔ r.equalMagnitude = true := by
  simp [CommonWeight,Row.equalMagnitude,Row.cap]

def Within {n} : List (Row n) → Prop
  | [] => True
  | r :: rs => Within rs ∧
    let gs := generate rs
    let p := r.pullback gs.get
    gs.length ≤ 64 ∧ (((∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)) ∨ CommonWeight p ∨ WeightedComposition.Within p ∨ DenseWithin p ∨ SparseWithin p)

/-- Mandatory output bounds use the reference covering subsets and occurrence
counts. The first clause preserves the previous inexpensive admission check. -/
def OutputWithin {n} (gs : List (Vec n)) : Prop :=
  (gs.length ≤ 12 ∧ 2 ^ gs.length * (gs.map total).sum ≤ 65536) ∨
  (gs.length ≤ 64 ∧ ((selections gs).map (selectionWords gs)).sum ≤ 65536)

def AdmittedUpTo (limit width : UInt64) (m : Matrix) : Prop :=
  0 < width ∧ width ≤ limit ∧ m.size ≤ 128 ∧ ∃ rs, readRows width.toNat m.toList = some rs ∧
    (Within rs ∨ Distributed.RunWithin (@Within) rs 64) ∧ OutputWithin (generate rs)

abbrev Admitted := AdmittedUpTo 32

/-- Reference encoding of a flat matrix. A representable variable count
survives the word boundary without truncation. -/
def sideWords {n} (names : Fin n → Variable) (s : Side) : Array UInt64 :=
  Array.ofFn fun i => (s.vars.count (names i)).toUInt64

def matrixWords {n} (names : Fin n → Variable) (rows : List ACSystem.Row) : List (Array UInt64) :=
  rows.flatMap fun r => [sideWords names r.lhs, sideWords names r.rhs]

theorem read_matrixWords {n} (names : Fin n → Variable) (rows : List ACSystem.Row)
    (live : ∀ v ∈ variables rows, ∃ i, names i = v)
    (fits : ∀ r ∈ rows, ∀ s ∈ [r.lhs,r.rhs], ∀ i, s.vars.count (names i) < 2^64) :
    readRows n (matrixWords names rows) = some (rows.map (encode names)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have inTail (v) (h : v ∈ variables rs) : v ∈ variables (r::rs) := List.mem_append_right _ h
    have tail := ih (fun v hv => live v (inTail v hv))
      (fun row hr => fits row (List.mem_cons_of_mem _ hr))
    have side (s : Side) (hs : s ∈ [r.lhs,r.rhs]) :
        (sideWords names s).any (· > 0) = true ∧
        (fun i : Fin n => (sideWords names s)[i.val]!.toNat) = coefficients names s.vars := by
      have ht (i) := fits r (List.mem_cons_self ..) s hs i
      have get (i : Fin n) : (sideWords names s)[i.val]!.toNat = s.vars.count (names i) := by
        simp [sideWords, getElem!_pos, Nat.toUInt64, Nat.mod_eq_of_lt (ht i)]
      constructor
      · have mem : s.first ∈ variables (r::rs) := by
          apply List.mem_append_left
          rcases List.mem_cons.mp hs with h | h
          · subst s; exact List.mem_append_left _ (List.mem_cons_self ..)
          · obtain rfl := List.mem_singleton.mp h
            exact List.mem_append_right _ (List.mem_cons_self ..)
        obtain ⟨i,hi⟩ := live _ mem
        have pos : 0 < (sideWords names s)[i.val]!.toNat := by
          rw [get, hi]; apply List.count_pos_iff.mpr; exact List.mem_cons_self ..
        apply Array.any_eq_true.mpr
        refine ⟨i.val,by simp [sideWords],?_⟩
        simpa [UInt64.lt_iff_toNat_lt,sideWords] using pos
      · exact funext get
    obtain ⟨lp,lv⟩ := side r.lhs (by simp)
    obtain ⟨rp,rv⟩ := side r.rhs (by simp)
    change readRows n (sideWords names r.lhs :: sideWords names r.rhs :: matrixWords names rs) = _
    rw [readRows]
    simp only [lp,rp,lv,rv]
    simp [tail,encode,guard,show ∀ s, (sideWords names s).size = n by simp [sideWords]]

/-- The slot list for each coordinate must be the actual image of that
input variable in the corresponding substitution. All coordinates share w. -/
def Represents {f : sig.ACSym} {rows : List ACSystem.Row} {n}
    (fr : Frame f rows n) (w : UInt64 → Variable) (a : Arm) (σ : Substitution sig) : Prop :=
  a.size = n ∧ ∀ i : Fin n, ∃ x xs,
    (a[i.val]?.map (fun r => r.toList.map w)) = some (x :: xs) ∧
    σ.image (fr.names i) = (Side.mk x xs).term f

structure CorrectUpTo (limit : UInt64) (run : UInt64 → Matrix → Option Answers) : Prop where
  malformed : ∀ n m, readRows n.toNat m.toList = none → run n m = none
  completes : ∀ n m, AdmittedUpTo limit n m → (run n m).isSome
  semantic : ∀ {s : Signature} (f : s.ACSym) (rows : List ACSystem.Row) (avoid : List Variable)
    (n : UInt64) (fr : Frame f rows n.toNat) (m : Matrix)
    (_input : readRows n.toNat m.toList = some (rows.map (encode fr.names))) (out : Answers),
    run n m = some out →
    ∀ w : UInt64 → Variable, Function.Injective w → (∀ j, (w j).sort = s.acSort f) →
    (∀ j, w j ∉ variables rows ++ avoid) →
    ∃ pairs : List (Arm × Substitution s), out = (pairs.map Prod.fst).toArray ∧
      (∀ p ∈ pairs, Represents fr w p.1 p.2) ∧
      (Outcome.complete (pairs.map Prod.snd)).CorrectIn (problem f rows) avoid

abbrev Correct := CorrectUpTo 32

theorem AdmittedUpTo.mono {a b width : UInt64} {m : Matrix} (h : AdmittedUpTo a width m)
    (le : a ≤ b) : AdmittedUpTo b width m :=
  ⟨h.1,UInt64.le_trans h.2.1 le,h.2.2⟩

theorem CorrectUpTo.restrict {a b : UInt64} {run : UInt64 → Matrix → Option Answers}
    (ok : CorrectUpTo b run) (le : a ≤ b) : CorrectUpTo a run where
  malformed := ok.malformed
  completes n m domain := ok.completes n m (domain.mono le)
  semantic := ok.semantic

private theorem stored_get {n} (f : Vec n) : coordinates (Vector.ofFn f) = f := by
  funext i
  simp [coordinates]

private theorem minimize_compact {k n} (r : Row k) (g : Fin k → Vec n)
    (live : ∀ j, ∃ i, 0 < g j i) :
    minimize (lift g (r.cappedGenerators r.primitive.cap)) = minimize (lift g r.generators) := by
  rw [r.cappedGenerators_eq]
  apply minimize_lift_filter _ _ _ live
  intro c hc skip
  have ⟨limit,holds,nz⟩ := (r.mem_generators c).mp hc
  obtain ⟨d,hprim,dnz,le,size⟩ := BalanceBound.dominated_coordinate_cap r.primitive c
    ((r.primitive_holds c).mpr holds) nz
  have hd := (r.primitive_holds d).mp hprim
  refine ⟨d,(r.mem_generators _).mpr ⟨fun i => Nat.le_trans (le i) (limit i),hd,dnz⟩,
    decide_eq_true size,dnz,le,?_⟩
  rintro rfl
  simp [size] at skip

private theorem sparse_checks {n} (p : Row n) (area : DenseWithin p ∨ SparseWithin p) :
    p.sparseFits p.primitive.cap 16384 = true ∧ (p.sparseGenerators p.primitive.cap).length ≤ 2048 := by
  rcases area with dense | ⟨grid,count⟩
  · have checks : p.cappedFits p.primitive.cap 16384 = true ∧ (p.cappedGenerators p.primitive.cap).length ≤ 2048 := by
      rw [cappedFits_iff,p.cappedGenerators_eq]
      rcases dense with ⟨grid,count⟩|⟨lim,le,grid,count⟩
      · have old : GridBudget p p.limits 16384 := grid
        exact ⟨old.shrink (fun i => Nat.min_le_left ..),Nat.le_trans (List.length_filter_le ..) count⟩
      · exact ⟨grid.shrink (fun i => by dsimp [refLimits]; omega),Nat.le_trans (kept_mono p le) count⟩
    exact ⟨SparsePlane.fits_of_capped p checks.1,Nat.le_trans (SparsePlane.length_le ..) checks.2⟩
  · refine ⟨(SparsePlane.fits_iff ..).mpr grid,?_⟩
    rwa [SparsePlane.filtered,p.cappedGenerators_eq]

private theorem unitIntersection_eq {n} (gs : List (Vec n)) (p : Row gs.length)
    (uniform : p.equalMagnitude = true) (live : ∀ j, ∃ i, 0 < gs.get j i) :
    unitIntersection gs p = minimize (lift gs.get p.generators) := by
  let basis : Vector (Vec n) gs.length := ⟨gs.toArray, by simp⟩
  have get : (fun i : Fin gs.length => basis[i]) = gs.get := by funext i; simp [basis]
  change (if UnitBalance.separates basis then _ else _) = _
  simp [List.map_map,Function.comp_def,stored_get]
  by_cases apart : UnitBalance.separates basis = true
  · rw [ite_eq_left apart,←UnitBalance.minimize_unitLift p basis apart,UnitBalance.unitLift_eq,get]
    exact UnitBalance.minimize_lift p uniform _ live
  · rw [ite_eq_right apart,UnitBalance.unitLift_eq,get]
    exact UnitBalance.minimize_lift p uniform _ live

private theorem mixed_spec {k n} (p : Row k) (g : Fin k → Vec n) (live : ∀ j, ∃ i, 0 < g j i) :
    (∀ xs, mixedCoefficients p = some xs → minimize (lift g xs) = minimize (lift g p.generators)) ∧
    ((WeightedComposition.Within p ∨ DenseWithin p ∨ SparseWithin p) → (mixedCoefficients p).isSome) := by
  cases h : WeightedComposition.candidate p with
  | some xs =>
    refine ⟨?_,by simp [mixedCoefficients,h]⟩
    intro ys hy
    have eq : xs = ys := by simpa [mixedCoefficients,h] using hy
    exact eq ▸ WeightedComposition.candidate_lift p h g live
  | none =>
    constructor
    · intro xs hx
      simp [mixedCoefficients,h,guard,Option.bind_eq_some_iff] at hx
      rw [←hx.2.2]
      exact (SparsePlane.minimize_lift p _ _ live).trans (minimize_compact _ g live)
    · rintro (w|area)
      · have fit := WeightedComposition.candidate_complete p w
        simp [h] at fit
      · have ⟨fit,count⟩ := sparse_checks p area
        simp [mixedCoefficients,h,guard,fit,count]

theorem bounded_spec {n} (rs : List (Row n)) :
    (∀ gs, boundedBasis rs = some gs → gs = generate rs) ∧
    (Within rs → boundedBasis rs = some (generate rs)) := by
  induction rs with
  | nil => exact ⟨fun _ h => (Option.some.inj h).symm, fun _ => rfl⟩
  | cons r rs ih =>
    constructor
    · intro gs h
      simp only [boundedBasis, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨prev, hp, h⟩ := h
      rw [ih.1 _ hp] at h
      let prev := generate rs
      have live (j : Fin prev.length) := ((mem_generate rs _).mp (List.get_mem prev j)).2.1
      let p := r.pullback prev.get
      by_cases sided : (∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)
      · dsimp only [p,prev] at sided
        simp [stored_get,guard,sided] at h
        apply h.2.symm.trans
        simpa [p,prev,List.map_reverse,generate,intersect] using (neutral_basis_ordered rs p sided).symm
      · dsimp only [p,prev] at sided
        by_cases uniform : p.equalMagnitude = true
        · have exactBasis := unitIntersection_eq prev p uniform live
          dsimp only [p,prev] at uniform
          simp [stored_get,guard,sided,uniform] at h
          exact h.2.symm.trans exactBasis
        dsimp only [p,prev] at uniform
        simp [stored_get,guard,sided,uniform,List.map_map,Function.comp_def,Option.bind_eq_some_iff] at h
        obtain ⟨_,xs,pick,out⟩ := h
        exact out.symm.trans ((mixed_spec p prev.get live).1 xs pick)
    · rintro ⟨tail,width,domain⟩
      let prev := generate rs
      let p := r.pullback prev.get
      have live (j : Fin prev.length) := ((mem_generate rs _).mp (List.get_mem prev j)).2.1
      by_cases sided : (∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)
      · have ordered := neutral_basis_ordered rs p sided
        dsimp only [p,prev] at sided
        simpa [boundedBasis,ih.2 tail,stored_get,guard,width,sided,p,prev,generate,intersect] using ordered.symm
      by_cases uniform : p.equalMagnitude = true
      · have exactBasis := unitIntersection_eq prev p uniform live
        dsimp only [p,prev] at sided uniform
        simpa [boundedBasis,ih.2 tail,stored_get,guard,width,sided,uniform,generate,intersect] using exactBasis
      have spec := mixed_spec p prev.get live
      obtain ⟨xs,pick⟩ := Option.isSome_iff_exists.mp (spec.2 ((domain.resolve_left sided).resolve_left (fun h => uniform ((commonWeight_iff p).mp h))))
      have minimized := spec.1 xs pick
      dsimp only [p,prev] at sided uniform pick
      simpa [boundedBasis,ih.2 tail,stored_get,guard,width,sided,uniform,pick,List.map_map,
        Function.comp_def,generate,intersect] using minimized


theorem emit_correct {n} (f : sig.ACSym) (rows : List ACSystem.Row) (avoid : List Variable)
    (fr : Frame f rows n) (gs : List (Vec n)) (hc : BasisCorrect (rows.map (encode fr.names)) gs)
    (small : gs.length ≤ 64) (w : UInt64 → Variable) (wi : Function.Injective w)
    (wt : ∀ j, (w j).sort = sig.acSort f) (wf : ∀ j, w j ∉ variables rows ++ avoid) :
    ∃ pairs : List (Arm × Substitution sig), emit gs = (pairs.map Prod.fst).toArray ∧
      (∀ p ∈ pairs, Represents fr w p.1 p.2) ∧
      (Outcome.complete (pairs.map Prod.snd)).CorrectIn (problem f rows) avoid := by
  let slot := fun j : Fin gs.length => w j.val.toUInt64
  have inj : Function.Injective slot := by
    intro a b h
    have e := congrArg UInt64.toNat (wi h)
    have ha := a.isLt
    have hb := b.isLt
    simp [Nat.toUInt64, Nat.mod_eq_of_lt (show a.val < 2^64 by omega),
      Nat.mod_eq_of_lt (show b.val < 2^64 by omega)] at e
    exact Fin.ext e
  let make := selectedBranch fr gs hc slot (fun _ => wt _) (fun _ => wf _)
  let pairs := (selections gs).attach.map fun js => (arm gs js.val, (make js).answer)
  refine ⟨pairs, by simp [pairs, emit, Coverage.coveringSelections_eq, List.map_map, Function.comp_def], ?_, ?_⟩
  · intro p hp
    obtain ⟨js,_,rfl⟩ := List.mem_map.mp hp
    refine ⟨by simp [arm],fun i => ?_⟩
    have slots_eq : slots (make js).active (fr.names i) =
        (js.val.flatMap fun j => List.replicate (gs.get j i) j.val.toUInt64).map w := by
      simp [make, selectedBranch, branchFromBasis, slots, List.flatMap_map, List.map_flatMap, fr.inverse, slot]
    cases h : slots (make js).active (fr.names i) with
    | nil => exact False.elim ((make js).nonempty _ (fr.used i) h)
    | cons x xs =>
      refine ⟨x,xs,?_,?_⟩
      · simpa [arm] using slots_eq.symm.trans h
      · change (make js).image (fr.names i) = _
        simp [Branch.image,fr.used i,h]
  · have answers : pairs.map Prod.snd = (selections gs).attach.map (fun js => (make js).answer) := by
      simp [pairs,List.map_map,Function.comp_def]
    rw [answers]
    exact basis_answers_correct fr gs hc slot inj (fun _ => wt _) (fun _ => wf _)

private theorem basis_valid {n} (rs : List (Row n)) (gs : List (Vec n))
    (result : answerBasis rs = some gs) : gs.Perm (generate rs) := by
  cases old : boundedBasis rs with
  | some original =>
    have eq : original = gs := by simpa [answerBasis,old] using result
    rw [←eq,(bounded_spec rs).1 original old]
  | none =>
    apply (Distributed.run_permutation (@boundedBasis) _ rs (by simpa [answerBasis,old] using result)).1
    intro k rows basis got
    rw [(bounded_spec rows).1 basis got]

private theorem basis_complete {n} (rs : List (Row n)) (floor : Distributed.RunWithin (@Within) rs 64) :
    (answerBasis rs).isSome := by
  have done := Distributed.run_complete (@boundedBasis) (@Within)
    (fun rows h => ⟨_,(bounded_spec rows).2 h,List.Perm.refl _⟩) rs 64 floor
  simp [answerBasis,done]

private theorem output_fits {n} (gs : List (Vec n)) (h : OutputWithin gs) : fitsOutput gs = true := by
  simpa [OutputWithin,fitsOutput,Coverage.packetFits_iff] using h

theorem outputWithin_perm {n} {xs ys : List (Vec n)} (p : xs.Perm ys) :
    OutputWithin xs ↔ OutputWithin ys := by
  simp only [OutputWithin,p.length_eq,(p.map total).sum_nat,outputWords_perm p]

/-- Every successful matrix packet encodes a complete Hilbert basis of the
decoded system. The bounded number of generators also bounds fresh slots. -/
theorem solveUpTo_returned {limit width : UInt64} {m : Matrix} {out : Answers}
    (done : solveUpTo limit width m = some out) :
    ∃ rs gs, (0 < width ∧ width ≤ limit ∧ m.size ≤ 128) ∧
      readRows width.toNat m.toList = some rs ∧
      gs.Perm (generate rs) ∧ gs.length ≤ 64 ∧ emit gs = out := by
  by_cases size : (0 < width ∧ width ≤ limit) ∧ m.size ≤ 128
  · cases read : readRows width.toNat m.toList with
    | none => simp [solveUpTo,size,read,guard] at done
    | some rs =>
      cases hg : answerBasis rs with
      | none => simp [solveUpTo,size,read,hg,guard] at done
      | some gs =>
        by_cases fit : fitsOutput gs = true
        · have emitted : emit gs = out := by simpa [solveUpTo,read,guard,size,hg,fit] using done
          have bounds := fit
          simp [fitsOutput] at bounds
          exact ⟨rs,gs,⟨size.1.1,size.1.2,size.2⟩,rfl,basis_valid rs gs hg,
            bounds.elim (fun h => Nat.le_trans h.1 (by decide : 12 ≤ 64)) And.left,emitted⟩
        · simp [solveUpTo,size,read,hg,fit,guard,failure] at done
  · simp [solveUpTo,size,guard,failure] at done

theorem solveUpTo_correct (limit : UInt64) : CorrectUpTo limit (solveUpTo limit) where
  malformed := by
    intro n m h
    simp [solveUpTo,h,guard]
  completes := by
    rintro n m ⟨hp,hn,hm,rs,read,old | new,words⟩
    · have basis := (bounded_spec rs).2 old
      simp [solveUpTo,answerBasis,hp,hn,hm,read,basis,output_fits _ words,guard]
    · obtain ⟨gs,h⟩ := Option.isSome_iff_exists.mp (basis_complete rs new)
      have fit := output_fits gs ((outputWithin_perm (basis_valid rs gs h)).mpr words)
      simp [solveUpTo,hp,hn,hm,read,h,fit,guard]
  semantic := by
    intro s f rows avoid n fr m input out result w inj typed fresh
    obtain ⟨rs,gs,_,decoded,perm,small,rfl⟩ := solveUpTo_returned result
    rw [input] at decoded
    cases decoded
    have basis := BasisCorrect.of_mem (generate_correct _) (fun _ => perm.mem_iff)
    exact emit_correct f rows avoid fr gs basis small w inj typed fresh

theorem solve_correct : Correct solve := solveUpTo_correct 32

end Tamarin.Homogeneous
