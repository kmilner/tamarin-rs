import Tamarin.ACBasisComplete
import Tamarin.ACCompactPlane
import Tamarin.ACPrimitiveRow
import Tamarin.ACGridBudget
import Tamarin.ACBalanceBound
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

def Within {n} : List (Row n) → Prop
  | [] => True
  | r :: rs => Within rs ∧
    let gs := generate rs
    let p := r.pullback gs.get
    gs.length ≤ 64 ∧ (((∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)) ∨ DenseWithin p ∨ SparseWithin p)

/-- Mandatory output bounds use the reference covering subsets and occurrence
counts. The first clause preserves the previous inexpensive admission check. -/
def OutputWithin {n} (gs : List (Vec n)) : Prop :=
  (gs.length ≤ 12 ∧ 2 ^ gs.length * (gs.map total).sum ≤ 65536) ∨
  (gs.length ≤ 64 ∧ ((selections gs).map (selectionWords gs)).sum ≤ 65536)

def Admitted (width : UInt64) (m : Matrix) : Prop :=
  0 < width ∧ width ≤ 32 ∧ m.size ≤ 128 ∧ ∃ rs, readRows width.toNat m.toList = some rs ∧
    Within rs ∧ OutputWithin (generate rs)

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

structure Correct (run : UInt64 → Matrix → Option Answers) : Prop where
  malformed : ∀ n m, readRows n.toNat m.toList = none → run n m = none
  completes : ∀ n m, Admitted n m → (run n m).isSome
  semantic : ∀ {s : Signature} (f : s.ACSym) (rows : List ACSystem.Row) (avoid : List Variable)
    (n : UInt64) (fr : Frame f rows n.toNat) (m : Matrix)
    (_input : readRows n.toNat m.toList = some (rows.map (encode fr.names))) (out : Answers),
    run n m = some out →
    ∀ w : UInt64 → Variable, Function.Injective w → (∀ j, (w j).sort = s.acSort f) →
    (∀ j, w j ∉ variables rows ++ avoid) →
    ∃ pairs : List (Arm × Substitution s), out = (pairs.map Prod.fst).toArray ∧
      (∀ p ∈ pairs, Represents fr w p.1 p.2) ∧
      (Outcome.complete (pairs.map Prod.snd)).CorrectIn (problem f rows) avoid

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
        simp [stored_get,guard,sided,List.map_map,Function.comp_def,Option.bind_eq_some_iff] at h
        exact h.2.2.2.symm.trans ((SparsePlane.minimize_lift p _ _ live).trans (minimize_compact _ prev.get live))
    · rintro ⟨tail,width,domain⟩
      let prev := generate rs
      let p := r.pullback prev.get
      have live (j : Fin prev.length) := ((mem_generate rs _).mp (List.get_mem prev j)).2.1
      by_cases sided : (∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)
      · have ordered := neutral_basis_ordered rs p sided
        dsimp only [p,prev] at sided
        simpa [boundedBasis,ih.2 tail,stored_get,guard,width,sided,p,prev,generate,intersect] using ordered.symm
      have checks := sparse_checks p (domain.resolve_left sided)
      have minimized := (SparsePlane.minimize_lift p _ _ live).trans (minimize_compact p prev.get live)
      dsimp only [p,prev] at sided
      simp [boundedBasis,ih.2 tail,stored_get,guard,width,sided,
        show (r.pullback (generate rs).get).sparseFits (r.pullback (generate rs).get).primitive.cap 16384 = true from checks.1,
        show ((r.pullback (generate rs).get).sparseGenerators (r.pullback (generate rs).get).primitive.cap).length ≤ 2048 from checks.2,
        List.map_map,Function.comp_def]
      exact minimized

private theorem emit_correct {n} (f : sig.ACSym) (rows : List ACSystem.Row) (avoid : List Variable)
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

theorem solve_correct : Correct solve where
  malformed := by
    intro n m h
    simp [solve,h,guard]
  completes := by
    rintro n m ⟨hp,hn,hm,rs,read,within,output⟩
    have fit : fitsOutput (generate rs) = true := by
      simpa [OutputWithin,fitsOutput,Coverage.packetFits_iff] using output
    simp [solve,hp,hn,hm,read,(bounded_spec rs).2 within,fit,guard]
  semantic := by
    intro s f rows avoid n fr m input out result w inj typed fresh
    by_cases size : (0 < n ∧ n ≤ 32) ∧ m.size ≤ 128
    · cases hg : boundedBasis (rows.map (encode fr.names)) with
      | none => simp [solve,input,guard,size,hg] at result
      | some gs =>
        by_cases fit : fitsOutput gs = true
        · have eo : emit gs = out := by simpa [solve,input,guard,size,hg,fit] using result
          subst out
          have eq := (bounded_spec _).1 gs hg
          subst gs
          simp [fitsOutput] at fit
          have width := fit.elim (fun h => Nat.le_trans h.1 (by decide : 12 ≤ 64)) And.left
          exact emit_correct f rows avoid fr _ (generate_correct _) width w inj typed fresh
        · simp [solve,input,guard,size,hg,fit] at result; contradiction
    · simp [solve,guard,size] at result; contradiction

end Tamarin.Homogeneous
