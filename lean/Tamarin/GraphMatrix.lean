import TamarinRuntime.GraphMatrix

/-! Fixed occurrence and coefficient semantics for the graph-to-matrix export. -/
namespace Tamarin.GraphMatrix
open Whole

mutual
  def leaves (symbol sort : UInt64) : Tree → Option (List UInt64)
    | .leaf k id s => if k = 0 ∧ s = sort then some [id] else none
    | .app k id ts => if k = 4 ∧ id = symbol then children symbol sort ts else none
  def children (symbol sort : UInt64) : List Tree → Option (List UInt64)
    | [] => some []
    | t :: ts => do
      let head ← leaves symbol sort t
      let tail ← children symbol sort ts
      return head ++ tail
end

def counts (width : UInt64) (ids : List UInt64) : Array UInt64 :=
  Array.ofFn fun i : Fin width.toNat => (ids.count i.val.toUInt64).toUInt64

def Side (width symbol sort : UInt64) (t : Tree) (a : Array UInt64) : Prop :=
  ∃ ids, leaves symbol sort t = some ids ∧ ids.length ≤ 4096 ∧
    (∀ i ∈ ids, i < width) ∧ a = counts width ids

inductive Rows (width symbol sort : UInt64) :
    List (Tree × Tree) → List (Array UInt64) → Prop where
  | nil : Rows width symbol sort [] []
  | cons {l r a b p rs} (left : Side width symbol sort l a) (right : Side width symbol sort r b)
      (rest : Rows width symbol sort p rs) : Rows width symbol sort ((l,r) :: p) (a :: b :: rs)

def Declared (decls : Array UInt64) (symbol sort : UInt64) : Prop :=
  ∃ ds, declarations decls.toList = some ds ∧ ∃ d ∈ ds, d.kind = 4 ∧ d.id = symbol ∧ d.output = sort

/-- The whole prefix is a column inventory. Extra all-zero columns could otherwise
introduce bindings for variables absent from the residual equations. -/
def UsesAll (width : UInt64) (m : Homogeneous.Matrix) : Prop :=
  ∀ i : Fin width.toNat, ∃ a ∈ m.toList, ∃ v, a[i.val]? = some v ∧ 0 < v

def Represents (width symbol sort : UInt64) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) (m : Homogeneous.Matrix) : Prop :=
  0 < width ∧ width ≤ 32 ∧ roots.size ≤ 128 ∧ Declared decls symbol sort ∧
    (∃ p, Wire.decodeProblem decls nodes roots = some p ∧ Rows width symbol sort p m.toList) ∧ UsesAll width m

abbrev Kernel := UInt64 → UInt64 → UInt64 → Array UInt64 → Array (Array UInt64) →
  Array UInt64 → Option Homogeneous.Matrix

def Correct (candidate : Kernel) : Prop :=
  ∀ width symbol sort decls nodes roots m, candidate width symbol sort decls nodes roots = some m ↔
    Represents width symbol sort decls nodes roots m

mutual
  private theorem gather_spec (sym s : UInt64) (t : Tree) (acc out : Array UInt64)
      (small : acc.size ≤ 4096) :
      gather sym s t acc = some out ↔ ∃ ids, leaves sym s t = some ids ∧
        acc.size + ids.length ≤ 4096 ∧ out.toList = acc.toList ++ ids := by
    cases t with
    | leaf k id sort =>
      by_cases ok : k = 0 ∧ sort = s
      · simp only [gather, leaves, ok.1, ok.2, true_and, ↓reduceIte,
          Option.some.injEq, exists_eq_left', List.length_singleton]
        by_cases room : acc.size < 4096
        · simp [room, show acc.size + 1 ≤ 4096 by omega, ← Array.toList_inj]
          exact eq_comm
        · simp [room, show ¬ acc.size + 1 ≤ 4096 by omega]
      · simp [gather, leaves, ok, show ¬ (k = 0 ∧ sort = s ∧ acc.size < 4096) from fun h => ok ⟨h.1,h.2.1⟩]
    | app k id args =>
      by_cases ok : k = 4 ∧ id = sym
      · simpa [gather, leaves, ok] using gatherChildren_spec sym s args acc out small
      · simp [gather, leaves, ok]
  private theorem gatherChildren_spec (sym s : UInt64) (ts : List Tree) (acc out : Array UInt64)
      (small : acc.size ≤ 4096) :
      gatherChildren sym s ts acc = some out ↔ ∃ ids, children sym s ts = some ids ∧
        acc.size + ids.length ≤ 4096 ∧ out.toList = acc.toList ++ ids := by
    cases ts with
    | nil => simp [gatherChildren, children, small, ← Array.toList_inj, eq_comm]
    | cons t ts =>
      simp only [gatherChildren, children, Option.bind_eq_bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq]
      constructor
      · rintro ⟨mid, step, tail⟩
        obtain ⟨a, ha, sizeA, eqA⟩ := (gather_spec sym s t acc mid small).mp step
        have lenA : mid.size = acc.size + a.length := by simpa using congrArg List.length eqA
        obtain ⟨b, hb, sizeB, eqB⟩ := (gatherChildren_spec sym s ts mid out (lenA ▸ sizeA)).mp tail
        exact ⟨a ++ b, ⟨a, ha, b, hb, rfl⟩,
          by simpa [lenA, Nat.add_assoc] using sizeB, by simp [eqB, eqA]⟩
      · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, bound, eq⟩
        simp only [List.length_append] at bound
        let mid := (acc.toList ++ a).toArray
        have lenA : mid.size = acc.size + a.length := by simp [mid]
        refine ⟨mid, (gather_spec sym s t acc mid small).mpr ⟨a, ha, by omega, by simp [mid]⟩,
          (gatherChildren_spec sym s ts mid out (by omega)).mpr ⟨b, hb, by omega, ?_⟩⟩
        simpa [mid] using eq
end

private def tally (ids : List UInt64) (acc : Array UInt64) :=
  ids.foldl (fun a k => a.modify k.toNat (· + 1)) acc

private theorem tally_cons (k : UInt64) (ks : List UInt64) (acc : Array UInt64) :
    tally (k :: ks) acc = tally ks (acc.modify k.toNat (· + 1)) := rfl

private theorem tally_size (ids : List UInt64) (acc : Array UInt64) : (tally ids acc).size = acc.size := by
  induction ids generalizing acc with
  | nil => rfl
  | cons k ks ih => simp [tally_cons, ih]

private theorem tally_get (ids : List UInt64) (acc : Array UInt64) (i : UInt64) :
    (tally ids acc)[i.toNat]? = acc[i.toNat]?.map (fun v => v + (ids.count i).toUInt64) := by
  induction ids generalizing acc with
  | nil => simp [tally]
  | cons k ks ih =>
    by_cases h : k = i
    · subst k
      simp [tally_cons, ih, Array.getElem?_modify, UInt64.add_assoc,
        UInt64.add_comm, Function.comp_def]
    · have ne : k.toNat ≠ i.toNat := fun e => h (UInt64.toNat_inj.mp e)
      simp [tally_cons, ih, Array.getElem?_modify, h, ne]

private theorem tally_counts (w : UInt64) (ids : List UInt64) :
    tally ids (Array.replicate w.toNat 0) = counts w ids := by
  apply Array.ext
  · simp [tally_size, counts]
  · intro i hi hrow
    have small : i < w.toNat := by simpa [counts] using hrow
    have bounded : i < 2^64 := Nat.lt_trans small w.toNat_lt
    have natEq : i.toUInt64.toNat = i := by simp [Nat.toUInt64, Nat.mod_eq_of_lt bounded]
    have get := tally_get ids (Array.replicate w.toNat 0) i.toUInt64
    simp [natEq, small, Array.getElem?_eq_getElem hi] at get
    simpa [counts] using get
theorem histogram_counts (w : UInt64) (xs : Array UInt64) :
    histogram w xs = counts w xs.toList := by
  simpa only [histogram, tally, Array.foldl_toList] using tally_counts w xs.toList

/-- Reading a bounded word coefficient as a natural number recovers the
mathematical multiplicity exactly. -/
theorem count_exact (w : UInt64) (xs : List UInt64) (h : xs.length ≤ 4096) (i : Fin w.toNat) :
    (counts w xs)[i.val]!.toNat = xs.count i.val.toUInt64 := by
  have n := List.count_le_length (l := xs) (a := i.val.toUInt64)
  simp [counts, getElem!_pos, Nat.toUInt64, Nat.mod_eq_of_lt (show xs.count i.val.toUInt64 < 2^64 by omega)]

theorem row_spec (w sym s : UInt64) (t : Tree) (r : Array UInt64) :
    row w sym s t = some r ↔ Side w sym s t r := by
  simp only [row, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨ids, got, h⟩
    obtain ⟨xs, hxs, size, eq⟩ := (gather_spec sym s t #[] ids (by decide)).mp got
    simp only [List.nil_append] at eq
    simp only [← Array.all_toList, histogram_counts, eq] at h
    split at h
    next scope => exact ⟨xs,hxs, by simpa using size,
      fun i hi => of_decide_eq_true (List.all_eq_true.mp scope i hi), (Option.some.inj h).symm⟩
    next => contradiction
  · rintro ⟨xs, hxs, size, scope, rfl⟩
    refine ⟨xs.toArray, (gather_spec sym s t #[] xs.toArray (by decide)).mpr
      ⟨xs, hxs, by simpa using size, by simp⟩, ?_⟩
    have yes : xs.all (fun i => decide (i < w)) = true := List.all_eq_true.mpr
      fun i hi => decide_eq_true (scope i hi)
    simp only [← Array.all_toList, yes, ↓reduceIte, histogram_counts]

theorem buildRows_spec (w sym s : UInt64) (p : List (Tree × Tree)) (rs : List (Array UInt64)) :
    buildRows w sym s p = some rs ↔ Rows w sym s p rs := by
  induction p generalizing rs with
  | nil =>
    constructor
    · rintro ⟨⟩; exact .nil
    · intro h; cases h; rfl
  | cons pair tail ih =>
    obtain ⟨l,r⟩ := pair
    simp only [buildRows, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    constructor
    · rintro ⟨a, hl, b, hr, rest, hrest, rfl⟩
      exact .cons ((row_spec ..).mp hl) ((row_spec ..).mp hr) ((ih _).mp hrest)
    · intro h
      cases h with
      | cons hl hr hrest => exact ⟨_,(row_spec ..).mpr hl,_,(row_spec ..).mpr hr,_,(ih _).mpr hrest,rfl⟩

private theorem read_spec (w sym s : UInt64) (ds : Array UInt64) (ns : Array (Array UInt64))
    (roots : Array UInt64) (m : Homogeneous.Matrix) :
    readMatrix w sym s ds ns roots = some m ↔
      0 < w ∧ w ≤ 32 ∧ roots.size ≤ 128 ∧ Declared ds sym s ∧
        ∃ p, Wire.decodeProblem ds ns roots = some p ∧ Rows w sym s p m.toList := by
  unfold readMatrix Declared Whole.Wire.decodeProblem
  cases hd : declarations ds.toList with
  | none => simp [guard]
  | some d =>
    by_cases good : 0 < w ∧ w ≤ 32 ∧ roots.size ≤ 128
    · by_cases declared : ∃ x ∈ d, x.kind = 4 ∧ x.id = sym ∧ x.output = s
      · simp [good.1, good.2.1, good.2.2, declared, guard,
          Option.bind_eq_some_iff, buildRows_spec, ← Array.toList_inj, and_assoc]
        constructor
        · rintro ⟨ts,ht,p,hp,h⟩; exact ⟨p,⟨ts,ht,hp⟩,h⟩
        · rintro ⟨p,⟨ts,ht,hp⟩,h⟩; exact ⟨ts,ht,p,hp,h⟩
      · simp [good.1, good.2.1, good.2.2, guard, failure, and_assoc, declared]
    · have no : ¬ (0 < w ∧ w ≤ 32 ∧ roots.size ≤ 128 ∧ (∃ d' ∈ d, d'.kind = 4 ∧ d'.id = sym ∧ d'.output = s) ∧
          ∃ p, ((decodeNodes d ns).bind fun ts => readEquations ts roots.toList) = some p ∧ Rows w sym s p m.toList) :=
        fun h => good ⟨h.1,h.2.1,h.2.2.1⟩
      simpa [guard, good, failure] using no

private theorem used_spec (w : UInt64) (m : Homogeneous.Matrix) : allUsed w m ↔ UsesAll w m := by
  simp [allUsed, UsesAll, Array.mem_iff_getElem, Option.any_eq_true]
  constructor
  · intro h i
    obtain ⟨j,hj,v,get,pos⟩ := h i
    exact ⟨_,⟨j,hj,rfl⟩,v,get,pos⟩
  · intro h i
    obtain ⟨_,⟨j,hj,rfl⟩,v,get,pos⟩ := h i
    exact ⟨j,hj,v,get,pos⟩

theorem build_correct : Correct build := by
  intro w sym s ds ns roots m
  cases result : readMatrix w sym s ds ns roots with
  | none =>
    have no := mt (read_spec w sym s ds ns roots m).mpr (by simp [result])
    simp [build, result, Represents]
    grind
  | some a =>
    obtain ⟨hw,limit,maxRoots,decl,q,hq,rows⟩ := (read_spec ..).mp result
    constructor
    · intro h
      simp only [build, result, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      next use =>
        cases Option.some.inj h
        exact ⟨hw,limit,maxRoots,decl,⟨q,hq,rows⟩,(used_spec ..).mp use⟩
      next => contradiction
    · rintro ⟨_,_,_,_,layout,use⟩
      have eq := (read_spec ..).mpr ⟨hw,limit,maxRoots,decl,layout⟩
      cases Option.some.inj (result.symm.trans eq)
      simp [build, result, (used_spec ..).mpr use]

end Tamarin.GraphMatrix
