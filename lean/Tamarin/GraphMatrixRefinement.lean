import Tamarin.GraphMatrix
import Tamarin.HomogeneousContract
import Tamarin.WholeContract

/-! A homogeneous matrix is determined by the ordered variable occurrences of
its decoded residual equations. Flattening an AC node preserves every one of
those occurrences, including references shared elsewhere in the graph. -/
namespace Tamarin.GraphMatrixRefinement
open Whole WholeProblem ACSystem Homogeneous
variable {sig : Signature}

private theorem word_nat {n : UInt64} (i : Fin n.toNat) : i.val.toUInt64.toNat = i.val :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt n.toNat_lt_size)

/-- Matching a column index against the request-local ID counts the same
variables as matching the column's semantic variable on a live side. -/
private theorem count_ids {n : UInt64} (c : Codec sig) (names : Fin n.toNat → Variable)
    (columns : ∀ i, c.vars.put (names i) = i.val.toUInt64)
    (vs : List Variable) (live : ∀ v ∈ vs, ∃ i, names i = v) (i : Fin n.toNat) :
    (vs.map c.vars.put).count i.val.toUInt64 = vs.count (names i) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have tail := ih (fun w hw => live w (List.mem_cons_of_mem _ hw))
    obtain ⟨j, rfl⟩ := live v (List.mem_cons_self ..)
    have same : j.val.toUInt64 = i.val.toUInt64 ↔ names j = names i := by
      constructor
      · intro h
        have natEq := congrArg UInt64.toNat h
        rw [word_nat,word_nat] at natEq
        exact congrArg names (Fin.ext natEq)
      · intro h
        exact (columns j).symm.trans ((congrArg c.vars.put h).trans (columns i))
    simp only [List.map_cons, List.count_cons, tail, columns, beq_iff_eq, same]

private theorem side_live {f : sig.ACSym} {rows width} (fr : Frame f rows width)
    {r : ACSystem.Row} (hr : r ∈ rows) {s : Side} (hs : s ∈ [r.lhs, r.rhs]) :
    ∀ v ∈ s.vars, ∃ i, fr.names i = v := by
  intro v hv
  apply fr.live
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  rcases List.mem_cons.mp hs with h | h
  · exact List.mem_append_left _ (h ▸ hv)
  · exact List.mem_append_right _ ((List.mem_singleton.mp h) ▸ hv)

private theorem children_append (symbol sort : UInt64) (xs ys : List Tree) :
    GraphMatrix.children symbol sort (xs ++ ys) =
      (do return (← GraphMatrix.children symbol sort xs) ++ (← GraphMatrix.children symbol sort ys)) := by
  induction xs with
  | nil => cases h : GraphMatrix.children symbol sort ys <;> simp [GraphMatrix.children, h]
  | cons x xs ih =>
    simp only [List.cons_append, GraphMatrix.children, ih]
    cases GraphMatrix.leaves symbol sort x <;> cases GraphMatrix.children symbol sort xs <;>
      cases GraphMatrix.children symbol sort ys <;> simp [List.append_assoc]

private theorem layout_leaves (symbol sort : UInt64) {a b : Tree} (h : Layout a b) :
    GraphMatrix.leaves symbol sort a = GraphMatrix.leaves symbol sort b := by
  induction h with
  | refl => rfl
  | trans _ _ ih ij => exact ih.trans ij
  | child k i pre post _ ih =>
    simp only [GraphMatrix.leaves, children_append, GraphMatrix.children, ih]
  | flatten i pre inner post =>
    by_cases hi : i = symbol
    · subst i
      simp only [GraphMatrix.leaves, and_self, ite_true, children_append, GraphMatrix.children]
      cases GraphMatrix.children symbol sort pre <;> cases GraphMatrix.children symbol sort inner <;>
        cases GraphMatrix.children symbol sort post <;> simp [List.append_assoc]
    · simp [GraphMatrix.leaves, hi]

private theorem encoded_leaves (c : Codec sig) (f : sig.ACSym) (s : Side)
    (sorted : ∀ v ∈ s.vars, v.sort = sig.acSort f) :
    GraphMatrix.leaves (c.acs.put f) (sortWord (sig.acSort f)) (encode c (s.term f)) =
      some (s.vars.map c.vars.put) := by
  obtain ⟨x, xs⟩ := s
  induction xs generalizing x with
  | nil =>
    simp [Side.term, ACRepresentation.fold, encode, GraphMatrix.leaves, Side.vars, sorted x (by simp [Side.vars])]
  | cons y ys ih =>
    have hx := sorted x (List.mem_cons_self ..)
    have hy := ih y (fun v hv => sorted v (List.mem_cons_of_mem _ hv))
    change GraphMatrix.leaves _ _ (.app 4 _ [encode c (.var x), encode c ((Side.mk y ys).term f)]) = _
    simp [GraphMatrix.leaves, GraphMatrix.children, hy, encode, hx, Side.vars]

private theorem side_iff (c : Codec sig) (f : sig.ACSym) {width : UInt64}
    (names : Fin width.toNat → Variable) (columns : ∀ i, c.vars.put (names i) = i.val.toUInt64)
    (sorts : ∀ i, (names i).sort = sig.acSort f) (s : Side) (live : ∀ v ∈ s.vars, ∃ i, names i = v)
    {t : Tree} (layout : Layout (encode c (s.term f)) t) (a : Array UInt64) :
    GraphMatrix.Side width (c.acs.put f) (sortWord (sig.acSort f)) t a ↔
      s.vars.length ≤ 4096 ∧ a = sideWords names s := by
  have sorted (v) (hv : v ∈ s.vars) : v.sort = sig.acSort f := by
    obtain ⟨i,rfl⟩ := live v hv
    exact sorts i
  have leaves := (layout_leaves _ _ layout).symm.trans (encoded_leaves c f s sorted)
  have ids (j) (hj : j ∈ s.vars.map c.vars.put) : j < width := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hj
    obtain ⟨i,rfl⟩ := live v hv
    simpa only [columns, UInt64.lt_iff_toNat_lt, word_nat] using i.isLt
  have counts : GraphMatrix.counts width (s.vars.map c.vars.put) = sideWords names s := by
    unfold GraphMatrix.counts sideWords
    exact congrArg Array.ofFn (funext fun i => congrArg Nat.toUInt64 (count_ids c names columns _ live i))
  constructor
  · rintro ⟨xs, hx, small, _, ha⟩
    cases Option.some.inj (hx.symm.trans leaves)
    exact ⟨by simpa using small, ha.trans counts⟩
  · rintro ⟨small, ha⟩
    exact ⟨_, leaves, by simpa using small, ids, ha.trans counts.symm⟩

/-- The upper bound is on occurrences per expanded side. Repeated references
to one variable count separately. -/
def Fits (rows : List ACSystem.Row) : Prop :=
  ∀ r ∈ rows, ∀ s ∈ [r.lhs,r.rhs], s.vars.length ≤ 4096

private theorem rows_iff (c : Codec sig) (f : sig.ACSym) {width : UInt64}
    (names : Fin width.toNat → Variable) (columns : ∀ i, c.vars.put (names i) = i.val.toUInt64)
    (sorts : ∀ i, (names i).sort = sig.acSort f) (rows : List ACSystem.Row)
    (live : ∀ r ∈ rows, ∀ s ∈ [r.lhs, r.rhs], ∀ v ∈ s.vars, ∃ i, names i = v)
    {wire} (layout : RowLayout (encodeRows c (problem f rows)) wire) (mat : List (Array UInt64)) :
    GraphMatrix.Rows width (c.acs.put f) (sortWord (sig.acSort f)) wire mat ↔
      Fits rows ∧ mat = matrixWords names rows := by
  induction rows generalizing wire mat with
  | nil =>
    cases layout
    constructor
    · intro h
      cases h
      exact ⟨by simp [Fits], rfl⟩
    · rintro ⟨_, rfl⟩
      exact .nil
  | cons row rs ih =>
    cases layout with
    | cons ll lr tail =>
      have next := ih (fun r hr => live r (List.mem_cons_of_mem _ hr)) tail
      have lhs := side_iff c f names columns sorts row.lhs (live row (by simp) _ (by simp)) ll
      have rhs := side_iff c f names columns sorts row.rhs (live row (by simp) _ (by simp)) lr
      have budget : Fits (row :: rs) ↔
          (row.lhs.vars.length ≤ 4096 ∧ row.rhs.vars.length ≤ 4096) ∧ Fits rs := by
        simp [Fits]
      constructor
      · intro h
        cases h with
        | cons l r other =>
          obtain ⟨hl,rfl⟩ := (lhs _).mp l
          obtain ⟨hr,rfl⟩ := (rhs _).mp r
          obtain ⟨ht,rfl⟩ := (next _).mp other
          exact ⟨budget.mpr ⟨⟨hl,hr⟩,ht⟩,rfl⟩
      · rintro ⟨hf,rfl⟩
        obtain ⟨⟨hl,hr⟩,ht⟩ := budget.mp hf
        exact .cons ((lhs _).mpr ⟨hl,rfl⟩) ((rhs _).mpr ⟨hr,rfl⟩) ((next _).mpr ⟨ht,rfl⟩)

/-- For every successful conversion, layout and column identity alone determine
the entire matrix. The side budget implies that no UInt64 coefficient wrapped. -/
theorem matrix_of_build {kernel : GraphMatrix.Kernel} (verified : GraphMatrix.Correct kernel)
    (c : Codec sig) (f : sig.ACSym) (rows : List ACSystem.Row) (width : UInt64)
    (fr : Frame f rows width.toNat) (columns : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {decls nodes roots wire m} (decoded : Wire.decodeProblem decls nodes roots = some wire)
    (layout : RowLayout (encodeRows c (problem f rows)) wire)
    (success : kernel width (c.acs.put f) (sortWord (sig.acSort f)) decls nodes roots = some m) :
    m.toList = matrixWords fr.names rows ∧
      ∀ r ∈ rows, ∀ s ∈ [r.lhs, r.rhs], ∀ i, s.vars.count (fr.names i) < 2^64 := by
  obtain ⟨_, _, _, _, ⟨p, hp, hm⟩, _⟩ := (verified _ _ _ _ _ _ _).mp success
  cases Option.some.inj (hp.symm.trans decoded)
  obtain ⟨small, mat⟩ := (rows_iff c f fr.names columns fr.sorts rows
    (fun _ hr _ hs => side_live fr hr hs) layout _).mp hm
  refine ⟨mat, fun r hr s hs i => ?_⟩
  have := small r hr s hs
  have := List.count_le_length (a := fr.names i) (l := s.vars)
  omega

private theorem uses_all {f : sig.ACSym} {rows : List ACSystem.Row} {width : UInt64}
    (fr : Frame f rows width.toNat) (small : Fits rows) (i : Fin width.toNat) :
    ∃ a ∈ (matrixWords fr.names rows).toArray.toList, ∃ v, a[i.val]? = some v ∧ 0 < v := by
  obtain ⟨r, hr, contains⟩ := List.mem_flatMap.mp (fr.used i)
  obtain ⟨s, hs, hv⟩ : ∃ s ∈ [r.lhs,r.rhs], fr.names i ∈ s.vars := by
    rcases List.mem_append.mp contains with hl | hr
    · exact ⟨_, List.mem_cons_self .., hl⟩
    · exact ⟨_, by simp, hr⟩
  refine ⟨sideWords fr.names s, ?_, (s.vars.count (fr.names i)).toUInt64, ?_, ?_⟩
  · rw [List.toList_toArray]
    apply List.mem_flatMap.mpr
    refine ⟨r, hr, ?_⟩
    rcases List.mem_cons.mp hs with h | h
    · simp [h]
    · simp [List.mem_singleton.mp h]
  · simp [sideWords, i.isLt]
  · have := small r hr s hs
    have := List.count_le_length (a := fr.names i) (l := s.vars)
    have positive := List.count_pos_iff.mpr hv
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by change _ < 2^64; omega)]
    exact positive

/-- Every faithfully laid out pure system within the declared bounds is
converted, independently of whether the basis solver can finish the system. -/
theorem build_of_matrix {kernel : GraphMatrix.Kernel} (verified : GraphMatrix.Correct kernel)
    (c : Codec sig) (f : sig.ACSym) (rows : List ACSystem.Row) (width : UInt64)
    (fr : Frame f rows width.toNat) (columns : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {decls nodes roots wire} (decoded : Wire.decodeProblem decls nodes roots = some wire)
    (layout : RowLayout (encodeRows c (problem f rows)) wire)
    (declared : GraphMatrix.Declared decls (c.acs.put f) (sortWord (sig.acSort f)))
    (pos : 0 < width) (widthBound : width ≤ 32) (rootBound : roots.size ≤ 128) (small : Fits rows) :
    kernel width (c.acs.put f) (sortWord (sig.acSort f)) decls nodes roots =
      some (matrixWords fr.names rows).toArray := by
  apply (verified _ _ _ _ _ _ _).mpr
  refine ⟨pos, widthBound, rootBound, declared, ⟨wire, decoded, ?_⟩, uses_all fr small⟩
  apply (rows_iff c f fr.names columns fr.sorts rows (fun _ hr _ hs => side_live fr hr hs) layout _).mpr
  exact ⟨small, List.toList_toArray⟩

end Tamarin.GraphMatrixRefinement
