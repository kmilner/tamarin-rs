import Tamarin.BinaryXorShapes

namespace Tamarin.Rewriting.BinaryXor
open Cancellation ACRepresentation
variable {sig : Signature} (T : Table sig)
noncomputable section
open Classical

private def merge (xs ys : List (Class sig)) : Term sig :=
  if xs.isEmpty then assemble T ys else if ys.isEmpty then assemble T xs else .ac T.f (assemble T xs) (assemble T ys)

private theorem assemble_append (xs ys : List (Class sig)) : EquivB (assemble T (xs ++ ys)) (merge T xs ys) := by
  cases xs with
  | nil => exact .refl _
  | cons a as =>
    cases ys with
    | nil => rw [List.append_nil]; exact .refl _
    | cons b bs =>
      change EquivB (T.value (((a::as) ++ b::bs).map rep)) _
      rw [List.map_append]
      exact fold_append T.f (rep a) (as.map rep) (rep b) (bs.map rep)

private theorem cases_of_parts {a b out : Term sig} {H I J : List (Class sig)}
    (gh : Good T (assemble T H)) (gi : Good T (assemble T I)) (gj : Good T (assemble T J))
    (left : EquivB a (merge T H I)) (right : EquivB b (merge T H J)) (value : EquivB out (merge T I J)) :
    ∃ sh, Instance T a b out sh := by
  have fit (sh) (eq : sh.images T (assemble T H) (assemble T I) (assemble T J) =
      (merge T H I,merge T H J,merge T I J)) : Instance T a b out sh := by
    exact ⟨_,_,_,gh,gi,gj,by rw [eq]; exact left,by rw [eq]; exact right,by rw [eq]; exact value⟩
  cases H <;> cases I <;> cases J <;> first
    | exact ⟨.unitLeft,fit _ rfl⟩
    | exact ⟨.unitRight,fit _ rfl⟩
    | exact ⟨.same,fit _ rfl⟩
    | exact ⟨.disjoint,fit _ rfl⟩
    | exact ⟨.leftContains,fit _ rfl⟩
    | exact ⟨.rightContains,fit _ rfl⟩
    | exact ⟨.overlap,fit _ rfl⟩

/-- For arbitrary normalized message operands take their intersection and
two differences as sets of structural equivalence classes. Empty parts
choose the unit/diagonal/containment cases; a partial overlap leaves
two nonempty differences and their symmetric difference as the output. -/
theorem classify {a b out : Term sig} (ha : Good T a) (hb : Good T b)
    (nf : NormalForm T.R (.ac T.f a b) out) : ∃ sh, Instance T a b out sh := by
  let L := pieces T a
  let R := pieces T b
  let H := L.filter (fun k => decide (k ∈ R))
  let I := L.filter (fun k => decide (k ∉ R))
  let J := R.filter (fun k => decide (k ∉ L))
  obtain ⟨dl,zl,fl⟩ := pieces_good T ha
  obtain ⟨dr,zr,fr⟩ := pieces_good T hb
  have dh : H.Nodup := dl.filter _
  have di : I.Nodup := dl.filter _
  have dj : J.Nodup := dr.filter _
  have mh (k) : k ∈ H ↔ k ∈ L ∧ k ∈ R := by simp [H]
  have mi (k) : k ∈ I ↔ k ∈ L ∧ k ∉ R := by simp [I]
  have mj (k) : k ∈ J ↔ k ∈ R ∧ k ∉ L := by simp [J]
  have dhi : (H++I).Nodup := List.nodup_append.mpr ⟨dh,di,fun k hk u hu e => (mi _ |>.mp hu).2 (e ▸ ((mh _).mp hk).2)⟩
  have dhj : (H++J).Nodup := List.nodup_append.mpr ⟨dh,dj,fun k hk u hu e => (mj _ |>.mp hu).2 (e ▸ ((mh _).mp hk).1)⟩
  have dij : (I++J).Nodup := List.nodup_append.mpr ⟨di,dj,fun k hk u hu e => (mj _ |>.mp hu).2 (e ▸ ((mi _).mp hk).1)⟩
  have left : L.Perm (H++I) := (List.perm_ext_iff_of_nodup dl dhi).mpr (fun k => by
    change k ∈ L ↔ _; rw [List.mem_append,mh,mi]; by_cases h : k ∈ R <;> simp [h])
  have right : R.Perm (H++J) := (List.perm_ext_iff_of_nodup dr dhj).mpr (fun k => by
    change k ∈ R ↔ _; rw [List.mem_append,mh,mj]; by_cases h : k ∈ L <;> simp [h])
  have zh : T.zeroClass ∉ H := fun h => zl ((mh _).mp h).1
  have zi : T.zeroClass ∉ I := fun h => zl ((mi _).mp h).1
  have zj : T.zeroClass ∉ J := fun h => zr ((mj _).mp h).1
  have gh := assemble_good T (fun k hk => fl k ((mh k).mp hk).1) dh zh
  have gi := assemble_good T (fun k hk => fl k ((mi k).mp hk).1) di zi
  have gj := assemble_good T (fun k hk => fr k ((mj k).mp hk).1) dj zj
  apply cases_of_parts T gh gi gj
  · exact (assemble_input T ha).trans ((assemble_perm T left).trans (assemble_append T ..))
  · exact (assemble_input T hb).trans ((assemble_perm T right).trans (assemble_append T ..))
  · apply EquivB.trans _ (assemble_append T I J)
    have ty : HasSort (.ac T.f a b) .msg := T.fSort ▸ HasSort.ac T.f a b (T.fSort ▸ ha.1) (T.fSort ▸ hb.1)
    apply (parity_normalForm T ty T.fSort _ dij (by simpa using And.intro zi zj) _ out).mp nf
    · intro k hk
      rw [FreshXor.Flat.Table.bag,flatten_ac] at hk
      exact (List.mem_append.mp hk).elim (fact_of_mem T ha) (fact_of_mem T hb)
    · intro k ne
      rw [FreshXor.Flat.Table.bag,flatten_ac,List.count_append,List.count_append]
      change ((T.bag a).count k + (T.bag b).count k) % 2 = _
      rw [← pieces_count T a k ne,← pieces_count T b k ne]
      change (L.count k + R.count k) % 2 = _
      rw [left.count_eq k,right.count_eq k,List.count_append,List.count_append]
      omega

end
end Tamarin.Rewriting.BinaryXor
