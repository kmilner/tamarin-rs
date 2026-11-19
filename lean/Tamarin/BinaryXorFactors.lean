import Tamarin.BinaryXor
import Tamarin.SortClash

/-! A normalized AC sum consists of distinct normal factors, or the unit.
Individual factors are identified modulo the full structural theory B. -/
namespace Tamarin.Rewriting.BinaryXor
open Cancellation ACRepresentation
variable {sig : Signature} (T : Table sig)
noncomputable section
open Classical

abbrev rep (k : Class sig) : Term sig := (Quotient.exists_rep k).choose
theorem rep_key (k : Class sig) : classOf (rep k) = k := (Quotient.exists_rep k).choose_spec

def Fact (k : Class sig) : Prop := Good T (rep k) ∧ T.bag (rep k) = [k]

theorem sort_equiv {a b : Term sig} (e : EquivB a b) (h : HasSort a .msg) : HasSort b .msg :=
  Term.checkSort_sound _ _ (SortClash.check_equiv e _ ▸ Term.checkSort_complete h)

theorem fact_of_mem {t : Term sig} (good : Good T t) {k : Class sig} (hk : k ∈ T.bag t) : Fact T k := by
  rw [FreshXor.Flat.Table.bag,DHProduct.classes] at hk
  obtain ⟨a,ha,eq⟩ := List.mem_map.mp hk
  have e : EquivB a (rep k) := Quotient.exact (eq.trans (rep_key k).symm)
  have hn := ((DHProduct.subgroup_normal_iff T.f t).mp good.2).1 a ha
  have hs := ACRepresentation.flatten_hasSort T.f t (T.fSort ▸ good.1) a ha
  refine ⟨⟨sort_equiv e (T.fSort ▸ hs), (normal_equiv _ e).mp hn⟩,?_⟩
  have perm := (flatten_equiv T.f e).symm
  rw [DHProduct.atom_factors _ _ _ ha,eq] at perm
  exact List.perm_singleton.mp perm

theorem dup_msg {a : Term sig} (h : HasSort a .msg) : T.R (.ac T.f a a) T.zero := by
  let σ := Substitution.binding T.param a (T.paramSort ▸ h)
  refine ⟨_,T.duplicate,σ,?_,(T.toTable.fixes_zero σ).symm⟩
  simp [σ,Substitution.binding,Substitution.apply,Term.subst]

private theorem blocked {t p v : Term sig} (normal : Normal T.R t) (sub : DHProduct.Subbag T.f p t)
    (step : T.R p v) : False := by
  rcases sub.context with eq | ⟨rest,eq⟩
  · exact normal _ ⟨_,_,eq,.root step,.refl _⟩
  · exact normal _ ⟨_,_,eq,.ac_left _ rest (.root step),.refl _⟩

theorem nodup {t : Term sig} (good : Good T t) : (T.bag t).Nodup := by
  apply List.nodup_iff_count.mpr
  intro k
  apply Classical.byContradiction; intro h
  have pos := List.count_pos_iff.mp (show 0 < (T.bag t).count k by omega)
  have fact := fact_of_mem T good pos
  have perm := List.perm_cons_erase pos
  have cnt := perm.count_eq k
  rw [List.count_cons_self] at cnt
  have more := List.count_pos_iff.mp (show 0 < ((T.bag t).erase k).count k by omega)
  have both := perm.trans ((List.perm_cons_erase more).cons k)
  apply blocked T good.2 (p := .ac T.f (rep k) (rep k)) _ (dup_msg T fact.1.1)
  refine ⟨((T.bag t).erase k).erase k,?_⟩
  change (T.bag t).Perm (T.bag (.ac T.f (rep k) (rep k)) ++ _)
  rw [FreshXor.Flat.Table.bag,flatten_ac]
  change (T.bag t).Perm ((T.bag (rep k) ++ T.bag (rep k)) ++ _)
  rw [fact.2]
  exact both

theorem unit_alone {t : Term sig} (good : Good T t) (hz : T.zeroClass ∈ T.bag t) :
    T.bag t = [T.zeroClass] := by
  have perm := List.perm_cons_erase hz
  cases e : (T.bag t).erase T.zeroClass with
  | nil => rw [e] at perm; exact List.perm_singleton.mp perm
  | cons k ks =>
    rw [e] at perm
    have mem := perm.mem_iff.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
    have fact := fact_of_mem T good mem
    apply False.elim (blocked T good.2 (p := .ac T.f (rep k) T.zero) _ (T.unit fact.1.1))
    refine ⟨ks,?_⟩
    change (T.bag t).Perm (T.bag (.ac T.f (rep k) T.zero) ++ ks)
    rw [FreshXor.Flat.Table.bag,flatten_ac]
    change (T.bag t).Perm ((T.bag (rep k) ++ T.bag T.zero) ++ ks)
    rw [fact.2,T.bag_zero]
    exact perm.trans (List.Perm.swap ..)

theorem pure_good {t : Term sig} (g : Good T t) :
    T.PureFrom (fun _ => True) t := by
  intro k hk
  exact Or.inr ⟨rep k,trivial,(fact_of_mem T g hk).1.2,rep_key k⟩

def pieces (t : Term sig) := (T.bag t).filter fun k => k != T.zeroClass

theorem pieces_count (t : Term sig) (k : Class sig) (ne : k ≠ T.zeroClass) :
    (pieces T t).count k = (T.bag t).count k := by simp [pieces,List.count_filter,ne]

theorem bag_of_pieces {t : Term sig} (g : Good T t) :
    T.bag t = if (pieces T t).isEmpty then [T.zeroClass] else pieces T t := by
  by_cases hz : T.zeroClass ∈ T.bag t
  · rw [pieces,unit_alone T g hz]; simp
  · have eq : pieces T t = T.bag t := List.filter_eq_self.mpr fun k hk => by
        have ne : k ≠ T.zeroClass := fun h => hz (h ▸ hk)
        simp [ne]
    rw [eq]
    cases e : T.bag t with
    | nil => exact False.elim (T.bag_nonempty t e)
    | cons => rfl

/-- Parity at the nonunit classes determines any normal, typed output. -/
theorem normal_eq {s t : Term sig} (gs : Good T s) (gt : Good T t)
    (same : ∀ k, k ≠ T.zeroClass → (T.bag s).count k % 2 = (T.bag t).count k % 2) : EquivB s t := by
  have perm : (pieces T s).Perm (pieces T t) := by
    apply List.perm_iff_count.mpr
    intro k
    by_cases ne : k ≠ T.zeroClass
    · rw [pieces_count T _ k ne,pieces_count T _ k ne]
      have h := same k ne
      have a := List.nodup_iff_count.mp (nodup T gs) k
      have b := List.nodup_iff_count.mp (nodup T gt) k
      omega
    · obtain rfl := Classical.not_not.mp ne
      have absent (t : Term sig) : T.zeroClass ∉ pieces T t := by simp [pieces]
      rw [List.count_eq_zero.mpr (absent _),List.count_eq_zero.mpr (absent _)]
  apply equiv_of_flatten_perm T.f
  change (T.bag s).Perm (T.bag t)
  rw [bag_of_pieces T gs,bag_of_pieces T gt]
  have e : (pieces T s).isEmpty = (pieces T t).isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff_length_eq_zero,perm.length_eq]
  rw [e]
  split <;> first | exact .refl _ | exact perm

/-- Uniqueness only needs a typed input whose opaque nonunit factors
have normal representatives. The input itself can still contain redexes. -/
theorem unique_of_pure {t u v : Term sig} (sort : HasSort t .msg) (pure : T.PureFrom (fun _ => True) t)
    (nu : NormalForm T.R t u) (nv : NormalForm T.R t v) : EquivB u v := by
  have pu := T.reduces_kept nu.1 pure
  have pv := T.reduces_kept nv.1 pure
  exact normal_eq T ⟨nu.2.2 _ sort,nu.2.1⟩ ⟨nv.2.2 _ sort,nv.2.1⟩ fun k ne =>
    (pu.2 k ne).symm.trans (pv.2 k ne)

theorem unique {a b u v : Term sig} (ha : Good T a) (hb : Good T b)
    (nu : NormalForm T.R (.ac T.f a b) u) (nv : NormalForm T.R (.ac T.f a b) v) : EquivB u v := by
  have sort : HasSort (.ac T.f a b) .msg := T.fSort ▸ HasSort.ac T.f _ _ (T.fSort ▸ ha.1) (T.fSort ▸ hb.1)
  have pure := (T.pure_ac ..).mpr ⟨pure_good T ha,pure_good T hb⟩
  exact unique_of_pure T sort pure nu nv

end
end Tamarin.Rewriting.BinaryXor
