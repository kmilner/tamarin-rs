import Tamarin.VariantJoinPacked
import Tamarin.VariantJoinSubsumption

/-! An exact family can contain strict specializations and duplicate rows.
Requiring irredundancy determines the observable family up to permutation
and mutual instancehood on all caller images and all normal values. -/
namespace Tamarin.Rewriting.VariantJoin
variable {s : Signature} {I A : Type}

def Row.instanceSetoid : Setoid (Row s I A) where
  r p q := p.Subsumes q ∧ q.Subsumes p
  iseqv := ⟨fun p => ⟨Row.Subsumes.refl p,Row.Subsumes.refl p⟩,
    fun h => ⟨h.2,h.1⟩,fun h k => ⟨h.1.trans k.1,k.2.trans h.2⟩⟩

/-- The same witness substitution must explain every occurrence across
input and output slots in each direction of this equivalence. -/
def Row.instanceClass (r : Row s I A) : Quotient (Row.instanceSetoid (s := s) (I := I) (A := A)) :=
  Quotient.mk _ r

private theorem Irredundant.equal_of_subsumes {rows : List (Row s I A)}
    (h : Irredundant rows) {p q} (hp : p ∈ rows) (hq : q ∈ rows) (sub : p.Subsumes q) : p = q := by
  induction rows with
  | nil => contradiction
  | cons r rows ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hp with rfl|p'
    · rcases List.mem_cons.mp hq with rfl|q'
      · rfl
      · exact ((head _ q').1 sub).elim
    · rcases List.mem_cons.mp hq with rfl|q'
      · exact ((head _ p').2 sub).elim
      · exact ih tail p' q'

private theorem Irredundant.distinct_classes {rows : List (Row s I A)} (h : Irredundant rows) :
    (rows.map Row.instanceClass).Nodup := by
  apply List.pairwise_map.mpr
  apply h.imp
  intro p q ne eq
  exact ne.1 (Quotient.exact eq).1

variable {R : Root s} {keys : List Variable} {query : A → Term s}

/-- Each raw row has its own normalized, typed assignment on the caller's
keys. Testing it against another exact family gives one ordinary sorted
instance witness on the entire row, including the output slots. -/
private theorem Exact.covered_row {rows others : List (Row s (Key keys) A)}
    (family : Exact R Subtype.val query rows) (other : Exact R Subtype.val query others)
    (vars : Normalized R Substitution.identity) {r} (mem : r ∈ rows) (sort : r.Sorted)
    (norm : r.IsNormal R) : ∃ p ∈ others, p.Subsumes r := by
  let σ := r.project sort
  have ns := r.project_normal sort vars norm
  have atRow : Denotes R r (fun i => σ.image i.val) r.value := by
    refine ⟨.identity,vars,?_,?_⟩
    · intro i; rw [Substitution.apply_identity]; exact r.project_key sort i ▸ .refl _
    · intro a; rw [Substitution.apply_identity]; exact .refl _
  have nf := (family σ ns r.value norm.2).mpr ⟨r,mem,atRow⟩
  obtain ⟨p,mp,δ,_,fit⟩ := (other σ ns r.value norm.2).mp nf
  exact ⟨p,mp,δ,fun i => r.project_key sort i ▸ fit.inputs i, fit.values⟩

/-- Comparing implementations requires neither a global normalizer nor an
enumeration order. Both families observe the same caller keys and query slots,
and each row provides normal, sort-respecting caller images and normal values.
No assumption on the behavior of the two solvers off this query is needed. -/
theorem Exact.irredundant_perm {left right : List (Row s (Key keys) A)}
    (l : Exact R Subtype.val query left) (r : Exact R Subtype.val query right)
    (vars : Normalized R Substitution.identity)
    (okL : ∀ p ∈ left, p.Sorted ∧ p.IsNormal R) (okR : ∀ p ∈ right, p.Sorted ∧ p.IsNormal R)
    (il : Irredundant left) (ir : Irredundant right) :
    (left.map Row.instanceClass).Perm (right.map Row.instanceClass) := by
  have incl {as bs : List (Row s (Key keys) A)}
      (a : Exact R Subtype.val query as) (b : Exact R Subtype.val query bs)
      (oka : ∀ p ∈ as, p.Sorted ∧ p.IsNormal R) (okb : ∀ p ∈ bs, p.Sorted ∧ p.IsNormal R)
      (ia : Irredundant as) : as.map Row.instanceClass ⊆ bs.map Row.instanceClass := by
    rintro k hk
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
    obtain ⟨q,hq,qp⟩ := a.covered_row b vars hp (oka _ hp).1 (oka _ hp).2
    obtain ⟨p',hp',p'q⟩ := b.covered_row a vars hq (okb _ hq).1 (okb _ hq).2
    obtain rfl := ia.equal_of_subsumes hp' hp (p'q.trans qp)
    exact List.mem_map.mpr ⟨q,hq,Quotient.sound ⟨qp,p'q⟩⟩
  exact (List.perm_ext_iff_of_nodup il.distinct_classes ir.distinct_classes).mpr fun _ =>
    ⟨fun h => incl l r okL okR il h,fun h => incl r l okR okL ir h⟩

end Tamarin.Rewriting.VariantJoin
