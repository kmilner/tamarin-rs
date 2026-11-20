import Tamarin.DHChurchRosserAlgebra
import Tamarin.DHKindProducts
import Tamarin.SortedACNormalAlgebra

/-! Multiplication on normal classes at the common kind. Ill-sorted factors
persist as a multiset. The maximal Msg-sorted subbag is determined by its
signed multiplicities and by whether a sorted factor was present at all.
The latter distinction retains a unit adjacent to wholly ill-sorted factors. -/
namespace Tamarin.Rewriting.DHPeer.ChurchRosser
open Balance Cancellation ShortVariantPaths NormalAlgebra
variable {sig : Signature} {s : Symbols sig} {R : Root sig} {T : Table s} {E : ExtraTable T}
variable [DecidableEq sig.ACSym]

private noncomputable def weight (s : Symbols sig) (R : Root sig) (k : Class sig) : Class sig → Int :=
  Quotient.lift (fun t => (read s R k t).getD 0) (fun _ _ h => congrArg (fun p => p.getD 0) (equiv s R k h))

private theorem raw_count (k : Class sig) (t : Term sig) (nt : Normal R t) :
    ((flatten s.mul t).map (weight s R k)).sum = (read s R k t).getD 0 := by
  induction t with
  | ac f a b ih ik =>
    by_cases h : s.mul = f
    · subst f
      obtain ⟨na,nb⟩ := normal_ac_children _ nt
      obtain ⟨x,hx⟩ := defined s R k na
      obtain ⟨y,hy⟩ := defined s R k nb
      have rd := read_mul s R k a b
      change read s R k (.ac s.mul a b) = _ at rd
      simp [flatten_ac,ih na,ik nb,rd,hx,hy,plus]
    · simp [flatten,h,weight,classOf] <;> rfl
  | _ => simp [flatten,weight,classOf] <;> rfl

private noncomputable def multiplicity (s : Symbols sig) (R : Root sig) (k : Class sig) (xs : List (Class sig)) :=
  (xs.map (weight s R k)).sum

private theorem typed_read {t : Term sig} (nt : Normal R t) (k) :
    read s R k t = some (multiplicity s R k (flatten s.mul t)) := by
  obtain ⟨n,eq⟩ := defined s R k nt
  simp only [multiplicity,raw_count k t nt,eq]; rfl

private noncomputable def signed (E : ExtraTable T) : SortedAC.ProductInvariant s.mul (ruleRoot T.rules) where
  rel xs ys := ∀ k, multiplicity s (ruleRoot T.rules) k xs = multiplicity s (ruleRoot T.rules) k ys
  ofPerm := by
    intro a b perm k
    unfold multiplicity
    induction perm with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap => simp [Int.add_left_comm]
    | trans _ _ l r => exact l.trans r
  symm h k := (h k).symm
  trans h i k := (h k).trans (i k)
  append := by
    intro a b c d h i k
    simp only [multiplicity,List.map_append,List.sum_append_int] at *
    rw [h k,i k]
  distinguish := by
    intro x y tx ty nx ny h
    obtain ⟨_,_,cx⟩ := decompose E.presentation (fun _ => plain_of_inverse E) tx nx
    obtain ⟨_,_,cy⟩ := decompose E.presentation (fun _ => plain_of_inverse E) ty ny
    exact cx.injective cy (fun k => by rw [typed_read nx,typed_read ny,h k])

/-- Signed multiplicities distinguish normal sorted products. The general AC
construction retains the surrounding ill-sorted factors at the common kind. -/
noncomputable def protectedProduct (tab : ProtectedTable E) : Product s (ruleRoot T.rules) := by
  let bounds := product_paths tab.inventory tab.product tab.inverse tab.unit
  let k := bounds.choose
  have go := bounds.choose_spec
  apply (signed E).product s.mulSort tab.product.redex_typed (k := k)
  intro x y tx ty nx ny
  obtain ⟨u,tu,path,nu⟩ := go x y tx ty nx ny
  refine ⟨u,tu,path,nu,?_⟩
  intro j
  have readXY : read s (ruleRoot T.rules) j (s.product.mul x y) =
      some (multiplicity s (ruleRoot T.rules) j (flatten s.mul (s.product.mul x y))) := by
    rw [read_mul,typed_read nx,typed_read ny]
    simp [multiplicity,DHProduct.Ops.mul,Symbols.product,flatten_ac,plus]
  exact Option.some.inj ((tab.inventory.reduces j path.reduces _ readXY).symm.trans (typed_read nu j))

/-- Specialize the operation to a table containing exactly the DH rules. -/
noncomputable def kindProduct (tab : ExactTable E) : Product s (ruleRoot T.rules) :=
  protectedProduct tab.protectedTable

end Tamarin.Rewriting.DHPeer.ChurchRosser
