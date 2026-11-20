import Tamarin.BinaryXorClassification
import Tamarin.VariantComposition
import Tamarin.SortedACPaths

/-! A uniform bound for a complete XOR head over arbitrary normal operands.
The common sorted factors cancel as a group, even when ill-sorted factors
surround them in the original AC term. -/
namespace Tamarin.Rewriting.BinaryXor
open ShortVariantPaths ConstructorVariants
variable {sig : Signature} (T : Table sig)

theorem sorted_paths (a b : Term sig) (ha : Good T a) (hb : Good T b) :
    ∃ u, Good T u ∧ Path T.R 2 (.ac T.f a b) u := by
  have ty : HasSort (.ac T.f a b) .msg := T.fSort ▸ HasSort.ac _ _ _ (T.fSort ▸ ha.1) (T.fSort ▸ hb.1)
  obtain ⟨u,nf⟩ := normal_exists T ty T.fSort
    (normalFactors_ac T (fun _ => fact_of_mem T ha) (fun _ => fact_of_mem T hb))
  obtain ⟨shape,⟨h,i,j,gh,gi,gj,left,right,result⟩⟩ := classify T ha hb nf
  exact ⟨u,⟨nf.2.2 _ ty,nf.2.1⟩,((shape_path T shape gh.1 gi.1 gj.1).rebase
    (.ac_congr T.f left right)).post result.symm⟩

theorem kind_paths [DecidableEq sig.ACSym]
    (typed : ∀ {p q}, head p = .ac T.f → T.R p q → HasSort p .msg)
    (a b : Term sig) (na : Normal T.R a) (nb : Normal T.R b) :
    ∃ u, Path T.R 2 (.ac T.f a b) u ∧ Normal T.R u := by
  obtain ⟨u,path,normal,_⟩ := SortedAC.paths T.fSort typed (fun _ _ => True)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (k := 2) (by
      intro x y tx ty nx ny
      obtain ⟨u,gu,p⟩ := sorted_paths T x y ⟨tx,nx⟩ ⟨ty,ny⟩
      exact ⟨u,gu.1,p,gu.2,trivial⟩) a b na nb
  exact ⟨u,path,normal⟩

end Tamarin.Rewriting.BinaryXor
