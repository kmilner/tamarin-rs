import Tamarin.ReferenceMatching
import Tamarin.VariantJoinSubsumption

/-! Folding on Maude variant rows compares the substitution images and the
value tuple under a single matcher. Each insertion retains a representative
for every old row and for the new one. -/
namespace Tamarin.ReferenceVariantFolding
open Rewriting VariantJoin MaudeOperations
variable {s : Signature} {I A : Type}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def subsumes (ins : List I) (outs : List A) (g t : Row s I A) : Bool :=
  let p := rowMatch ins outs g t
  !((ReferenceMatching.matcher s).run p trivial (patternVariables p)).isEmpty

theorem subsumes_iff {ins : List I} {outs : List A} (inputs : ∀ i, i ∈ ins)
    (outputs : ∀ a, a ∈ outs) (g t : Row s I A) :
    subsumes ins outs g t = true ↔ g.Subsumes t := by
  have checked := plain_match (ReferenceMatching.matcher s) (rowMatch ins outs g t) trivial
  simpa [subsumes] using (subsumes_iff_match inputs outputs g t checked).symm

def insert (ins : List I) (outs : List A) (kept : List (Row s I A)) (row : Row s I A) :=
  if kept.any (fun old => subsumes ins outs old row) then kept
  else row :: kept.filter (fun old => !subsumes ins outs row old)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem irred_cons {row : Row s I A} {rows : List (Row s I A)} :
    Irredundant (row :: rows) ↔ (∀ r ∈ rows, ¬row.Subsumes r ∧ ¬r.Subsumes row) ∧ Irredundant rows :=
  List.pairwise_cons

private theorem insert_correct {ins : List I} {outs : List A} (inputs : ∀ i, i ∈ ins)
    (outputs : ∀ a, a ∈ outs) (kept : List (Row s I A)) (row : Row s I A) (irred : Irredundant kept) :
    let result := insert ins outs kept row
    Irredundant result ∧ (∀ r ∈ result, r ∈ row :: kept) ∧
      ∀ r ∈ row :: kept, ∃ g ∈ result, g.Subsumes r := by
  simp only [insert]
  split
  · next accepted =>
    obtain ⟨g,hg,sub⟩ := List.any_eq_true.mp accepted
    refine ⟨irred,fun _ h => List.mem_cons_of_mem _ h,?_⟩
    rintro r hr
    rcases List.mem_cons.mp hr with rfl | old
    · exact ⟨g,hg,(subsumes_iff inputs outputs ..).mp sub⟩
    · exact ⟨r,old,Row.Subsumes.refl r⟩
  · next fresh =>
    refine ⟨irred_cons.mpr ⟨?_,irred.filter _⟩, ?_, ?_⟩
    · intro r hr
      obtain ⟨mem,live⟩ := List.mem_filter.mp hr
      exact ⟨fun h => by simp [(subsumes_iff inputs outputs ..).mpr h] at live,
        fun h => fresh (List.any_eq_true.mpr ⟨r,mem,(subsumes_iff inputs outputs ..).mpr h⟩)⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mp hm).1
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | old
      · exact ⟨_,List.mem_cons_self,Row.Subsumes.refl _⟩
      · by_cases sub : subsumes ins outs row r = true
        · exact ⟨row,List.mem_cons_self,(subsumes_iff inputs outputs ..).mp sub⟩
        · exact ⟨r,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨old,by simpa using sub⟩),Row.Subsumes.refl r⟩

def foldRows (ins : List I) (outs : List A) : List (Row s I A) → List (Row s I A)
  | [] => []
  | r :: rs => insert ins outs (foldRows ins outs rs) r

theorem fold_correct {ins : List I} {outs : List A} (inputs : ∀ i, i ∈ ins)
    (outputs : ∀ a, a ∈ outs) (rows : List (Row s I A)) :
    let result := foldRows ins outs rows
    Irredundant result ∧ (∀ r ∈ result, r ∈ rows) ∧
      ∀ r ∈ rows, ∃ g ∈ result, g.Subsumes r := by
  induction rows with
  | nil => exact ⟨.nil,by simp [foldRows],by simp⟩
  | cons r rs ih =>
    obtain ⟨irred,subset,cover⟩ := ih
    obtain ⟨irred',subset',cover'⟩ := insert_correct inputs outputs _ r irred
    refine ⟨irred',fun a ha => ?_,fun a ha => ?_⟩
    · exact List.mem_cons.mpr ((List.mem_cons.mp (subset' a ha)).imp id (subset a))
    · rcases List.mem_cons.mp ha with rfl | hm
      · exact cover' a List.mem_cons_self
      · obtain ⟨g,hg,sub⟩ := cover a hm
        obtain ⟨k,hk,older⟩ := cover' g (List.mem_cons_of_mem _ hg)
        exact ⟨k,hk,older.trans sub⟩

theorem fold_exact {ins : List I} {outs : List A} (inputs : ∀ i, i ∈ ins)
    (outputs : ∀ a, a ∈ outs) {rules : List (Equation s)} {ids : I → Variable} {query : A → Term s}
    {rows : List (Row s I A)} (family : Exact (ruleRoot rules) ids query rows)
    (vars : Normalized (ruleRoot rules) Substitution.identity) :
    Exact (ruleRoot rules) ids query (foldRows ins outs rows) := by
  obtain ⟨_,subset,cover⟩ := fold_correct inputs outputs rows
  exact family.pruned vars subset (fun r hr _ => cover r hr)

end Tamarin.ReferenceVariantFolding
