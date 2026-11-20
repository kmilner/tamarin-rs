import Tamarin.CheckedVariantAgreement
import Tamarin.CompleteNarrowing
import Tamarin.FrontierWork

/-! A finite family can be complete while specializing two of its rows to
the same input gives distinct normal values. Re-open the right row even
for self-overlap, unify all input images, and check the two result terms
on every surviving ordinary unifier. -/
namespace Tamarin.CheckedVariants
open Rewriting MaudeOperations VariantJoin RootNarrowing ReferenceVariantFrontier
variable {s : Signature} {n : Nat} {rs : List (Equation s)}

def UniqueValues (R : Root s) (q : List (Term s)) : Prop :=
  ∀ ρ : Substitution s, Normalized R ρ → ∀ xs ys,
    Aligned (fun t u => NormalForm R (ρ.apply t) u) q xs →
    Aligned (fun t u => NormalForm R (ρ.apply t) u) q ys → Aligned EquivB xs ys

structure Reply (R : Root s) (q : List (Term s)) (rows : List (Variant s)) : Prop
    extends VariantReply R q [] rows where
  unique : UniqueValues R q

private def variables {I : Type} (keys : List I) (p : State s I) :=
  (p.value () :: keys.map p.input).flatMap Term.variables

private theorem variables_iff {I : Type} (keys : List I) (allKeys : ∀ i, i ∈ keys) (p : State s I) (v) :
    v ∈ variables keys p ↔ p.Uses v := by
  simp [variables,Row.Uses,List.mem_flatMap,allKeys]
  constructor
  · rintro (h | ⟨t,⟨i,rfl⟩,h⟩)
    · exact .inr ⟨(),h⟩
    · exact .inl ⟨i,h⟩
  · rintro (⟨i,h⟩ | ⟨⟨⟩,h⟩)
    · exact .inr ⟨_,⟨i,rfl⟩,h⟩
    · exact .inl h

private def names {I : Type} (keys : List I) (p q : State s I) :=
  FreshAnswer.freshPermutation (variables keys q) (variables keys p) (Substitution.identity (sig := s))

private def opened {I : Type} (keys : List I) (p q : State s I) : State s I :=
  let rename := ((names keys p q).subst s).apply
  ⟨fun i => rename (q.input i),fun i => rename (q.value i)⟩

private theorem disjoint {I : Type} (ks : List I) (allKeys : ∀ i, i ∈ ks) (p q : State s I)
    (v) (left : p.Uses v) (right : (opened ks p q).Uses v) : False := by
  let π := names ks p q
  have away (t : Term s) (inside : ∀ w, t.Occurs w → q.Uses w)
      (occur : ((π.subst s).apply t).Occurs v) : False := by
    obtain ⟨w,hw,rfl⟩ := (Term.occurs_rename t π.forward v).mp occur
    have mem := (variables_iff ks allKeys q w).mpr (inside w hw)
    have hit : w ∈ FreshAnswer.rangeVariables (variables ks q) (Substitution.identity (sig := s)) :=
      List.mem_flatMap.mpr ⟨w,mem,by simp [Substitution.identity,Term.variables]⟩
    exact FreshAnswer.renaming_avoids _ (variables ks p) _ w hit
      (List.mem_append_left _ ((variables_iff ks allKeys p _).mpr left))
  rcases right with ⟨i,h⟩|⟨i,h⟩
  · exact away _ (fun w hw => .inl ⟨i,hw⟩) h
  · exact away _ (fun w hw => .inr ⟨i,hw⟩) h

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def differentImpossible (rs : List (Equation s)) (fuel : Nat) (a b : Term s) :=
  FrontierWork.admits rs [a,b] (fuel+1) &&
    (ReferenceMatching.equal a b || !(ReferenceReduction.successors rs a).isEmpty ||
      !(ReferenceReduction.successors rs b).isEmpty)

private theorem sameIfNormal (bound : ReferenceReduction.Bound rs) (fuel : Nat) (a b : Term s)
    (ok : differentImpossible rs fuel a b) (na : Normal (ruleRoot rs) a) (nb : Normal (ruleRoot rs) b) : EquivB a b := by
  have no (t : Term s) (norm : Normal (ruleRoot rs) t) : (ReferenceReduction.successors rs t).isEmpty = true := by
    apply List.isEmpty_iff.mpr
    exact List.eq_nil_iff_forall_not_mem.mpr (fun u hu => norm u ((ReferenceReduction.exactSteps _ bound ..).mp ⟨u,hu,.refl _⟩))
  exact (ReferenceMatching.equal_iff ..).mp (by simpa [differentImpossible,no _ na,no _ nb] using (Bool.and_eq_true_iff.mp ok).2)

private def checkPair {I : Type} (rs : List (Equation s)) (fuel : Nat) (ks : List I) (p q : State s I) :=
  let r := opened ks p q
  let problem := VariantJoin.problem p r ks []
  let keep := [p.value (),r.value ()].flatMap Term.variables
  let u := MixedUnification.verified (s := s)
  let fields := problem.variables.eraseDups.length
  (determined ks p q fuel).val ||
    (5 ^ min 12 fields ≤ 1024 * (fuel+1) &&
    FrontierWork.admits [] (problem.flatMap fun e => [e.lhs,e.rhs]) (fuel+1)) &&
    (u.solve problem trivial keep).all fun μ =>
      differentImpossible rs fuel (μ.apply (p.value ())) (μ.apply (r.value ()))

private theorem pair_correct {I : Type} (bound : ReferenceReduction.Bound rs)
    (vars : Normalized (ruleRoot rs) Substitution.identity) (fuel : Nat) (ks : List I) (allKeys : ∀ i, i ∈ ks)
    (p q : State s I) (ok : checkPair rs fuel ks p q) : CompatibleValues (ruleRoot rs) p q := by
  rcases Bool.or_eq_true_iff.mp ok with known | ok
  · exact ((determined ks p q fuel).property known).agrees.compatible
  let r := opened ks p q
  let u := MixedUnification.verified (s := s)
  let problem := VariantJoin.problem p r ks []
  let keep := [p.value (),r.value ()].flatMap Term.variables
  let answers := u.solve problem trivial keep
  apply compatible_of_csu vars p q r ⟨names ks p q,fun _ => .refl _,fun _ => .refl _⟩ (disjoint ks allKeys p q)
    ks allKeys answers (u.correct ..)
  · intro μ hm
    apply Reserves.of_scoped (u.domain _ trivial _ μ hm) (u.fresh _ trivial _ μ hm)
    exact fun w hw => by simpa [keep,List.mem_flatMap,Observed] using hw.1
  · intro μ hm normal
    exact sameIfNormal bound fuel _ _ (List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 μ hm)
      (normal.2 (.inl ())) (normal.2 (.inr ()))

private def coordinate (keys : List Variable) (p : Point s n) (i : Fin n) : State s (Key keys) :=
  ⟨(p.row keys).input,fun _ => p.value i⟩

def compatible (rs : List (Equation s)) (fuel : Nat) (keys : List Variable) (points : List (Point s n)) :=
  n * points.length * points.length ≤ 256 * (fuel+1) &&
    points.all fun p => points.all fun q => (List.finRange n).all fun i =>
    checkPair rs fuel keys.attach (coordinate keys p i) (coordinate keys q i)

theorem unique_of_checked (bound : ReferenceReduction.Bound rs) (vars : Normalized (ruleRoot rs) Substitution.identity)
    (query : Fin n → Term s) (fuel : Nat) (points : List (Point s n))
    (family : CompleteVariants (ruleRoot rs) (List.ofFn query) (points.map (Point.answer · (keysOf query))))
    (ok : compatible rs fuel (keysOf query) points) : UniqueValues (ruleRoot rs) (List.ofFn query) := by
  let keys := keysOf query
  intro ρ nρ xs ys left right
  obtain ⟨a,rfl,normA⟩ := read_aligned query xs left
  obtain ⟨b,rfl,normB⟩ := read_aligned query ys right
  have getRow (endpoints : Fin n → Term s)
      (nf : ∀ i, NormalForm (ruleRoot rs) (ρ.apply (query i)) (endpoints i)) :
      ∃ p ∈ points, ∀ i, Denotes (ruleRoot rs) (coordinate keys p i) (fun j => ρ.image j.val)
        (fun _ => endpoints i) := by
    obtain ⟨_,mem,δ,nδ,hit,values⟩ := family.2 ρ nρ _ (alignedFn query endpoints nf)
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
    refine ⟨p,hp,fun i => ⟨δ,nδ,fun j => ?_,fun _ => ?_⟩⟩
    · have h := hit j.val ((observed query j.val).mp j.property)
      change EquivB _ (δ.apply (((p.row keys).project (fun k => p.assignment.sorted k.val)).image j.val)) at h
      rwa [(p.row keys).project_key (fun k => p.assignment.sorted k.val) j] at h
    · exact VariantSaturation.atFn endpoints p.value values i
  obtain ⟨p,hp,pa⟩ := getRow a normA
  obtain ⟨q,hq,qb⟩ := getRow b normB
  apply alignedFn
  intro i
  have good := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 p hp) q hq) i (List.mem_finRange _)
  exact pair_correct bound vars fuel _ (List.mem_attach keys) _ _ good _ _ _ (fun j => nρ j.val)
    (normA i).2.1 (normB i).2.1 (pa i) (qb i)

end Tamarin.CheckedVariants
