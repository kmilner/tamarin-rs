import Tamarin.ACEquationExtensions
import Tamarin.FoldingNarrowing

/-! One-step narrowing from the same ordinary unifier used by Maude's unify
command. Every rule application is independently renamed apart from the whole
query. A lifted branch retains all input variables and untouched observations. -/
namespace Tamarin.TableNarrowing
open Rewriting RootNarrowing VariantJoin ContextualReduction
variable {s : Signature}

private def apart (r : Equation s) (t : Term s) (anchors : List (Term s)) :=
  FreshAnswer.freshPermutation r.lhs.variables ((t :: anchors).flatMap Term.variables) (Substitution.identity (sig := s))

private def schema {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (t : Term s) (anchors : List (Term s)) (r : {r // r ∈ rules}) :=
  Schema.openRule rules r.val r.property (bound _ r.property) (apart r.val t anchors)

private theorem fresh {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (t : Term s) (anchors : List (Term s)) (r : {r // r ∈ rules}) (v : Variable)
    (occ : (schema bound t anchors r).lhs.Occurs v) : ¬(t.Occurs v ∨ Observed anchors v) := by
  obtain ⟨w,hw,rfl⟩ := (Term.occurs_rename r.val.lhs (apart r.val t anchors).forward v).mp occ
  have mem : w ∈ FreshAnswer.rangeVariables r.val.lhs.variables (Substitution.identity (sig := s)) :=
    List.mem_flatMap.mpr ⟨w,(r.val.lhs.mem_variables w).mpr hw,by simp [Substitution.identity,Term.variables]⟩
  have disjoint := FreshAnswer.renaming_avoids _ ((t :: anchors).flatMap Term.variables) _ w mem
  intro seen
  apply disjoint
  apply List.mem_append_left
  simpa [apart,List.mem_flatMap,Observed] using seen

private def atSchema (u : VerifiedUnifier s (fun _ => True)) {R : Root s} (t : Term s)
    (anchors : List (Term s)) (p : Schema R) : List (Branch s) :=
  (u.solve (p.problem t) trivial (anchors.flatMap Term.variables)).map fun μ => ⟨μ,μ.apply p.rhs⟩

def roots (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (anchors : List (Term s)) (t : Term s) : List (Branch s) :=
  rules.attach.flatMap fun r => atSchema u t anchors (schema bound t anchors r)

theorem roots_genuine (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (anchors : List (Term s)) (t : Term s) (b : Branch s) (hb : b ∈ roots u bound anchors t) :
    StepModulo (ruleRoot rules) (b.subst.apply t) b.value := by
  obtain ⟨r,_,hm⟩ := List.mem_flatMap.mp hb
  obtain ⟨μ,hμ,rfl⟩ := List.mem_map.mp hm
  exact (schema bound t anchors r).replay t (u.correct _ trivial _) hμ

theorem roots_cover (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (anchors : List (Term s)) (t : Term s) (ρ : Substitution s) {v} (fire : AtRoot (ruleRoot rules) (ρ.apply t) v) :
    ∃ b ∈ roots u bound anchors t, FitsOn (fun w => t.Occurs w ∨ Observed anchors w) ρ v b.subst b.value := by
  obtain ⟨_,_,left,⟨r,hr,τ,rfl,rfl⟩,right⟩ := fire
  let i := (⟨r,hr⟩ : {p // p ∈ rules})
  let p := schema bound t anchors i
  have presents : p.Presents r := ⟨apart r t anchors,rfl,rfl⟩
  obtain ⟨η,l,h⟩ := presents.instance τ
  let reserved := anchors.flatMap Term.variables
  have safe (μ) (hμ : μ ∈ u.solve (p.problem t) trivial reserved) : Reserves (p.problem t) anchors μ :=
    Reserves.of_scoped (u.domain _ trivial _ μ hμ) (u.fresh _ trivial _ μ hμ)
      (fun w hw => by simpa [reserved,List.mem_flatMap,Observed] using hw.1)
  obtain ⟨μ,hμ,fit⟩ := (p.lift_in_context t anchors (fresh bound t anchors i)
    (u.correct _ trivial reserved) safe ρ v).mp ⟨η,l ▸ left,h ▸ right.symm⟩
  exact ⟨_,List.mem_flatMap.mpr ⟨i,List.mem_attach _ i,List.mem_map_of_mem hμ⟩,fit⟩

/-- Ordinary unification at an augmented root includes all proper AC
subproduct transitions when the specialized product has the operator's sort. -/
theorem ac_cover (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)} (base : ReferenceReduction.Bound rules)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs) (f : s.ACSym) (anchors : List (Term s))
    (t : Term s) (ρ : Substitution s) {v} (typed : HasSort (ρ.apply t) (s.acSort f))
    (step : ACSubproductReduction.Occurrence (ruleRoot rules) f (ρ.apply t) v) :
    ∃ b ∈ roots u (ACEquationExtensions.bound base) anchors t,
      FitsOn (fun w => t.Occurs w ∨ Observed anchors w) ρ v b.subst b.value :=
  roots_cover u _ _ _ _ (ACEquationExtensions.atRoot_of_occurrence rules base apps f _ _ typed step)

theorem extended_genuine (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)}
    (base : ReferenceReduction.Bound rules) (anchors : List (Term s)) (t : Term s) (b : Branch s)
    (hb : b ∈ roots u (ACEquationExtensions.bound base) anchors t) :
    StepModulo (ruleRoot rules) (b.subst.apply t) b.value :=
  (ACEquationExtensions.modulo rules ..).mp (roots_genuine u _ anchors t b hb)

end Tamarin.TableNarrowing
