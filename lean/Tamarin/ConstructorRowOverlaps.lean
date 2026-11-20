import Tamarin.MixedConstructorRows
import Tamarin.TableNarrowing
import Tamarin.MixedUnification
import Tamarin.FrontierWork

/-! Check competing constructor-pattern rules with the complete ordinary
unifier modulo C/AC. Each competing rule is renamed apart. The same
unifier instantiates both results, including every repeated variable. -/
namespace Tamarin.ConstructorRows
open Rewriting ConstructorVariants ContextualReduction MixedUnification
variable {s : Signature} {rs : Problem s} {r : Equation s}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Each candidate is a symbolic root rewrite on the original pattern.
Anchoring the original RHS preserves its variable images under specialization. -/
def rootAgreement (scope : ReferenceReduction.Bound rs) (r : Equation s) : Bool :=
  (TableNarrowing.roots MixedUnification.verified scope [r.rhs] r.lhs).all fun b =>
    ReferenceMatching.equal b.value (b.subst.apply r.rhs)

theorem rootAgreement_iff (scope : ReferenceReduction.Bound rs) (r : Equation s) :
    rootAgreement scope r ↔ ∀ (σ : Substitution s) v,
      AtRoot (ruleRoot rs) (σ.apply r.lhs) v → EquivB v (σ.apply r.rhs) := by
  constructor
  · intro checked σ v step
    obtain ⟨b,hb,δ,agree,value⟩ := TableNarrowing.roots_cover MixedUnification.verified scope [r.rhs] r.lhs σ step
    have result := (ReferenceMatching.equal_iff ..).mp (List.all_eq_true.mp checked b hb)
    have base := r.rhs.subst_equiv σ.image (δ.compose b.subst).image
      (fun x hx => agree x (.inr ⟨_,List.mem_cons_self,hx⟩))
    change EquivB (σ.apply r.rhs) ((δ.compose b.subst).apply r.rhs) at base
    rw [Substitution.apply_compose] at base
    exact value.trans ((result.subst δ.image).trans base.symm)
  · intro all
    apply List.all_eq_true.mpr
    intro b hb
    apply (ReferenceMatching.equal_iff ..).mpr
    exact all _ _ (TableNarrowing.roots_atRoot _ _ _ _ _ hb)

private def returnedChild (r : Equation s) : Bool :=
  match r.lhs with
  | .free _ xs => (List.finRange _).any fun i => (subterms (xs i)).contains r.rhs
  | .comm _ a b => (subterms a).contains r.rhs || (subterms b).contains r.rhs
  | _ => false

/-- A common free projection path forces both outputs to agree on every
overlap. This includes self-overlap of rules capturing an entire AC expression. -/
private def commonPath (r q : Equation s) : Bool :=
  (DestructorTable.paths r.lhs).any fun p =>
    DestructorTable.atPath r.lhs p == some r.rhs && DestructorTable.atPath q.lhs p == some q.rhs

private theorem commonPath_sound {q : Equation s} (h : commonPath r q) (σ τ : Substitution s)
    (eq : EquivB (σ.apply r.lhs) (τ.apply q.lhs)) : EquivB (σ.apply r.rhs) (τ.apply q.rhs) := by
  obtain ⟨p,_,both⟩ := List.any_eq_true.mp h
  obtain ⟨l,k⟩ := Bool.and_eq_true_iff.mp both
  exact DestructorTable.path_congr eq (DestructorTable.apply_path σ (eq_of_beq l))
    (DestructorTable.apply_path τ (eq_of_beq k))

/-- Check one pair at a time, short-circuiting after a rejected competitor.
The automatic work allowance affects only admission; rootAgreement_iff
characterizes the unrestricted finite check. -/
private def pairAgrees (r q : Equation s) : Bool :=
  !(headEq (head r.lhs) (head q.lhs)) || commonPath r q ||
    (FrontierWork.admitsRootPair r.lhs q.lhs &&
      if h : CheckedReduction.rangeBound [q] then rootAgreement ((CheckedReduction.rangeBound_iff [q]).mp h) r
      else false)

def overlapRow (rs : Problem s) (r : Equation s) : Bool :=
  pattern rs r.lhs && returnedChild r && rs.all (pairAgrees r)

private theorem checks (ok : overlapRow rs r) :
    Pattern rs r.lhs ∧ returnedChild r ∧ ∀ q ∈ rs, pairAgrees r q := by
  obtain ⟨parts,pass⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨pat,child⟩ := Bool.and_eq_true_iff.mp parts
  exact ⟨(pattern_iff ..).mp pat,child,List.all_eq_true.mp pass⟩

private theorem pairAgrees_sound {q : Equation s} (ok : pairAgrees r q)
    (app : Application r.lhs) (other : Application q.lhs) (σ τ : Substitution s)
    (eq : EquivB (σ.apply r.lhs) (τ.apply q.lhs)) : EquivB (τ.apply q.rhs) (σ.apply r.rhs) := by
  rcases Bool.or_eq_true_iff.mp ok with cheap | symbolic
  · rcases Bool.or_eq_true_iff.mp cheap with distinct | path
    · have atHead := (instance_head r app σ).symm.trans (eq.head_eq.trans (instance_head q other τ))
      exact (headEq_false .. |>.mp (by simpa using distinct) atHead).elim
    · exact (commonPath_sound path σ τ eq).symm
  · have certified := (Bool.and_eq_true_iff.mp symbolic).2
    split at certified
    next scope =>
      exact (rootAgreement_iff ((CheckedReduction.rangeBound_iff [q]).mp scope) r).mp certified σ _
        ⟨_,_,eq,⟨q,List.mem_cons_self,τ,rfl,rfl⟩,.refl _⟩
    next => contradiction

theorem overlapRow_subterm (ok : overlapRow rs r) : SubtermVariants.Row r := by
  have h := (checks ok).2.1
  cases src : r.lhs <;> simp [returnedChild,SubtermVariants.Row,src] at h ⊢
  · exact .inr h
  · exact .inr h

theorem overlapRow_result (ok : overlapRow rs r) (mem : r ∈ rs) (apps : ∀ q ∈ rs, Application q.lhs)
    (σ : Substitution s) (norm : Normalized (ruleRoot rs) σ) {u}
    (form : NormalForm (ruleRoot rs) (σ.apply r.lhs) u) : EquivB u (σ.apply r.rhs) := by
  obtain ⟨pat,child,pairs⟩ := checks ok
  have same (v) : AtRoot (ruleRoot rs) (σ.apply r.lhs) v → EquivB v (σ.apply r.rhs) := by
    rintro ⟨_,_,pre,⟨q,hq,τ,rfl,rfl⟩,post⟩
    exact post.symm.trans (pairAgrees_sound (pairs q hq) (apps r mem) (apps q hq) σ τ pre)
  have fire : StepModulo (ruleRoot rs) (σ.apply r.lhs) (σ.apply r.rhs) :=
    ⟨_,_,.refl _,.root ⟨r,mem,σ,rfl,rfl⟩,.refl _⟩
  rcases RootNarrowing.firstStep form.1 with eq | ⟨v,step,tail⟩
  · exact (((normal_equiv _ eq).mpr form.2.1) _ fire).elim
  have eq := same v (root_of_pattern apps σ norm pat step)
  have nf : Normal (ruleRoot rs) (σ.apply r.rhs) := by
    cases src : r.lhs <;> simp [Pattern,returnedChild,src] at pat child
    case free f xs =>
      obtain ⟨i,sub⟩ := child
      exact SubtermVariants.subnormal σ sub ((constructor_normal rs apps).2 (xs i) (pat i) σ norm)
    case comm f a b =>
      rcases child with sub | sub
      · exact SubtermVariants.subnormal σ sub ((constructor_normal rs apps).2 a pat.1 σ norm)
      · exact SubtermVariants.subnormal σ sub ((constructor_normal rs apps).2 b pat.2 σ norm)
  exact (normal_reduces_equiv tail ((normal_equiv _ eq).mpr nf)).symm.trans eq

end Tamarin.ConstructorRows
