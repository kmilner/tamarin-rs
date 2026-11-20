import Tamarin.NarrowingFrontier
import Tamarin.TableDecrease

/-! Newman's lemma for Tamarin's actual reduction relation, including free,
C and AC congruence and rewriting up to B at every position. A terminating
presentation needs joinability only for pairs of single genuine steps. -/
namespace Tamarin.TableConfluence
open Rewriting MaudeOperations
variable {s : Signature} {R : Root s}

def Joinable (R : Root s) (a b : Term s) : Prop :=
  ∃ w, Reduces R a w ∧ Reduces R b w

def LocalConfluence (R : Root s) : Prop :=
  ∀ {t a b}, StepModulo R t a → StepModulo R t b → Joinable R a b

private theorem hasNormal (wf : WellFounded (fun b a => StepModulo R a b)) (t : Term s) :
    ∃ n, Reduces R t n ∧ Normal R n := by
  induction t using wf.induction with
  | h t ih =>
    by_cases hasStep : ∃ u, StepModulo R t u
    · obtain ⟨u,step⟩ := hasStep
      obtain ⟨v,tail,nf⟩ := ih u step
      exact ⟨v,(Reduces.step step).trans tail,nf⟩
    · exact ⟨t,.basis (.refl _),fun u st => hasStep ⟨u,st⟩⟩

private theorem uniqueNormal (wf : WellFounded (fun b a => StepModulo R a b))
    (peaks : LocalConfluence R) (t : Term s) : ∀ {a b},
    Reduces R t a → Reduces R t b → Normal R a → Normal R b → EquivB a b := by
  induction t using wf.induction with
  | h t ih =>
    intro a b left right na nb
    rcases RootNarrowing.firstStep left with same | ⟨u,su,ua⟩
    · exact normal_reduces_equiv ((Reduces.basis same.symm).trans right) na
    rcases RootNarrowing.firstStep right with same | ⟨v,sv,vb⟩
    · exact (normal_reduces_equiv ((Reduces.basis same.symm).trans left) nb).symm
    obtain ⟨w,uw,vw⟩ := peaks su sv
    obtain ⟨n,wn,normal⟩ := hasNormal wf w
    exact (ih u su ua (uw.trans wn) na normal).trans
      (ih v sv (vw.trans wn) vb normal nb)

/-- Local joins may use different B representatives or take multiple steps
on either side. Neither a one-step diamond nor deterministic rules are required. -/
theorem ofLocal (wf : WellFounded (fun b a => StepModulo R a b)) (peaks : LocalConfluence R)
    (sorts : ∀ {a b}, StepModulo R a b → ∀ k, HasSort a k → HasSort b k) :
    CanonicalPresentation R where
  terminating := wf
  sortPreserving := sorts
  confluent left right := by
    obtain ⟨a,la,na⟩ := hasNormal wf _
    obtain ⟨b,rb,nb⟩ := hasNormal wf _
    have eq := uniqueNormal wf peaks _ (left.trans la) (right.trans rb) na nb
    exact ⟨b,la.trans (.basis eq),rb⟩

/-- At each source it suffices to join the finitely many representatives of
its one-step results. This includes rewriting strict AC subproducts. -/
theorem local_iff_successors [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] {rules : List (Equation s)}
    (bound : ReferenceReduction.Bound rules) : LocalConfluence (ruleRoot rules) ↔
      ∀ t, ∀ a ∈ ReferenceReduction.successors rules t, ∀ b ∈ ReferenceReduction.successors rules t,
        Joinable (ruleRoot rules) a b := by
  constructor
  · intro peaks t a ha b hb
    exact peaks ((ReferenceReduction.exactSteps rules bound ..).mp ⟨a,ha,.refl _⟩)
      ((ReferenceReduction.exactSteps rules bound ..).mp ⟨b,hb,.refl _⟩)
  · intro pairs t a b sa sb
    obtain ⟨u,hu,ea⟩ := (ReferenceReduction.exactSteps rules bound ..).mpr sa
    obtain ⟨v,hv,eb⟩ := (ReferenceReduction.exactSteps rules bound ..).mpr sb
    obtain ⟨w,uw,vw⟩ := pairs t u hu v hv
    exact ⟨w,(Reduces.basis ea.symm).trans uw,(Reduces.basis eb.symm).trans vw⟩

/-- Completes the two syntactic table checks with the sole remaining local
peak obligation. The resulting presentation can be used by any rewrite strategy. -/
theorem ofDecreasing {rules : List (Equation s)} (decrease : TableDecrease.decreasing rules)
    (sorts : TableDecrease.sorted rules) (peaks : LocalConfluence (ruleRoot rules)) :
    CanonicalPresentation (ruleRoot rules) :=
  ofLocal (TableDecrease.terminating decrease) peaks (TableDecrease.sortPreserving sorts)

end Tamarin.TableConfluence
