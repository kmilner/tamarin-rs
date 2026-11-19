import Tamarin.ACUnifierExclusion
import Tamarin.RecursiveACMatch
import Tamarin.ACSubgroups

/-! A successful binary AC root reduction needs a genuine directional match
and agreement of every match of the active rules. In particular a variable
of the subject is never specialized to make the rule applicable. -/
namespace Tamarin.Rewriting.ACRootReduction
open ConstructorVariants Cancellation RecursiveACMatch NestedTreeMatch
variable {s : Signature}

/-- The same sorted rule substitution is tested at both positions. Each
directional search observes a single operand of the prepared rule. -/
def Branch [DecidableEq s.ACSym] (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : RecursiveACMatch.Cancellation) (l r a b rhs out : Term s) : Prop :=
  ∃ (enc : Encoding s) (left right : Observation s) (arms : List (Substitution s)),
    Search select flat orient cancel enc l a left ∧ Search select flat orient cancel enc r b right ∧
    (∀ σ, left σ → right σ → ∃ θ ∈ arms,
      Substitution.AgreesOn (fun v => l.Occurs v ∨ r.Occurs v) σ θ) ∧
    (∀ θ ∈ arms, (∀ v, rhs.Occurs v → l.Occurs v ∨ r.Occurs v) ∧ EquivB (θ.apply rhs) out)

private theorem Branch.agrees [DecidableEq s.ACSym] {select flat orient cancel}
    (verified : RecursiveACMatch.Correct select flat orient cancel) {l r a b rhs out : Term s}
    (branch : Branch select flat orient cancel l r a b rhs out) (σ : Substitution s)
    (left : EquivB (σ.apply l) a) (right : EquivB (σ.apply r) b) : EquivB (σ.apply rhs) out := by
  obtain ⟨_,_,_,_,hl,hr,coverage,outputs⟩ := branch
  have rl := ((verified hl l a (.refl _) (.refl _) [] σ).mp (by simpa [Matching.Matches] using left)).1
  have rr := ((verified hr r b (.refl _) (.refl _) [] σ).mp (by simpa [Matching.Matches] using right)).1
  obtain ⟨θ,hm,agree⟩ := coverage σ rl rr
  obtain ⟨scope,eq⟩ := outputs θ hm
  exact (rhs.subst_equiv σ.image θ.image fun v h => agree v (scope v h)).trans eq

/-- AC operands are counted before matching; shapes longer than two cannot
fit. A binary pattern is prepared modulo B and tried in both alignments.
The successful candidate also replays an active rule, so an empty search
cannot manufacture a normal answer. -/
def Semantic (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : RecursiveACMatch.Cancellation) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (rules : List (Equation s))
    (_ : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (a b out : Term s),
    flatten f a = [classOf a] → flatten f b = [classOf b] →
    Normal (ruleRoot rules) a → Normal (ruleRoot rules) b →
    Normal (ruleRoot rules) out → HasSort out (s.acSort f) →
    (∃ rule ∈ rules, ∃ σ : Substitution s, EquivB (.ac f a b) (σ.apply rule.lhs) ∧ EquivB (σ.apply rule.rhs) out) →
    (∀ rule ∈ rules, head rule.lhs = .ac f →
      2 < (flatten f rule.lhs).length ∨ ∃ l r, EquivB rule.lhs (.ac f l r) ∧
        Branch select flat orient cancel l r a b rule.rhs out ∧
        Branch select flat orient cancel l r b a rule.rhs out) →
    NormalForm (ruleRoot rules) (.ac f a b) out ∧
      ∀ u, NormalForm (ruleRoot rules) (.ac f a b) u → EquivB u out

theorem semantic {select flat orient cancel} (verified : RecursiveACMatch.Correct select flat orient cancel) :
    Semantic select flat orient cancel := by
  intro s _ rules apps f a b out ha hb na nb no typed hit all
  obtain ⟨rule,hm,σ,lhs,rhs⟩ := hit
  have fires := ACSubgroups.replay rules hm σ lhs rhs
  refine ⟨⟨.step fires,no,fun _ hs => .widen typed (Term.rootSort_le hs)⟩,?_⟩
  intro u form
  apply ACUnifierExclusion.normalForm_pair_root_unique ha hb na nb no fires _ form
  rintro _ _ eq ⟨r,hr,τ,rfl,rfl⟩
  rcases all r hr ((instance_head r (apps r hr) τ).symm.trans eq.head_eq.symm) with large|⟨p,q,layout,direct,cross⟩
  · have size := (flatten_equiv f eq).length_eq
    rw [flatten_ac,ha,hb] at size
    have lower := ACUnifierExclusion.factor_lower_bound f r.lhs τ
    simp only [List.singleton_append,List.length_cons,List.length_nil] at size
    omega
  · have aligned := (AtomicACPair.equiv_iff f a b (τ.apply p) (τ.apply q) ha hb).mp
        (eq.trans (layout.subst τ.image))
    rcases aligned with ⟨l,h⟩|⟨l,h⟩
    · exact direct.agrees verified τ l.symm h.symm
    · exact cross.agrees verified τ h.symm l.symm

/-- Completed directional searches for the two aligned factors have no
common binding. Subject variables retain their identities throughout. -/
def Empty [DecidableEq s.ACSym] (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : RecursiveACMatch.Cancellation) (l r a b : Term s) : Prop :=
  ∃ (enc : Encoding s) (left right : Observation s), Search select flat orient cancel enc l a left ∧
    Search select flat orient cancel enc r b right ∧ ∀ σ, ¬ (left σ ∧ right σ)

private theorem Empty.incompatible [DecidableEq s.ACSym] {select flat orient cancel}
    (verified : RecursiveACMatch.Correct select flat orient cancel) {l r a b : Term s}
    (miss : Empty select flat orient cancel l r a b) (σ : Substitution s)
    (left : EquivB (σ.apply l) a) (right : EquivB (σ.apply r) b) : False := by
  obtain ⟨_,_,_,hl,hr,empty⟩ := miss
  exact empty σ ⟨((verified hl l a (.refl _) (.refl _) [] σ).mp (by simpa [Matching.Matches] using left)).1,
    ((verified hr r b (.refl _) (.refl _) [] σ).mp (by simpa [Matching.Matches] using right)).1⟩

def EmptySemantic (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : RecursiveACMatch.Cancellation) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (rules : List (Equation s))
    (_ : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (a b : Term s),
    flatten f a = [classOf a] → flatten f b = [classOf b] →
    Normal (ruleRoot rules) a → Normal (ruleRoot rules) b →
    (∀ rule ∈ rules, head rule.lhs = .ac f →
      2 < (flatten f rule.lhs).length ∨ ∃ l r, EquivB rule.lhs (.ac f l r) ∧
        Empty select flat orient cancel l r a b ∧ Empty select flat orient cancel l r b a) →
    NormalForm (ruleRoot rules) (.ac f a b) (.ac f a b)

theorem emptySemantic {select flat orient cancel} (verified : RecursiveACMatch.Correct select flat orient cancel) :
    EmptySemantic select flat orient cancel := by
  intro s _ rules apps f a b ha hb na nb all
  refine ⟨.basis (.refl _),?_,fun _ h => h⟩
  intro u st
  obtain ⟨_,_,eq,⟨r,hr,τ,rfl,_⟩,_⟩ := (ACUnifierExclusion.pair_step_iff ha hb na nb).mp st
  rcases all r hr ((instance_head r (apps r hr) τ).symm.trans eq.head_eq.symm) with large|⟨p,q,layout,direct,cross⟩
  · have size := (flatten_equiv f eq).length_eq
    rw [flatten_ac,ha,hb] at size
    have lower := ACUnifierExclusion.factor_lower_bound f r.lhs τ
    simp only [List.singleton_append,List.length_cons,List.length_nil] at size
    omega
  · rcases (AtomicACPair.equiv_iff f a b (τ.apply p) (τ.apply q) ha hb).mp (eq.trans (layout.subst τ.image))
      with ⟨l,h⟩|⟨l,h⟩
    · exact direct.incompatible verified τ l.symm h.symm
    · exact cross.incompatible verified τ h.symm l.symm

end Tamarin.Rewriting.ACRootReduction
