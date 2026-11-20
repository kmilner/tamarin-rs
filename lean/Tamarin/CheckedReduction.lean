import Tamarin.ReductionHeight
import Tamarin.FiniteOccurs

/-! Check every reachable normal endpoint before accepting a reduction on an
uncertified table. Fuel bounds rewrite depth; exhausting it yields no answer. -/
namespace Tamarin.CheckedReduction
open MaudeOperations Rewriting
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Every variable on a rule's right side must be supplied by matching its left side. -/
def rangeBound (rs : List (Equation s)) : Bool :=
  rs.all fun r => r.rhs.variables.all fun v => r.lhs.variables.contains v

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem rangeBound_iff (rs : List (Equation s)) : rangeBound rs ↔ ReferenceReduction.Bound rs := by
  simp [rangeBound,ReferenceReduction.Bound,Term.mem_variables]

private def next (rs : List (Equation s)) (t : Term s) := ReferenceReduction.successors rs t

-- The structural matcher and AC subproduct finder enumerate partitions
-- eagerly. Charge the branching heads before constructing any successor list.
private def branching : Term s → Nat
  | .atom _ | .var _ => 0
  | .free _ xs => (List.ofFn (fun i => branching (xs i))).sum
  | .comm _ a b | .ac _ a b => branching a + branching b + 1

/-- Preflight the actual search tree. Fuel bounds depth. A separate work
allowance is split among siblings, so the traversals following this check
cannot multiply that allowance at every level. Larger callers can supply a
larger allowance without changing the semantics of a successful reduction. -/
def affordable (rs : List (Equation s)) : Nat → Nat → Term s → Bool
  | 0, _, _ => false
  | n+1, budget, t =>
    let heads := branching t
    if heads ≥ budget.log2 then false else
    let charge := ((List.range (heads+1)).map Nat.succ).prod * (FiniteOccurs.nodes t) * (rs.length+1)
    if charge > budget then false else
    let children := next rs t
    let per := (budget - charge) / children.length
    children.all (affordable rs n per)

/-- Search one path for a reachable normal form. The second traversal below
checks that all other paths terminate with the same value modulo B. -/
def choose (rs : List (Equation s)) : Nat → Term s → Option (Term s)
  | 0, _ => none
  | n+1, t => match next rs t with
    | [] => some t
    | u :: _ => choose rs n u

def agrees (rs : List (Equation s)) (result : Term s) : Nat → Term s → Bool
  | 0, _ => false
  | n+1, t => match next rs t with
    | [] => ReferenceMatching.equal t result
    | u :: us => (u :: us).all (agrees rs result n)

def sorts (a b : Term s) : Bool :=
  [SortId.pub,.fresh,.msg,.node,.nat].all fun k => !a.checkSort k || b.checkSort k

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sorts_iff (a b : Term s) : sorts a b ↔ ∀ k, HasSort a k → HasSort b k := by
  simp only [sorts,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true']
  constructor
  · intro h k ha
    have mem : k ∈ [SortId.pub,.fresh,.msg,.node,.nat] := by cases k <;> decide
    exact Term.checkSort_sound _ _ ((h k mem).resolve_left (by simp [Term.checkSort_complete ha]))
  · intro h k _
    cases ha : a.checkSort k with
    | false => exact .inl rfl
    | true => exact .inr (Term.checkSort_complete (h k (Term.checkSort_sound _ _ ha)))

def run (rs : List (Equation s)) (fuel : Nat) (t : Term s) : Option (Term s) :=
  match choose rs fuel t with
  | none => none
  | some v => if sorts t v && agrees rs v fuel t then some v else none

variable {rs : List (Equation s)} (bound : ReferenceReduction.Bound rs)
include bound
private theorem edge {a u : Term s} (hu : u ∈ next rs a) : StepModulo (ruleRoot rs) a u :=
  (ReferenceReduction.exactSteps rs bound ..).mp ⟨_,hu,.refl _⟩

private theorem normal {t : Term s} (st : next rs t = []) : Normal (ruleRoot rs) t := by
  intro u hu
  obtain ⟨v,hv,_⟩ := (ReferenceReduction.exactSteps rs bound ..).mpr hu
  rw [show ReferenceReduction.successors rs t = [] from st] at hv
  exact List.not_mem_nil hv

theorem chosen (n : Nat) (t u : Term s) (h : choose rs n t = some u) :
    Reduces (ruleRoot rs) t u ∧ Normal (ruleRoot rs) u := by
  induction n generalizing t with
  | zero => contradiction
  | succ n ih =>
    cases hs : next rs t with
    | nil =>
      simp [choose,hs] at h
      subst u
      exact ⟨.basis (.refl _),normal bound hs⟩
    | cons a as =>
      have ⟨path,nf⟩ := ih a (by simpa [choose,hs] using h)
      exact ⟨.trans (.step (edge bound (by simp [hs] : a ∈ next rs t))) path,nf⟩

/-- Two genuinely different, reachable normal forms of the original input. -/
def Conflicting (rules : Problem s) (t : Term s) : Prop :=
  ∃ a b, NormalForm (ruleRoot rules) t a ∧ NormalForm (ruleRoot rules) t b ∧ ¬ EquivB a b

/-- Every rewrite path from this input has strictly fewer than the given
number of genuine steps. This uses the semantic relation modulo C/AC. -/
def Within (rules : Problem s) : Nat → Term s → Prop
  | 0,_ => False
  | n+1,t => ∀ u, StepModulo (ruleRoot rules) t u → Within rules n u

/-- A finite stage must decide a bounded tree when every reachable irreducible
endpoint preserves the sorts of its source. This condition is local to the query. -/
def Settled (rules : Problem s) (depth : Nat) (t : Term s) : Prop :=
  Within rules depth t ∧ ∀ u, Reduces (ruleRoot rules) t u → Normal (ruleRoot rules) u →
    ∀ k, HasSort t k → HasSort u k

private def differentLeaf (rules : Problem s) (source expected : Term s) : Nat → Term s → Bool
  | 0,_ => false
  | k+1,t => match next rules t with
    | [] => sorts source t && !ReferenceMatching.equal expected t
    | cs => cs.any (differentLeaf rules source expected k)

/-- Only a second irreducible endpoint witnesses disagreement. Exhausting a
branch, encountering a cycle, or rejecting a sort cannot establish it. -/
def ambiguous (rules : Problem s) (fuel : Nat) (t : Term s) : Bool :=
  match choose rules fuel t with
  | none => false
  | some v => sorts t v && differentLeaf rules t v fuel t

private theorem differentLeaf_sound (source expected : Term s) (k : Nat) (t : Term s)
    (hit : differentLeaf rs source expected k t) :
    ∃ u, Reduces (ruleRoot rs) t u ∧ Normal (ruleRoot rs) u ∧
      (∀ sort, HasSort source sort → HasSort u sort) ∧ ¬ EquivB expected u := by
  induction k generalizing t with
  | zero => contradiction
  | succ k ih =>
    cases children : next rs t with
    | nil =>
      obtain ⟨safe,diff⟩ := Bool.and_eq_true_iff.mp (by simpa [differentLeaf,children] using hit :
        sorts source t && !ReferenceMatching.equal expected t)
      exact ⟨t,.basis (.refl _),normal bound children,(sorts_iff ..).mp safe,
        fun h => by simp [(ReferenceMatching.equal_iff ..).mpr h] at diff⟩
    | cons a as =>
      obtain ⟨c,mem,seen⟩ := List.any_eq_true.mp (by simpa only [differentLeaf,children] using hit :
        (a :: as).any (differentLeaf rs source expected k))
      obtain ⟨u,path,out⟩ := ih c seen
      exact ⟨u,(Reduces.step (edge bound (children ▸ mem))).trans path,out⟩

theorem ambiguous_sound (fuel : Nat) (t : Term s) (hit : ambiguous rs fuel t) : Conflicting rs t := by
  cases branch : choose rs fuel t with
  | none => simp [ambiguous,branch] at hit
  | some v =>
    obtain ⟨safe,diff⟩ := Bool.and_eq_true_iff.mp (by simpa only [ambiguous,branch] using hit :
      sorts t v && differentLeaf rs t v fuel t)
    obtain ⟨path,irreducible⟩ := chosen bound fuel t v branch
    obtain ⟨u,reach,nf,sorts,ne⟩ := differentLeaf_sound bound t v fuel t diff
    exact ⟨v,u,⟨path,irreducible,(sorts_iff ..).mp safe⟩,⟨reach,nf,sorts⟩,ne⟩

private theorem chooses_of_within (n : Nat) (t : Term s) (tree : Within rs n t) :
    ∃ u, choose rs n t = some u := by
  induction n generalizing t with
  | zero => contradiction
  | succ n ih =>
    cases children : next rs t with
    | nil => exact ⟨t,by simp [choose,children]⟩
    | cons a as =>
      obtain ⟨u,h⟩ := ih a (tree a (edge bound (by simp [children] : a ∈ next rs t)))
      exact ⟨u,by simp [choose,children,h]⟩

private theorem compare_of_within (source expected : Term s)
    (safe : ∀ u, Reduces (ruleRoot rs) source u → Normal (ruleRoot rs) u → ∀ k, HasSort source k → HasSort u k)
    (n : Nat) (t : Term s) (tree : Within rs n t) (path : Reduces (ruleRoot rs) source t) :
    agrees rs expected n t ∨ differentLeaf rs source expected n t := by
  induction n generalizing t with
  | zero => contradiction
  | succ n ih =>
    cases children : next rs t with
    | nil =>
      by_cases eq : EquivB t expected
      · exact .inl (by simp [agrees,children,(ReferenceMatching.equal_iff ..).mpr eq])
      · have diff : ReferenceMatching.equal expected t = false :=
          Bool.eq_false_iff.mpr (fun h => eq (((ReferenceMatching.equal_iff ..).mp h).symm))
        exact .inr (by simp [differentLeaf,children,(sorts_iff ..).mpr (safe t path (normal bound children)),diff])
    | cons a as =>
      by_cases all : (a :: as).all (agrees rs expected n)
      · exact .inl (by simpa only [agrees,children] using all)
      · obtain ⟨u,mem,bad⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr all)
        have st := edge bound (children ▸ mem)
        have differs := (ih u (tree u st) (path.trans (.step st))).resolve_left bad
        exact .inr (by simpa only [differentLeaf,children] using List.any_eq_true.mpr ⟨u,mem,differs⟩)

theorem decides_settled {n : Nat} {t : Term s} (settled : Settled rs n t) :
    (∃ u, run rs n t = some u) ∨ ambiguous rs n t := by
  obtain ⟨tree,safe⟩ := settled
  obtain ⟨v,h⟩ := chooses_of_within bound n t tree
  obtain ⟨path,nf⟩ := chosen bound n t v h
  have sorted := (sorts_iff ..).mpr (safe v path nf)
  rcases compare_of_within bound t v safe n t tree (.basis (.refl _)) with same | diff
  · exact .inl ⟨v,by simp [run,h,sorted,same]⟩
  · exact .inr (by simp [ambiguous,h,sorted,diff])

theorem settled_of_height (canonical : CanonicalPresentation (ruleRoot rs)) (n : Nat) (t : Term s)
    (enough : ReductionHeight.height bound canonical.terminating t < n) : Settled rs n t := by
  refine ⟨?_,fun _ path _ k ht => ?_⟩
  · induction n generalizing t with
    | zero => omega
    | succ n ih =>
      intro u st
      exact ih u (by have := ReductionHeight.step bound canonical.terminating st; omega)
  · exact RootNarrowing.reduction_invariant (fun u => HasSort u k)
      (fun h e => Term.checkSort_sound _ _ ((SortClash.check_equiv e k) ▸ Term.checkSort_complete h))
      (fun h st => canonical.sortPreserving st k h) path ht

private theorem first {a b : Term s} (path : Reduces (ruleRoot rs) a b) :
    EquivB a b ∨ ∃ u ∈ next rs a, Reduces (ruleRoot rs) u b := by
  rcases RootNarrowing.firstStep path with same | ⟨u,step,tail⟩
  · exact .inl same
  · obtain ⟨v,hv,eq⟩ := (ReferenceReduction.exactSteps rs bound a u).mpr step
    exact .inr ⟨v,hv,(Reduces.basis eq).trans tail⟩

/-- Every reachable normal endpoint agrees with the checked target, even if
other terms of the active presentation have different normal forms. -/
theorem agrees_sound (v : Term s) (n : Nat) (t u : Term s) (h : agrees rs v n t)
    (red : Reduces (ruleRoot rs) t u) (nf : Normal (ruleRoot rs) u) : EquivB u v := by
  induction n generalizing t with
  | zero => contradiction
  | succ n ih =>
    cases hs : next rs t with
    | nil =>
      have eq := normal_reduces_equiv red (normal bound hs)
      exact eq.symm.trans ((ReferenceMatching.equal_iff ..).mp (by simpa [agrees,hs] using h))
    | cons a as =>
      have checkedChildren : ∀ c ∈ next rs t, agrees rs v n c := by
        simpa [agrees,hs,List.all_eq_true] using h
      rcases first bound red with eq|⟨u',hm,rest⟩
      · exact False.elim (((normal_equiv _ eq).mpr nf) a (edge bound (by simp [hs] : a ∈ next rs t)))
      · exact ih _ (checkedChildren _ hm) rest

theorem correct {t u : Term s} {n} (h : run rs n t = some u) :
    ReductionReply (ruleRoot rs) t u := by
  cases hc : choose rs n t with
  | none => simp [run,hc] at h
  | some v =>
    by_cases hv : sorts t v && agrees rs v n t
    · obtain ⟨safe,others⟩ := Bool.and_eq_true_iff.mp hv
      simp [run,hc,safe,others] at h
      subst u
      have ⟨path,nf⟩ := chosen bound n t v hc
      exact ⟨⟨path,nf,(sorts_iff ..).mp safe⟩,fun u hu => agrees_sound bound _ _ _ _ others hu.1 hu.2.1⟩
    · simp only [run,hc] at h
      split at h <;> contradiction


omit bound [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem common_budget {α : Type} (xs : List α) (P : α → Nat → Prop)
    (h : ∀ a ∈ xs, ∃ k, ∀ j ≥ k, P a j) : ∃ k, ∀ j ≥ k, ∀ a ∈ xs, P a j := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨k,hk⟩ := h x List.mem_cons_self
    obtain ⟨l,hl⟩ := ih (fun a ha => h a (.tail _ ha))
    refine ⟨max k l,fun j hj a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl|ha
    · exact hk _ (Nat.le_trans (Nat.le_max_left ..) hj)
    · exact hl _ (Nat.le_trans (Nat.le_max_right ..) hj) _ ha

/-- Exhaustive search on a terminating finite-branching table needs only a
finite work allowance. This also applies to a term whose shape changes during
rewriting, including a right side that introduces additional AC factors. -/
theorem finite_budget (measure : Term s → Nat)
    (smaller : ∀ {a b}, StepModulo (ruleRoot rs) a b → measure b < measure a)
    (depth : Nat) (t : Term s) (enough : measure t < depth) :
    ∃ k, ∀ j ≥ k, affordable rs depth j t := by
  induction depth generalizing t with
  | zero => omega
  | succ n ih =>
    obtain ⟨k,children⟩ := common_budget (next rs t) (fun u j => affordable rs n j u) (by
      intro a ha
      have lt := smaller (edge bound ha)
      exact ih a (by omega))
    let charge := ((List.range (branching t+1)).map Nat.succ).prod * FiniteOccurs.nodes t * (rs.length+1)
    let cap := 2^(branching t+1)
    refine ⟨cap + charge + k * (next rs t).length,fun j hj => ?_⟩
    have capFits : cap ≤ j := by omega
    have positive : 0 < cap := Nat.pow_pos (by decide)
    have headroom := (Nat.le_log2 (Nat.ne_of_gt (Nat.lt_of_lt_of_le positive capFits))).mpr capFits
    change branching t+1 ≤ j.log2 at headroom
    have paid : charge ≤ j := by omega
    rw [affordable]
    dsimp only
    split
    · omega
    split
    · next bad => exact (Nat.not_lt.mpr paid bad).elim
    apply List.all_eq_true.mpr
    intro a ha
    have nonempty := List.length_pos_of_mem ha
    exact children _ ((Nat.le_div_iff_mul_le nonempty).mpr (by change k * (next rs t).length ≤ j - charge; omega)) a ha

theorem chosen_within (measure : Term s → Nat)
    (smaller : ∀ {a b}, StepModulo (ruleRoot rs) a b → measure b < measure a)
    (n : Nat) (t : Term s) (enough : measure t < n) : ∃ v, choose rs n t = some v := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    cases hs : next rs t with
    | nil => exact ⟨t,by simp [choose,hs]⟩
    | cons a as =>
      have lt := smaller (edge bound (by simp [hs] : a ∈ next rs t))
      obtain ⟨v,hv⟩ := ih a (by omega)
      exact ⟨v,by simp [choose,hs,hv]⟩

private theorem agrees_within (measure : Term s → Nat)
    (smaller : ∀ {a b}, StepModulo (ruleRoot rs) a b → measure b < measure a)
    {v : Term s} (n : Nat) (t : Term s) (enough : measure t < n)
    (endpoints : ∀ u, Reduces (ruleRoot rs) t u → Normal (ruleRoot rs) u → EquivB u v) :
    agrees rs v n t := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    cases hs : next rs t with
    | nil => simpa [agrees,hs,ReferenceMatching.equal_iff] using endpoints t (.basis (.refl _)) (normal bound hs)
    | cons a as =>
      have per (b) (hb : b ∈ next rs t) : agrees rs v n b := by
        have st := edge bound hb
        have lt := smaller st
        exact ih b (by omega) (fun u hr => endpoints u (.trans (.step st) hr))
      simpa [agrees,hs,List.all_eq_true] using per

theorem completes (canonical : CanonicalPresentation (ruleRoot rs)) (measure : Term s → Nat)
    (smaller : ∀ {a b}, StepModulo (ruleRoot rs) a b → measure b < measure a)
    (t : Term s) (fuel : Nat) (enough : measure t < fuel) : ∃ v, run rs fuel t = some v := by
  obtain ⟨v,hv⟩ := chosen_within bound measure smaller fuel t enough
  obtain ⟨red,nf⟩ := chosen bound fuel t v hv
  have hs : sorts t v := (sorts_iff ..).mpr fun k hk =>
    RootNarrowing.reduction_invariant (fun z => HasSort z k)
      (fun h e => Term.checkSort_sound _ _ ((SortClash.check_equiv e k) ▸ Term.checkSort_complete h))
      (fun h st => canonical.sortPreserving st k h) red hk
  have ha : agrees rs v fuel t := agrees_within bound measure smaller _ _ enough fun u path normal => by
    obtain ⟨w,l,r⟩ := canonical.confluent path red
    exact (normal_reduces_equiv l normal).trans (normal_reduces_equiv r nf).symm
  exact ⟨v,by simp [run,hv,hs,ha]⟩

theorem eventually (canonical : CanonicalPresentation (ruleRoot rs)) (t : Term s) :
    ∃ fuel v, run rs fuel t = some v := by
  let height := ReductionHeight.height bound canonical.terminating
  exact ⟨height t+1,completes bound canonical height (ReductionHeight.step bound canonical.terminating)
    t _ (Nat.lt_succ_self _)⟩

end Tamarin.CheckedReduction
