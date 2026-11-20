import Tamarin.SymbolWeight
import Tamarin.MixedReconstruction
import Tamarin.WholeProblem
import Tamarin.SpecializedRule

/-! A finite table may define any number of nullary free symbols using ground
constructor terms. Multiple definitions of a symbol may differ by C or AC.
Expanding every occurrence gives a common reduct for arbitrary rewrite paths,
including paths through kind-level terms and contexts rearranged modulo B. -/
namespace Tamarin.ConstantDefinitions
open Rewriting
variable {s : Signature} [DecidableEq s.FreeSym]

/-- Ground constructor terms contain no variable and no free symbol defined
at the root of any left-hand side. This describes syntax in the caller's
signature without choosing a representative equation. -/
def GroundConstructor (rs : Problem s) : Term s → Prop
  | .var _ => False
  | .atom _ => True
  | .free f xs => (∀ r ∈ rs, ∀ args, r.lhs ≠ .free f args) ∧ ∀ i, GroundConstructor rs (xs i)
  | .comm _ a b | .ac _ a b => GroundConstructor rs a ∧ GroundConstructor rs b

/-- Two nullary applications of the same free symbol have identical left
sides. Every pair of definitions must therefore agree, independently of
the order in which the checker reads the table. -/
structure Presentation (rs : Problem s) : Prop where
  shapes : ∀ r ∈ rs, ∃ f xs, r.lhs = .free f xs ∧ s.arity f = 0 ∧ GroundConstructor rs r.rhs
  coherent : ∀ r ∈ rs, ∀ q ∈ rs, r.lhs = q.lhs → EquivB r.rhs q.rhs

def freeHead : Term s → Option s.FreeSym
  | .free f _ => some f
  | _ => none

def entry (rs : Problem s) (f : s.FreeSym) : Option (Equation s) :=
  rs.find? fun r => freeHead r.lhs == some f

/-- A ground constructor expression may contain free, C and AC symbols;
none of its free symbols may have a definition in this table. -/
def constructorTerm (rs : Problem s) : Term s → Bool
  | .var _ => false
  | .atom _ => true
  | .free f xs => (entry rs f).isNone && (List.finRange _).all fun i => constructorTerm rs (xs i)
  | .comm _ a b | .ac _ a b => constructorTerm rs a && constructorTerm rs b

omit [DecidableEq s.FreeSym] in
private theorem head_iff (t : Term s) (f : s.FreeSym) :
    freeHead t = some f ↔ ∃ xs, t = .free f xs := by
  cases t <;> simp [freeHead]
  rintro rfl
  exact ⟨_,HEq.rfl⟩

theorem undefined_iff (rs : Problem s) (f : s.FreeSym) :
    entry rs f = none ↔ ∀ r ∈ rs, ∀ xs, r.lhs ≠ .free f xs := by
  simp [entry,List.find?_eq_none,head_iff]

theorem constructor_iff (rs : Problem s) (t : Term s) :
    constructorTerm rs t ↔ GroundConstructor rs t := by
  induction t with
  | var _ | atom _ => simp [constructorTerm,GroundConstructor]
  | free f xs ih =>
    simp [constructorTerm,GroundConstructor,List.all_eq_true,Option.isNone_iff_eq_none,undefined_iff,ih]
  | comm f a b l r | ac f a b l r => simp [constructorTerm,GroundConstructor,l,r]

variable [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Shared symbol IDs let the existing verified canonical-tree comparison
test duplicate definitions without enumerating AC matches. -/
private def names {α : Type} [DecidableEq α] (terms : List (Term s)) (pick : Term s → Option α) :
    WholeProblem.Names α :=
  let symbols := terms.filterMap pick
  ⟨fun x => UInt64.ofNat (symbols.idxOf x), fun id => symbols[id.toNat]?⟩

private def codec (a b : Term s) : WholeProblem.Codec s :=
  let ts := MixedUnification.subterms a ++ MixedUnification.subterms b
  ⟨names ts (fun | .var v => some v | _ => none),names ts (fun | .atom n => some n | _ => none),
    names ts freeHead,names ts (fun | .comm f .. => some f | _ => none),
    names ts (fun | .ac f .. => some f | _ => none)⟩

private def live (c : WholeProblem.Codec s) (t : Term s) : Decidable (WholeProblem.Live c t) :=
  match t with
  | .var _ | .atom _ => inferInstanceAs (Decidable (_ = _))
  | .free f xs =>
    letI _child (i : Fin (s.arity f)) := live c (xs i)
    inferInstanceAs (Decidable (_ ∧ ∀ _, _))
  | .comm _ a b | .ac _ a b =>
    letI := live c a
    letI := live c b
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private def agree (a b : Term s) : Bool :=
  if a == b then true else
    let c := codec a b
    if @decide _ (live c a) && @decide _ (live c b) then WholeProblem.key c a == WholeProblem.key c b
    else ReferenceMatching.equal a b

private theorem agree_iff (a b : Term s) : agree a b ↔ EquivB a b := by
  unfold agree
  split
  · next same => cases beq_iff_eq.mp same; simp [EquivB.refl]
  · dsimp only
    split
    · next h =>
      obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
      rw [beq_iff_eq]
      exact WholeProblem.canonical_iff _ (@of_decide_eq_true _ (live _ _) ha) (@of_decide_eq_true _ (live _ _) hb)
    · exact ReferenceMatching.equal_iff a b

private def row (rs : Problem s) (r : Equation s) : Bool :=
  match r.lhs with
  | .free f _ => s.arity f == 0 && constructorTerm rs r.rhs &&
      (entry rs f).any (fun chosen => agree r.rhs chosen.rhs)
  | _ => false

def accepts (rs : Problem s) : Bool := rs.all (row rs)

private theorem view {rs : Problem s} (ok : accepts rs) {r : Equation s} (mem : r ∈ rs) :
    ∃ f xs, r.lhs = .free f xs ∧ s.arity f = 0 ∧ constructorTerm rs r.rhs ∧
      ∃ chosen, entry rs f = some chosen ∧ EquivB r.rhs chosen.rhs := by
  have test := List.all_eq_true.mp ok r mem
  cases h : r.lhs with
  | free f xs =>
    simp only [row,h,Bool.and_eq_true,beq_iff_eq] at test
    refine ⟨f,xs,rfl,test.1.1,test.1.2,?_⟩
    cases picked : entry rs f with
    | none => simp [picked] at test
    | some chosen => exact ⟨chosen,rfl,(agree_iff ..).mp (by simpa [picked] using test.2)⟩
  | _ => simp [row,h] at test

/-- The finite admission check recognizes exactly the declared presentation
class. A change to the search or to table lookup cannot narrow its domain. -/
theorem accepts_iff (rs : Problem s) : accepts rs ↔ Presentation rs := by
  constructor
  · intro ok
    refine ⟨fun r mem => ?_,fun r mem q member same => ?_⟩
    · obtain ⟨f,xs,src,zero,clean,_⟩ := view ok mem
      exact ⟨f,xs,src,zero,(constructor_iff ..).mp clean⟩
    · obtain ⟨f,xs,src,_,_,u,left,lu⟩ := view ok mem
      obtain ⟨g,ys,dst,_,_,v,right,rv⟩ := view ok member
      have eq := congrArg freeHead same
      simp only [src,dst,freeHead,Option.some.injEq] at eq
      subst g
      cases Option.some.inj (left.symm.trans right)
      exact lu.trans rv.symm
  · intro spec
    apply List.all_eq_true.mpr
    intro r mem
    obtain ⟨f,xs,src,zero,clean⟩ := spec.shapes r mem
    cases lookup : entry rs f with
    | none => exact ((undefined_iff rs f).mp lookup r mem xs src).elim
    | some chosen =>
      have head : freeHead chosen.lhs = some f :=
        beq_iff_eq.mp (List.find?_some (p := fun q : Equation s => freeHead q.lhs == some f) lookup)
      obtain ⟨ys,chosenSource⟩ := (head_iff ..).mp head
      have args : xs = ys := funext fun i => False.elim (by have := i.isLt; omega)
      have eq := spec.coherent r mem chosen (List.mem_of_find?_eq_some lookup) (src.trans (args ▸ chosenSource.symm))
      simp [row,src,zero,(constructor_iff ..).mpr clean,lookup,(agree_iff ..).mpr eq]

def expand (rs : Problem s) : Term s → Term s
  | .var v => .var v
  | .atom a => .atom a
  | .free f xs => match entry rs f with
    | some r => r.rhs
    | none => .free f (fun i => expand rs (xs i))
  | .comm f a b => .comm f (expand rs a) (expand rs b)
  | .ac f a b => .ac f (expand rs a) (expand rs b)

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem constructor_ground {rs : Problem s} {t : Term s} (clean : constructorTerm rs t) :
    ∀ v, ¬ t.Occurs v := by
  induction t with
  | var v => cases clean
  | atom _ => exact fun _ h => h.elim
  | free f xs ih =>
    intro v ⟨i,hi⟩
    exact ih i (List.all_eq_true.mp (Bool.and_eq_true_iff.mp clean).2 i (List.mem_finRange i)) v hi
  | ac f a b ia ib | comm f a b ia ib =>
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp clean
    exact fun v h => h.elim (ia l v) (ib r v)

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem constructor_free {rs : Problem s} {f : s.FreeSym} {xs}
    (clean : constructorTerm rs (.free f xs)) :
    entry rs f = none ∧ ∀ i, constructorTerm rs (xs i) :=
  ⟨Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp clean).1,
    fun i => List.all_eq_true.mp (Bool.and_eq_true_iff.mp clean).2 i (List.mem_finRange i)⟩

theorem row_shape {rs : Problem s} (ok : accepts rs) {r : Equation s} (mem : r ∈ rs) :
    ∃ f xs, r.lhs = .free f xs ∧ s.arity f = 0 ∧ (entry rs f).isSome ∧ constructorTerm rs r.rhs := by
  obtain ⟨f,xs,head,zero,clean,chosen,found,_⟩ := view ok mem
  exact ⟨f,xs,head,zero,by simp [found],clean⟩

theorem bound {rs : Problem s} (ok : accepts rs) : ReferenceReduction.Bound rs := by
  intro r hr v hv
  obtain ⟨_,_,_,_,_,clean⟩ := row_shape ok hr
  exact (constructor_ground clean v hv).elim

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem expand_clean {rs : Problem s} {t : Term s} (clean : constructorTerm rs t) :
    expand rs t = t := by
  induction t with
  | var _ | atom _ => rfl
  | free f xs ih =>
    have h := Bool.and_eq_true_iff.mp clean
    have off : entry rs f = none := Option.isNone_iff_eq_none.mp h.1
    simp only [expand,off]
    exact congrArg (Term.free f) (funext fun i => ih i (List.all_eq_true.mp h.2 i (List.mem_finRange i)))
  | ac f a b ia ib | comm f a b ia ib =>
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp clean
    simp [expand,ia l,ib r]

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem expand_free (rs : Problem s) (f : s.FreeSym) (xs ys : Fin (s.arity f) → Term s)
    (kids : ∀ i, EquivB (expand rs (xs i)) (expand rs (ys i))) :
    EquivB (expand rs (.free f xs)) (expand rs (.free f ys)) := by
  cases h : entry rs f with
  | none => simpa only [expand,h] using EquivB.free f _ _ kids
  | some r => simp only [expand,h]; exact .refl _

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem expand_basis (rs : Problem s) {a b : Term s} (h : EquivB a b) :
    EquivB (expand rs a) (expand rs b) := by
  induction h with
  | refl => exact .refl _
  | trans _ _ l r => exact l.trans r
  | symm _ ih => exact ih.symm
  | free f xs ys _ ih => exact expand_free rs f xs ys ih
  | comm_congr f _ _ l r => exact .comm_congr f l r
  | ac_congr f _ _ l r => exact .ac_congr f l r
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

private theorem expand_step {rs : Problem s} (ok : accepts rs) {a b : Term s} (h : Step (ruleRoot rs) a b) :
    EquivB (expand rs a) (expand rs b) := by
  induction h with
  | root root =>
    obtain ⟨r,mem,σ,rfl,rfl⟩ := root
    obtain ⟨f,xs,source,_,clean,chosen,lookup,agree⟩ := view ok mem
    rw [source,SpecializedRule.apply_ground (constructor_ground clean),expand_clean clean]
    simpa only [Substitution.apply,Term.subst,expand,lookup] using agree.symm
  | free f xs i _ ih =>
    apply expand_free
    intro j
    by_cases eq : j = i
    · simpa [eq] using ih
    · simp only [eq,ite_false]; exact .refl _
  | comm_left f _ _ ih => exact .comm_congr f ih (.refl _)
  | comm_right f _ _ ih => exact .comm_congr f (.refl _) ih
  | ac_left f _ _ ih => exact .ac_congr f ih (.refl _)
  | ac_right f _ _ ih => exact .ac_congr f (.refl _) ih

private theorem expand_path {rs : Problem s} (ok : accepts rs) {a b : Term s} (h : Reduces (ruleRoot rs) a b) :
    EquivB (expand rs a) (expand rs b) := by
  induction h with
  | basis h => exact expand_basis rs h
  | step h =>
    obtain ⟨_,_,pre,one,post⟩ := h
    exact (expand_basis rs pre).trans ((expand_step ok one).trans (expand_basis rs post))
  | trans _ _ l r => exact l.trans r
  | free f xs ys _ ih => exact expand_free rs f xs ys ih
  | ac f _ _ l r => exact .ac_congr f l r
  | comm f _ _ l r => exact .comm_congr f l r

theorem entry_step {rs : Problem s} (ok : accepts rs) {f : s.FreeSym} {r : Equation s}
    (lookup : entry rs f = some r) (xs : Fin (s.arity f) → Term s) :
    StepModulo (ruleRoot rs) (.free f xs) r.rhs := by
  have mem := List.mem_of_find?_eq_some lookup
  have head : freeHead r.lhs = some f := beq_iff_eq.mp (List.find?_some (p := fun e : Equation s => freeHead e.lhs == some f) lookup)
  obtain ⟨g,ys,source,zero,_⟩ := view ok mem
  simp only [source,freeHead,Option.some.injEq] at head
  subst g
  have eq : xs = ys := funext fun i => False.elim (by have := i.isLt; omega)
  subst xs
  refine ⟨_,_,.refl _,Step.root ⟨r,mem,Substitution.identity,?_,?_⟩,.refl _⟩
  · simpa using source.symm
  · simp

theorem reachable {rs : Problem s} (ok : accepts rs) (t : Term s) :
    Reduces (ruleRoot rs) t (expand rs t) := by
  induction t with
  | atom _ | var _ => exact .basis (.refl _)
  | ac f a b l r => exact .ac f l r
  | comm f a b l r => exact .comm f l r
  | free f xs ih =>
    cases lookup : entry rs f with
    | none => simpa only [expand,lookup] using Reduces.free f _ _ ih
    | some r =>
      simpa only [expand,lookup] using Reduces.step (entry_step ok lookup xs)

def weight (rs : Problem s) : Head s → Nat
  | .free f => if (entry rs f).isSome then 1 else 0
  | _ => 0

omit [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem clean_zero {rs : Problem s} {t : Term s} (clean : constructorTerm rs t) :
    SymbolWeight.rank (weight rs) t = 0 := by
  induction t with
  | var _ | atom _ => rfl
  | free f xs ih =>
    obtain ⟨off,kids⟩ := constructor_free clean
    change (List.ofFn fun i => SymbolWeight.rank _ (xs i)).sum + weight rs (.free f) = 0
    simp [List.sum_eq_zero_iff_forall_eq_nat,fun i => ih i (kids i),weight,off]
  | ac f a b l r | comm f a b l r =>
    change SymbolWeight.rank _ a + SymbolWeight.rank _ b + 0 = 0
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp clean
    simp [l ha,r hb]

theorem decreases {rs : Problem s} (ok : accepts rs) : SymbolWeight.decreasing (weight rs) rs := by
  apply List.all_eq_true.mpr
  intro r hr
  obtain ⟨f,xs,src,_,on,clean⟩ := row_shape ok hr
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [clean_zero clean,src]
    change 0 < _ + weight rs (.free f)
    simp [weight,on]
  · apply List.all_eq_true.mpr
    intro v hv
    exact (constructor_ground clean v ((Term.mem_variables ..).mp hv)).elim

private theorem expand_zero {rs : Problem s} (ok : accepts rs) (t : Term s) :
    SymbolWeight.rank (weight rs) (expand rs t) = 0 := by
  induction t with
  | var _ | atom _ => rfl
  | ac f a b l r | comm f a b l r =>
    change SymbolWeight.rank _ (expand rs a) + SymbolWeight.rank _ (expand rs b) + 0 = 0
    simp [l,r]
  | free f xs ih =>
    cases found : entry rs f with
    | some r =>
      obtain ⟨_,_,_,_,_,clean⟩ := row_shape ok (List.mem_of_find?_eq_some found)
      simpa only [expand,found] using clean_zero clean
    | none =>
      simp only [expand,found]
      change (List.ofFn fun i => SymbolWeight.rank _ (expand rs (xs i))).sum + weight rs (.free f) = 0
      simp [weight,found,List.sum_eq_zero_iff_forall_eq_nat,ih]

theorem normal_expand {rs : Problem s} (ok : accepts rs) (t : Term s) :
    Normal (ruleRoot rs) (expand rs t) := by
  intro u st
  have lt := SymbolWeight.step_lt (decreases ok) st
  rw [expand_zero ok] at lt
  exact Nat.not_lt_zero _ lt

/-- The two rewrite paths may expose different defined constants, at any
positions modulo B. Both endpoints reduce to the same expansion up to B. -/
theorem confluent {rs : Problem s} (ok : accepts rs) {t u v : Term s}
    (left : Reduces (ruleRoot rs) t u) (right : Reduces (ruleRoot rs) t v) :
    ∃ w, Reduces (ruleRoot rs) u w ∧ Reduces (ruleRoot rs) v w :=
  ⟨expand rs v,(reachable ok u).trans (.basis ((expand_path ok left).symm.trans (expand_path ok right))),
    reachable ok v⟩

/-- One structural pass through the input suffices even for a definition
whose ground constructor result is larger than its left side. -/
theorem reductionReply {rs : Problem s} (ok : accepts rs) (sorted : TableDecrease.sorted rs) (t : Term s) :
    MaudeOperations.ReductionReply (ruleRoot rs) t (expand rs t) := by
  have path := reachable ok t
  have nf := normal_expand ok t
  refine ⟨⟨path,nf,?_⟩,fun u other => ?_⟩
  · intro k typed
    exact RootNarrowing.reduction_invariant (fun x => HasSort x k)
      (fun h e => Term.checkSort_sound _ _ ((SortClash.check_equiv e k) ▸ Term.checkSort_complete h))
      (fun h step => TableDecrease.sortPreserving sorted step k h) path typed
  · obtain ⟨_,a,b⟩ := confluent ok other.1 path
    exact (normal_reduces_equiv a other.2.1).trans (normal_reduces_equiv b nf).symm

end Tamarin.ConstantDefinitions
