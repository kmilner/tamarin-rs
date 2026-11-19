import Tamarin.ACSubproductReduction

/-! Ordinary reduction by an arbitrary live rule table. Complete directional
matches at the outer head and one-step transitions inside its operands suffice
to build every edge. The search may evaluate them in any order. -/
namespace Tamarin.Rewriting.ContextualReduction
open ConstructorVariants ACSubproductReduction
variable {s : Signature} {R : Root s}

/-- One rule fires at the whole term, modulo structural equations. -/
def AtRoot (R : Root s) (a b : Term s) : Prop :=
  ∃ p q, EquivB a p ∧ R p q ∧ EquivB q b

/-- One directional match per rule with the target head suffices. In
particular a C root match considers both alignments under one substitution. -/
theorem root_iff (rules : List (Equation s)) (a b : Term s)
    (apps : ∀ r ∈ rules, Application r.lhs)
    (scope : ∀ r ∈ rules, head r.lhs = head a → ∀ v, r.rhs.Occurs v → r.lhs.Occurs v)
    (answers : Equation s → List (Substitution s))
    (runs : ∀ r ∈ rules, head r.lhs = head a → RuleMatches r a (answers r)) :
    AtRoot (ruleRoot rules) a b ↔ ∃ r ∈ rules, head r.lhs = head a ∧
      ∃ θ ∈ answers r, EquivB (θ.apply r.rhs) b := by
  constructor
  · rintro ⟨_,_,eq,⟨r,hr,σ,rfl,rfl⟩,out⟩
    have hd := (instance_head r (apps r hr) σ).symm.trans eq.head_eq.symm
    obtain ⟨θ,hm,agree⟩ := (runs r hr hd).complete σ eq.symm
    exact ⟨r,hr,hd,θ,hm,(r.rhs.subst_equiv _ _ (fun v hv => (agree v (scope r hr hd v hv)).symm)).trans out⟩
  · rintro ⟨r,hr,hd,θ,hm,out⟩
    exact ⟨_,_,((runs r hr hd).sound θ hm).symm,⟨r,hr,θ,rfl,rfl⟩,out⟩

theorem free_iff (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (b : Term s) :
    StepModulo R (.free f xs) b ↔ AtRoot R (.free f xs) b ∨
      ∃ i v, StepModulo R (xs i) v ∧ EquivB (.free f (fun j => if j = i then v else xs j)) b := by
  rw [free_steps_iff]
  apply or_congr_left
  constructor
  · rintro ⟨ys,v,h,hit,r⟩
    exact ⟨_,_,.free _ _ _ h,hit,r⟩
  · rintro ⟨p,q,l,hit,r⟩
    obtain ⟨ys,rfl,h⟩ := free_equiv_view l
    exact ⟨ys,q,h,hit,r⟩

private theorem left (f : s.CSym) (other : Term s) {a b : Term s} (st : StepModulo R a b) :
    StepModulo R (.comm f a other) (.comm f b other) := by
  obtain ⟨p,q,l,hit,r⟩ := st
  exact ⟨_,_,.comm_congr f l (.refl _),.comm_left f other hit,.comm_congr f r (.refl _)⟩

private theorem rebase {a b a' b' : Term s} (l : EquivB a' a) (st : StepModulo R a b) (r : EquivB b b') :
    StepModulo R a' b' := by
  obtain ⟨p,q,before,hit,after⟩ := st
  exact ⟨_,_,l.trans before,hit,after.trans r⟩

/-- In either orientation a step strictly under a C head changes exactly one
of the original operands. This preserves competition between parent and child
rewrites, including in a theory with several normal forms. -/
theorem comm_iff (f : s.CSym) (x y b : Term s) :
    StepModulo R (.comm f x y) b ↔ AtRoot R (.comm f x y) b ∨
      (∃ v, StepModulo R x v ∧ EquivB (.comm f v y) b) ∨
      (∃ v, StepModulo R y v ∧ EquivB (.comm f x v) b) := by
  constructor
  · rintro ⟨term,c,before,st,after⟩
    obtain ⟨a,d,rfl⟩ : ∃ a d, term = Term.comm f a d := by
      cases term with
      | comm g a d => obtain rfl : f = g := Head.comm.inj before.head_eq; exact ⟨a,d,rfl⟩
      | _ => cases before.head_eq
    cases st with
    | root hit => exact .inl ⟨_,_,before,hit,after⟩
    | comm_left _ _ child =>
      rcases (Commutative.equiv_iff ..).mp before with ⟨l,r⟩|⟨l,r⟩
      · exact .inr (.inl ⟨_,⟨_,_,l,child,.refl _⟩,(EquivB.comm_congr f (.refl _) r).trans after⟩)
      · exact .inr (.inr ⟨_,⟨_,_,r,child,.refl _⟩,(EquivB.comm_swap ..).trans
          ((EquivB.comm_congr f (.refl _) l).trans after)⟩)
    | comm_right _ _ child =>
      rcases (Commutative.equiv_iff ..).mp before with ⟨l,r⟩|⟨l,r⟩
      · exact .inr (.inr ⟨_,⟨_,_,r,child,.refl _⟩,(EquivB.comm_congr f l (.refl _)).trans after⟩)
      · exact .inr (.inl ⟨_,⟨_,_,l,child,.refl _⟩,(EquivB.comm_swap ..).trans
          ((EquivB.comm_congr f r (.refl _)).trans after)⟩)
  · rintro (⟨_,_,l,hit,r⟩|⟨v,hit,r⟩|⟨v,hit,r⟩)
    · exact ⟨_,_,l,.root hit,r⟩
    · exact rebase (.refl _) (left f y hit) r
    · exact rebase (.comm_swap ..) (left f x hit) ((EquivB.comm_swap ..).trans r)

/-- A complete one-step traversal of a term. Integer IDs, canonical forms,
and the order of visiting rules or children do not appear in this contract.
The caller must account for every successor contributed by every component. -/
inductive Generated [DecidableEq s.ACSym] (R : Root s) : Term s → (Term s → Prop) → Prop where
  | normal (a) (ends : Normal R a) : Generated R a (fun _ => False)
  | free (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (root : Term s → Prop)
      (child : Fin (s.arity f) → Term s → Prop)
      (roots : ∀ b, AtRoot R (.free f xs) b ↔ root b)
      (children : ∀ i, Generated R (xs i) (child i)) :
      Generated R (.free f xs) (fun b => root b ∨ ∃ i v, child i v ∧
        EquivB (.free f (fun j => if j = i then v else xs j)) b)
  | comm (f : s.CSym) (x y : Term s) (root l r : Term s → Prop)
      (roots : ∀ b, AtRoot R (.comm f x y) b ↔ root b)
      (left : Generated R x l) (right : Generated R y r) :
      Generated R (.comm f x y) (fun b => root b ∨ (∃ v, l v ∧ EquivB (.comm f v y) b) ∨
        (∃ v, r v ∧ EquivB (.comm f x v) b))
  | ac (f : s.ACSym) (x y : Term s) (groups : Term s → Prop) (child : Term s → Term s → Prop)
      (roots : ∀ b, Occurrence R f (.ac f x y) b ↔ groups b)
      (children : ∀ p ∈ ACRepresentation.flatten f (.ac f x y), Generated R p (child p)) :
      Generated R (.ac f x y) (fun b => groups b ∨ ∃ p ∈ ACRepresentation.flatten f (.ac f x y),
        ∃ q rest, child p q ∧ EquivB (.ac f x y) (plug f rest p) ∧ EquivB (plug f rest q) b)
  | read {a before after} (trace : Generated R a before) (outputs : ∀ b, before b ↔ after b) :
      Generated R a after

theorem Generated.exact [DecidableEq s.ACSym] {a : Term s} {out} (h : Generated R a out) :
    ∀ b, StepModulo R a b ↔ out b := by
  induction h with
  | normal _ hn => exact fun b => ⟨hn b,False.elim⟩
  | free f xs root child roots _ ih =>
    intro b
    rw [free_iff,roots]
    exact or_congr_right (exists_congr fun i => exists_congr fun v => and_congr_left fun _ => ih i v)
  | comm f x y root l r roots _ _ il ir =>
    intro b
    rw [comm_iff,roots]
    apply or_congr_right
    exact or_congr (exists_congr fun v => and_congr_left fun _ => il v)
      (exists_congr fun v => and_congr_left fun _ => ir v)
  | ac f x y groups child roots _ ih =>
    intro b
    rw [all_steps_iff f,roots]
    apply or_congr_right
    exact exists_congr fun p => and_congr_right fun hp => exists_congr fun q => exists_congr fun k =>
      and_congr_left fun _ => ih p hp q
  | read _ outputs ih => exact fun b => (ih b).trans (outputs b)

/-- A visited terminal of a completed ordinary reduction graph has the
unique normal value for the original query. The graph may contain states at
different heads and several competing rewrites at each level of a term. -/
theorem complete [DecidableEq s.ACSym] (states : List (Term s)) (next : Term s → List (Term s))
    (start result : Term s) (seed : start ∈ states)
    (runs : ∀ a ∈ states, Generated R a (fun b => ∃ v ∈ next a, EquivB v b))
    (closed : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states)
    (ends : ∀ a ∈ states, next a = [] → EquivB a result)
    (visited : Visited next start result) (leaf : next result = [])
    (sorts : ∀ k, HasSort start k → HasSort result k) :
    NormalForm R start result ∧ ∀ u, NormalForm R start u → EquivB u result :=
  completed states next start result seed (fun a ha => (runs a ha).exact) closed ends visited leaf sorts

end Tamarin.Rewriting.ContextualReduction
