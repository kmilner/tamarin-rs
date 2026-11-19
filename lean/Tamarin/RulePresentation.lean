import Tamarin.Rewriting
import Tamarin.ACRepresentation

/-! A presentation may decode an AC rule in a different operand order or
association. Ordinary root rewriting is syntax-directed, but the operations
observed by callers are invariant under replacement of rules modulo B. -/
namespace Tamarin.Rewriting.RulePresentation
variable {sig : Signature} {P Q : List (Equation sig)}

def Includes (P Q : List (Equation sig)) := ∀ r ∈ P, ∃ q ∈ Q, EquivB r.lhs q.lhs ∧ EquivB r.rhs q.rhs

structure Same (P Q : List (Equation sig)) : Prop where
  forward : Includes P Q
  backward : Includes Q P

/-- Per-equation rearrangement is enough, even when the rewrite table
also includes unrelated symbols. Flattened operands can be permuted
independently for each rule. -/
theorem Same.reorder (rules : List (Equation sig)) (prepare : Equation sig → Equation sig)
    (cert : ∀ r ∈ rules, prepare r = r ∨ ∃ f xs ys, xs.Perm ys ∧
      ACRepresentation.decode f xs = some r.lhs ∧ ACRepresentation.decode f ys = some (prepare r).lhs ∧
      EquivB r.rhs (prepare r).rhs) : Same rules (rules.map prepare) := by
  have eq (r) (hr : r ∈ rules) : EquivB r.lhs (prepare r).lhs ∧ EquivB r.rhs (prepare r).rhs := by
    rcases cert r hr with h | ⟨f,_,_,perm,l,r',rhs⟩
    · rw [h]; exact ⟨.refl _,.refl _⟩
    · exact ⟨ACRepresentation.decode_perm f perm _ _ l r',rhs⟩
  constructor
  · intro r hr; exact ⟨_,List.mem_map_of_mem hr,eq r hr⟩
  · intro p hp; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    exact ⟨r,hr,(eq r hr).1.symm,(eq r hr).2.symm⟩

private theorem step {a b : Term sig} (present : Includes P Q) (h : Step (ruleRoot P) a b) :
    StepModulo (ruleRoot Q) a b := by
  induction h with
  | root hr =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := hr
    obtain ⟨q,hq,l,r⟩ := present r hr
    exact ⟨_,_,l.subst σ.image,.root ⟨q,hq,σ,rfl,rfl⟩,(r.subst σ.image).symm⟩
  | comm_left f c _ ih =>
    obtain ⟨x,y,l,st,r⟩ := ih
    exact ⟨_,_,.comm_congr f l (.refl c),.comm_left f c st,.comm_congr f r (.refl c)⟩
  | comm_right f c _ ih =>
    obtain ⟨x,y,l,st,r⟩ := ih
    exact ⟨_,_,.comm_congr f (.refl c) l,.comm_right f c st,.comm_congr f (.refl c) r⟩
  | ac_left f c _ ih =>
    obtain ⟨x,y,l,st,r⟩ := ih
    exact ⟨_,_,.ac_congr f l (.refl c),.ac_left f c st,.ac_congr f r (.refl c)⟩
  | ac_right f c _ ih =>
    obtain ⟨x,y,l,st,r⟩ := ih
    exact ⟨_,_,.ac_congr f (.refl c) l,.ac_right f c st,.ac_congr f (.refl c) r⟩
  | @free f args i u _ ih =>
    obtain ⟨x,y,l,st,r⟩ := ih
    let newArgs := fun j => if j=i then x else args j
    have s' : Step (ruleRoot Q) (newArgs i) y := by simpa [newArgs] using st
    refine ⟨_,_,.free f args newArgs ?_,.free f newArgs i s',.free f _ _ ?_⟩
    · intro j; by_cases e : j=i
      · subst j; simpa [newArgs] using l
      · simpa [newArgs,e] using EquivB.refl (args j)
    · intro j; by_cases e : j=i
      · subst j; simpa using r
      · simpa [newArgs,e] using EquivB.refl (args j)

private theorem modulo {a b : Term sig} (present : Includes P Q) (h : StepModulo (ruleRoot P) a b) :
    StepModulo (ruleRoot Q) a b := by
  obtain ⟨_,_,e,s,k⟩ := h
  obtain ⟨x,y,l,st,r⟩ := step present s
  exact ⟨x,y,e.trans l,st,r.trans k⟩

private theorem reduces {a b : Term sig} (present : Includes P Q) (h : Reduces (ruleRoot P) a b) :
    Reduces (ruleRoot Q) a b := by
  induction h with
  | basis e => exact .basis e
  | step s => exact .step (modulo present s)
  | trans _ _ l r => exact .trans l r
  | free f a b _ ih => exact .free f a b ih
  | comm f _ _ l r => exact .comm f l r
  | ac f _ _ l r => exact .ac f l r

theorem Same.normal (h : Same P Q) : Normal (ruleRoot P) = Normal (ruleRoot Q) := by
  funext a; apply propext
  exact ⟨fun n b s => n b (modulo h.backward s),fun n b s => n b (modulo h.forward s)⟩

theorem Same.forms (h : Same P Q) : NormalForm (ruleRoot P) = NormalForm (ruleRoot Q) := by
  funext a b; apply propext
  simp only [NormalForm,h.normal]
  exact and_congr_left (fun _ => ⟨reduces h.forward,reduces h.backward⟩)

theorem Same.variants (h : Same P Q) (terms : List (Term sig)) (arms : List (Variant sig)) :
    (CompleteVariants (ruleRoot P) terms arms ∧ ∀ a ∈ arms, a.Reconstructible (ruleRoot P) terms) ↔
    (CompleteVariants (ruleRoot Q) terms arms ∧ ∀ a ∈ arms, a.Reconstructible (ruleRoot Q) terms) := by
  simp only [CompleteVariants,Variant.Sound,Variant.Reconstructible,Variant.Covers,Normalized,h.normal,h.forms]

end Tamarin.Rewriting.RulePresentation
