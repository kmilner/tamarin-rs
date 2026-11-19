import Tamarin.DHPeerInverse

/-! Signed multiplicities for exponents with irreducible opaque factors. A term
outside multiplication, inversion and the unit contributes its entire B class.
A reducible opaque term has no reading, so arbitrary additional equations at
other heads cannot collapse two distinct irreducible factors. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants Cancellation

namespace Balance
variable {sig : Signature}

def plus (a b : Option Int) : Option Int := do return (← a) + (← b)
def minus (a : Option Int) := a.map Neg.neg
private theorem plus_swap (a b : Option Int) : plus a b = plus b a := by
  cases a <;> cases b <;> simp [plus,Int.add_comm]
private theorem plus_assoc (a b c : Option Int) : plus (plus a b) c = plus a (plus b c) := by
  cases a <;> cases b <;> cases c <;> simp [plus,Int.add_assoc]

/-- Only defined readings impose an obligation on descendants. -/
def Preserved (a b : Option Int) := ∀ n, a = some n → b = some n

private theorem reflP (x : Option Int) : Preserved x x := fun _ h => h
private theorem transP {a b c : Option Int} (p : Preserved a b) (q : Preserved b c) : Preserved a c :=
  fun n h => q n (p n h)
private theorem addP {a b c d : Option Int} (p : Preserved a b) (q : Preserved c d) :
    Preserved (plus a c) (plus b d) := by
  cases a <;> cases c <;> simp_all [Preserved,plus]
private theorem negP {a b : Option Int} (p : Preserved a b) : Preserved (minus a) (minus b) := by
  cases a <;> simp_all [Preserved,minus]

noncomputable section
open Classical

def alien (R : Root sig) (k : Class sig) (t : Term sig) : Option Int :=
  if Normal R t then some (if classOf t = k then 1 else 0) else none

private theorem alien_eq {R : Root sig} {k : Class sig} {a b : Term sig} (h : EquivB a b) :
    alien R k a = alien R k b := by simp only [alien,normal_equiv R h,show classOf a = classOf b from Quotient.sound h]

private theorem alien_red {R : Root sig} {k : Class sig} {a b : Term sig} (h : Reduces R a b) :
    Preserved (alien R k a) (alien R k b) := by
  by_cases hn : Normal R a
  · rw [alien_eq (normal_reduces_equiv h hn)]
    apply reflP
  · simp [Preserved,alien,hn]

def read (s : Symbols sig) (R : Root sig) (k : Class sig) : Term sig → Option Int
  | .ac f a b => if f = s.mul then plus (read s R k a) (read s R k b) else alien R k (.ac f a b)
  | .free f xs =>
    if h : f = s.inv then minus (read s R k (xs ⟨0, by rw [h,s.invArity]; decide⟩))
    else if f = s.one then some 0 else alien R k (.free f xs)
  | .var v => alien R k (.var v)
  | .atom a => alien R k (.atom a)
  | .comm f a b => alien R k (.comm f a b)

private theorem oneInv (s : Symbols sig) : s.one ≠ s.inv := by
  intro h; have := s.oneArity; rw [h,s.invArity] at this; contradiction

@[simp] theorem read_one (s : Symbols sig) (R : Root sig) (k : Class sig) :
    read s R k s.product.one = some 0 := by simp [Symbols.product,read,oneInv]

@[simp] theorem read_inv (s : Symbols sig) (R : Root sig) (k : Class sig) (a) :
    read s R k (s.product.inv a) = minus (read s R k a) := by simp [Symbols.product,read]

@[simp] theorem read_mul (s : Symbols sig) (R : Root sig) (k : Class sig) (a b) :
    read s R k (s.product.mul a b) = plus (read s R k a) (read s R k b) := by simp [Symbols.product,DHProduct.Ops.mul,read]

theorem equiv (s : Symbols sig) (R : Root sig) (k : Class sig) {t u} (e : EquivB t u) :
    read s R k t = read s R k u := by
  induction e with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b h ih =>
    simp only [read]
    split
    · rw [ih]
    · split
      · rfl
      · exact alien_eq (.free f a b h)
  | comm_swap f a b => exact alien_eq (.comm_swap f a b)
  | comm_congr f h l _ _ => exact alien_eq (.comm_congr f h l)
  | ac_congr f h l ih ik =>
    by_cases eq : f = s.mul
    · simp [read,eq,ih,ik]
    · simpa [read,eq] using (alien_eq (R := R) (k := k) (.ac_congr f h l))
  | ac_swap f a b =>
    by_cases eq : f = s.mul
    · simp [read,eq,plus_swap]
    · simpa [read,eq] using (alien_eq (R := R) (k := k) (.ac_swap f a b))
  | ac_assoc f a b c =>
    by_cases eq : f = s.mul
    · simp [read,eq,plus_assoc]
    · simpa [read,eq] using (alien_eq (R := R) (k := k) (.ac_assoc f a b c))

theorem defined (s : Symbols sig) (R : Root sig) (k : Class sig) {t : Term sig} (hn : Normal R t) :
    ∃ n, read s R k t = some n := by
  induction t with
  | var | atom | comm => simp [read,alien,hn]
  | ac f a b ia ib =>
    by_cases eq : f = s.mul
    · obtain ⟨m,hm⟩ := ia (normal_ac_children _ hn).1
      obtain ⟨n,hq⟩ := ib (normal_ac_children _ hn).2
      simp [read,eq,hm,hq,plus]
    · simp [read,eq,alien,hn]
  | free f xs ih =>
    simp only [read]; split
    · next eq =>
      let i : Fin (sig.arity f) := ⟨0,by rw [eq,s.invArity]; decide⟩
      obtain ⟨n,h⟩ := ih i (normal_free_child _ _ hn i)
      change ∃ m, minus (read s R k (xs i)) = some m
      rw [h]; exact ⟨_,rfl⟩
    · split <;> simp [alien,hn]

/-- Congruence and arbitrary interleavings of steps preserve every defined
multiplicity if the actual root steps do. -/
theorem reduces (s : Symbols sig) (R : Root sig) (k : Class sig)
    (root : ∀ a b, R a b → Preserved (read s R k a) (read s R k b)) {t u}
    (h : Reduces R t u) : Preserved (read s R k t) (read s R k u) := by
  have freeC (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig)
      (red : Reduces R (.free f a) (.free f b))
      (hyp : ∀ i, Preserved (read s R k (a i)) (read s R k (b i))) :
      Preserved (read s R k (.free f a)) (read s R k (.free f b)) := by
    simp only [read]; split
    · exact negP (hyp _)
    · split
      · apply reflP
      · exact alien_red red
  have acC (f : sig.ACSym) (a b c d : Term sig) (red : Reduces R (.ac f a b) (.ac f c d))
      (ha : Preserved (read s R k a) (read s R k c)) (hb : Preserved (read s R k b) (read s R k d)) :
      Preserved (read s R k (.ac f a b)) (read s R k (.ac f c d)) := by
    by_cases eq : f = s.mul
    · simpa [read,eq] using addP ha hb
    · simpa [read,eq] using (alien_red (k := k) red)
  have stepRed {a b : Term sig} (hs : Step R a b) : Reduces R a b :=
    .step ⟨_,_,.refl _,hs,.refl _⟩
  have one {a b : Term sig} (hs : Step R a b) : Preserved (read s R k a) (read s R k b) := by
    induction hs with
    | root h => exact root _ _ h
    | free f xs i step ih =>
      apply freeC _ _ _ (stepRed (.free f xs i step))
      intro j; split
      · next h => subst j; exact ih
      · apply reflP
    | comm_left f c step _ => exact alien_red (stepRed (.comm_left f c step))
    | comm_right f c step _ => exact alien_red (stepRed (.comm_right f c step))
    | ac_left f c step ih => exact acC _ _ _ _ _ (stepRed (.ac_left f c step)) ih (reflP _)
    | ac_right f c step ih => exact acC _ _ _ _ _ (stepRed (.ac_right f c step)) (reflP _) ih
  induction h with
  | basis e => rw [equiv s R k e]; apply reflP
  | step hs =>
    obtain ⟨a,b,eq,step,eq'⟩ := hs
    rw [equiv s R k eq,← equiv s R k eq']
    exact one step
  | trans _ _ ih ik => exact transP ih ik
  | free f a b h ih => exact freeC f a b (.free f a b h) ih
  | comm f h l _ _ => exact alien_red (.comm f h l)
  | ac f h l ih ik => exact acC _ _ _ _ _ (.ac f h l) ih ik

/-- Restrict just the three interpreted heads. Unrelated equations, such as
decryption rules, may appear in the same live table. -/
def Inventory {s : Symbols sig} {T : Table s} (E : ExtraTable T) : Prop :=
  (∀ eq ∈ T.rules, Application eq.lhs) ∧
  ∀ eq ∈ T.rules, (head eq.lhs = .ac s.mul ∨ head eq.lhs = .free s.inv ∨ head eq.lhs = .free s.one) →
    (∃ r : Rule, (r = .inverse ∨ r = .inverseRest ∨ r = .inside ∨ r = .insideRest) ∧
      eq = r.instantiate s (fun i => .var (T.actual r i))) ∨
    ∃ r : ExtraRule, eq = r.instantiate s (fun i => .var (E.actual r i))

theorem read_alien (s : Symbols sig) (R : Root sig) (k : Class sig) (t : Term sig)
    (hm : head t ≠ .ac s.mul) (hi : head t ≠ .free s.inv) (ho : head t ≠ .free s.one) :
    read s R k t = alien R k t := by
  cases t with
  | ac f a b => simp [read,show f ≠ s.mul from fun eq => hm (eq ▸ rfl)]
  | free f xs =>
    simp [read,show f ≠ s.inv from fun eq => hi (eq ▸ rfl),show f ≠ s.one from fun eq => ho (eq ▸ rfl)]
  | var | atom | comm => rfl

private theorem exponent_rule (s : Symbols sig) (R : Root sig) (k : Class sig) (e : Fin 3 → Term sig)
    (r : Rule) (tag : r = .inverse ∨ r = .inverseRest ∨ r = .inside ∨ r = .insideRest) :
    Preserved (read s R k (r.equation.1.eval s e)) (read s R k (r.equation.2.eval s e)) := by
  rcases tag with rfl | rfl | rfl | rfl
  all_goals
    simp only [Rule.equation, Expr.eval, read, ↓reduceIte, oneInv]
    cases read s R k (e 0) <;> cases read s R k (e 1) <;> cases read s R k (e 2) <;>
      simp [Preserved,plus,minus] <;> omega

private theorem extra_rule (s : Symbols sig) (R : Root sig) (k : Class sig) (e : Fin 3 → Term sig)
    (r : ExtraRule) : Preserved (read s R k (r.equation.1.eval s e)) (read s R k (r.equation.2.eval s e)) := by
  cases r
  all_goals
    simp only [ExtraRule.equation, Expr.eval, read, ↓reduceIte, oneInv]
    cases read s R k (e 0) <;> cases read s R k (e 1) <;> cases read s R k (e 2) <;>
      simp [Preserved,plus,minus] <;> omega

theorem Inventory.reduces {s : Symbols sig} {T : Table s} {E : ExtraTable T} (inventory : Inventory E)
    (k : Class sig) {t u} (path : Reduces (ruleRoot T.rules) t u) :
    Preserved (read s (ruleRoot T.rules) k t) (read s (ruleRoot T.rules) k u) := by
  apply Balance.reduces _ _ _ _ path
  intro a b hr
  by_cases recognized : head a = .ac s.mul ∨ head a = .free s.inv ∨ head a = .free s.one
  · obtain ⟨eq,mem,σ,rfl,rfl⟩ := hr
    rw [instance_head eq (inventory.1 eq mem) σ] at recognized
    rcases inventory.2 eq mem recognized with ⟨r,tag,rfl⟩ | ⟨r,rfl⟩
    · simpa [Rule.instantiate,Expr.subst_eval] using exponent_rule s (ruleRoot T.rules) k
        (fun i => σ.apply (.var (T.actual r i))) r tag
    · simpa [ExtraRule.instantiate,Expr.subst_eval] using extra_rule s (ruleRoot T.rules) k
        (fun i => σ.apply (.var (E.actual r i))) r
  · rw [read_alien _ _ _ _ (fun h => recognized (.inl h)) (fun h => recognized (.inr (.inl h))) (fun h => recognized (.inr (.inr h)))]
    have hn : ¬ Normal (ruleRoot T.rules) a := fun n => n _ ⟨_,_,.refl _,.root hr,.refl _⟩
    simp [alien,hn,Preserved]

end
end Balance
end Tamarin.Rewriting.DHPeer
