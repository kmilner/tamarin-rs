import Tamarin.ACUnifierExclusion
import Tamarin.ObservationRepresentative

/-! A binary AC context can expose changing operands when every reachable pair
still consists of two indivisible factors and the active rules cannot fire there. -/
namespace Tamarin.Rewriting.GuardedACContext
open Cancellation ConstructorVariants
variable {s : Signature} {R : Root s} {f : s.ACSym} {a b : Term s}

structure Guard (R : Root s) (f : s.ACSym) (a b : Term s) : Prop where
  left : ∀ l, Reduces R a l → flatten f l = [classOf l]
  right : ∀ r, Reduces R b r → flatten f r = [classOf r]
  excluded : ∀ l r, Reduces R a l → Reduces R b r →
    ∀ p q, EquivB (.ac f l r) p → ¬R p q

private def PairView (R : Root s) (f : s.ACSym) (a b t : Term s) :=
  ∃ l r, Reduces R a l ∧ Reduces R b r ∧ EquivB (.ac f l r) t

private theorem transport {t u : Term s} (h : PairView R f a b t) (e : EquivB t u) :
    PairView R f a b u := by
  obtain ⟨l,r,hl,hr,eq⟩ := h
  exact ⟨l,r,hl,hr,eq.trans e⟩

private theorem congr (guard : Guard R f a b) {g c d l r}
    (cl : Reduces R c l) (dr : Reduces R d r) (h : PairView R f a b (.ac g c d)) :
    PairView R f a b (.ac g l r) := by
  obtain ⟨x,y,hx,hy,eq⟩ := h
  obtain rfl := Head.ac.inj eq.head_eq
  rcases (AtomicACPair.equiv_iff f x y c d (guard.left x hx) (guard.right y hy)).mp eq with
    ⟨xc,yd⟩ | ⟨xd,yc⟩
  · exact ⟨l,r,(hx.trans (.basis xc)).trans cl,(hy.trans (.basis yd)).trans dr,.refl _⟩
  · exact ⟨r,l,(hx.trans (.basis xd)).trans dr,(hy.trans (.basis yc)).trans cl,.ac_swap ..⟩

theorem reduces_view (guard : Guard R f a b) {u} (red : Reduces R (.ac f a b) u) :
    ∃ l r, Reduces R a l ∧ Reduces R b r ∧ EquivB (.ac f l r) u := by
  have go {x y : Term s} (h : Reduces R x y) : PairView R f a b x → PairView R f a b y := by
    induction h with
    | basis e => exact fun v => transport v e
    | trans _ _ ih ik => exact fun v => ik (ih v)
    | free | comm => rintro ⟨_,_,_,_,eq⟩; cases eq.head_eq
    | ac g cl dr _ _ => exact congr guard cl dr
    | step st =>
      intro v
      obtain ⟨p,q,before,step,after⟩ := st
      have vp := transport v before
      apply transport _ after
      cases step with
      | root hr =>
        obtain ⟨l,r,hl,hr',eq⟩ := vp
        exact (guard.excluded l r hl hr' _ _ eq hr).elim
      | free | comm_left | comm_right =>
        obtain ⟨_,_,_,_,eq⟩ := vp
        cases eq.head_eq
      | ac_left _ _ child => exact congr guard (.step ⟨_,_,.refl _,child,.refl _⟩) (.basis (.refl _)) vp
      | ac_right _ _ child => exact congr guard (.basis (.refl _)) (.step ⟨_,_,.refl _,child,.refl _⟩) vp
  exact go red ⟨a,b,.basis (.refl _),.basis (.refl _),.refl _⟩

theorem normalForm_iff (guard : Guard R f a b) (ta : HasSort a (s.acSort f)) (tb : HasSort b (s.acSort f))
    (sa : a.rootSort = s.acSort f) (sb : b.rootSort = s.acSort f) (u : Term s) :
    NormalForm R (.ac f a b) u ↔ ∃ l r, NormalForm R a l ∧ NormalForm R b r ∧ EquivB (.ac f l r) u := by
  constructor
  · intro nf
    obtain ⟨l,r,hl,hr,eq⟩ := reduces_view guard nf.1
    have ns := normal_ac_children _ ((normal_equiv R eq).mpr nf.2.1)
    have ok := Term.checkSort_complete (nf.2.2 _ (HasSort.ac f _ _ ta tb))
    rw [←SortClash.check_equiv eq] at ok
    simp only [Term.checkSort,Bool.and_eq_true] at ok
    exact ⟨l,r,⟨hl,ns.1,fun _ hs => .widen (Term.checkSort_sound _ _ ok.1.2) (sa ▸ Term.rootSort_le hs)⟩,
      ⟨hr,ns.2,fun _ hs => .widen (Term.checkSort_sound _ _ ok.2) (sb ▸ Term.rootSort_le hs)⟩,eq⟩
  · rintro ⟨l,r,hl,hr,eq⟩
    refine ⟨(.ac f hl.1 hr.1 : Reduces R _ _).trans (.basis eq),(normal_equiv R eq).mp ?_,?_⟩
    · intro v st
      obtain ⟨p,q,h,root,_⟩ := (ACUnifierExclusion.pair_step_iff (guard.left _ hl.1)
        (guard.right _ hr.1) hl.2.1 hr.2.1).mp st
      exact guard.excluded _ _ hl.1 hr.1 _ _ h root
    · intro sort hs
      apply Term.checkSort_sound
      rw [←SortClash.check_equiv eq]
      exact Term.checkSort_complete (.widen (.ac f _ _ (hl.2.2 _ ta) (hr.2.2 _ tb)) (Term.rootSort_le hs))

/-- Concrete admission inspects only the two persistent heads and the full
active equation bucket. A repeated pattern has the same instance on both
sides. Larger left sides cannot shrink to two factors under substitution. -/
def Fits (t : Term s) (g : s.FreeSym) : Prop :=
  match t with
  | .var _ => True
  | .free h _ => h = g
  | _ => False

private theorem fits_of_head {t : Term s} {g : s.FreeSym} {σ : Substitution s}
    (h : head (σ.apply t) = .free g) : Fits t g := by
  cases t <;> simp_all [Fits,Substitution.apply,Term.subst,head,headModel,Model.eval]

def RuleExcluded (f : s.ACSym) (g h : s.FreeSym) (lhs : Term s) : Prop :=
  2 < (flatten f lhs).length ∨ ∃ x y, lhs = .ac f x y ∧
    (x = y ∨ (¬(Fits x g ∧ Fits y h) ∧ ¬(Fits x h ∧ Fits y g)))

theorem of_free_heads (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (g h : s.FreeSym) (different : g ≠ h) (xs ys)
    (ig : ∀ args v, ¬ruleRoot rules (.free g args) v)
    (ih : ∀ args v, ¬ruleRoot rules (.free h args) v)
    (bucket : ∀ r ∈ rules, head r.lhs = .ac f → RuleExcluded f g h r.lhs) :
    Guard (ruleRoot rules) f (.free g xs) (.free h ys) := by
  constructor
  · intro l hl; obtain ⟨ls,rfl,_⟩ := StableVariants.reduces_free_view g ig hl; rfl
  · intro r hr; obtain ⟨rs,rfl,_⟩ := StableVariants.reduces_free_view h ih hr; rfl
  · rintro l r hl hr p q eq ⟨rule,mem,σ,rfl,_⟩
    obtain ⟨ls,rfl,_⟩ := StableVariants.reduces_free_view g ig hl
    obtain ⟨rs,rfl,_⟩ := StableVariants.reduces_free_view h ih hr
    rcases bucket rule mem ((instance_head rule (apps rule mem) σ).symm.trans eq.head_eq.symm) with large|⟨x,y,e,miss⟩
    · have size := (flatten_equiv f eq).length_eq
      rw [flatten_ac] at size
      have limit := ACUnifierExclusion.factor_lower_bound f rule.lhs σ
      change 2 = _ at size
      omega
    · rw [e] at eq
      rcases (AtomicACPair.equiv_iff f _ _ _ _ rfl rfl).mp eq with ⟨gx,hy⟩|⟨gy,hx⟩
      · rcases miss with rfl|m
        · exact different (Head.free.inj (gx.head_eq.trans hy.head_eq.symm))
        · exact m.1 ⟨fits_of_head gx.head_eq.symm,fits_of_head hy.head_eq.symm⟩
      · rcases miss with rfl|m
        · exact different (Head.free.inj (gy.head_eq.trans hx.head_eq.symm))
        · exact m.2 ⟨fits_of_head hx.head_eq.symm,fits_of_head gy.head_eq.symm⟩

/-- Retaining both child observations in the join preserves irredundancy:
the two distinct heads recover the ordered slots from the parent's value. -/
theorem distinct_slots (g h : s.FreeSym) (different : g ≠ h) (xs ys xs' ys') :
    EquivB (.ac f (.free g xs) (.free h ys)) (.ac f (.free g xs') (.free h ys')) ↔
      EquivB (.free g xs) (.free g xs') ∧ EquivB (.free h ys) (.free h ys') := by
  rw [AtomicACPair.equiv_iff f _ _ _ _ rfl rfl]
  exact ⟨fun e => e.elim id (fun c => (different (Head.free.inj c.1.head_eq)).elim),Or.inl⟩
end Tamarin.Rewriting.GuardedACContext
