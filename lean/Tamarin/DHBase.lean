import Tamarin.DHPeerClassification
import Tamarin.RootNormalForms

/-! Root analysis for a power under the three exponentiation rules in the
Tamarin DH presentation. Other heads may have arbitrary active equations. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig}

def Symbols.neutralTerm (s : Symbols sig) : Term sig :=
  .free s.neutral fun i => Fin.elim0 (s.neutralArity ▸ i)

/-- Every live rule at this head is exactly one of these three equations. -/
def PowerBucket (T : Table s) : Prop :=
  (∀ eq ∈ T.rules, Application eq.lhs) ∧
  ∀ eq ∈ T.rules, head eq.lhs = .free s.pow →
    ∃ r : Rule, (r = .expOne ∨ r = .tower ∨ r = .neutral) ∧
      eq = r.instantiate s (fun i => .var (T.actual r i))

private def ix (s : Symbols sig) (i : Fin 2) : Fin (sig.arity s.pow) := ⟨i.val, by have h := s.powArity; have hi := i.isLt; omega⟩
private theorem index_val (s : Symbols sig) (i : Fin 2) : (ix s i).val = i.val := by
  rfl

theorem splitPower (s : Symbols sig) {t : Term sig} (h : head t = .free s.pow) :
    ∃ a b, t = s.power a b := by
  cases t <;> cases h
  rename_i xs
  refine ⟨xs (ix s 0), xs (ix s 1), congrArg (Term.free s.pow) (funext fun i => ?_)⟩
  have bound := i.isLt
  have ar := s.powArity
  change xs i = (if i.val = 0 then _ else _)
  split <;> apply congrArg xs <;> apply Fin.ext <;> rw [index_val] <;> simp_all <;> omega

theorem nullary {f : sig.FreeSym} (arity : sig.arity f = 0)
    {t : Term sig} (h : head t = .free f) :
    t = .free f (fun i => Fin.elim0 (arity ▸ i)) := by
  cases t <;> cases h
  exact congrArg (Term.free f) (funext fun i => Fin.elim0 (arity ▸ i))

private theorem proj {a b c d : Term sig} (e : EquivB (s.power a b) (s.power c d)) :
    EquivB a c ∧ EquivB b d := by
  have args := (Matching.free_equiv_iff ..).mp e
  exact ⟨by simpa [index_val] using args (ix s 0), by simpa [index_val] using args (ix s 1)⟩

private theorem sorts {a b : Term sig} (h : HasSort (s.power a b) .msg) :
    HasSort a .msg ∧ HasSort b .msg := by
  have hs := Term.checkSort_complete h
  simp only [Symbols.power, Term.checkSort, Bool.and_eq_true, List.all_eq_true] at hs
  have arg := fun i => Term.checkSort_sound _ _ (hs.2 i (List.mem_finRange i))
  exact ⟨by simpa [s.powInput,index_val] using arg (ix s 0),
    by simpa [s.powInput,index_val] using arg (ix s 1)⟩

private def env3 (a b c : Term sig) (i : Fin 3) : Term sig :=
  if i = 0 then a else if i = 1 then b else c
private theorem typed3 {a b c : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg)
    (hc : HasSort c .msg) : ∀ i, HasSort (env3 a b c i) .msg := by
  intro i; unfold env3; split <;> first | assumption | split <;> assumption

/-- Every possible root step on B-equivalent arguments, including its result. -/
inductive PowerStep (s : Symbols sig) (a e out : Term sig) : Prop where
  | one (he : head e = .free s.one) (value : EquivB out a) : PowerStep s a e out
  | neutral (ha : head a = .free s.neutral) (value : EquivB out s.neutralTerm) : PowerStep s a e out
  | tower {b p} (base : EquivB a (s.power b p))
      (value : EquivB out (s.power b (.ac s.mul p e))) : PowerStep s a e out

theorem PowerBucket.root {T : Table s} (bucket : PowerBucket T) (a e : Term sig) {t out}
    (input : EquivB (s.power a e) t) (root : ruleRoot T.rules t out) : PowerStep s a e out := by
  obtain ⟨eq,mem,σ,rfl,rfl⟩ := root
  have hh : head eq.lhs = .free s.pow := (instance_head eq (bucket.1 eq mem) σ).symm.trans input.head_eq.symm
  obtain ⟨r,tag,rfl⟩ := bucket.2 eq mem hh
  rcases tag with rfl | rfl | rfl
  all_goals
    simp only [Rule.instantiate, Expr.subst_eval] at input ⊢
    obtain ⟨left,right⟩ := proj input
  · exact .one right.head_eq left.symm
  · apply PowerStep.tower left
    apply EquivB.free; intro i; split
    · exact .refl _
    · exact .ac_congr _ (.refl _) right.symm
  · exact .neutral left.head_eq (.refl _)

/-- This characterization refers to normality of the input children under
the entire rule table. A shaped peer cannot hide a reducible exponent. -/
theorem PowerBucket.normal_iff {T : Table s} (bucket : PowerBucket T) {a e : Term sig}
    (ha : HasSort a .msg) (he : HasSort e .msg) :
    Normal (ruleRoot T.rules) (s.power a e) ↔
      Normal (ruleRoot T.rules) a ∧ Normal (ruleRoot T.rules) e ∧
      head a ≠ .free s.pow ∧ head a ≠ .free s.neutral ∧ head e ≠ .free s.one := by
  constructor
  · intro hn
    have ban {t u : Term sig} (eq : s.power a e = t) (r : ruleRoot T.rules t u) : False :=
      hn u ⟨t, u, eq ▸ .refl _, .root r, .refl _⟩
    have child := normal_free_child s.pow _ hn
    refine ⟨by simpa [index_val] using child (ix s 0), by simpa [index_val] using child (ix s 1),
      ?_, ?_, ?_⟩
    · intro hh
      obtain ⟨b,p,eq⟩ := splitPower s hh
      obtain ⟨hb,hp⟩ := sorts (eq ▸ ha)
      exact ban (by rw [eq]; rfl) (T.fireRoot .tower _ (typed3 hb hp he))
    · intro hh
      exact ban (by rw [nullary s.neutralArity hh]; rfl) (T.fireRoot .neutral _ (typed3 he ha he))
    · intro hh
      exact ban (by rw [nullary s.oneArity hh]; rfl) (T.fireRoot .expOne _ (typed3 ha he ha))
  · rintro ⟨na,ne,ap,an,eo⟩
    apply normal_free_no_root
    · intro i
      change Normal _ (if _ then _ else _)
      split <;> assumption
    · intro ys hy b hr
      cases bucket.root a e (.free _ _ _ hy) hr with
      | one bad _ => exact eo bad
      | neutral bad _ => exact an bad
      | tower base _ => exact ap base.head_eq

/-- If a power with normal children has a single root result modulo B,
any genuine normalization continues from that result. The result can
itself contain a reducible exponent product. -/
private theorem first_root {R : Root sig} (f : sig.FreeSym)
    (xs : Fin (sig.arity f) → Term sig) (v : Term sig)
    (hn : ∀ i, Normal R (xs i))
    (only : ∀ y z, EquivB (.free f xs) y → R y z → EquivB z v)
    {out} (red : Reduces R (.free f xs) out) :
    EquivB (.free f xs) out ∨ Reduces R v out := by
  have walk {l r : Term sig} (path : Reduces R l r) : EquivB (.free f xs) l →
      EquivB (.free f xs) r ∨ Reduces R v r := by
    induction path with
    | basis eq => exact fun h => .inl (h.trans eq)
    | step step =>
      intro eq
      obtain ⟨t,u,ht,hs,hu⟩ := step
      obtain ⟨ys,w,hy,hr,hw⟩ := (stepModulo_free_iff hn).mp ⟨t,u,eq.trans ht,hs,hu⟩
      exact .inr (.basis ((only _ _ (.free _ _ _ hy) hr).symm.trans hw))
    | trans _ rest ih ik =>
      intro h
      rcases ih h with lhs | rhs
      · exact ik lhs
      · exact .inr (rhs.trans rest)
    | free g a b rs _ =>
      intro h
      obtain rfl := Head.free.inj h.head_eq
      have point := (Matching.free_equiv_iff _ _ _).mp h
      exact .inl (.free _ _ _ fun i => (point i).trans
        (normal_reduces_equiv (rs i) ((normal_equiv _ (point i)).mp (hn i))))
    | comm | ac => intro h; cases h.head_eq
  exact walk red (.refl _)

theorem PowerBucket.tower_tail {T : Table s} (bucket : PowerBucket T) {b p e out : Term sig}
    (hb : HasSort b .msg) (hp : HasSort p .msg) (he : HasSort e .msg)
    (nb : Normal (ruleRoot T.rules) (s.power b p)) (ne : Normal (ruleRoot T.rules) e)
    (unit : head e ≠ .free s.one)
    (nf : NormalForm (ruleRoot T.rules) (s.power (s.power b p) e) out) :
    Reduces (ruleRoot T.rules) (s.power b (.ac s.mul p e)) out := by
  have only : ∀ y z, EquivB (s.power (s.power b p) e) y → ruleRoot T.rules y z →
      EquivB z (s.power b (.ac s.mul p e)) := by
    intro y z h hr
    cases bucket.root _ _ h hr with
    | one bad _ => exact False.elim (unit bad)
    | neutral bad _ =>
      have bad' := Head.free.inj bad
      have := s.neutralArity
      have := s.powArity
      rw [bad'] at this
      omega
    | tower eq res =>
      obtain ⟨lhs,rhs⟩ := proj eq
      apply res.trans
      apply EquivB.free; intro i; split
      · exact lhs.symm
      · exact .ac_congr _ rhs.symm (.refl _)
  have normals : ∀ i : Fin (sig.arity s.pow), Normal (ruleRoot T.rules)
      (if i.val = 0 then s.power b p else e) := by intro i; split <;> assumption
  rcases first_root s.pow _ _ normals only nf.1 with same | tail
  · have blocked := (normal_equiv _ same).mpr nf.2.1
    exact False.elim (blocked _ ⟨_,_,.refl _,.root (T.fireRoot .tower _ (typed3 hb hp he)),.refl _⟩)
  · exact tail


private theorem underPower {R : Root sig} {g : sig.FreeSym} {b e : Term sig}
    {xs ys : Fin (sig.arity g) → Term sig} (nb : Normal R b)
    (h : EquivB (s.power b e) (.free g xs)) (r : ∀ i, Reduces R (xs i) (ys i)) :
    ∃ v, Reduces R e v ∧ EquivB (.free g ys) (s.power b v) := by
  obtain rfl := Head.free.inj h.head_eq
  have args := (Matching.free_equiv_iff ..).mp h
  have bp : EquivB b (xs (ix s 0)) := by simpa [index_val] using args (ix s 0)
  have ep : EquivB e (xs (ix s 1)) := by simpa [index_val] using args (ix s 1)
  have bEq := normal_reduces_equiv ((Reduces.basis bp).trans (r _)) nb
  refine ⟨ys (ix s 1), (Reduces.basis ep).trans (r _), .free _ _ _ fun i => ?_⟩
  have hi := i.isLt
  have ar := s.powArity
  change EquivB _ (if i.val = 0 then _ else _)
  split <;> rename_i branch
  · have eq : i = ix s 0 := Fin.ext (by simpa [index_val] using branch)
    exact eq ▸ bEq.symm
  · have eq : i = ix s 1 := Fin.ext (by rw [index_val]; change i.val = 1; omega)
    exact eq ▸ .refl _

/-- Every reduction of a power over a fixed normal base follows its exponent.
If the exponent reaches the unit, the power can also collapse to its base. -/
theorem PowerBucket.fixed_base {T : Table s} (bucket : PowerBucket T) {b e out : Term sig}
    (nb : Normal (ruleRoot T.rules) b) (bp : head b ≠ .free s.pow)
    (bn : head b ≠ .free s.neutral) (r : Reduces (ruleRoot T.rules) (s.power b e) out) :
    (∃ v, Reduces (ruleRoot T.rules) e v ∧ EquivB out (s.power b v)) ∨
      (Reduces (ruleRoot T.rules) e s.product.one ∧ EquivB out b) := by
  have walk {l t : Term sig} (path : Reduces (ruleRoot T.rules) l t) :
      ∀ e, EquivB (s.power b e) l →
      (∃ v, Reduces (ruleRoot T.rules) e v ∧ EquivB t (s.power b v)) ∨
      (Reduces (ruleRoot T.rules) e s.product.one ∧ EquivB t b) := by
    induction path with
    | basis eq => exact fun e h => .inl ⟨e,.basis (.refl _),(h.trans eq).symm⟩
    | trans _ rest ih ik =>
      intro e h
      rcases ih e h with ⟨v,rv,ev⟩ | ⟨one,eb⟩
      · rcases ik v ev.symm with ⟨w,rw,ew⟩ | ⟨one,eb⟩
        · exact .inl ⟨w,rv.trans rw,ew⟩
        · exact .inr ⟨rv.trans one,eb⟩
      · exact .inr ⟨one,(normal_reduces_equiv ((Reduces.basis eb.symm).trans rest) nb).symm⟩
    | free g xs ys rs _ => exact fun _ h => .inl (underPower nb h rs)
    | comm | ac => intro e h; cases h.head_eq
    | step step =>
      intro e h
      obtain ⟨l,t,hl,raw,ht⟩ := step
      have align := h.trans hl
      cases raw with
      | root rr =>
        cases bucket.root _ _ align rr with
        | tower base _ => exact False.elim (bp base.head_eq)
        | neutral hh _ => exact False.elim (bn hh)
        | one hh val =>
          have eq : e = s.product.one := nullary s.oneArity hh
          exact .inr ⟨eq ▸ .basis (.refl _),ht.symm.trans val⟩
      | free g xs i inner =>
        obtain ⟨v,rv,ev⟩ := underPower nb align (ys := fun j => if j = i then _ else xs j)
          (fun j => by
            split <;> rename_i eq
            · subst j; exact .step ⟨_,_,.refl _,inner,.refl _⟩
            · exact .basis (.refl _))
        exact .inl ⟨v,rv,ht.symm.trans ev⟩
      | comm_left | comm_right | ac_left | ac_right => cases align.head_eq
  exact walk r e (.refl _)


private theorem power_typed {b e : Term sig} (hb : HasSort b .msg) (he : HasSort e .msg) :
    HasSort (s.power b e) .msg := by
  rw [← s.powSort]; apply HasSort.free
  intro i; rw [s.powInput]; split <;> assumption

private theorem typed_basis {a b : Term sig} {k} (eq : EquivB a b) (h : HasSort a k) :
    HasSort b k := Term.checkSort_sound _ _ ((SortClash.check_equiv eq k) ▸ Term.checkSort_complete h)

/-- Project a complete tower normalization onto an exponent normal form.
This covers paths that simplify the product in any order and paths that
eliminate a unit power before or after regrouping factors. -/
theorem PowerBucket.tower_normal_value {T : Table s} (bucket : PowerBucket T) {b p e out : Term sig}
    (hb : HasSort b .msg) (hp : HasSort p .msg) (he : HasSort e .msg)
    (nb : Normal (ruleRoot T.rules) (s.power b p)) (ne : Normal (ruleRoot T.rules) e)
    (unit : head e ≠ .free s.one) (unitNormal : Normal (ruleRoot T.rules) s.product.one)
    (nf : NormalForm (ruleRoot T.rules) (s.power (s.power b p) e) out) :
    ∃ v, NormalForm (ruleRoot T.rules) (.ac s.mul p e) v ∧
      ((v = s.product.one ∧ EquivB out b) ∨ (head v ≠ .free s.one ∧ EquivB out (s.power b v))) := by
  have tail := bucket.tower_tail hb hp he nb ne unit nf
  obtain ⟨base,_,plain,nonneutral,_⟩ := (bucket.normal_iff hb hp).mp nb
  have makeForm {v} (red : Reduces (ruleRoot T.rules) (.ac s.mul p e) v)
      (norm : Normal (ruleRoot T.rules) v) (typed : HasSort v .msg) :
      NormalForm (ruleRoot T.rules) (.ac s.mul p e) v :=
    ⟨red,norm,fun _ h => .widen typed (s.mulSort ▸ Term.rootSort_le h)⟩
  rcases bucket.fixed_base base plain nonneutral tail with ⟨v,rv,ev⟩ | ⟨rv,ev⟩
  · have form := (normal_equiv _ ev).mp nf.2.1
    have typed := sorts (typed_basis ev (nf.2.2 _ (power_typed (power_typed hb hp) he)))
    obtain ⟨_,nv,_,_,nonunit⟩ := (bucket.normal_iff typed.1 typed.2).mp form
    exact ⟨v,makeForm rv nv typed.2,.inr ⟨nonunit,ev⟩⟩
  · have typed : HasSort s.product.one .msg := by
      rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)
    exact ⟨_,makeForm rv unitNormal typed,.inl ⟨rfl,ev⟩⟩

theorem PowerBucket.tower_unique {T : Table s} (bucket : PowerBucket T) {b p e u v : Term sig}
    (hb : HasSort b .msg) (hp : HasSort p .msg) (he : HasSort e .msg)
    (nb : Normal (ruleRoot T.rules) (s.power b p)) (ne : Normal (ruleRoot T.rules) e)
    (unit : head e ≠ .free s.one) (unitNormal : Normal (ruleRoot T.rules) s.product.one)
    (unique : ∀ x y, NormalForm (ruleRoot T.rules) (.ac s.mul p e) x →
      NormalForm (ruleRoot T.rules) (.ac s.mul p e) y → EquivB x y)
    (nu : NormalForm (ruleRoot T.rules) (s.power (s.power b p) e) u)
    (nv : NormalForm (ruleRoot T.rules) (s.power (s.power b p) e) v) : EquivB u v := by
  obtain ⟨x,nx,hx⟩ := bucket.tower_normal_value hb hp he nb ne unit unitNormal nu
  obtain ⟨y,ny,hy⟩ := bucket.tower_normal_value hb hp he nb ne unit unitNormal nv
  have eq := unique _ _ nx ny
  rcases hx with ⟨rfl,bx⟩ | ⟨no,px⟩ <;> rcases hy with ⟨rfl,by'⟩ | ⟨no',py⟩
  · exact bx.trans by'.symm
  · exact False.elim (no' eq.head_eq.symm)
  · exact False.elim (no eq.head_eq)
  · apply px.trans (EquivB.trans _ py.symm)
    apply EquivB.free; intro i; split
    · exact .refl _
    · exact eq


/-- For a received base raised to a normalized nonunit exponent, the only outstanding
uniqueness question lies in the exponent product of a tower. All remaining
root cases are decided by the three rules at the power head. -/
theorem PowerBucket.peer_unique_msg {T : Table s} (bucket : PowerBucket T)
    (unitNormal : Normal (ruleRoot T.rules) s.product.one)
    {Y r u v : Term sig} (products : ∀ p, HasSort p .msg →
      Normal (ruleRoot T.rules) p → head p ≠ .free s.one →
      ∀ x y, NormalForm (ruleRoot T.rules) (.ac s.mul p r) x →
        NormalForm (ruleRoot T.rules) (.ac s.mul p r) y → EquivB x y)
    (sy : HasSort Y .msg) (sm : HasSort r .msg) (nonunit : head r ≠ .free s.one)
    (ny : Normal (ruleRoot T.rules) Y) (nr : Normal (ruleRoot T.rules) r)
    (nu : NormalForm (ruleRoot T.rules) (s.power Y r) u)
    (nv : NormalForm (ruleRoot T.rules) (s.power Y r) v) : EquivB u v := by
  by_cases tower : head Y = .free s.pow
  · obtain ⟨b,p,rfl⟩ := splitPower s tower
    obtain ⟨hb,hp⟩ := sorts sy
    obtain ⟨_,np,_,_,unit⟩ := (bucket.normal_iff hb hp).mp ny
    exact bucket.tower_unique hb hp sm ny nr nonunit unitNormal (products p hp np unit) nu nv
  by_cases neutral : head Y = .free s.neutral
  · have eq : Y = s.neutralTerm := nullary s.neutralArity neutral
    have hn : ∀ i : Fin (sig.arity s.pow), Normal (ruleRoot T.rules) (if i.val = 0 then Y else r) := by
      intro i; split <;> assumption
    have result {x} (nf : NormalForm (ruleRoot T.rules) (s.power Y r) x) : EquivB x Y := by
      apply normalForm_free_root_unique hn ny _ _ nf
      · subst Y; exact ⟨_,_,.refl _,.root (T.fireRoot .neutral _ (typed3 sm sm sm)),.refl _⟩
      · intro ys hyp z hr
        cases bucket.root Y r (.free _ _ _ hyp) hr with
        | neutral _ val => exact eq ▸ val
        | tower base _ => exact False.elim (tower base.head_eq)
        | one hh _ => exact False.elim (nonunit hh)
    exact (result nu).trans (result nv).symm
  · have norm := (bucket.normal_iff sy sm).mpr ⟨ny,nr,tower,neutral,nonunit⟩
    exact (normal_reduces_equiv nu.1 norm).symm.trans (normal_reduces_equiv nv.1 norm)

theorem PowerBucket.peer_unique {T : Table s} (bucket : PowerBucket T)
    (unitNormal : Normal (ruleRoot T.rules) s.product.one)
    (products : ∀ p e, HasSort p .msg → HasSort e .fresh →
      Normal (ruleRoot T.rules) p → Normal (ruleRoot T.rules) e → head p ≠ .free s.one →
      ∀ x y, NormalForm (ruleRoot T.rules) (.ac s.mul p e) x →
        NormalForm (ruleRoot T.rules) (.ac s.mul p e) y → EquivB x y)
    {Y r u v : Term sig} (sy : HasSort Y .msg) (sr : HasSort r .fresh)
    (ny : Normal (ruleRoot T.rules) Y) (nr : Normal (ruleRoot T.rules) r)
    (nu : NormalForm (ruleRoot T.rules) (s.power Y r) u)
    (nv : NormalForm (ruleRoot T.rules) (s.power Y r) v) : EquivB u v := by
  exact bucket.peer_unique_msg unitNormal (fun p hp np unit => products p r hp sr np nr unit)
    sy (.widen sr .fresh_msg) (Factor.of_fresh s sr).nonUnit ny nr nu nv

end Tamarin.Rewriting.DHPeer
