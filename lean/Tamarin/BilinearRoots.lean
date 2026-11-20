import Tamarin.DHStaging
import Tamarin.ContextualReduction
import Tamarin.FreshSubstitution

/-! Bilinear pairing adds two point-action rules and one commutative map rule
to the live DH system. Their schemata share the caller's DH product and power
operators. Normality of each argument is always checked in the full theory. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer
variable {sig : Signature} {s : Symbols sig} {T : Table s}

structure Operators (sig : Signature) where
  pmult : sig.FreeSym
  emap : sig.CSym
  arity : sig.arity pmult = 2
  inputs : ∀ i, sig.inputSort pmult i = .msg
  pointSort : sig.outputSort pmult = .msg
  mapSort : sig.cSort emap = .msg

def Operators.point (β : Operators sig) (a p : Term sig) : Term sig :=
  .free β.pmult (fun i => if i.val = 0 then a else p)

abbrev Operators.map (β : Operators sig) (p q : Term sig) : Term sig := .comm β.emap p q

variable {β : Operators sig}

theorem Operators.point_subst (β : Operators sig) (ρ : Substitution sig) (a p : Term sig) :
    ρ.apply (β.point a p) = β.point (ρ.apply a) (ρ.apply p) := by
  apply congrArg (Term.free _); funext i; change ρ.apply (if _ then _ else _) = _; split <;> rfl

theorem Operators.point_sorted (β : Operators sig) {a p : Term sig} (ha : HasSort a .msg) (hp : HasSort p .msg) :
    HasSort (β.point a p) .msg := by
  rw [← β.pointSort]; apply HasSort.free; intro i; rw [β.inputs]; split <;> assumption

theorem Operators.map_sorted (β : Operators sig) {p q : Term sig} (hp : HasSort p .msg) (hq : HasSort q .msg) :
    HasSort (β.map p q) .msg := β.mapSort ▸ HasSort.comm _ _ _ (β.mapSort ▸ hp) (β.mapSort ▸ hq)

private def idx (β : Operators sig) (i : Fin 2) : Fin (sig.arity β.pmult) :=
  ⟨i.val,by have := β.arity; have := i.isLt; omega⟩

theorem Operators.split (β : Operators sig) {t : Term sig} (h : head t = .free β.pmult) :
    ∃ a p, t = β.point a p := by
  cases t <;> cases h
  rename_i xs
  refine ⟨xs (idx β 0),xs (idx β 1),congrArg (Term.free _) (funext fun i => ?_)⟩
  have := i.isLt
  have := β.arity
  change xs i = (if i.val = 0 then _ else _)
  split <;> apply congrArg xs <;> apply Fin.ext <;> simp_all [idx] <;> omega

theorem Operators.point_types (β : Operators sig) {a p : Term sig} (h : HasSort (β.point a p) .msg) :
    HasSort a .msg ∧ HasSort p .msg := by
  have hs := Term.checkSort_complete h
  simp only [Operators.point,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at hs
  have arg i := Term.checkSort_sound _ _ (hs.2 i (List.mem_finRange i))
  exact ⟨by simpa [idx,β.inputs] using arg (idx β 0),by simpa [idx,β.inputs] using arg (idx β 1)⟩

theorem Operators.point_equiv (β : Operators sig) {a p b q : Term sig}
    (h : EquivB (β.point a p) (β.point b q)) : EquivB a b ∧ EquivB p q := by
  have args := (Matching.free_equiv_iff ..).mp h
  exact ⟨by simpa [idx] using args (idx β 0),by simpa [idx] using args (idx β 1)⟩

theorem Operators.point_congr (β : Operators sig) {a p b q : Term sig} (l : EquivB a b) (r : EquivB p q) :
    EquivB (β.point a p) (β.point b q) := by apply EquivB.free; intro i; split <;> assumption

inductive Rule where | one | nested | extract

def Rule.equation (r : Rule) (s : Symbols sig) (β : Operators sig) (v : Fin 3 → Term sig) : Equation sig :=
  match r with
  | .one => ⟨β.point s.product.one (v 0),v 0⟩
  | .nested => ⟨β.point (v 0) (β.point (v 1) (v 2)),β.point (s.product.mul (v 0) (v 1)) (v 2)⟩
  | .extract => ⟨β.map (v 0) (β.point (v 1) (v 2)),s.power (β.map (v 0) (v 2)) (v 1)⟩

theorem Rule.instantiate_subst (r : Rule) (s : Symbols sig) (β : Operators sig) (v : Fin 3 → Term sig)
    (ρ : Substitution sig) : let w := r.equation s β (fun i => ρ.apply (v i))
    ρ.apply (r.equation s β v).lhs = w.lhs ∧ ρ.apply (r.equation s β v).rhs = w.rhs := by
  have one : ρ.apply s.product.one = s.product.one := by
    apply congrArg (Term.free _); funext i; exact Fin.elim0 (s.oneArity ▸ i)
  have em (a b) : ρ.apply (β.map a b) = β.map (ρ.apply a) (ρ.apply b) := rfl
  have times (a b) : ρ.apply (s.product.mul a b) = s.product.mul (ρ.apply a) (ρ.apply b) := rfl
  cases r <;> simp [Rule.equation,Operators.point_subst,DHExponent.Caller.apply_pow,one,em,times]

/-- The extra equations may occur anywhere in the list and may use their
own sorted variable indices. Each of the two head buckets is exhaustive. -/
structure Inventory (s : Symbols sig) (β : Operators sig) (rules : List (Equation sig)) where
  keys : Rule → Fin 3 → Variable
  typed : ∀ r i, (keys r i).sort = .msg
  distinct : ∀ r, Function.Injective (keys r)
  present : ∀ r : Rule, r.equation s β (fun i => .var (keys r i)) ∈ rules
  apps : ∀ e ∈ rules, Application e.lhs
  onlyPoint : ∀ e ∈ rules, head e.lhs = .free β.pmult → ∃ r : Rule, (r = .one ∨ r = .nested) ∧
    e = r.equation s β (fun i => .var (keys r i))
  onlyMap : ∀ e ∈ rules, head e.lhs = .comm β.emap → e = Rule.extract.equation s β (fun i => .var (keys .extract i))

variable {rules : List (Equation sig)}

/-- Distinct sorted schematic slots admit a single simultaneous substitution
even when the concrete values mention some of those same slots. -/
theorem sorted_assignment {n : Nat} (keys : Fin n → Variable) (injective : Function.Injective keys)
    (v : Fin n → Term sig) (typed : ∀ i, HasSort (v i) (keys i).sort) :
    ∃ ρ : Substitution sig, (fun i => ρ.apply (.var (keys i))) = v := by
  let bs := List.ofFn fun i => (keys i,v i)
  let ρ := Substitution.fromBindings bs (by
    intro k t h; obtain ⟨i,ei⟩ := List.mem_ofFn.mp h; cases ei; exact typed i)
  refine ⟨ρ,funext fun i => ?_⟩
  apply Substitution.lookupBinding_eq_of_mem
  · intro k t u ht hu
    obtain ⟨j,ej⟩ := List.mem_ofFn.mp ht
    obtain ⟨l,el⟩ := List.mem_ofFn.mp hu
    have eq := injective ((congrArg Prod.fst ej).trans (congrArg Prod.fst el).symm)
    exact (congrArg Prod.snd ej).symm.trans (eq ▸ congrArg Prod.snd el)
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem Inventory.fire (I : Inventory s β rules) (r : Rule) (v : Fin 3 → Term sig) (hv : ∀ i, HasSort (v i) .msg) :
    ruleRoot rules (r.equation s β v).lhs (r.equation s β v).rhs := by
  obtain ⟨ρ,vals⟩ := sorted_assignment _ (I.distinct r) v (fun i => I.typed r i ▸ hv i)
  have act := Rule.instantiate_subst r s β (fun i => .var (I.keys r i)) ρ
  dsimp only at act
  rw [vals] at act
  exact ⟨_,I.present r,ρ,act.1.symm,act.2.symm⟩

inductive PointStep (s : Symbols sig) (β : Operators sig) (a p out : Term sig) : Prop where
  | one (unit : head a = .free s.one) (result : EquivB out p)
  | nested {b q} (point : EquivB p (β.point b q)) (result : EquivB out (β.point (s.product.mul a b) q))

inductive MapStep (s : Symbols sig) (β : Operators sig) (p q out : Term sig) : Prop where
  | left {a r} (point : EquivB p (β.point a r)) (result : EquivB out (s.power (β.map r q) a))
  | right {a r} (point : EquivB q (β.point a r)) (result : EquivB out (s.power (β.map p r) a))

private theorem power_congr {x y z u : Term sig} (l : EquivB x y) (r : EquivB z u) :
    EquivB (s.power x z) (s.power y u) := by apply EquivB.free; intro i; split <;> assumption

theorem Inventory.point_root (I : Inventory s β rules) {a p t out : Term sig} (align : EquivB (β.point a p) t)
    (root : ruleRoot rules t out) : PointStep s β a p out := by
  obtain ⟨eq,mem,ρ,rfl,rfl⟩ := root
  have hd := (instance_head eq (I.apps eq mem) ρ).symm.trans align.head_eq.symm
  obtain ⟨r,tag,rfl⟩ := I.onlyPoint eq mem hd
  rcases tag with rfl|rfl
  all_goals
    rw [(Rule.instantiate_subst ..).1] at align
    rw [(Rule.instantiate_subst ..).2]
    obtain ⟨l,r⟩ := β.point_equiv align
  · exact .one l.head_eq r.symm
  · exact .nested r (β.point_congr (.ac_congr _ l.symm (.refl _)) (.refl _))

theorem Inventory.map_root (I : Inventory s β rules) {p q t out : Term sig} (align : EquivB (β.map p q) t)
    (root : ruleRoot rules t out) : MapStep s β p q out := by
  obtain ⟨eq,mem,ρ,rfl,rfl⟩ := root
  have hd := (instance_head eq (I.apps eq mem) ρ).symm.trans align.head_eq.symm
  obtain rfl := I.onlyMap eq mem hd
  rw [(Rule.instantiate_subst ..).1] at align
  rw [(Rule.instantiate_subst ..).2]
  rcases (Commutative.equiv_iff ..).mp align with ⟨l,r⟩|⟨l,r⟩
  · exact .right r (power_congr (.comm_congr _ l.symm (.refl _)) (.refl _))
  · exact .left l (power_congr ((EquivB.comm_swap ..).trans (.comm_congr _ (.refl _) r.symm)) (.refl _))

private def triple (a b c : Term sig) (i : Fin 3) := if i = 0 then a else if i = 1 then b else c

private theorem triple_typed {a b c : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) (hc : HasSort c .msg) :
    ∀ i, HasSort (triple a b c i) .msg := by intro i; unfold triple; split <;> first | assumption | split <;> assumption

theorem Inventory.one (I : Inventory s β rules) {p : Term sig} (hp : HasSort p .msg) :
    ruleRoot rules (β.point s.product.one p) p := I.fire .one (fun _ => p) (fun _ => hp)

theorem Inventory.nested (I : Inventory s β rules) {a b p : Term sig}
    (ha : HasSort a .msg) (hb : HasSort b .msg) (hp : HasSort p .msg) :
    ruleRoot rules (β.point a (β.point b p)) (β.point (s.product.mul a b) p) :=
  I.fire .nested _ (triple_typed ha hb hp)

theorem Inventory.extract (I : Inventory s β rules) {p a q : Term sig}
    (hp : HasSort p .msg) (ha : HasSort a .msg) (hq : HasSort q .msg) :
    ruleRoot rules (β.map p (β.point a q)) (s.power (β.map p q) a) :=
  I.fire .extract _ (triple_typed hp ha hq)

theorem Inventory.point_normal_iff (I : Inventory s β rules) {a p : Term sig} (ha : HasSort a .msg) (hp : HasSort p .msg) :
    Normal (ruleRoot rules) (β.point a p) ↔ Normal (ruleRoot rules) a ∧ Normal (ruleRoot rules) p ∧
      head a ≠ .free s.one ∧ head p ≠ .free β.pmult := by
  constructor
  · intro n
    have child := normal_free_child β.pmult _ n
    refine ⟨by simpa [idx] using child (idx β 0),by simpa [idx] using child (idx β 1),?_,?_⟩
    · intro h; obtain rfl := nullary s.oneArity h
      exact n _ ⟨_,_,.refl _,.root (I.one hp),.refl _⟩
    · intro h; obtain ⟨b,q,rfl⟩ := β.split h
      obtain ⟨hb,hq⟩ := β.point_types hp
      exact n _ ⟨_,_,.refl _,.root (I.nested ha hb hq),.refl _⟩
  · rintro ⟨na,np,unit,nest⟩
    apply normal_free_no_root
    · intro i; change Normal _ (if _ then _ else _); split <;> assumption
    · intro ys hy t hit
      cases I.point_root (.free _ _ _ hy) hit with
      | one h => exact unit h
      | nested h => exact nest h.head_eq

theorem Inventory.map_normal_iff (I : Inventory s β rules) {p q : Term sig} (hp : HasSort p .msg) (hq : HasSort q .msg) :
    Normal (ruleRoot rules) (β.map p q) ↔ Normal (ruleRoot rules) p ∧ Normal (ruleRoot rules) q ∧
      head p ≠ .free β.pmult ∧ head q ≠ .free β.pmult := by
  constructor
  · intro n
    obtain ⟨l,r⟩ := normal_comm_children β.emap n
    refine ⟨l,r,?_,?_⟩
    · intro h; obtain ⟨a,w,rfl⟩ := β.split h
      obtain ⟨ha,hw⟩ := β.point_types hp
      exact n _ ⟨_,_,.comm_swap ..,.root (I.extract hq ha hw),.refl _⟩
    · intro h; obtain ⟨a,w,rfl⟩ := β.split h
      obtain ⟨ha,hw⟩ := β.point_types hq
      exact n _ ⟨_,_,.refl _,.root (I.extract hp ha hw),.refl _⟩
  · rintro ⟨np,nq,l,r⟩ t st
    rcases (ContextualReduction.comm_iff ..).mp st with ⟨_,_,align,root,_⟩|⟨u,st,_⟩|⟨u,st,_⟩
    · cases I.map_root align root with
      | left h => exact l h.head_eq
      | right h => exact r h.head_eq
    · exact np u st
    · exact nq u st

end Tamarin.Rewriting.Bilinear
