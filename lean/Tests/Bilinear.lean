import Tamarin.BilinearScalars

/-! Reify the three equations from Rust's `bp_rules()` independently of the
Lean BP schema. The point nesting rule uses the reverse variable order, the
map uses its declared positional order, and both share all thirteen DH rules. -/
namespace Tamarin.BilinearTests
open Rewriting Rewriting.ConstructorVariants Rewriting.DHPeer

private inductive F where | pow | inv | one | neutral | point deriving DecidableEq
private def arity : F → Nat | .point | .pow => 2 | .inv => 1 | _ => 0
private abbrev sig : Signature where
  FreeSym := F
  CSym := Unit
  ACSym := Unit
  Atom := Nat
  arity := arity
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .fresh

private def s : Symbols sig :=
  ⟨.pow,.inv,.one,.neutral,(),rfl,rfl,rfl,rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,rfl,rfl,rfl⟩
private def op : Rewriting.Bilinear.Operators sig := ⟨.point,(),rfl,fun _ => rfl,rfl,rfl⟩
private abbrev Term' := Term sig
private def x (i : Nat) : Term' := .var ⟨i,.msg⟩
private def point (a p : Term') : Term' := .free F.point fun i => if i.val = 0 then a else p
private def power (a b : Term') : Term' := .free F.pow fun i => if i.val = 0 then a else b
private def one : Term' := .free F.one Fin.elim0
private def pointOne : Equation sig := ⟨point one (x 1),x 1⟩
private def nested : Equation sig := ⟨point (x 3) (point (x 2) (x 1)),point (.ac () (x 3) (x 2)) (x 1)⟩
private def extract : Equation sig := ⟨.comm () (x 1) (point (x 2) (x 3)),power (.comm () (x 1) (x 3)) (x 2)⟩

private def keys (i : Fin 3) : Variable := ⟨i.val,.msg⟩
private def bkeys : Rewriting.Bilinear.Rule → Fin 3 → Variable
  | .nested, i => ⟨3-i.val,.msg⟩
  | _, i => ⟨i.val+1,.msg⟩
private def standard (r : Rule) := r.instantiate s (fun i => .var (keys i))
private def group (r : ExtraRule) := r.instantiate s (fun i => .var (keys i))
private def basic : List Rule := [.expOne,.tower,.neutral,.inverse,.inverseRest,.inside,.insideRest]
private def others : List ExtraRule := [.mulOne,.invInv,.invOne,.join,.pull,.joinRest]
private def rules := basic.map standard ++ others.map group ++ [pointOne,nested,extract]
private abbrev R := ruleRoot rules

private def T : Table s where
  rules := rules
  actual _ := keys
  actualSort _ _ := rfl
  distinct _ _ _ h := Fin.ext (congrArg Variable.id h)
  present := by
    intro r; have m : r ∈ basic := by cases r <;> decide
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (f := standard) m))

private def E : ExtraTable T where
  actual _ := keys
  sorted _ _ := rfl
  distinct _ _ _ h := Fin.ext (congrArg Variable.id h)
  present := by
    intro r; have m : r ∈ others := by cases r <;> decide
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := group) m))

private theorem splitRules {e : Equation sig} (mem : e ∈ rules) :
    (∃ r, e = standard r) ∨ (∃ r, e = group r) ∨ e = pointOne ∨ e = nested ∨ e = extract := by
  rcases List.mem_append.mp mem with dh|bp
  · rcases List.mem_append.mp dh with a|b
    · obtain ⟨r,_,rfl⟩ := List.mem_map.mp a; exact .inl ⟨r,rfl⟩
    · obtain ⟨r,_,rfl⟩ := List.mem_map.mp b; exact .inr (.inl ⟨r,rfl⟩)
  · exact .inr (.inr (by simpa using bp))

private theorem apps : ∀ e ∈ rules, Application e.lhs := by
  intro e mem
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl <;> first | cases r <;> trivial | trivial

private def bp : Rewriting.Bilinear.Inventory s op rules where
  keys := bkeys
  typed r _ := by cases r <;> rfl
  distinct := by
    intro r i j h; apply Fin.ext
    have e := congrArg Variable.id h
    cases r <;> simp [bkeys] at e <;> have := i.isLt <;> have := j.isLt <;> omega
  present := by
    intro r; apply List.mem_append_right; cases r
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  apps := apps
  onlyPoint := by
    intro e mem hd
    rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl
    · cases r <;> cases hd
    · cases r <;> cases hd
    · exact ⟨.one,.inl rfl,rfl⟩
    · exact ⟨.nested,.inr rfl,rfl⟩
    · cases hd
  onlyMap := by
    intro e mem hd
    rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl
    · cases r <;> cases hd
    · cases r <;> cases hd
    · cases hd
    · cases hd
    · rfl

private theorem powers : PowerBucket T := by
  refine ⟨apps,?_⟩; intro eq mem hd
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl
  · cases r <;> first | exact ⟨.expOne,.inl rfl,rfl⟩ | exact ⟨.tower,.inr (.inl rfl),rfl⟩
                       | exact ⟨.neutral,.inr (.inr rfl),rfl⟩ | cases hd
  · cases r <;> cases hd
  all_goals cases hd

private theorem inverses : InverseBucket E := by
  refine ⟨apps,?_⟩; intro eq mem hd
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl
  · cases r <;> cases hd
  · cases r <;> first | exact ⟨.invInv,.inl rfl,rfl⟩ | exact ⟨.invOne,.inr (.inl rfl),rfl⟩
                       | exact ⟨.pull,.inr (.inr rfl),rfl⟩ | cases hd
  all_goals cases hd

private theorem inventory : Balance.Inventory E := by
  refine ⟨apps,?_⟩; intro eq mem hd
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl
  · apply Or.inl
    cases r <;> first | exact ⟨.inverse,.inl rfl,rfl⟩ | exact ⟨.inverseRest,.inr (.inl rfl),rfl⟩
                      | exact ⟨.inside,.inr (.inr (.inl rfl)),rfl⟩ | exact ⟨.insideRest,.inr (.inr (.inr rfl)),rfl⟩
                      | rcases hd with h|h|h <;> cases h
  · exact .inr ⟨r,rfl⟩
  all_goals rcases hd with h|h|h <;> cases h

private theorem unitN : Normal R s.product.one := by
  refine constructor_node_normal rules apps _ ?_ (fun i => Fin.elim0 i)
  · rintro mem; obtain ⟨e,mem,hd⟩ := List.mem_map.mp mem
    rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl|rfl <;> first | cases r <;> cases hd | cases hd

private def a : Term' := .atom 0
private def p : Term' := .atom 1
private def q : Term' := .atom 2
private theorem atomT (i : Nat) : HasSort (.atom (sig := sig) i) .msg := .widen (HasSort.atom (sig := sig) i) .fresh_msg
private theorem atomN (i : Nat) : Normal R (.atom (sig := sig) i) := (constructor_normal rules apps).2 (.atom i) (by simp [operators]) Substitution.identity (constructor_normal rules apps).1
private theorem invN : Normal R (s.product.inv a) := by
  apply inverses.normal_positive (atomN 0)
  · intro h; have eq := Quotient.exact (List.mem_singleton.mp h); cases eq.head_eq
  · intro u h; have eq := Quotient.exact (List.mem_singleton.mp h); cases eq.head_eq

private theorem invT : HasSort (s.product.inv a) .msg := .free _ _ (fun _ => atomT 0)
private theorem actionA : Normal R (op.point a p) := (bp.point_normal_iff (atomT 0) (atomT 1)).mpr
  ⟨atomN 0,atomN 1,(by intro h; cases h),(by intro h; cases h)⟩
private theorem actionInv : Normal R (op.point (s.product.inv a) q) := (bp.point_normal_iff invT (atomT 2)).mpr
  ⟨invN,atomN 2,(by intro h; cases h),(by intro h; cases h)⟩

private theorem cancels : NormalForm R (s.product.mul a (s.product.inv a)) one :=
  ⟨.step ⟨_,_,.refl _,.root (E.presentation.roots.direct a (atomT 0)),.refl _⟩,
    unitN,fun _ h => .widen (.free _ _ (fun i => Fin.elim0 i)) (Term.rootSort_le h)⟩

-- The two map operands contain opposite scalars. Both extraction orders must
-- produce the bare commutative map from their common folded product.
example (out : Term') : NormalForm R (op.map (op.point a p) (op.point (s.product.inv a) q)) out ↔ EquivB out (op.map p q) := by
  apply Iff.trans (bp.map_lift powers (atomT 0) invT (atomT 1) (atomT 2) actionA actionInv unitN)
  constructor
  · rintro ⟨m,prod,⟨_,eq⟩|⟨nu,eq⟩⟩
    · exact eq
    · exact (nu (inventory.product_unique (atomT 0) invT (atomN 0) invN prod cancels).head_eq).elim
  · intro eq; exact ⟨_,cancels,.inl ⟨rfl,eq⟩⟩

-- The unit and nesting rules overlap on the same sorted input.
example (out : Term') : NormalForm R (op.point one (op.point a p)) out ↔ EquivB out (op.point a p) :=
  bp.point_one inventory (op.point_sorted (atomT 0) (atomT 1)) actionA unitN

-- One extraction must inspect the left operand even though the declared rule
-- has the point action in the right slot.
example (out : Term') : NormalForm R (op.map (op.point a p) q) out ↔ EquivB out (s.power (op.map p q) a) :=
  bp.map_single powers (atomT 0) (atomT 1) (atomT 2) actionA (atomN 2) (by intro h; cases h)

-- Point and map heads with hidden child or parent redexes must be rejected.
example : ¬Normal R (op.point a (op.point a p)) := fun n =>
  ((bp.point_normal_iff (atomT 0) (op.point_sorted (atomT 0) (atomT 1))).mp n).2.2.2 rfl
example : ¬Normal R (op.map p (op.point a p)) := fun n =>
  ((bp.map_normal_iff (atomT 1) (op.point_sorted (atomT 0) (atomT 1))).mp n).2.2.2 rfl

end Tamarin.BilinearTests
