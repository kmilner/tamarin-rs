import Tamarin.DHSignedVariantFamily

/-! A DH table with a deliberately nonconfluent unrelated operator. Repeated
opaque factors compare modulo B, even when their children have opposite orders. -/
namespace Tamarin.DHProductUniquenessTests
open Rewriting Rewriting.DHPeer Rewriting.ConstructorVariants

private inductive F where | pow | inv | one | neutral | ambiguous
  deriving DecidableEq

private def arity : F → Nat | .pow => 2 | .inv => 1 | _ => 0

private abbrev sig : Signature where
  FreeSym := F
  CSym := Unit
  ACSym := Unit
  Atom := Bool
  arity := arity
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .msg

private abbrev Term' := Term sig
private def s : Symbols sig :=
  ⟨.pow,.inv,.one,.neutral,(),rfl,rfl,rfl,rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,rfl,rfl,rfl⟩
private def ambiguous : Term' := .free .ambiguous Fin.elim0
private def extra (b : Bool) : Equation sig := ⟨ambiguous,.atom b⟩
private def keys (i : Fin 3) : Variable := ⟨i.val,.msg⟩
private def standard (r : Rule) := r.instantiate s (fun i => .var (keys i))
private def group (r : ExtraRule) := r.instantiate s (fun i => .var (keys i))
private def basic : List Rule := [.expOne,.tower,.neutral,.inverse,.inverseRest,.inside,.insideRest]
private def others : List ExtraRule := [.mulOne,.invInv,.invOne,.join,.pull,.joinRest]
private def rules := basic.map standard ++ others.map group ++ [extra false,extra true]
private abbrev R := ruleRoot rules
private def T : Table s where
  rules := rules
  actual _ := keys
  actualSort _ _ := rfl
  distinct _ _ _ h := Fin.ext (congrArg Variable.id h)
  present := by
    intro r
    have mem : r ∈ basic := by cases r <;> decide
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (f := standard) mem))
private def E : ExtraTable T where
  actual _ := keys
  sorted _ _ := rfl
  distinct _ _ _ h := Fin.ext (congrArg Variable.id h)
  present := by
    intro r
    have mem : r ∈ others := by cases r <;> decide
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := group) mem))

private theorem splitRules {eq : Equation sig} (h : eq ∈ rules) :
    (∃ r, eq = standard r) ∨ (∃ r, eq = group r) ∨ eq = extra false ∨ eq = extra true := by
  rcases List.mem_append.mp h with dh|ex
  · rcases List.mem_append.mp dh with std | grp
    · obtain ⟨r,_,rfl⟩ := List.mem_map.mp std; exact .inl ⟨r,rfl⟩
    · obtain ⟨r,_,rfl⟩ := List.mem_map.mp grp; exact .inr (.inl ⟨r,rfl⟩)
  · exact .inr (.inr (by simpa using ex))

private theorem apps : ∀ eq ∈ rules, Application eq.lhs := by
  intro eq mem
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl
  · cases r <;> trivial
  · cases r <;> trivial
  all_goals trivial

private theorem inventory : Balance.Inventory E := by
  refine ⟨apps,?_⟩
  intro eq mem head
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl
  · apply Or.inl
    cases r <;> first
      | exact ⟨.inverse,.inl rfl,rfl⟩
      | exact ⟨.inverseRest,.inr (.inl rfl),rfl⟩
      | exact ⟨.inside,.inr (.inr (.inl rfl)),rfl⟩
      | exact ⟨.insideRest,.inr (.inr (.inr rfl)),rfl⟩
      | rcases head with h|h|h <;> cases h
  · exact .inr ⟨r,rfl⟩
  all_goals rcases head with h|h|h <;> cases h

private theorem absent {h : Head sig} (groupH : h ≠ .ac ()) (powH : h ≠ .free F.pow)
    (invH : h ≠ .free F.inv) (otherH : h ≠ .free F.ambiguous) : h ∉ ruleHeads rules := by
  intro mem
  obtain ⟨rule,mem,eq⟩ := List.mem_map.mp mem
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl
  · cases r <;> first | exact groupH eq.symm | exact powH eq.symm
  · cases r <;> first | exact groupH eq.symm | exact invH eq.symm
  all_goals exact otherH eq.symm

private theorem atomN (b : Bool) : Normal R (.atom b) :=
  constructor_node_normal rules apps _ (absent (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)) trivial
private theorem unitN : Normal R s.product.one :=
  constructor_node_normal rules apps _ (absent (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)) (fun i => Fin.elim0 i)
private def key : Term' := .comm () (.atom true) (.atom false)
private def swapped : Term' := .comm () (.atom false) (.atom true)
private theorem keyN : Normal R key := constructor_node_normal rules apps _ (absent (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)) ⟨atomN _,atomN _⟩
private theorem keyT : HasSort key .msg := .comm _ _ _ (.atom _) (.atom _)
private def pair := s.product.mul key swapped
private def repeated := s.product.mul key key
private def lhs := s.product.mul pair (s.product.inv repeated)
private theorem pairEq : EquivB pair repeated := .ac_congr _ (.refl _) (.comm_swap ..)
private theorem repT : HasSort repeated .msg := .ac _ _ _ keyT keyT
private theorem lhsT : HasSort lhs .msg := .ac _ _ _ (.ac _ _ _ keyT (.comm _ _ _ (.atom _) (.atom _)))
  (.free _ _ fun _ => repT)

-- One match cancels the entire repeated product. Another cancels only one
-- occurrence inside its inverse. Both paths must recover exactly the unit.
private theorem direct : Reduces R lhs s.product.one :=
  .step ⟨_,_,.ac_congr _ pairEq (.refl _),.root (E.presentation.roots.direct repeated repT),.refl _⟩

private theorem individual : Reduces R lhs s.product.one := by
  have rebracket : EquivB lhs (s.product.mul key (s.product.mul (s.product.inv repeated) key)) :=
    (EquivB.ac_congr _ pairEq (.refl _)).trans ((EquivB.ac_assoc ..).trans (.ac_congr _ (.refl _) (.ac_swap ..)))
  exact (Reduces.basis rebracket).trans ((Reduces.ac _ (.basis (.refl _))
    (Reduces.step ⟨_,_,.refl _,.root (E.presentation.roots.inside key key keyT keyT),.refl _⟩)).trans
    (.step ⟨_,_,.refl _,.root (E.presentation.roots.direct key keyT),.refl _⟩))

private theorem recognized (k) : ∃ n, Balance.read s R k lhs = some n := by
  obtain ⟨n,h⟩ := Balance.defined s R k keyN
  have eq : EquivB swapped key := .comm_swap ..
  have hs := (Balance.equiv s R k eq).trans h
  change Balance.read s R k swapped = some n at hs
  exact ⟨0,by simp [lhs,pair,repeated,Balance.plus,Balance.minus,h,hs]; omega⟩

example (v : Term') (nf : NormalForm R lhs v) : EquivB v s.product.one := by
  classical
  exact Balance.normal_unique inventory E.presentation (fun _ => Balance.plain_of_inverse E)
    recognized (nf.2.2 _ lhsT) (.free _ _ fun i => Fin.elim0 i) nf.2.1 unitN nf.1 direct

-- Preserve an additional positive copy of the same composite factor.
example (v : Term') (nf : NormalForm R (s.product.mul lhs key) v) : EquivB v key := by
  classical
  have path : Reduces R (s.product.mul lhs key) key :=
    (Reduces.ac _ individual (.basis (.refl _))).trans (.step ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule key keyT),.refl _⟩)
  refine Balance.normal_unique inventory E.presentation (fun _ => Balance.plain_of_inverse E) ?_
    (nf.2.2 _ (.ac _ _ _ lhsT keyT)) keyT nf.2.1 keyN nf.1 path
  intro k
  obtain ⟨l,hl⟩ := recognized k
  obtain ⟨r,hr⟩ := Balance.defined s R k keyN
  exact ⟨l+r,by change Balance.read s R k (s.product.mul lhs key) = _; rw [Balance.read_mul,hl,hr]; rfl⟩

private theorem ambiguousRoot (b : Bool) : R ambiguous (.atom b) := by
  refine ⟨extra b,?_,.identity,?_,?_⟩
  · apply List.mem_append_right; cases b <;> simp
  · exact (Substitution.apply_identity _).symm
  · exact (Substitution.apply_identity _).symm

-- Dropping irreducibility of opaque operands would be unsound. This very
-- table has a product with two distinct normal forms.
example : let x := s.product.mul ambiguous s.product.one
    NormalForm R x (.atom true) ∧ NormalForm R x (.atom false) ∧ ¬ EquivB (Term.atom (sig := sig) true) (.atom false) := by
  have value (b : Bool) : NormalForm R (s.product.mul ambiguous s.product.one) (.atom b) := by
    refine ⟨?_,atomN _,fun z h => .widen (.atom _) (Term.rootSort_le h)⟩
    exact (Reduces.step ⟨_,_,.refl _,.root (E.presentation.unitRule ambiguous (.free _ _ fun i => Fin.elim0 i)),.refl _⟩).trans
      (.step ⟨_,_,.refl _,.root (ambiguousRoot b),.refl _⟩)
  exact ⟨value true,value false,fun e => by cases e.head_eq⟩

private theorem powers : PowerBucket T := by
  refine ⟨apps,?_⟩
  intro eq mem hd
  rcases splitRules mem with ⟨r,rfl⟩|⟨r,rfl⟩|rfl|rfl
  · cases r <;> first
      | exact ⟨.expOne,.inl rfl,rfl⟩
      | exact ⟨.tower,.inr (.inl rfl),rfl⟩
      | exact ⟨.neutral,.inr (.inr rfl),rfl⟩
      | cases hd
  · cases r <;> cases hd
  all_goals cases hd

-- A C head stays fixed when a Msg parameter occurs twice and its normalized
-- image can contain arbitrary DH operations. No operand of the power has
-- to carry the Fresh sort.
private def parameter (v : Variable) : Term' := .comm () (.var v) (.var v)

example (v : Variable) (sort : v.sort = .msg) (σ : Substitution sig) (hn : Normalized R σ)
    (Y : Term') (hy : HasSort Y .msg) (ny : Normal R Y) :
    let t := σ.apply (parameter v)
    Factor s t ∧ ∀ x y, NormalForm R (s.power Y t) x → NormalForm R (s.power Y t) y → EquivB x y := by
  let t := σ.apply (parameter v)
  have fixed : Factor s (parameter v) := by constructor <;> intro eq <;> cases eq
  have factor := fixed.subst (by intro w eq; cases eq) σ
  have sv : HasSort (σ.image v) .msg := sort ▸ σ.sorted v
  have st : HasSort t .msg := .comm _ _ _ sv sv
  have normal : Normal R t := constructor_node_normal rules apps _ (absent (by intro e; cases e)
    (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)) ⟨hn v,hn v⟩
  exact ⟨factor,fun _ _ => inventory.peer_unique_msg powers unitN hy st factor.nonUnit ny normal⟩

-- The three algebraically meaningful heads each violate the factor
-- condition, even when the product or inverse is already irreducible.
example (a b : Term') : ¬Factor s (s.product.mul a b) ∧ ¬Factor s (s.product.inv a) ∧ ¬Factor s s.product.one :=
  ⟨fun h => h.nonMul rfl,fun h => h.nonInv rfl,fun h => h.nonUnit rfl⟩

-- Repeated inputs and two correlated observations under the nonconfluent
-- ambient table. Variables of sort Msg can specialize to any signed product.
example (e : SignedMatrix.Expr 3) (ρ : Substitution sig) (hne : Normalized R ρ) {a b}
    (l : NormalForm R (ρ.apply (e.term s (fun i => .var (keys i)))) a)
    (r : NormalForm R (ρ.apply (e.term s (fun i => .var (keys i)))) b) : EquivB a b :=
  e.pointwise_unique inventory _ (fun i => HasSort.var (keys i)) (fun i _ hn => hn (keys i)) ρ hne l r

example (es : List (SignedMatrix.Expr 3)) (ρ : Substitution sig) (hn : Normalized R ρ) {u v} :
    let input := es.foldl (fun t e => s.power t (e.term s (fun i => .var (keys i)))) (.var (keys 0))
    NormalForm R (ρ.apply input) u → NormalForm R (ρ.apply input) v → EquivB u v :=
  SignedMatrix.spine_pointwise_unique inventory powers unitN _ (fun i => HasSort.var (keys i))
    (fun i _ h => h (keys i)) _ (HasSort.var (keys 0)) (fun _ h => h (keys 0)) es ρ hn

private def signedConstraints : List (SignedMatrix.Constraint 3) :=
  [(.mul (.inv (.input 0)) (.input 1), .input 2), (.mul (.input 2) (.input 2), .input 1)]

-- Check the compiled rows against -a + b = c and 2c = b directly, including
-- the all-unit assignment and a different sign in each input position.
private def checksMatrix (a b c : Int) : Bool := Id.run do
  let counts : Fin 3 → Int := fun i => if i.val == 0 then a else if i.val == 1 then b else c
  let mag := fun i => (counts i).natAbs
  let rows := signedConstraints.map (SignedMatrix.row (fun i => decide (counts i < 0)))
  let accepted := rows.all fun r => ACBasis.dot r.pos mag == ACBasis.dot r.neg mag
  return accepted == (b - a == c && 2*c == b)

#guard ([-3,-2,-1,0,1,2,3] : List Int).all fun a =>
  ([-3,-2,-1,0,1,2,3] : List Int).all fun b =>
    ([-3,-2,-1,0,1,2,3] : List Int).all (checksMatrix a b)

-- Two shared columns occur twice in coordinate 0. The first changes sign in
-- coordinate 1. The empty branch produces the DH unit in both coordinates.
private def sampleBasis (_ : Fin 2 → Bool) : List (ACBasis.Vec 2) :=
  [fun i => if i.val = 0 then 2 else 1]
private def chosen : List (SignedMatrix.Column sampleBasis) :=
  [⟨fun i => i.val == 1, ⟨0,by decide⟩⟩, ⟨fun _ => false, ⟨0,by decide⟩⟩]
private def parameterIds (i : Fin 2) (negative : Bool) :=
  (SignedMatrix.slots sampleBasis chosen i negative).map fun g => g.1 1

#guard parameterIds 0 false == [false,false,true,true]
#guard parameterIds 0 true == []
#guard parameterIds 1 false == [false]
#guard parameterIds 1 true == [true]

example (i : Fin 2) (name : SignedMatrix.Column sampleBasis → Variable) :
    SignedMatrix.template s sampleBasis [] name i = s.product.one := by
  cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
              | zero => rfl
              | succ k => exact k.elim0

-- x = inv(x) has only the unit solution. For y = inv(x) the
-- reference family represents the unit, each single sign, and a mixture.
private def kind : Term' → Nat
  | .free .one _ => 0
  | .var _ => 1
  | .free .inv _ => 2
  | .ac _ _ _ => 3
  | _ => 4
#guard ((SignedMatrix.referenceFamily (n := 1) s [(.inv (.input 0),0)]).map
  (fun r => kind (r 0))) == [0]
#guard (((SignedMatrix.referenceFamily (n := 2) s [(.inv (.input 0),1)]).map
  (fun r => 10 * kind (r 0) + kind (r 1))).mergeSort) == [0,12,21,33]

-- Truncated, overfull, and output-referencing programs must all defer.
#guard [#[],#[1],#[3,2],#[3,3],#[4]].all fun p => SignedGraph.run 1 #[p] == #[0]
#guard SignedGraph.run 0 #[#[0]] == #[1,1,0,0]
#guard (SignedGraph.run 1 #[#[3,3,2,3,2]]).extract 0 2 == #[1,4]
#guard (SignedGraph.run 1 #[#[3,3,2],#[3,1]]).extract 0 2 == #[1,4]

end Tamarin.DHProductUniquenessTests
