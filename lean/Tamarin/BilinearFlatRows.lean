import Tamarin.BilinearRowLift

/-! The direct and single-extraction BP variants are concrete symbolic rows.
The witness names are shared between their raw caller images and the output. -/
namespace Tamarin.Rewriting.Bilinear
open DHPeer ConstructorVariants VariantJoin
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {op : LiftOp} {T : Table s}

inductive Flat : LiftOp → Type where
  | actionPlain : Flat .action
  | actionUnit : Flat .action
  | mapPlain : Flat .pairing
  | mapLeft : Flat .pairing
  | mapRight : Flat .pairing

def Flat.all : (op : LiftOp) → List (Flat op)
  | .action => [.actionPlain,.actionUnit]
  | .pairing => [.mapPlain,.mapLeft,.mapRight]

theorem Flat.mem_all (f : Flat op) : f ∈ Flat.all op := by cases f <;> simp [all]

private def pair (l r : Term sig) : Bool → Term sig | false => l | true => r

private def Flat.instantiate (f : Flat op) (s : Symbols sig) (β : Operators sig)
    (env : Fin 3 → Term sig) : Row sig Bool Unit :=
  match f with
  | .actionPlain => ⟨pair (env 0) (env 1),fun _ => β.point (env 0) (env 1)⟩
  | .actionUnit => ⟨pair s.product.one (env 1),fun _ => env 1⟩
  | .mapPlain => ⟨pair (env 0) (env 1),fun _ => β.map (env 0) (env 1)⟩
  | .mapLeft => ⟨pair (β.point (env 2) (env 0)) (env 1),fun _ => s.power (β.map (env 0) (env 1)) (env 2)⟩
  | .mapRight => ⟨pair (env 0) (β.point (env 2) (env 1)),fun _ => s.power (β.map (env 0) (env 1)) (env 2)⟩

def Flat.row (f : Flat op) (s : Symbols sig) (β : Operators sig) (keys : Fin 3 → Variable) :
    Row sig Bool Unit := f.instantiate s β (fun i => .var (keys i))

def Flat.Matches (f : Flat op) (s : Symbols sig) (β : Operators sig) (x : Bool → Term sig) (out : Term sig) : Prop :=
  match f with
  | .actionPlain => EquivB out (β.point (x false) (x true))
  | .actionUnit => x false = s.product.one ∧ EquivB out (x true)
  | .mapPlain => EquivB out (β.map (x false) (x true))
  | .mapLeft => ∃ a p, x false = β.point a p ∧ EquivB out (s.power (β.map p (x true)) a)
  | .mapRight => ∃ b q, x true = β.point b q ∧ EquivB out (s.power (β.map (x false) q) b)

private theorem oneT (s : Symbols sig) : HasSort s.product.one .msg := by
  rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)

private def three (a b c : Term sig) (i : Fin 3) := if i = 0 then a else if i = 1 then b else c

private theorem three_typed {a b c : Term sig} (sa : HasSort a .msg) (sb : HasSort b .msg) (sc : HasSort c .msg) :
    ∀ i, HasSort (three a b c i) .msg := by intro i; unfold three; split <;> first | assumption | split <;> assumption

private theorem abstract_flat (f : Flat op) {x : Bool → Term sig} {out : Term sig} (typed : ∀ i, HasSort (x i) .msg)
    (shape : f.Matches s β x out) :
    ∃ env : Fin 3 → Term sig, (∀ i, HasSort (env i) .msg) ∧ (∀ i, x i = (f.instantiate s β env).input i) ∧
      EquivB out ((f.instantiate s β env).value ()) := by
  cases f with
  | actionPlain | mapPlain =>
    exact ⟨_,three_typed (typed false) (typed true) (typed false),fun i => by cases i <;> rfl,shape⟩
  | actionUnit =>
    obtain ⟨unit,value⟩ := shape
    exact ⟨_,three_typed (typed false) (typed true) (typed false),fun i => by cases i <;> first | exact unit | rfl,value⟩
  | mapLeft =>
    obtain ⟨a,p,inp,value⟩ := shape
    have ⟨sa,sp⟩ := β.point_types (inp ▸ typed false)
    exact ⟨_,three_typed sp (typed true) sa,fun i => by cases i <;> first | exact inp | rfl,value⟩
  | mapRight =>
    obtain ⟨b,q,inp,value⟩ := shape
    have ⟨sb,sq⟩ := β.point_types (inp ▸ typed true)
    exact ⟨_,three_typed (typed false) sq sb,fun i => by cases i <;> first | exact inp | rfl,value⟩

private theorem specialize (f : Flat op) (s : Symbols sig) (β : Operators sig) (keys : Fin 3 → Variable)
    (δ : Substitution sig) (env : Fin 3 → Term sig) (h : (fun i => δ.apply (.var (keys i))) = env) :
    (∀ i, δ.apply ((f.row s β keys).input i) = (f.instantiate s β env).input i) ∧
    δ.apply ((f.row s β keys).value ()) = (f.instantiate s β env).value () := by
  have vars (i) : δ.apply (.var (keys i)) = env i := congrFun h i
  have one : δ.apply s.product.one = s.product.one :=
    congrArg (Term.free _) (funext fun i => Fin.elim0 (s.oneArity ▸ i))
  have map (a b) : δ.apply (β.map a b) = β.map (δ.apply a) (δ.apply b) := rfl
  cases f <;> constructor
  all_goals first | intro i; cases i | skip
  all_goals simp [Flat.row,Flat.instantiate,pair,one,map,vars,Operators.point_subst,DHExponent.Caller.apply_pow]

theorem Flat.covers (f : Flat op) {rules : List (Equation sig)} (keys : Fin 3 → Variable)
    (inj : Function.Injective keys) (sk : ∀ i, (keys i).sort = .msg)
    (vars : Normalized (ruleRoot rules) Substitution.identity) {x : Bool → Term sig} {out : Term sig}
    (typed : ∀ i, HasSort (x i) .msg) (normal : ∀ i, Normal (ruleRoot rules) (x i)) (value : Normal (ruleRoot rules) out)
    (shape : f.Matches s β x out) : Denotes (ruleRoot rules) (f.row s β keys) x (fun _ => out) := by
  obtain ⟨env,se,ins,v⟩ := abstract_flat f typed shape
  obtain ⟨δ,h⟩ := sorted_assignment keys inj env (fun i => sk i ▸ se i)
  obtain ⟨inputs,output⟩ := specialize f s β keys δ env h
  exact (normal_witness vars normal (fun _ => value) (δ := δ)
    ⟨fun i => ((ins i).trans (inputs i).symm) ▸ EquivB.refl _,fun _ => output ▸ v⟩).2

theorem Flat.typed (f : Flat op) (s : Symbols sig) (β : Operators sig)
    (keys : Fin 3 → Variable) (sk : ∀ i, (keys i).sort = .msg) :
    ∀ i, HasSort ((f.row s β keys).input i) .msg := by
  have tv (i) : HasSort (Term.var (sig := sig) (keys i)) .msg := sk i ▸ HasSort.var _
  cases f <;> intro i <;> cases i <;> first | exact tv _ | exact oneT s | exact β.point_sorted (tv _) (tv _)

theorem Flat.sound [DecidableEq sig.ACSym] {E : ExtraTable T} (f : Flat op)
    (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (keys : Fin 3 → Variable) (sk : ∀ i, (keys i).sort = .msg) :
    let z := f.row s β keys
    (∀ i, Normal (ruleRoot T.rules) (z.input i)) ∧ NormalForm (ruleRoot T.rules) (op.call β z.input) (z.value ()) := by
  have nv (i) := (constructor_normal T.rules I.apps).1 (keys i)
  have tv (i) : HasSort (Term.var (sig := sig) (keys i)) .msg := sk i ▸ HasSort.var _
  have nu (i) : head (Term.var (sig := sig) (keys i)) ≠ .free s.one := by intro h; cases h
  have plain (i) : head (Term.var (sig := sig) (keys i)) ≠ .free β.pmult := by intro h; cases h
  have np (i j) := (I.point_normal_iff (tv i) (tv j)).mpr ⟨nv i,nv j,nu i,plain j⟩
  have nm (i j) := (I.map_normal_iff (tv i) (tv j)).mpr ⟨nv i,nv j,plain i,plain j⟩
  cases f <;> constructor
  case actionPlain.left | actionUnit.left | mapPlain.left | mapLeft.left | mapRight.left =>
    intro i; cases i <;> first | exact nv _ | exact unit | exact np _ _
  case actionPlain.right => exact ⟨.basis (.refl _),np 0 1,fun _ h => h⟩
  case actionUnit.right => exact (I.point_one group (tv 1) (nv 1) unit).mpr (.refl _)
  case mapPlain.right => exact ⟨.basis (.refl _),nm 0 1,fun _ h => h⟩
  case mapLeft.right => exact (I.map_single pow (tv 2) (tv 0) (tv 1) (np 2 0) (nv 1) (plain 1)).mpr (.refl _)
  case mapRight.right =>
    apply (I.map_results pow unit (tv 0) (β.point_sorted (tv 2) (tv 1)) (nv 0) (np 2 1)).mpr
    exact .right rfl (plain 0) (.refl _)

end Tamarin.Rewriting.Bilinear
