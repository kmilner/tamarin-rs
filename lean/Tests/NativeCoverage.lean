import Tamarin.ConstructorReduction
import Tamarin.DHPeer
import Tamarin.MatchingFree
import Tamarin.SortCheck
import Tamarin.VariablePermutation

/-! Generate well-sorted algebra requests directly from the specification. Each
line carries its active theory, operation, expectation and postfix term(s).
The public Rust adapter consumes this test format. -/
namespace Tamarin.NativeCoverage
open Rewriting ConstructorVariants

inductive Symbol where | hash | zero | pair | fst | snd | red | blue
  deriving DecidableEq

abbrev sig : Signature where
  FreeSym := Symbol
  CSym := Empty
  ACSym := Unit
  Atom := Bool
  arity := fun | .hash | .fst | .snd => 1 | .zero | .red | .blue => 0 | .pair => 2
  inputSort := fun _ _ => .msg
  outputSort := fun _ => .msg
  cSort := Empty.elim
  acSort := fun _ => .msg
  atomSort := fun _ => .pub

abbrev Expr := Term sig
def plus (l r : Expr) : Expr := .ac () l r
def hash (t : Expr) : Expr := .free .hash (fun _ => t)
def zero : Expr := .free .zero Fin.elim0
def x : Expr := .var ⟨0,.msg⟩
def y : Expr := .var ⟨1,.msg⟩

def pair (a b : Expr) : Expr := .free .pair (fun i => if i.val = 0 then a else b)
def first (t : Expr) : Expr := .free .fst (fun _ => t)
def second (t : Expr) : Expr := .free .snd (fun _ => t)

def red : Expr := .free .red Fin.elim0
def blue : Expr := .free .blue Fin.elim0

inductive Theory where | ac | xor | xorPair | markers
  deriving DecidableEq

def xorRules : List (Equation sig) := [⟨plus x zero,x⟩, ⟨plus x x,zero⟩, ⟨plus x (plus x y),y⟩]

def rules : Theory → List (Equation sig)
  | .ac => []
  | .markers => [⟨plus red red, red⟩, ⟨plus blue blue, blue⟩]
  | .xorPair => xorRules ++ [⟨first (pair x y),x⟩, ⟨second (pair x y),y⟩]
  | .xor => xorRules

private def sameHead : DecidableEq (Head sig) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

def constructorOnly (th : Theory) (t : Expr) : Bool :=
  !(operators t).any fun f => (ruleHeads (rules th)).any fun g => @decide _ (sameHead f g)

/-- Ground observations in the generated variant presentations have a unique
normal value, including when their active AC root rewrites. -/
def identitySlot (th : Theory) (t : Expr) := t.variables.isEmpty || constructorOnly th t

/-- Every expression emitted in this bounded grammar lies in the stable,
inert-constructor and single-cancellation fragment. Require completion on
these concrete requests, including when one variable appears at two depths. -/
def variantExpectation (th : Theory) (ts : List Expr) : String :=
  if ts.all (identitySlot th) then "identity" else "complete"

/-- The mandatory constructor cases have an identity variant for every
normalized valuation. Adding repeated observations preserves this fact. -/
theorem constructor_family (th : Theory) (ts : List Expr) (safe : ∀ t ∈ ts, constructorOnly th t = true) :
    CompleteVariants (ruleRoot (rules th)) ts [⟨Substitution.identity, ts⟩] := by
  apply (identity_variants (rules th) ts ?_ ?_ []).1
  · cases th <;> simp [rules,xorRules,Application,plus,first,second]
  · intro t ht f hf mem
    have h := safe t ht
    simp [constructorOnly] at h
    exact h f hf f mem rfl

def matchClash (p s : Expr) : Bool :=
  match p with
  | .var _ => false
  | _ => !(@decide _ (sameHead (head p) (head s)))

theorem matchClash_sound {p s : Expr} (h : matchClash p s = true) (σ : Substitution sig) :
    ¬ EquivB (σ.apply p) s := by
  intro e
  have eq : head (σ.apply p) = head s := e.head_eq
  cases p <;> simp_all [matchClash,Substitution.apply,Term.subst,head,headModel,Model.eval]

def groundAnswer (l r : List sig.Atom) := decide (l.Perm r)

theorem groundAnswer_correct (l r : List sig.Atom) :
    groundAnswer l r = true ↔ EquivB (FlatAC.term () l) (FlatAC.term () r) := by
  simpa [groundAnswer] using (FlatAC.equiv_iff_perm (sig := sig) () l r).symm

/-- Both equations must use the same capture. For ground targets their
images are also fixed under any ordinary unifier (FlatAC.subst_term). -/
theorem sharedCapture_iff (a b : Expr) (ha : HasSort a .msg) :
    (∃ σ : Substitution sig, EquivB (σ.apply x) a ∧ EquivB (σ.apply x) b) ↔ EquivB a b := by
  constructor
  · rintro ⟨σ,l,r⟩
    exact l.symm.trans r
  · intro eq
    let v : Variable := ⟨0,.msg⟩
    refine ⟨Substitution.binding v a ha,?_⟩
    change EquivB ((Substitution.binding v a ha).image v) a ∧ EquivB ((Substitution.binding v a ha).image v) b
    rw [Substitution.binding_image_self]
    exact ⟨.refl _,eq⟩

theorem hash_equiv_iff (a b : Expr) : EquivB (hash a) (hash b) ↔ EquivB a b := by
  constructor
  · intro h
    exact ((Matching.free_equiv_iff ..).mp h) 0
  · exact fun h => .free _ _ _ (fun _ => h)

theorem hash_normalForm (th : Theory) {t u : Expr} (child : NormalForm (ruleRoot (rules th)) t u) :
    NormalForm (ruleRoot (rules th)) (hash t) (hash u) := by
  apply free_normalForm (rules th) _ .hash _ _ _ (fun _ => child)
  · cases th <;> simp [rules,xorRules,Application,plus,first,second]
  · change ¬ List.Mem (Head.free (sig := sig) .hash) (ruleHeads (rules th))
    cases th <;> intro h <;> repeat' cases ‹List.Mem _ _›

def code : Expr → String
  | .var v => (if v.sort == .fresh then "f" else "m") ++ toString v.id
  | .atom b => if b then "b" else "a"
  | .free .hash args => code (args 0) ++ ".h"
  | .free .zero _ => "z"
  | .free .red _ => "R"
  | .free .blue _ => "B"
  | .free .fst args => code (args 0) ++ ".l"
  | .free .snd args => code (args 0) ++ ".r"
  | .free .pair args => code (args 0) ++ "." ++ code (args 1) ++ ".p"
  | .comm f _ _ => nomatch f
  | .ac _ l r => code l ++ "." ++ code r ++ ".+"

/-- Index by number of syntax nodes, so small witnesses are explored even
when they never appear as a subterm in the protocol corpus. -/
def layers (th : Theory) (maxSize : Nat) : Array (List Expr) := Id.run do
  let leaves : List Expr := [.atom false,.atom true,x,y,.var ⟨0,.fresh⟩,.var ⟨1,.fresh⟩]
  let mut out := #[[], if th == .xor then zero :: leaves else leaves]
  for n in [2:maxSize+1] do
    let binary := (List.range (n-2)).flatMap fun i =>
      out[i+1]!.flatMap fun l => out[n-2-i]!.map (plus l)
    out := out.push (out[n-1]!.map hash ++ binary)
  return out

def emit (th : Theory) (op expected : String) (ts : List Expr) : IO Unit := do
  let name := match th with | .ac => "ac" | .xor => "xor" | .xorPair => "xor-pair" | .markers => "markers"
  IO.println (String.intercalate "\t" ([name,op,expected] ++ ts.map code))

/-- Two independent idempotent markers share an otherwise free AC operation.
The two constructor symbols differ from public names, including names with
the same displayed spelling. Reduction keeps rigid variables unchanged. -/
inductive Factor where | red | blue | name | message | fresh
  deriving DecidableEq

def Factor.term : Factor → Expr
  | .red => NativeCoverage.red | .blue => NativeCoverage.blue | .name => .atom true
  | .message => x | .fresh => .var ⟨0,.fresh⟩

def Factor.marker : Factor → Bool
  | .red | .blue => true
  | _ => false

def normalCount (xs : List Factor) (f : Factor) : Nat :=
  if f.marker then min 1 (xs.count f) else xs.count f

/-- A marker step consumes one of two equal occurrences. Every projected
normal-form count is invariant under either rule in an arbitrary context. -/
theorem normalCount_step (xs : List Factor) (m f : Factor) (hm : m.marker = true) :
    normalCount (m::m::xs) f = normalCount (m::xs) f := by
  by_cases e : m = f
  · subst f; simp [normalCount,hm]
  · simp [normalCount,e]

theorem normalCount_perm {xs ys : List Factor} (perm : xs.Perm ys) (f : Factor) :
    normalCount xs f = normalCount ys f := by simp [normalCount,perm.count_eq f]

/-- When no marker pair remains, the invariant reads back the exact
multiplicity of every operand, including unbounded duplicates of names or variables. -/
theorem normalCount_irreducible (xs : List Factor)
    (normal : ∀ m : Factor, m.marker = true → xs.count m ≤ 1) (f : Factor) :
    normalCount xs f = xs.count f := by
  cases h : f.marker with
  | false => simp [normalCount,h]
  | true => simp [normalCount,h,Nat.min_eq_right (normal f h)]

def normalWord (xs : List Factor) : List Factor :=
  [.red,.blue,.name,.message,.fresh].flatMap fun f => List.replicate (normalCount xs f) f

theorem normalWord_count (xs : List Factor) (f : Factor) :
    (normalWord xs).count f = normalCount xs f := by
  cases f <;> simp [normalWord,List.count_replicate]

def markerCase (xs : List Factor) : IO Unit := do
  let (a::args, b::rest) := (xs,normalWord xs) | throw (IO.userError "empty marker product")
  let input := args.foldl (fun acc f => plus acc f.term) a.term
  let nf := rest.foldl (fun acc f => plus acc f.term) b.term
  emit .markers "reduce" "exact" [input,nf]

def markerCoverage : IO Unit := do
  for rule in rules .markers do
    emit .markers "rule" "oriented" [rule.lhs,rule.rhs]
  let mut words : List (List Factor) := [[]]
  for _ in [:4] do
    words := words.flatMap fun w => [.red,.blue,.name,.message].map (fun f => f::w)
    for w in words do markerCase w
  for w in [[.fresh,.fresh,.red,.red], [.red,.blue,.fresh,.red,.blue,.red],
      [.blue,.blue,.blue,.blue,.message,.message], [.fresh,.name,.fresh,.name]] do
    markerCase w
  -- A reducible child and a reducible parent require nested one-step coverage.
  let inner := plus blue (plus x blue)
  emit .markers "reduce" "exact"
    [plus red (plus (hash inner) red), plus red (hash (plus x blue))]
  -- Ordinary reduction treats x as rigid. Variant generation must also
  -- explain substitutions that introduce new marker occurrences at this head.
  for fixedSlot in [hash x,plus red red] do
    emit .markers "variants" "identity" [fixedSlot,x]
  for (active,count) in [(plus x red,3), (plus x x,7), (plus x y,13), (plus (plus red x) blue,7)] do
    emit .markers "variants" ("rows=" ++ toString count) [active,x]

/-- Serialize the same DH expression language used by the rule proofs. Leaves
refer to ordinary sorted terms, so repeated occurrences share caller variables. -/
def dhCode {α} (leaf : α → String) : DHPeer.Expr α → String
  | .var a => leaf a
  | .pow a b => dhCode leaf a ++ "." ++ dhCode leaf b ++ ".pow"
  | .mul a b => dhCode leaf a ++ "." ++ dhCode leaf b ++ ".+"
  | .inv a => dhCode leaf a ++ ".inv"
  | .one => "one"
  | .neutral => "neutral"

def dhCoverage : IO Unit := do
  let emitDH (op expect : String) (ts : List (DHPeer.Expr Expr)) :=
    IO.println (String.intercalate "\t" (["dh",op,expect] ++ ts.map (dhCode code)))
  let g : DHPeer.Expr Expr := .var (.atom false)
  let m : DHPeer.Expr Expr := .var x
  let n : DHPeer.Expr Expr := .var y
  let r : DHPeer.Expr Expr := .var (.var ⟨0,.fresh⟩)
  for rule in [DHPeer.Rule.expOne,.tower,.neutral,.inverse,.inverseRest,.inside,.insideRest] do
    let slot := fun (i : Fin 3) => code (if i.val = 0 then x else if i.val = 1 then y else .var ⟨0,.fresh⟩)
    IO.println (String.intercalate "\t" ["dh","reduce","exact",
      dhCode slot rule.equation.1, dhCode slot rule.equation.2])
  let tower := DHPeer.Expr.pow (.pow g m) r
  for (t,count) in [(DHPeer.Expr.pow g m,2), (.pow m r,7), (.inv r,1), (.inv m,4), (.mul m r,6),
      (.mul m m,4), (.mul m n,47), (.pow (.pow g m) (.inv r),6), (.mul m (.inv r),6), (.inv (.mul m r),8)] do
    emitDH "variants" ("rows=" ++ toString count) [t,m]
  emitDH "variants" "rows=12" [tower,.pow g n]
  emitDH "variants" "rows=14" [tower,.pow (.pow g m) (.var (.atom true))]
  for t in [DHPeer.Expr.pow m n, .pow (.pow g m) n, .pow g (.mul m n)] do
    emitDH "variants" "rows=48" [t,m]
  emitDH "variants" "probe-rows=160" [.pow (.pow n m) r,m]
  for t in [DHPeer.Expr.pow g r,.inv r,.mul r r] do
    for op in ["unify","match"] do
      emitDH op "yes" [m,t,m,t]
      emitDH op "no" [m,t,m,.neutral]

def generate : IO Unit := do
  markerCoverage
  dhCoverage
  for th in [Theory.ac,.xor] do
    let terms := layers th 5
    for layer in terms do
      for t in layer do
        if !(t.checkSort .msg) then throw (IO.userError "ill-sorted coverage term")
        let ctor := constructorOnly th t
        emit th "reduce" (if ctor then "identity" else "complete") [t]
        emit th "variants" (variantExpectation th [t,t]) [t,t]
    -- Cross one constructor boundary beyond the exhaustive node budget.
    -- The outer sum can still cancel a hash against a caller-supplied factor.
    if th == .xor then
      for outer in [x,y,hash x] do
        for inner in [plus x (.atom false),plus y (.atom true),plus x y] do
          let t := plus outer (hash inner)
          emit th "variants" (variantExpectation th [t,inner]) [t,inner]
      -- Wider correlated instances also exercise ordinary unifier and search budgets.
      for a in [x,y] do
        emit th "variants" "complete" [plus (.var ⟨0,.fresh⟩) (plus a (hash (plus x y)))]
    -- Joint node budget for an ordinary equation. Operands on the right
    -- of a matching request remain rigid, including their variables.
    for leftSize in [1:5] do
      for rightSize in [1:6-leftSize] do
        for p in terms[leftSize]! do
          for s in terms[rightSize]! do
            emit th "unify" "probe" [p,s]
            emit th "match" (if matchClash p s then "no" else "probe") [p,s]
            emit th "variants" (variantExpectation th [p,s]) [p,s]
    -- Ground words admit an independent exact answer under both theories.
    let words : List (List sig.Atom) := [[false],[true],[false,false],[false,true],[true,false],
      [true,true],[false,false,false],[true,false,true]]
    for l in words do
      for r in words do
        let expected := if groundAnswer l r then "yes" else "no"
        let a := FlatAC.term () l
        let b := FlatAC.term () r
        for op in ["unify","match"] do
          emit th op expected [a,b]
          emit th op expected [x,a,x,b]
          emit th op expected [hash x,hash a,hash x,hash b]

  -- Compose active operations from the mixed table in both orders. Each
  -- pack observes the outer value alongside its changing argument.
  for inner in [first x,second x,plus x (.atom false),hash (plus x y)] do
    for outer in [first inner,second inner,plus y inner,plus inner (hash inner)] do
      emit .xorPair "variants" "complete" [outer,inner]
      emit .xorPair "reduce" "complete" [outer]
  -- A rigid pair in the outer AC product contains two correlated inner sums.
  -- Vary which inner variable also appears as an outer collector.
  for a in [x,y] do
    let child := pair (plus (.atom true) x) (plus x y)
    emit .xorPair "variants" "complete" [plus (.var ⟨0,.fresh⟩) (plus a child)]
  emit .xorPair "reduce" "complete" [first (pair x y)]
  emit .xorPair "variants" "complete" [first x,second x]

end Tamarin.NativeCoverage

def main : IO Unit := Tamarin.NativeCoverage.generate
