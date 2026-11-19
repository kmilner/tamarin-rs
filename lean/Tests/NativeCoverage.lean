import Tamarin.ConstructorReduction
import Tamarin.MatchingFree
import Tamarin.SortCheck
import Tamarin.VariableElimination

/-! Generate well-sorted algebra requests directly from the specification. Each
line carries its active theory, operation, expectation and postfix term(s).
The public Rust adapter consumes this test format. -/
namespace Tamarin.NativeCoverage
open Rewriting ConstructorVariants

inductive Symbol where | hash | zero
  deriving DecidableEq

abbrev sig : Signature where
  FreeSym := Symbol
  CSym := Empty
  ACSym := Unit
  Atom := Bool
  arity := fun | .hash => 1 | .zero => 0
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

inductive Theory where | ac | xor
  deriving DecidableEq

def rules : Theory → List (Equation sig)
  | .ac => []
  | .xor => [⟨plus x zero,x⟩, ⟨plus x x,zero⟩, ⟨plus x (plus x y),y⟩]

private def sameHead : DecidableEq (Head sig) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

def constructorOnly (th : Theory) (t : Expr) : Bool :=
  !(operators t).any fun f => (ruleHeads (rules th)).any fun g => @decide _ (sameHead f g)

/-- The mandatory constructor cases have an identity variant for every
normalized valuation. Adding repeated observations preserves this fact. -/
theorem constructor_family (th : Theory) (ts : List Expr) (safe : ∀ t ∈ ts, constructorOnly th t = true) :
    CompleteVariants (ruleRoot (rules th)) ts [⟨Substitution.identity, ts⟩] := by
  apply (identity_variants (rules th) ts ?_ ?_ []).1
  · cases th <;> simp [rules,Application,plus]
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
  · cases th <;> simp [rules, Application, plus]
  · change ¬ List.Mem (Head.free (sig := sig) .hash) (ruleHeads (rules th))
    cases th <;> intro h <;> repeat' cases ‹List.Mem _ _›

def code : Expr → String
  | .var v => (if v.sort == .fresh then "f" else "m") ++ toString v.id
  | .atom b => if b then "b" else "a"
  | .free .hash args => code (args 0) ++ ".h"
  | .free .zero _ => "z"
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
  let name := if th == .ac then "ac" else "xor"
  IO.println (String.intercalate "\t" ([name,op,expected] ++ ts.map code))

def generate : IO Unit := do
  for th in [Theory.ac,.xor] do
    let terms := layers th 5
    for layer in terms do
      for t in layer do
        if !(t.checkSort .msg) then throw (IO.userError "ill-sorted coverage term")
        let ctor := constructorOnly th t
        emit th "reduce" (if ctor then "identity" else "complete") [t]
        emit th "variants" (if ctor then "identity" else "probe") [t,t]
    -- Joint node budget for an ordinary equation. Operands on the right
    -- of a matching request remain rigid, including their variables.
    for leftSize in [1:5] do
      for rightSize in [1:6-leftSize] do
        for p in terms[leftSize]! do
          for s in terms[rightSize]! do
            emit th "unify" "probe" [p,s]
            emit th "match" (if matchClash p s then "no" else "probe") [p,s]
            emit th "variants" (if constructorOnly th p && constructorOnly th s then "identity" else "probe") [p,s]
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

end Tamarin.NativeCoverage

def main : IO Unit := Tamarin.NativeCoverage.generate
