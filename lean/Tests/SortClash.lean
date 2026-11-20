import TamarinCI

namespace Tamarin.SortClashTests

private abbrev sig : Signature := { Pairing.signature with acSort := fun _ => .nat }
private def one : Term sig := .atom (1, .nat)
private def v (s : SortId) : Variable := ⟨0, s⟩
private def sum (x : Term sig) : Term sig := Term.ac 0 x one

-- The open Msg factor can become a Nat without changing its declared sort.
example : ∃ σ : Substitution sig, EquivB (σ.apply (sum (.var (v .msg)))) (sum one) := by
  let σ := Substitution.binding (v .msg) one (HasSort.widen (.atom _) Subsort.nat_msg)
  exact ⟨σ, by simp [σ, sum, one, Substitution.binding, Substitution.apply, Term.subst, EquivB.refl]⟩

-- An ill-sorted product can unify with another ill-sorted product. This
-- solution swaps the factors and retains the same unbound Fresh variable.
example : let x := (Term.var (v .fresh) : Term sig)
    EquivB (sum x) (.ac 0 one x) ∧ ¬ HasSort (sum x) .nat := by
  intro x
  refine ⟨.ac_swap .., ?_⟩
  intro h
  have bad := Term.checkSort_complete h
  contradiction

private def probe := [Term.var (v .fresh), sum (.var (v .fresh))]

example (avoid : List Variable) :
    let answer : Rewriting.Variant sig := ⟨Substitution.identity, probe⟩
    Rewriting.CompleteVariants (Rewriting.ruleRoot []) probe [answer] ∧ answer.Safe probe avoid ∧
      answer.Reconstructible (Rewriting.ruleRoot []) probe := by
  apply MaudeOperations.VariantReply.singleton_iff.mp
  apply exportedConstructorVariant_semantic [] probe #[] #[1] (fun _ => 1)
  · simp
  · simp [Rewriting.ConstructorVariants.ruleHeads]
  · simp
  · exact (exportedConstructorVariant_correct _ _).mpr (by simp)

-- The same early rejection now runs on complete terms in the mixed solver.
example : CompleteSet [⟨sum (.var (v .fresh)), .var (v .msg)⟩] [] :=
  NarrowingClash.refutes (by decide_cbv)

-- Evaluate sort membership independently for every pair of profiles of
-- length 1–4. At the two extremal assignments every unknown factor becomes
-- Nat or every unknown factor becomes Fresh. These give all possible
-- truth values for the conjunction of the children's Nat memberships.
private def rows : Nat → List (List UInt64)
  | 0 => [[]]
  | n+1 => (rows n).flatMap fun r => [0,1,2].map (· :: r)

private def inhabits (r : List UInt64) (unknownIsNat : Bool) :=
  r.all fun w => if w == 0 then unknownIsNat else w == 1

private def product (codes : List UInt64) (id : Nat) : Term sig :=
  codes.foldr (fun code rest =>
    let factor := if code == 0 then .var ⟨id, .msg⟩ else if code == 1 then one else .var ⟨id, .fresh⟩
    Term.ac 0 factor rest) one

def stress : IO Unit := do
  let samples := [1,2,3,4].flatMap rows
  for a in samples do
    for b in samples do
      let overlap := [false,true].any fun x =>
        [false,true].any fun y => inhabits a x == inhabits b y
      if NarrowingClash.impossible ⟨product a 0,product b 1⟩ == overlap then
        throw (IO.userError s!"incorrect sort clash for {a} and {b}")
  IO.println s!"{samples.length * samples.length} pairs of nonempty sort profiles"

end Tamarin.SortClashTests

def main := Tamarin.SortClashTests.stress
