import Tamarin.MatchingConjunction
import Tamarin.RootNormalForms
import Tamarin.RuleAtHead
import TamarinRuntime.Candidate

namespace Tamarin.Rewriting.RootExclusion
open ConstructorVariants

/-- Every rule in the bucket must have a rigid argument incompatible with the
subject. A malformed row or an all-wildcard matching row must prevent exclusion. -/
def Correct (run : Array (Array UInt64) → Array UInt64 → Bool) : Prop :=
  ∀ rows args, run rows args = true ↔ ∀ row ∈ rows, row.size = args.size ∧
    ∃ i : Fin row.size, row[i] ≠ 0 ∧ row[i] ≠ args[i.val]!

theorem correct : Correct RuntimeCandidate.excludeRoot := by
  intro rows args
  simp only [RuntimeCandidate.excludeRoot, Array.all_eq_true_iff_forall_mem,
    Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  apply forall_congr'
  intro row
  apply forall_congr'
  intro _
  by_cases h : row.size = args.size
  · simp only [h, true_and, Array.isEqv_eq_decide, dite_true]
    simp [h, Fin.exists_iff, Bool.or_eq_true] <;> grind
  · simp [h]

variable {s : Signature}

/-- A rule variable can match a subject headed by any operator. Only an
application in the pattern requires a particular operator at that position. -/
def required (code : Head s → UInt64) (t : Term s) : UInt64 :=
  match t with
  | .var _ | .atom _ => 0
  | _ => code (head t)

private theorem survives (code : Head s → UInt64) (p : Term s) (σ : Substitution s) :
    required code p ≠ 0 → required code p = code (head (σ.apply p)) := by
  cases p <;> simp [required] <;> intros <;> rfl

/-- A certificate about argument heads proves irreducibility modulo B for
the whole free application once the children are normal. The bucket may contain
arbitrary right sides and overlapping rules. Code collisions can only defer. -/
theorem normal {run} (hc : Correct run) (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.FreeSym) (xs : Fin (s.arity f) → Term s)
    (children : ∀ i, Normal (ruleRoot rules) (xs i)) (code : Head s → UInt64)
    (rows : Array (Array UInt64))
    (allRules : ∀ p rhs, (⟨.free f p, rhs⟩ : Equation s) ∈ rules →
      (Array.ofFn fun i => required code (p i)) ∈ rows)
    (ok : run rows (Array.ofFn fun i => code (head (xs i))) = true) :
    NormalForm (ruleRoot rules) (.free f xs) (.free f xs) := by
  refine ⟨.basis (.refl _), normal_free_no_root children ?_, fun _ h => h⟩
  intro ys hy b root
  obtain ⟨p, rhs, mem, σ, eq, _⟩ := (ruleRoot_free_iff rules f apps ys b).mp root
  obtain ⟨_, i, nz, clash⟩ := (hc ..).mp ok _ (allRules p rhs mem)
  let j : Fin (s.arity f) := ⟨i.val, by simpa using i.isLt⟩
  have actual : head (xs j) = head (σ.apply (p j)) := (eq j) ▸ (hy j).head_eq
  have nonzero : required code (p j) ≠ 0 := by simpa [j] using nz
  have bound : i.val < (Array.ofFn fun k => code (head (xs k))).size := by simpa only [Array.size_ofFn] using j.isLt
  rw [getElem!_pos (Array.ofFn fun k => code (head (xs k))) i.val bound] at clash
  exact clash (by simpa [j] using
    (survives code (p j) σ nonzero).trans (congrArg code actual.symm))

/-- A concrete free application with normal children is normal when complete
rigid-subject matching refutes every rule at its head, including nonlinear
patterns. Rule variables may share names with the subject. -/
theorem normal_of_empty_matches (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (children : ∀ i, Normal (ruleRoot rules) (xs i))
    (empty : ∀ p rhs, (⟨.free f p,rhs⟩ : Equation s) ∈ rules →
      Matching.Complete [⟨.free f p,.free f xs⟩] (fun _ => True) []) :
    Normal (ruleRoot rules) (.free f xs) := by
  classical
  apply normal_free_no_root children
  intro ys eqv b root
  obtain ⟨p,rhs,mem,σ,eq,_⟩ := (ruleRoot_free_iff rules f apps ys b).mp root
  let q : Problem s := [⟨.free f p,.free f xs⟩]
  have hm : Matching.Matches q σ := by
    intro e he
    obtain rfl : e = _ := List.mem_singleton.mp he
    exact .free _ _ _ fun i => by simpa only [eq i, Substitution.apply] using (eqv i).symm
  exact ((empty p rhs mem).exists_match_iff.mp ⟨σ,hm⟩) rfl

end Tamarin.Rewriting.RootExclusion
