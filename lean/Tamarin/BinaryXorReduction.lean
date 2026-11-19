import Tamarin.BinaryXorNormal
import Tamarin.RulePresentation

namespace Tamarin.Rewriting.BinaryXor
open Cancellation ACRepresentation
variable {sig : Signature} (T : Table sig)
noncomputable section
open Classical

private theorem value_reps (xs : List (Term sig)) : EquivB (T.value xs) (assemble T (xs.map classOf)) := by
  cases xs with
  | nil => exact .refl _
  | cons a as =>
    induction as generalizing a with
    | nil => exact Quotient.exact (rep_key (classOf a)).symm
    | cons b bs ih => exact .ac_congr T.f (Quotient.exact (rep_key (classOf a)).symm) (ih b)

abbrev ParityKernel := UInt64 → Bool

/-- On canonical operands, one word counts one equivalence class of whole
terms. The active unit is omitted independently of its multiplicity. -/
def Reduction (run : ParityKernel) : Prop :=
  ∀ {s : Signature} (T : Table s) (live : List (Equation s)) (_ : RulePresentation.Same T.rules live)
    (a b : Term s) (xs ys : List (Term s)),
    (∀ t ∈ a::b::xs, (HasSort t .msg ∧ Normal (ruleRoot live) t) ∧ T.bag t = [classOf t]) →
    (ys.map classOf).Nodup → ∀ (count : Class s → UInt64),
    (∀ k, k ≠ T.zeroClass → (count k).toNat = ((a::b::xs).map classOf).count k) →
    (∀ k, k ∈ ys.map classOf ↔ k ≠ T.zeroClass ∧ run (count k) = true) →
    ∀ u, NormalForm (ruleRoot live) (T.value (a::b::xs)) u ↔ EquivB u (T.value ys)

theorem reduction {run} (kernel : ∀ n, run n = true ↔ n.toNat % 2 = 1) : Reduction run := by
  intro s T live presentation a b xs ys good nd count exactCount selected u
  rw [← presentation.forms]
  rw [← presentation.normal] at good
  have facts k (h : k ∈ (a::b::xs).map classOf) : Fact T k := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
    obtain ⟨gx,ax⟩ := good x hx
    exact fact_of_mem T gx (ax ▸ List.mem_cons_self)
  have layout : T.bag (T.value (a::b::xs)) = (a::b::xs).map classOf :=
    fold_classes T (fun t h => (good t h).2)
  have normal := parity_normalForm T
    (value_typed T (a::b::xs) (fun t h => (good t h).1.1)) T.fSort
    (fun k hk => facts k (layout ▸ hk)) nd
    (fun z => ((selected _).mp z).1 rfl)
  have nf := normal (fun k ne => by
    rw [layout,← exactCount k ne]
    by_cases h : k ∈ ys.map classOf
    · rw [nd.count_of_mem h,(kernel _).mp ((selected k).mp h).2]
    · rw [List.count_eq_zero.mpr h]
      have even : (count k).toNat % 2 ≠ 1 := fun e => h ((selected _).mpr ⟨ne,(kernel _).mpr e⟩)
      omega) u
  exact nf.trans ⟨fun e => e.trans (value_reps T ys).symm,fun e => e.trans (value_reps T ys)⟩

end
end Tamarin.Rewriting.BinaryXor
