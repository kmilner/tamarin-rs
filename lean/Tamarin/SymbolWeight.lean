import Tamarin.TableDecrease

/-! A nonnegative weight per operator gives a substitution-independent termination
check for entire rule tables. C and AC rearrangements preserve the sum. -/
namespace Tamarin.SymbolWeight
open Rewriting ConstructorVariants
variable {s : Signature}

private abbrev model (w : Head s → Nat) : Model s where
  Carrier := Nat
  atom := fun a => w (.atom a)
  free := fun f xs => (List.ofFn xs).sum + w (.free f)
  comm := fun f a b => a + b + w (.comm f)
  ac := fun f a b => a + b + w (.ac f)
  comm_swap := by intros; omega
  ac_swap := by intros; omega
  ac_assoc := by intros; omega

def rank (w : Head s → Nat) (t : Term s) : Nat := (model w).eval (fun _ => (0 : Nat)) t

theorem substituted (w : Head s → Nat) (ρ : Substitution s) (t : Term s) :
    rank w (ρ.apply t) = rank w t + (t.variables.map (fun v => rank w (ρ.image v))).sum := by
  let extra := fun v => rank w (ρ.image v)
  induction t with
  | var v => change extra v = 0 + ([v].map extra).sum; simp
  | atom a => rfl
  | ac f a b ia ib | comm f a b ia ib =>
    change rank w (ρ.apply a) + rank w (ρ.apply b) + _ = rank w a + rank w b + _ +
      (((a.variables ++ b.variables).map extra).sum)
    rw [ia,ib,List.map_append,List.sum_append]; dsimp only [extra]; omega
  | free f xs ih =>
    change (List.ofFn fun i => rank w (ρ.apply (xs i))).sum + _ = (List.ofFn fun i => rank w (xs i)).sum + _ +
      (((List.ofFn (fun i => (xs i).variables)).flatten.map extra).sum)
    simp only [List.map_flatten,List.map_ofFn,UnifierSize.sum_flat,Function.comp_def]
    rw [show (fun i => rank w (ρ.apply (xs i))) =
      (fun i => rank w (xs i) + ((xs i).variables.map extra).sum) from funext ih, UnifierSize.sum_parts]
    omega

/-- If normalized images contain no positive weight, the rank of an open
query bounds every normalized instance, including nonground instances. -/
theorem rank_apply {R : Root s} {w : Head s → Nat}
    (zero : ∀ {u}, Normal R u → rank w u = 0) (ρ : Substitution s) (norm : Normalized R ρ) (t : Term s) :
    rank w (ρ.apply t) = rank w t := by
  rw [substituted]
  simp [fun v => zero (norm v),List.sum_eq_zero_iff_forall_eq_nat]

def decreasing (w : Head s → Nat) (rs : List (Equation s)) : Bool :=
  rs.all fun r => rank w r.rhs < rank w r.lhs && TableDecrease.nonduplicating r

theorem bound {w : Head s → Nat} {rs : List (Equation s)} (ok : decreasing w rs) : ReferenceReduction.Bound rs :=
  TableDecrease.bound_of_nonduplicating fun r hr => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok r hr)).2

private theorem inside_lt {w : Head s → Nat} {rs : List (Equation s)} (ok : decreasing w rs) {a b}
    (one : Step (ruleRoot rs) a b) : rank w b < rank w a := by
  induction one with
  | root fire =>
    obtain ⟨r,mem,σ,rfl,rfl⟩ := fire
    rw [substituted,substituted]
    obtain ⟨smaller,linear⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok _ mem)
    exact Nat.add_lt_add_of_lt_of_le (of_decide_eq_true smaller) (UnifierSize.weighted_le _ _ _ (TableDecrease.counts linear))
  | @free f xs i u st ih =>
    change (List.ofFn (fun j => rank w (if j = i then u else xs j))).sum + w (.free f) <
      (List.ofFn (fun j => rank w (xs j))).sum + w (.free f)
    apply Nat.add_lt_add_right
    apply TableDecrease.sum_lt i
    · simpa using ih
    · intro j ne; simp [ne]
  | ac_left _ _ _ ih | comm_left _ _ _ ih => exact Nat.add_lt_add_right (Nat.add_lt_add_right ih _) _
  | ac_right _ _ _ ih | comm_right _ _ _ ih => exact Nat.add_lt_add_right (Nat.add_lt_add_left ih _) _

theorem step_lt {w : Head s → Nat} {rs : List (Equation s)} (ok : decreasing w rs) {a b}
    (st : StepModulo (ruleRoot rs) a b) : rank w b < rank w a := by
  obtain ⟨l,r,before,one,after⟩ := st
  have left : rank w a = rank w l := before.eval_eq (model w) _
  have right : rank w r = rank w b := after.eval_eq (model w) _
  rw [left,← right]
  exact inside_lt ok one

theorem terminating {w : Head s → Nat} {rs : List (Equation s)} (ok : decreasing w rs) :
    WellFounded (fun b a => StepModulo (ruleRoot rs) a b) :=
  Subrelation.wf (fun h => step_lt ok h) (measure (rank w)).wf

end Tamarin.SymbolWeight
