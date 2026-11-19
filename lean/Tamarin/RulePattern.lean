import Tamarin.ConstructorVariants
import Tamarin.MatchingFree

/-! Properties of rule patterns used when narrowing against a finite table.
Variables in a free pattern can repeat, and their images may themselves
contain arbitrary free, commutative and associative-commutative terms. -/
namespace Tamarin.Rewriting.RulePattern
variable {sig : Signature}

/-- A pattern with positionally distinguishable arguments. -/
inductive Free : Term sig → Prop
  | var (v) : Free (.var v)
  | atom (a) : Free (.atom a)
  | free (f args) : (∀ i, Free (args i)) → Free (.free f args)

/-- A free pattern determines the images of all its variables modulo B.
No linearity assumption is needed, even for repeated occurrences in
different argument positions. -/
theorem image_equiv {t : Term sig} {σ τ : Substitution sig} {v : Variable}
    (ht : Free t) (he : EquivB (σ.apply t) (τ.apply t)) (hv : t.Occurs v) :
    EquivB (σ.image v) (τ.image v) := by
  induction ht with
  | var w => obtain rfl := hv; exact he
  | atom => exact False.elim hv
  | free f args _ ih =>
    obtain ⟨i, hi⟩ := hv
    exact ih i ((Matching.free_equiv_iff f _ _).mp he i) hi

/-- Normality of an instantiated pattern implies normality of each variable
image appearing in it, including below a C or AC node. This implication
does not require its operators to be constructors. -/
theorem image_normal {R : Root sig} {t : Term sig} {σ : Substitution sig} {v : Variable}
    (hn : Normal R (σ.apply t)) (hv : t.Occurs v) : Normal R (σ.image v) := by
  induction t with
  | var w => obtain rfl := hv; exact hn
  | atom => exact False.elim hv
  | free f args ih =>
    obtain ⟨i, hi⟩ := hv
    exact ih i (normal_free_child f _ hn i) hi
  | comm f a b ia ib =>
    obtain ⟨ha, hb⟩ := normal_comm_children f hn
    exact hv.elim (ia ha) (ib hb)
  | ac f a b ia ib =>
    obtain ⟨ha, hb⟩ := normal_ac_children f hn
    exact hv.elim (ia ha) (ib hb)

end Tamarin.Rewriting.RulePattern
