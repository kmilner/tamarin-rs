import Tamarin.DHExponent

/-! Symbolic arm soundness for a free message exponent. The residuals are
fresh message variables while the positive factor retains its caller syntax. -/
namespace Tamarin.Rewriting.DHExponent
open DHPeer ConstructorVariants DHTower Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- Symbolic output terms and input images are irreducible before the caller
instantiates its witnesses. The positive witness must differ from the other
residual and from the distinguished positive factor. -/
theorem symbolic (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (y p n : Variable) (r : Term sig)
    (sy : HasSort (.var y : Term sig) .msg) (sp : HasSort (.var p : Term sig) .msg)
    (sn : HasSort (.var n : Term sig) .msg) (sr : HasSort r .msg) (nr : Normal (ruleRoot T.rules) r)
    (factor : Factor s r) (pn : p ≠ n) (pr : ¬EquivB (.var p) r) (k : Branch) :
    let v := env (.var y) r (.var p) (.var n)
    Normal (ruleRoot T.rules) (k.image.eval s v) ∧ Realizes s (ruleRoot T.rules) (k.image.eval s v) r k v := by
  let v := env (.var y) r (.var p) (.var n)
  let R := ruleRoot T.rules
  have vars := (constructor_normal _ pow.1).1
  have varPos (w : Variable) (sw : HasSort (.var w : Term sig) .msg) : Positive s R (.var w) :=
    .factor sw (vars _) (by constructor <;> intro eq <;> cases eq)
  have rp : Positive s R r := .factor sr nr factor
  have np := varPos n sn
  have pp := varPos p sp
  have nrp := np.mul mul rp
  have invNormal {u : Term sig} (pos : Positive s R u) : Normal R (s.product.inv u) :=
    inv.normal_positive pos.normal pos.noUnit pos.noInv
  have mixed {u : Term sig} (pos : Positive s R u) (apart : classOf (.var p) ∉ Cancellation.flatten s.mul u) :
      Normal R (s.product.mul (.var p) (s.product.inv u)) := by
    apply (assembled_normal mul inv unit (p := some (.var p)) (n := some u) _ _ _).2.1
    · intro w h; cases h; exact pp
    · intro w h; cases h; exact pos
    · intro key h1 h2; exact apart ((List.mem_singleton.mp h2) ▸ h1)
  have apartR : classOf (.var p) ∉ Cancellation.flatten s.mul r := by
    rw [factor.single]
    exact fun h => pr (Quotient.exact (List.mem_singleton.mp h))
  have apartN : classOf (.var p : Term sig) ∉ Cancellation.flatten s.mul (.var n) :=
    fun h => pn (Head.var.inj (Quotient.exact (List.mem_singleton.mp h)).head_eq)
  have apartNR : classOf (.var p) ∉ Cancellation.flatten s.mul (s.product.mul (.var n) r) := by
    change classOf (.var p) ∉ Cancellation.flatten s.mul (.ac s.mul (.var n) r)
    rw [Cancellation.flatten_ac]
    exact fun h => (List.mem_append.mp h).elim apartN apartR
  have normal : Normal R (k.image.eval s v) ∧ Normal R (k.result.eval s v) := by
    cases k with
    | unchanged => exact ⟨vars _,((varPos y sy).mul mul rp).normal⟩
    | unit => exact ⟨unit,nr⟩
    | cancelPositive => exact ⟨mixed rp apartR,vars _⟩
    | cancelAll => exact ⟨invNormal rp,unit⟩
    | cancelMixed => exact ⟨mixed nrp apartNR,mixed np apartN⟩
    | cancelNegative => exact ⟨invNormal nrp,invNormal np⟩
  have typed : ∀ i, HasSort (v i) .msg := by intro i; cases i <;> assumption
  have laws := E.presentation.roots.laws
  have red : Reduces R (s.product.mul (k.image.eval s v) r) (k.result.eval s v) := by
    cases k with
    | unchanged => exact .basis (.refl _)
    | unit => exact .step ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule r sr),.refl _⟩
    | cancelPositive => exact laws.cancelWith _ _ sp sr
    | cancelAll => exact laws.cancel _ sr
    | cancelMixed => exact laws.cancelBoth _ _ _ sp sn sr
    | cancelNegative => exact laws.cancelInside _ _ sn sr
  refine ⟨normal.1,typed,?_,.refl _,⟨red,normal.2,fun _ h =>
    .widen (k.result.sorted _ _ typed) (s.mulSort ▸ Term.rootSort_le h)⟩,?_,?_⟩
  · intro i; cases i <;> first | exact nr | exact vars _
  · cases k <;> constructor <;> intro h <;> first
      | rfl
      | exact (invNotUnit s _ h).elim
      | cases h
  · cases k <;> constructor <;> intro h <;> first
      | rfl
      | exact (factor.nonUnit h).elim
      | exact (invNotUnit s _ h).elim
      | cases h

end Tamarin.Rewriting.DHExponent
