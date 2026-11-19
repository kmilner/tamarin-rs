import Tamarin.PairingRewriting
import TamarinRuntime.Interface

namespace Tamarin.Pairing

/-- Fixed interpretation of the numeric recipes; invalid codes are failures,
never empty complete answer sets. -/
def decodeConstructors (code : UInt8) : Option (List PSubst) :=
  if code = 1 then some [Substitution.identity] else none

def decodeVariants (code : UInt8) (split : PSubst) : Option (List PSubst) :=
  if code = 1 then some [Substitution.identity]
  else if code = 3 then some [Substitution.identity, split] else none

def decodeProject (code : UInt8) (a b : PTerm) : Option PTerm :=
  if code = 1 then some a else if code = 2 then some b else none

end Pairing
open Pairing

/-- Semantic contract of the recipe ABI. Coverage includes normalized nonground
substitutions. Validity and completeness are required of the decoded answers;
output safety requires fresh, distinct message parameters. -/
structure PairingBackend.Correct (backend : PairingBackend) : Prop where
  constructors : ∀ (q : List PTerm) (_hq : ∀ t ∈ q, Constructor t) (avoid : List Variable),
    ∃ answers, decodeConstructors (backend.variants false) = some answers ∧
      CompleteVariants q answers ∧ ∀ σ ∈ answers, OutputSafe q avoid σ
  projections : ∀ (first : Bool) (x a b : Variable)
    (hx : x.sort = .msg) (ha : a.sort = .msg) (hb : b.sort = .msg)
    (_hab : a ≠ b) (_hax : a ≠ x) (_hbx : b ≠ x)
    (q : List PTerm) (_hq : ProjectionQuery first x q) (_hqx : Observed q x)
    (avoid : List Variable) (_haa : a ∉ avoid) (_hba : b ∉ avoid),
    ∃ answers, decodeVariants (backend.variants true) (splitSubst x a b hx ha hb) = some answers ∧
      CompleteVariants q answers ∧ ∀ σ ∈ answers, OutputSafe q avoid σ
  normalization : ∀ (first : Bool) (a b : PTerm) (_ha : Normal a) (_hb : Normal b),
    ∃ t, decodeProject (backend.project first) a b = some t ∧
      Reduces (projection first (pair a b)) t ∧ Normal t

/-- Completeness forces both bits for the current scalar ABI. Derive this
from the semantic contract so users of the mask need no knowledge of the
selected candidate's implementation. -/
theorem PairingBackend.Correct.openMask {backend : PairingBackend} (h : backend.Correct) :
    backend.variants true = 3 := by
  let x : Variable := ⟨0, .msg⟩
  let a : Variable := ⟨1, .msg⟩
  let b : Variable := ⟨2, .msg⟩
  let q := [fst (.var x)]
  have hq : ProjectionQuery true x q := fun t ht => Or.inr (List.mem_singleton.mp ht)
  have occurs : Observed q x := ⟨_, List.mem_singleton_self _, 0, rfl⟩
  obtain ⟨answers, hd, hc, _⟩ := h.projections true x a b rfl rfl rfl
    (by decide) (by decide) (by decide) q hq occurs [] (by simp) (by simp)
  by_cases full : backend.variants true = 3
  · exact full
  by_cases ident : backend.variants true = 1
  · simp [decodeVariants, ident] at hd
    subst answers
    let σ := splitSubst x a b rfl rfl rfl
    obtain ⟨arm, ha, δ, _, _, values⟩ := hc.2 σ (split_normalized x a b rfl rfl rfl)
    obtain rfl := List.mem_singleton.mp ha
    have e := values _ (List.mem_singleton_self _)
    have hx : σ.image x = pair (.var a) (.var b) := Substitution.binding_image_self ..
    change normalize (fst (σ.image x)) = δ.apply (normalize (fst (.var x))) at e
    rw [hx] at e
    exact nomatch e
  · simp [decodeVariants, ident, full] at hd

/-- The linked recipe kernel must also inhabit the shared, algorithm-independent
rewriting/variant contract. The older specialized obligations remain required. -/
structure PairingBackend.SharedCorrect (backend : PairingBackend) : Prop where
  constructors : ∀ (q : List PTerm) (_hq : ∀ t ∈ q, Constructor t) (avoid : List Variable),
    ∃ answers, decodeConstructors (backend.variants false) = some answers ∧
      Rewriting.CompleteVariants root q (answers.map (referenceVariant q)) ∧
      ∀ σ ∈ answers, (referenceVariant q σ).Safe q avoid
  projections : ∀ (first : Bool) (x a b : Variable)
    (hx : x.sort = .msg) (ha : a.sort = .msg) (hb : b.sort = .msg)
    (_hab : a ≠ b) (_hax : a ≠ x) (_hbx : b ≠ x)
    (q : List PTerm) (_hq : ProjectionQuery first x q) (_hqx : Observed q x)
    (avoid : List Variable) (_haa : a ∉ avoid) (_hba : b ∉ avoid),
    ∃ answers, decodeVariants (backend.variants true) (splitSubst x a b hx ha hb) = some answers ∧
      Rewriting.CompleteVariants root q (answers.map (referenceVariant q)) ∧
      ∀ σ ∈ answers, (referenceVariant q σ).Safe q avoid
  normalization : ∀ (first : Bool) (a b : PTerm) (_ha : Normal a) (_hb : Normal b),
    ∃ t, decodeProject (backend.project first) a b = some t ∧
      Rewriting.NormalForm root (projection first (pair a b)) t

theorem PairingBackend.Correct.shared {backend : PairingBackend} (h : backend.Correct) :
    backend.SharedCorrect := by
  constructor
  · intro q hq avoid
    obtain ⟨answers, he, hc, hs⟩ := h.constructors q hq avoid
    exact ⟨answers, he, variants_refine hc, fun σ hσ => safe_refine (hs σ hσ)⟩
  · intro first x a b hx ha hb hab hax hbx q hq hqx avoid haa hba
    obtain ⟨answers, he, hc, hs⟩ := h.projections first x a b hx ha hb hab hax hbx q hq hqx avoid haa hba
    exact ⟨answers, he, variants_refine hc, fun σ hσ => safe_refine (hs σ hσ)⟩
  · intro first a b ha hb
    obtain ⟨t, he, hr, hn⟩ := h.normalization first a b ha hb
    exact ⟨t, he, normalForm_of_reduces hr hn⟩

end Tamarin
