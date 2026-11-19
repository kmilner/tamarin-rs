import Tamarin.DHPeerProduct
import Tamarin.DHProductCanonical

namespace Tamarin.Rewriting.DHPeer.Balance
open ConstructorVariants DHProduct
variable {sig : Signature} {s : Symbols sig}

theorem splitInv (s : Symbols sig) {t : Term sig} (h : head t = .free s.inv) : ∃ x, t = s.product.inv x := by
  cases t <;> cases h
  rename_i xs
  let j : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  refine ⟨xs j, congrArg (Term.free s.inv) (funext fun i => congrArg xs (Fin.ext ?_))⟩
  have hi := i.isLt
  have ar := s.invArity
  change i.val = 0
  omega

private def double (a b : Term sig) (i : Fin 3) := if i = 0 then a else b

private theorem sorts {a b : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) :
    ∀ i, HasSort (double a b i) .msg := by intro i; unfold double; split <;> assumption

/-- A normal inverse cannot contain a unit or a negative factor anywhere
among the positive factors of its argument. Exposing a single occurrence
requires grouping arbitrary AC factors; the remaining subgroup stays typed. -/
theorem plain_of_inverse [DecidableEq sig.ACSym] {T : Table s} (E : ExtraTable T) {n : Term sig}
    (typed : HasSort (s.product.inv n) .msg) (normal : Normal (ruleRoot T.rules) (s.product.inv n)) :
    Plain s (ruleRoot T.rules) n := by
  have sn := E.presentation.invChild n typed
  let idx : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  have nn : Normal (ruleRoot T.rules) n := normal_free_child s.inv _ normal idx
  intro u hu
  have split := DHProduct.extract s.mul s.mulSort n u sn nn hu
  have su : HasSort u .msg := s.mulSort ▸ ACRepresentation.flatten_hasSort s.mul n (s.mulSort ▸ sn) u hu
  have fire {rhs x : Term sig} (h : EquivB n x) (root : ruleRoot T.rules (s.product.inv x) rhs) : False :=
    normal rhs ⟨_,_,E.presentation.invCongr h,.root root,.refl _⟩
  refine ⟨((subgroup_normal_iff s.mul n).mp nn).1 _ hu,?_,?_⟩
  · intro head
    obtain ⟨x,rfl⟩ := splitInv s head
    have sx := E.presentation.invChild x su
    rcases split with eq|⟨rem,eq,sr,_⟩
    · exact fire eq (E.fireRoot .invInv _ (sorts sx sx))
    · exact fire (eq.trans (.ac_swap ..)) (E.fireRoot .pull _ (sorts sx sr))
  · intro head
    obtain rfl : u = s.product.one := DHPeer.nullary s.oneArity head
    rcases split with eq|⟨rem,eq,sr,_⟩
    · exact fire eq (E.fireRoot .invOne _ (sorts sn sn))
    · exact nn _ ⟨_,_,eq,.root (E.presentation.unitRule rem sr),.refl _⟩

end Tamarin.Rewriting.DHPeer.Balance
